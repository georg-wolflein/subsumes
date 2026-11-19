use std::fmt;

use serde_json::Value;

use crate::context::{Budget, Context, Exhausted};
use crate::normalize::{self, Cause, Outcome};
use crate::schema::Graph;
use crate::term::VarId;
use crate::{Error, Reason, RegexDialect, Side, Verdict, inspect, lower, schema};

/// The work budget of a check, unless another is set. It is there so that a check ends: one
/// that spends all of it takes a few seconds. How many steps a check takes is no measure of how
/// fast it is.
const DEFAULT_BUDGET: u64 = 10_000_000;

/// The settings of a check: its work budget, and the dialect that its patterns are read in.
///
/// A checker does not change while it checks, so one can be shared between threads.
///
/// ```
/// use serde_json::json;
/// use subsumes::{Checker, RegexDialect};
///
/// let checker = Checker::new()
///     .budget(100_000)
///     .regex_dialect(RegexDialect::Rust);
///
/// let a = json!({"type": "string"});
/// let b = json!({"type": "string", "minLength": 1});
/// let verdict = checker.subsumes(&a, &b)?;
/// # Ok::<(), subsumes::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct Checker {
    budget: u64,
    regex_dialect: RegexDialect,
}

impl Checker {
    /// A checker with the default work budget, 10 million steps, which is a few seconds of
    /// work at most, and that reads patterns as ECMA-262 does.
    #[must_use]
    pub fn new() -> Self {
        Self {
            budget: DEFAULT_BUDGET,
            regex_dialect: RegexDialect::default(),
        }
    }

    /// Sets the work budget of one check, in steps. A check that needs more returns
    /// [`Verdict::Unknown`] with [`Reason::Budget`].
    #[must_use]
    pub fn budget(mut self, steps: u64) -> Self {
        self.budget = steps;
        self
    }

    /// Sets the dialect that every `pattern` and every key of `patternProperties` is read
    /// in, in both schemas. Without it that is [`RegexDialect::Ecma262`].
    #[must_use]
    pub fn regex_dialect(mut self, dialect: RegexDialect) -> Self {
        self.regex_dialect = dialect;
        self
    }

    /// Does `a` accept every instance that is valid under `b`?
    ///
    /// # Errors
    ///
    /// When `a` or `b` cannot be checked at all; see [`Error`].
    pub fn subsumes(&self, a: &Value, b: &Value) -> Result<Verdict, Error> {
        self.check(a, b).map(|check| check.verdict)
    }

    /// The same check as [`subsumes`](Self::subsumes), with the work it took.
    ///
    /// # Errors
    ///
    /// When `a` or `b` cannot be checked at all; see [`Error`].
    pub fn check(&self, a: &Value, b: &Value) -> Result<Check, Error> {
        self.check_with_converse(a, b).map(|(check, _)| check)
    }

    /// The same check as [`check`](Self::check), together with its converse: whether `b`
    /// subsumes `a`, which is checked when it is asked for. The two schemas accept the same
    /// instances when both verdicts are [`Verdict::Yes`].
    ///
    /// The two schemas are loaded once for both: parsed, their references resolved, and
    /// lowered to terms. The converse goes on with what the first check worked out about
    /// them, and pays for none of it again; see [`Converse`].
    ///
    /// ```
    /// use serde_json::json;
    /// use subsumes::{Checker, Verdict};
    ///
    /// let a = json!({"type": "integer", "minimum": 0});
    /// let b = json!({"type": "integer", "exclusiveMinimum": -1});
    /// let (a_subsumes_b, converse) = Checker::new().check_with_converse(&a, &b)?;
    /// let b_subsumes_a = converse.check();
    /// assert_eq!(a_subsumes_b.verdict, Verdict::Yes);
    /// assert_eq!(b_subsumes_a.verdict, Verdict::Yes);
    /// # Ok::<(), subsumes::Error>(())
    /// ```
    ///
    /// # Errors
    ///
    /// When `a` or `b` cannot be checked at all; see [`Error`].
    pub fn check_with_converse<'s>(
        &self,
        a: &'s Value,
        b: &'s Value,
    ) -> Result<(Check, Converse<'s>), Error> {
        let graph = schema::parse(a, b)?.link()?;
        let mut context = Context::new(self.budget, self.regex_dialect);
        let roots = lower::lower(&graph, &mut context);
        let mut converse = Converse {
            graph,
            context,
            roots,
            checker: self.clone(),
            a,
            b,
        };
        Ok((converse.decide(Side::A), converse))
    }

    /// What the library makes of the two schemas before it compares them, as JSON for a tool
    /// that shows it. There is one picture for each stage: the schema graph, with a node for
    /// every subschema, and the terms, with a node for every variable. A node has rows of what
    /// it says, and edges lead to the nodes it uses.
    ///
    /// The shape of the value follows the needs of such a tool and may change in any version.
    ///
    /// # Errors
    ///
    /// When `a` or `b` cannot be checked at all; see [`Error`].
    pub fn inspect(&self, a: &Value, b: &Value) -> Result<Value, Error> {
        let graph = schema::parse(a, b)?.link()?;
        let mut context = Context::new(self.budget, self.regex_dialect);
        // Without the budget for them there are no terms to show.
        let roots = lower::lower(&graph, &mut context).ok();
        Ok(inspect::stages(&graph, &context, roots))
    }
}

impl Default for Checker {
    fn default() -> Self {
        Self::new()
    }
}

/// A verdict together with the work it took.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct Check {
    /// The answer.
    pub verdict: Verdict,
    /// The steps of the work budget that the check spent. The count depends only on the two
    /// schemas and the settings, never on the machine, so two runs can be compared exactly.
    pub steps: u64,
}

/// The converse of a check: whether `b` subsumes `a`, after
/// [`Checker::check_with_converse`] has checked whether `a` subsumes `b`.
///
/// It answers the question of [`Checker::check`] with `b` and `a`, and is held to the same
/// standard: [`Verdict::Yes`] only where no instance of `a` is left that `b` does not
/// accept, and [`Verdict::No`] only with such an instance. It is not the same computation:
///
/// - **It has a budget of its own,** the whole budget of the checker, whatever the first
///   check spent.
/// - **Its steps are those of its own search.** What the first check built was paid for
///   there, and is not paid for again: the terms of the two schemas, the DFAs of their
///   patterns, how the names of their objects are cut, the languages of their
///   `propertyNames`, and which of them are definite. So it mostly takes fewer steps than a
///   check of `b` and `a` by themselves. Where the budget did not cover the terms, there is
///   nothing to go on with, and it ends at the budget too. What the first check found out
///   about values, whether a value satisfies a c-reference, is not taken over: an answer
///   found ready changes the way a search goes, and can cost it a verdict.
/// - **Its search may go another way.** Where it is free to choose, it goes by the order
///   in which the load met the schemas, which begins with `a` here and with `b` in a check
///   of its own, and the allowances of its tests are counted in the steps of its own
///   search. So it may also take more steps, and a counterexample may be another instance.
/// - **It decides at least what a check of its own decides.** Its search may end at the
///   budget or at a leaf where that of a check of `b` and `a` by themselves decides. So
///   where it decides nothing, `b` and `a` are checked by themselves, with a load and a
///   budget of their own, and the converse has the verdict of that check and the steps of
///   the two.
///
/// Its steps depend only on the two schemas, their order and the settings.
pub struct Converse<'s> {
    graph: Graph<'s>,
    context: Context,
    /// The variables of `a` and of `b`, unless the budget did not cover their terms.
    roots: Result<(VarId, VarId), Exhausted>,
    /// The checker of the first check, with the work budget of a check.
    checker: Checker,
    /// The two schemas, for a check of `b` and `a` by themselves.
    a: &'s Value,
    b: &'s Value,
}

impl Converse<'_> {
    /// Does `b` accept every instance that is valid under `a`?
    ///
    /// In the verdict `b` is the schema that should accept everything, as in a check of `b`
    /// and `a`: a [`Reason::Unsupported`] in `b` names it as [`Side::A`].
    #[must_use]
    pub fn check(mut self) -> Check {
        // The terms are made once and paid for once. Where the budget did not cover them,
        // there is nothing to go on with.
        if self.roots.is_ok() {
            self.context.budget = Budget::new(self.checker.budget);
        }
        let converse = self.decide(Side::B);
        if !matches!(converse.verdict, Verdict::Unknown { .. }) {
            return converse;
        }
        // The search of the converse may go another way than that of a check of its own,
        // and end at the budget or at a leaf where that one decides. So where it decides
        // nothing, `b` and `a` are checked by themselves, and the converse decides at least
        // what that check decides. Its steps are those of the two.
        let Self { checker, a, b, .. } = self;
        drop(self.graph);
        drop(self.context);
        match checker.check(b, a) {
            Ok(alone) => Check {
                verdict: alone.verdict,
                steps: converse.steps + alone.steps,
            },
            Err(_) => converse,
        }
    }

    /// Checks whether one schema of the load accepts every instance of the other. `wide`
    /// is the one that should accept everything.
    fn decide(&mut self, wide: Side) -> Check {
        let Self { graph, context, .. } = self;
        let outcome = self.roots.and_then(|(a, b)| match wide {
            Side::A => normalize::decide(context, a, b),
            Side::B => normalize::decide(context, b, a),
        });
        let verdict = match outcome {
            Ok(Outcome::Yes) => Verdict::Yes,
            Ok(Outcome::No(counterexample)) => Verdict::No { counterexample },
            Ok(Outcome::Unknown(Cause::Number | Cause::Depth)) => Verdict::Unknown {
                reason: Reason::Unrepresentable,
            },
            Ok(Outcome::Unknown(Cause::Leaf(leaf))) => {
                let leaf = context.terms.leaf(leaf);
                // A reason names a schema by its place in the check: the first argument or
                // the second.
                let schema = match (graph.node(leaf.node).side, wide) {
                    (side, Side::A) => side,
                    (Side::A, Side::B) => Side::B,
                    (Side::B, Side::B) => Side::A,
                };
                let location = leaf.location(graph);
                Verdict::Unknown {
                    reason: Reason::Unsupported { schema, location },
                }
            }
            Err(Exhausted) => Verdict::Unknown {
                reason: Reason::Budget,
            },
        };
        Check {
            verdict,
            steps: context.budget.spent(),
        }
    }
}

impl fmt::Debug for Converse<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Converse").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, json};

    use super::*;

    #[test]
    fn a_check_gives_one_of_three_verdicts_and_its_steps() {
        let checker = Checker::new();
        let (text, optional) = (
            json!({"type": "string"}),
            json!({"type": ["string", "null"]}),
        );
        let check = checker.check(&optional, &text).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        assert!(check.steps > 0);

        let check = checker.check(&text, &optional).unwrap();
        let counterexample = json!(null);
        assert_eq!(check.verdict, Verdict::No { counterexample });

        // The engine does not model `uniqueItems`, and says which keyword stands in the way.
        let (list, set) = (
            json!({"type": "array"}),
            json!({"type": "array", "uniqueItems": true}),
        );
        let check = checker.check(&set, &list).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::A,
                    location: "#/uniqueItems".to_owned(),
                },
            }
        );
    }

    #[test]
    fn subsumes_is_the_verdict_of_check() {
        let checker = Checker::new();
        let (a, b) = (json!({}), json!(false));
        assert_eq!(
            checker.subsumes(&a, &b).unwrap(),
            checker.check(&a, &b).unwrap().verdict
        );
    }

    #[test]
    fn draft_2020_12_is_accepted_with_and_without_the_empty_fragment() {
        let draft_2020_12 = "https://json-schema.org/draft/2020-12/schema";
        for dialect in [draft_2020_12.to_owned(), format!("{draft_2020_12}#")] {
            let schema = json!({"$schema": dialect});
            assert!(Checker::new().check(&schema, &schema).is_ok());
        }
    }

    #[test]
    fn another_dialect_is_an_error_that_names_the_side() {
        let draft_07 = json!({"$schema": "http://json-schema.org/draft-07/schema#"});
        let error = Checker::new().check(&json!({}), &draft_07).unwrap_err();
        assert_eq!(
            error,
            Error::UnsupportedDialect {
                schema: Side::B,
                location: "#/$schema".to_owned(),
                dialect: "http://json-schema.org/draft-07/schema#".to_owned(),
            }
        );
    }

    #[test]
    fn a_value_that_is_no_schema_is_an_error() {
        for value in [json!(null), json!(1), json!("string"), json!([])] {
            let error = Checker::new().check(&value, &json!(true)).unwrap_err();
            assert_eq!(error, Error::NotASchema { schema: Side::A });
        }
    }

    #[test]
    fn both_schemas_are_loaded_before_anything_is_answered() {
        let checker = Checker::new();
        let invalid = json!({"properties": {"age": {"minimum": "0"}}});
        assert_eq!(
            checker.check(&json!({}), &invalid).unwrap_err(),
            Error::InvalidKeyword {
                schema: Side::B,
                location: "#/properties/age/minimum".to_owned(),
                message: "must be a number".to_owned(),
            }
        );
        let dangling = json!({"items": {"$ref": "#/$defs/item"}});
        assert_eq!(
            checker.check(&dangling, &json!({})).unwrap_err(),
            Error::UnresolvedReference {
                schema: Side::A,
                location: "#/items/$ref".to_owned(),
                reference: "#/$defs/item".to_owned(),
            }
        );
    }

    #[test]
    fn a_schema_has_to_carry_what_it_references() {
        let uri = "https://example.com/name.json";
        let alone = json!({"$ref": uri});
        assert!(matches!(
            Checker::new().check(&alone, &json!(true)),
            Err(Error::UnresolvedReference { .. })
        ));
        let bundled = json!({"$ref": uri, "$defs": {"name": {"$id": uri, "type": "string"}}});
        assert!(Checker::new().check(&bundled, &alone).is_err());
        assert!(Checker::new().check(&bundled, &bundled).is_ok());
    }

    /// Pairs of schemas with each verdict in each direction.
    fn pairs() -> Vec<(Value, Value)> {
        let (text, optional) = (
            json!({"type": "string"}),
            json!({"type": ["string", "null"]}),
        );
        let integer = json!({"type": "integer"});
        let natural = json!({"type": "integer", "minimum": 0});
        let required = json!({"type": "object", "properties": {"p": integer}, "required": ["p"]});
        let one = json!({"type": "object", "properties": {"p": {"const": 1}}});
        let list = json!({
            "$defs": {
                "list": {
                    "type": ["object", "null"],
                    "properties": {"next": {"$ref": "#/$defs/list"}},
                },
            },
            "$ref": "#/$defs/list",
        });
        let short = json!({"type": "object", "properties": {"next": {"type": "null"}}});
        vec![
            (optional, text),
            (json!({"minimum": 0}), json!({"exclusiveMinimum": -1})),
            (integer, natural),
            (json!({"type": "array"}), json!({"uniqueItems": true})),
            (required, one),
            (list, short),
        ]
    }

    #[test]
    fn the_first_check_of_a_pair_is_the_check_itself() {
        let checker = Checker::new();
        for (a, b) in pairs() {
            let (check, _) = checker.check_with_converse(&a, &b).unwrap();
            assert_eq!(check, checker.check(&a, &b).unwrap(), "{a} {b}");
        }
    }

    #[test]
    fn the_converse_is_whether_b_subsumes_a() {
        let checker = Checker::new();
        for (a, b) in pairs() {
            let (_, converse) = checker.check_with_converse(&a, &b).unwrap();
            let converse = converse.check();
            assert_eq!(
                converse.verdict,
                checker.subsumes(&b, &a).unwrap(),
                "{a} {b}"
            );
        }
    }

    #[test]
    fn a_reason_of_the_converse_names_the_schemas_as_its_arguments() {
        // Only `b` has the keyword, and it is the first argument of the converse.
        let (a, b) = (
            json!({"type": "array"}),
            json!({"type": "array", "uniqueItems": true}),
        );
        let (check, converse) = Checker::new().check_with_converse(&a, &b).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        let reason = Reason::Unsupported {
            schema: Side::A,
            location: "#/uniqueItems".to_owned(),
        };
        assert_eq!(converse.check().verdict, Verdict::Unknown { reason });
    }

    #[test]
    fn the_converse_decides_what_a_check_of_its_own_decides_where_an_instance_is_deep() {
        // `y` is a chain of 119 objects or `null`. The first check finds the chain for it,
        // which is too deep to be put ten objects down in the second alternative of A. A
        // check of B subsumes A by itself hands `null` on to `y` from the first alternative
        // and gives an instance of the second. The converse does not take over the answers
        // of the first check, so it does the same.
        let mut definitions = Map::new();
        definitions.insert("d0".to_owned(), json!({"type": "object"}));
        for depth in 1..119 {
            let next = json!({"$ref": format!("#/$defs/d{}", depth - 1)});
            let link = json!({"type": "object", "required": ["n"], "properties": {"n": next}});
            definitions.insert(format!("d{depth}"), link);
        }
        let chain = json!({"$ref": "#/$defs/d118"});
        definitions.insert("y".to_owned(), json!({"anyOf": [chain, {"type": "null"}]}));
        let nothing = json!({"allOf": [{"type": "string"}, {"type": "number"}]});
        let y = json!({"$ref": "#/$defs/y"});
        let first = json!({
            "type": "object",
            "required": ["p", "r"],
            "properties": {"p": y, "r": nothing},
            "allOf": [{"not": {"properties": {"p": {"not": {"type": "null"}}}}}],
        });
        let mut down = json!({"type": "object", "required": ["v"], "properties": {"v": y}});
        for _ in 0..10 {
            down = json!({"type": "object", "required": ["w"], "properties": {"w": down}});
        }
        let second = json!({"type": "object", "required": ["m"], "properties": {"m": down}});
        let a = json!({"$defs": definitions, "anyOf": [first, second]});
        let b = json!({
            "$defs": definitions,
            "type": "object",
            "required": ["q"],
            "properties": {"q": y},
        });
        let checker = Checker::new();
        assert!(matches!(
            checker.subsumes(&b, &a).unwrap(),
            Verdict::No { .. }
        ));
        let (_, converse) = checker.check_with_converse(&a, &b).unwrap();
        assert!(matches!(converse.check().verdict, Verdict::No { .. }));
    }

    #[test]
    fn a_converse_that_decides_nothing_is_checked_by_itself() {
        // `b` holds a keyword that is not supported, on which the converse depends. It is
        // checked again by itself, and has the reason of that check and the steps of both.
        let (a, b) = (
            json!({"type": "array"}),
            json!({"type": "array", "uniqueItems": true}),
        );
        let checker = Checker::new();
        let alone = checker.check(&b, &a).unwrap();
        let (_, converse) = checker.check_with_converse(&a, &b).unwrap();
        let converse = converse.check();
        assert_eq!(converse.verdict, alone.verdict);
        assert!(converse.steps > alone.steps);
    }

    #[test]
    fn the_converse_has_a_budget_of_its_own() {
        // A string that the pattern does not match is found by way of its DFA, which this
        // budget does not cover. That everything accepts what the pattern matches takes no
        // DFA, and the converse is decided with the budget that the first check spent.
        let (a, b) = (json!({"pattern": "^(a|b)*a(a|b){10}$"}), json!({}));
        let small = Checker::new().budget(1_000);
        let (check, converse) = small.check_with_converse(&a, &b).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Budget
            }
        );
        assert_eq!(converse.check().verdict, Verdict::Yes);
    }

    #[test]
    fn the_converse_pays_for_no_dfa_that_the_first_check_built() {
        // Each direction needs the DFA of the pattern, of some 8,000 states: the first
        // looks for a string of twelve characters or more outside it, and the converse for
        // a shorter one inside it, of which there is none. Most of the work of a check of
        // the converse by itself is to build the DFA.
        let a = json!({"type": "string", "pattern": "^(a|b)*a(a|b){12}$"});
        let b = json!({"type": "string", "minLength": 12});
        let checker = Checker::new();
        let alone = checker.check(&b, &a).unwrap();
        assert_eq!(alone.verdict, Verdict::Yes);
        let (_, converse) = checker.check_with_converse(&a, &b).unwrap();
        let converse = converse.check();
        assert_eq!(converse.verdict, Verdict::Yes);
        assert!(
            converse.steps * 4 < alone.steps,
            "{} {}",
            converse.steps,
            alone.steps
        );
    }

    #[test]
    fn an_instance_that_the_first_check_found_costs_the_converse_no_verdict_for_its_depth() {
        // In the first check the value of `q` is a chain of 120 objects inside one another,
        // which is handed on from the value of `p`. In the converse the same schema is asked
        // of a value eight objects down, where the chain would make the object too deep to
        // give, and `null` is what a task of its own finds.
        let mut definitions = serde_json::Map::new();
        definitions.insert("V".to_owned(), json!({"type": ["object", "null"]}));
        definitions.insert("d0".to_owned(), json!({"type": "object"}));
        for depth in 1..120 {
            let inside = format!("#/$defs/d{}", depth - 1);
            let chain = json!({
                "type": "object",
                "required": ["n"],
                "properties": {"n": {"$ref": inside}},
            });
            definitions.insert(format!("d{depth}"), chain);
        }
        let b = json!({
            "$defs": definitions,
            "type": "object",
            "properties": {"q": {"$ref": "#/$defs/V"}},
            "anyOf": [
                {
                    "required": ["q", "p"],
                    "allOf": [
                        {"properties": {"p": {"$ref": "#/$defs/V"}}},
                        {"properties": {"p": {"$ref": "#/$defs/d119"}}},
                    ],
                },
                {"required": ["q"]},
            ],
        });
        let mut a = json!({
            "type": "object",
            "required": ["v"],
            "properties": {"v": {"type": ["object", "null"]}},
        });
        for _ in 0..8 {
            a = json!({"type": "object", "required": ["m"], "properties": {"m": a}});
        }
        let (check, converse) = Checker::new().check_with_converse(&a, &b).unwrap();
        let Verdict::No { counterexample } = check.verdict else {
            panic!("{:?}", check.verdict);
        };
        assert!(counterexample["q"]["n"].is_object(), "{counterexample}");
        let Verdict::No { counterexample } = converse.check().verdict else {
            panic!("the converse is decided");
        };
        let inside = (0..8).fold(&counterexample, |value, _| &value["m"]);
        assert_eq!(inside, &json!({"v": null}), "{counterexample}");
    }
}
