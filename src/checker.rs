use serde_json::Value;

use crate::context::Context;
use crate::normalize::{self, Cause, Outcome};
use crate::{Error, Reason, Verdict, inspect, lower, schema};

/// The work budget of the Python version; to be set anew once there is an engine to measure.
const DEFAULT_BUDGET: u64 = 500_000;

/// The settings of a check. So far that is its work budget.
///
/// A checker does not change while it checks, so one can be shared between threads.
///
/// ```
/// use serde_json::json;
/// use subsumes::Checker;
///
/// let checker = Checker::new().budget(100_000);
///
/// let a = json!({"type": "string"});
/// let b = json!({"type": "string", "minLength": 1});
/// let verdict = checker.subsumes(&a, &b)?;
/// # Ok::<(), subsumes::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct Checker {
    budget: u64,
}

impl Checker {
    /// A checker with the default work budget.
    #[must_use]
    pub fn new() -> Self {
        Self {
            budget: DEFAULT_BUDGET,
        }
    }

    /// Sets the work budget of one check, in steps. A check that needs more returns
    /// [`Verdict::Unknown`] with [`Reason::Budget`].
    #[must_use]
    pub fn budget(mut self, steps: u64) -> Self {
        self.budget = steps;
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
        let graph = schema::parse(a, b)?.link()?;
        // What a `$dynamicRef` accepts depends on the schemas that led to it, which the terms
        // do not say yet.
        if let Some(node) = lower::dynamic_reference(&graph) {
            let reason = Reason::Unsupported {
                schema: graph.node(node).side,
                location: graph.keyword_location(node, "$dynamicRef"),
            };
            return Ok(Check {
                verdict: Verdict::Unknown { reason },
                steps: 0,
            });
        }
        let mut context = Context::new(self.budget);
        let outcome = lower::lower(&graph, &mut context)
            .and_then(|(a, b)| normalize::decide(&mut context, a, b));
        let verdict = match outcome {
            Ok(Outcome::Yes) => Verdict::Yes,
            Ok(Outcome::No(counterexample)) => Verdict::No { counterexample },
            Ok(Outcome::Unknown(Cause::Number)) => Verdict::Unknown {
                reason: Reason::Unrepresentable,
            },
            Ok(Outcome::Unknown(Cause::Leaf(leaf))) => {
                let leaf = context.terms.leaf(leaf);
                let reason = Reason::Unsupported {
                    schema: graph.node(leaf.node).side,
                    location: leaf.location(&graph),
                };
                Verdict::Unknown { reason }
            }
            Err(_) => Verdict::Unknown {
                reason: Reason::Budget,
            },
        };
        Ok(Check {
            verdict,
            steps: context.budget.spent(),
        })
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
        let mut context = Context::new(self.budget);
        // Without the budget for them there are no terms to show.
        let roots = lower::lower(&graph, &mut context).ok();
        Ok(inspect::stages(&graph, &context.terms, roots))
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

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::Side;

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

        // The engine does not model strings yet, and says which keyword stands in the way.
        let named = json!({"type": "string", "minLength": 1});
        let check = checker.check(&named, &text).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::A,
                    location: "#/minLength".to_owned(),
                },
            }
        );
    }

    #[test]
    fn a_check_that_reaches_a_dynamic_reference_is_unknown_and_names_it() {
        // Through `a` the dynamic reference leads to a schema that accepts everything, and
        // through `d` alone to one that accepts nothing. So B accepts everything, and terms
        // that give the reference one meaning would make B a schema and its own negation.
        let b = json!({
            "$id": "https://example.com/root",
            "$ref": "a",
            "not": {"$ref": "d"},
            "$defs": {
                "d": {
                    "$id": "d",
                    "$dynamicRef": "#x",
                    "$defs": {"x": {"$dynamicAnchor": "x", "not": {}}},
                },
                "a": {
                    "$id": "a",
                    "$ref": "d",
                    "$defs": {"x": {"$dynamicAnchor": "x"}},
                },
            },
        });
        let check = Checker::new().check(&json!(false), &b).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::B,
                    location: "#/$defs/d/$dynamicRef".to_owned(),
                },
            }
        );
        assert_eq!(check.steps, 0);
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
}
