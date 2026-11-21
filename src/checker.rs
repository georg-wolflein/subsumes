use serde_json::Value;

use crate::context::Context;
use crate::normalize::{self, Cause, Outcome};
use crate::{Error, Reason, RegexDialect, Verdict, inspect, lower, schema};

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
        self.check(a, b).map(|(verdict, _)| verdict)
    }

    /// The verdict of [`subsumes`](Self::subsumes) with the steps of the budget that the
    /// check spent. The steps are for the tests of the budget and no part of the API: they
    /// end a check and are no measure of it.
    pub(crate) fn check(&self, a: &Value, b: &Value) -> Result<(Verdict, u64), Error> {
        let graph = schema::parse(a, b)?.link()?;
        let mut context = Context::new(self.budget, self.regex_dialect);
        let outcome = lower::lower(&graph, &mut context)
            .and_then(|(a, b)| normalize::decide(&mut context, a, b));
        let verdict = match outcome {
            Ok(Outcome::Yes) => Verdict::Yes,
            Ok(Outcome::No(counterexample)) => Verdict::No { counterexample },
            Ok(Outcome::Unknown(Cause::Number | Cause::Depth)) => Verdict::Unknown {
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
        Ok((verdict, context.budget.spent()))
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

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::Side;

    #[test]
    fn a_check_gives_one_of_three_verdicts() {
        let checker = Checker::new();
        let (text, optional) = (
            json!({"type": "string"}),
            json!({"type": ["string", "null"]}),
        );
        assert_eq!(checker.subsumes(&optional, &text).unwrap(), Verdict::Yes);

        let counterexample = json!(null);
        assert_eq!(
            checker.subsumes(&text, &optional).unwrap(),
            Verdict::No { counterexample }
        );

        // The engine does not model `uniqueItems`, and says which keyword stands in the way.
        let (list, set) = (
            json!({"type": "array"}),
            json!({"type": "array", "uniqueItems": true}),
        );
        assert_eq!(
            checker.subsumes(&set, &list).unwrap(),
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::A,
                    location: "#/uniqueItems".to_owned(),
                },
            }
        );
    }

    #[test]
    fn draft_2020_12_is_accepted_with_and_without_the_empty_fragment() {
        let draft_2020_12 = "https://json-schema.org/draft/2020-12/schema";
        for dialect in [draft_2020_12.to_owned(), format!("{draft_2020_12}#")] {
            let schema = json!({"$schema": dialect});
            assert!(Checker::new().subsumes(&schema, &schema).is_ok());
        }
    }

    #[test]
    fn another_dialect_is_an_error_that_names_the_side() {
        let draft_07 = json!({"$schema": "http://json-schema.org/draft-07/schema#"});
        let error = Checker::new().subsumes(&json!({}), &draft_07).unwrap_err();
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
            let error = Checker::new().subsumes(&value, &json!(true)).unwrap_err();
            assert_eq!(error, Error::NotASchema { schema: Side::A });
        }
    }

    #[test]
    fn both_schemas_are_loaded_before_anything_is_answered() {
        let checker = Checker::new();
        let invalid = json!({"properties": {"age": {"minimum": "0"}}});
        assert_eq!(
            checker.subsumes(&json!({}), &invalid).unwrap_err(),
            Error::InvalidKeyword {
                schema: Side::B,
                location: "#/properties/age/minimum".to_owned(),
                message: "must be a number".to_owned(),
            }
        );
        let dangling = json!({"items": {"$ref": "#/$defs/item"}});
        assert_eq!(
            checker.subsumes(&dangling, &json!({})).unwrap_err(),
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
            Checker::new().subsumes(&alone, &json!(true)),
            Err(Error::UnresolvedReference { .. })
        ));
        let bundled = json!({"$ref": uri, "$defs": {"name": {"$id": uri, "type": "string"}}});
        assert!(Checker::new().subsumes(&bundled, &alone).is_err());
        assert!(Checker::new().subsumes(&bundled, &bundled).is_ok());
    }
}
