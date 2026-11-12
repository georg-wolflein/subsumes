use std::collections::BTreeMap;
use std::sync::{Arc, OnceLock};

use serde_json::Value;

use crate::schema::{self, Documents};
use crate::{Error, Reason, Side, Verdict};

/// The work budget of the Python version; to be set anew once there is an engine to measure.
const DEFAULT_BUDGET: u64 = 500_000;

/// The settings of a check: its work budget and the documents that references may point to.
///
/// A checker does not change while it checks, so one can be shared between threads.
///
/// ```
/// use serde_json::json;
/// use subsumes::Checker;
///
/// let checker = Checker::new()
///     .budget(100_000)
///     .resource("https://example.com/name.json", json!({"type": "string"}));
///
/// let a = json!({"$ref": "https://example.com/name.json"});
/// let b = json!({"type": "string", "minLength": 1});
/// let verdict = checker.subsumes(&a, &b)?;
/// # Ok::<(), subsumes::Error>(())
/// ```
#[derive(Debug, Clone)]
pub struct Checker {
    budget: u64,
    resources: BTreeMap<String, Arc<Value>>,
    /// The resources as the load stage needs them, indexed at the first check.
    documents: OnceLock<Result<Documents, Error>>,
}

impl Checker {
    /// A checker with the default work budget and no documents.
    #[must_use]
    pub fn new() -> Self {
        Self {
            budget: DEFAULT_BUDGET,
            resources: BTreeMap::new(),
            documents: OnceLock::new(),
        }
    }

    /// Sets the work budget of one check, in steps. A check that needs more returns
    /// [`Verdict::Unknown`] with [`Reason::Budget`].
    #[must_use]
    pub fn budget(mut self, steps: u64) -> Self {
        self.budget = steps;
        self
    }

    /// Adds a document that a `$ref` in either schema may point to, under its URI. Nothing is
    /// ever fetched: a reference resolves to the schema itself, to a document added here or to
    /// a meta-schema of the draft.
    ///
    /// A document is read only when a reference leads to it. One that is then not a valid
    /// schema is an [`Error`] of that check.
    #[must_use]
    pub fn resource(mut self, uri: &str, document: Value) -> Self {
        self.resources.insert(uri.to_owned(), Arc::new(document));
        self.documents = OnceLock::new();
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
        let unlinked = schema::parse(a, b)?;
        // A schema without references needs nothing but itself, so no index is built for it.
        let scope = |side, schema| {
            if unlinked.has_references(side) {
                self.documents()?.scope(side, schema).map(Some)
            } else {
                Ok(None)
            }
        };
        let (scope_a, scope_b) = (scope(Side::A, a)?, scope(Side::B, b)?);
        let _graph = unlinked.link(scope_a.as_ref(), scope_b.as_ref())?;
        // Without an engine nothing is supported, so the whole of A is the construct in the way.
        Ok(Check {
            verdict: Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::A,
                    location: "#".to_owned(),
                },
            },
            steps: 0,
        })
    }

    fn documents(&self) -> Result<&Documents, Error> {
        let documents = self
            .documents
            .get_or_init(|| Documents::new(&self.resources));
        documents.as_ref().map_err(Error::clone)
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

    #[test]
    fn every_check_is_unknown_for_now() {
        let check = Checker::new()
            .check(&json!({"type": "integer"}), &json!(true))
            .unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::A,
                    location: "#".to_owned(),
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
    fn a_reference_resolves_to_a_document_of_the_checker() {
        let uri = "https://example.com/name.json";
        let schema = json!({"$ref": uri});
        let checker = Checker::new();
        assert!(matches!(
            checker.check(&schema, &json!(true)),
            Err(Error::UnresolvedReference { .. })
        ));
        // A document added after a check is seen by the next one.
        let checker = checker.resource(uri, json!({"type": "string"}));
        assert!(checker.check(&schema, &schema).is_ok());
    }

    #[test]
    fn documents_that_cannot_be_used_fail_the_checks_that_need_them() {
        let checker = Checker::new().resource("not a uri", json!({}));
        assert!(checker.check(&json!({}), &json!(true)).is_ok());
        let error = checker
            .check(&json!({"$ref": "#"}), &json!(true))
            .unwrap_err();
        assert!(matches!(error, Error::InvalidDocuments { .. }), "{error:?}");
    }
}
