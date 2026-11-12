//! Whether a counterexample is one.
//!
//! The library returns the counterexample of a `No` unchecked: it holds no validator. Here a
//! validator is asked, the `jsonschema` crate. The counterexample must be valid under the
//! narrow schema, whose instances were to be accepted, and invalid under the wide schema,
//! which was to accept them.
//!
//! The validator reads the schemas as closely to the library as it can: as draft 2020-12,
//! with patterns matched by the `regex` crate and with `format` asserted. Two things it still
//! reads in its own way, which matter once a counterexample is a string that a pattern or a
//! format is about: it translates a pattern from ECMA 262 before the `regex` crate sees it,
//! and it has its own idea of each format.

use jsonschema::{Draft, PatternOptions, Validator};
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// What the validator makes of the counterexample of a `No`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Confirmation {
    /// The narrow schema accepts it and the wide schema rejects it.
    Confirmed,
    /// The narrow schema rejects it, so the wide schema did not have to accept it.
    RejectedByNarrow,
    /// The wide schema accepts it, so it does not tell the two apart.
    AcceptedByWide,
    /// The validator did not look at it, for the reason given.
    NotChecked(String),
}

impl Confirmation {
    /// Whether the validator found that the counterexample is none.
    pub fn is_refuted(&self) -> bool {
        matches!(self, Self::RejectedByNarrow | Self::AcceptedByWide)
    }
}

/// What a results file says that was written before counterexamples were checked.
impl Default for Confirmation {
    fn default() -> Self {
        Self::NotChecked("the run is older than the check of counterexamples".to_owned())
    }
}

/// Asks the validator about a counterexample.
pub fn confirmation(wide: &Value, narrow: &Value, counterexample: &Value) -> Confirmation {
    let validators = validator(narrow).and_then(|narrow| Ok((validator(wide)?, narrow)));
    match validators {
        Ok((_, narrow)) if !narrow.is_valid(counterexample) => Confirmation::RejectedByNarrow,
        Ok((wide, _)) if wide.is_valid(counterexample) => Confirmation::AcceptedByWide,
        Ok(_) => Confirmation::Confirmed,
        Err(refusal) => Confirmation::NotChecked(refusal),
    }
}

/// The validator of a schema, or why it does not take the schema.
fn validator(schema: &Value) -> Result<Validator, String> {
    jsonschema::options()
        .with_draft(Draft::Draft202012)
        .with_pattern_options(PatternOptions::regex())
        .should_validate_formats(true)
        .build(schema)
        .map_err(|error| format!("the validator does not take a schema: {error}"))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn a_counterexample_is_valid_under_the_narrow_schema_only() {
        let (wide, narrow) = (
            json!({"type": "string"}),
            json!({"type": ["string", "null"]}),
        );
        assert_eq!(
            confirmation(&wide, &narrow, &json!(null)),
            Confirmation::Confirmed
        );
        // The wide schema accepts a string as well.
        assert_eq!(
            confirmation(&wide, &narrow, &json!("")),
            Confirmation::AcceptedByWide
        );
        // The narrow schema accepts no number.
        assert_eq!(
            confirmation(&wide, &narrow, &json!(0)),
            Confirmation::RejectedByNarrow
        );
        // One that is nothing at all: the narrow schema is asked first.
        let anything = json!(true);
        assert_eq!(
            confirmation(&anything, &narrow, &json!(0)),
            Confirmation::RejectedByNarrow
        );
        assert!(Confirmation::RejectedByNarrow.is_refuted());
        assert!(Confirmation::AcceptedByWide.is_refuted());
        assert!(!Confirmation::Confirmed.is_refuted());
        assert!(!Confirmation::default().is_refuted());
    }

    #[test]
    fn the_validator_follows_references_and_boolean_schemas() {
        let list = json!({
            "$ref": "#/$defs/list",
            "$defs": {"list": {"type": ["array", "null"], "items": {"$ref": "#/$defs/list"}}},
        });
        assert_eq!(
            confirmation(&json!(false), &list, &json!([[null], []])),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&json!(false), &list, &json!([[0]])),
            Confirmation::RejectedByNarrow
        );
        // A schema that refers to the meta-schema of the draft carries it, as the library does.
        let schema = json!({"$ref": "https://json-schema.org/draft/2020-12/schema"});
        assert_eq!(
            confirmation(&json!(false), &schema, &json!({"type": "string"})),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&json!(false), &schema, &json!({"type": 1})),
            Confirmation::RejectedByNarrow
        );
    }

    #[test]
    fn a_format_is_asserted() {
        let (anything, date) = (json!(false), json!({"format": "date"}));
        assert_eq!(
            confirmation(&anything, &date, &json!("2026-11-12")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&anything, &date, &json!("yesterday")),
            Confirmation::RejectedByNarrow
        );
        // A format says nothing about what is no string.
        assert_eq!(
            confirmation(&anything, &date, &json!(0)),
            Confirmation::Confirmed
        );
    }

    #[test]
    fn a_pattern_is_one_of_the_regex_crate() {
        // A search, as the draft says: the pattern may match anywhere.
        let (anything, pattern) = (json!(false), json!({"pattern": "b+"}));
        assert_eq!(
            confirmation(&anything, &pattern, &json!("abba")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&anything, &pattern, &json!("aa")),
            Confirmation::RejectedByNarrow
        );
        // The `regex` crate has no look-around, so the validator does not take the schema
        // and the counterexample goes unchecked, whichever of the two schemas it is.
        let look_ahead = json!({"pattern": "a(?=b)"});
        for (wide, narrow) in [(&anything, &look_ahead), (&look_ahead, &json!(true))] {
            let Confirmation::NotChecked(why) = confirmation(wide, narrow, &json!("ab")) else {
                panic!("the validator took a pattern with a look-ahead");
            };
            assert!(
                why.starts_with("the validator does not take a schema: "),
                "{why}"
            );
        }
    }

    #[test]
    fn a_pattern_is_read_as_ecma_262_first() {
        // To the `regex` crate, and so to the library, `\d` is any digit of Unicode. The
        // validator makes `[0-9]` of it, as ECMA 262 has it. No counterexample depends on
        // that yet; this test is here to fail when the validator changes its mind.
        let (anything, digit) = (json!(false), json!({"pattern": "^\\d$"}));
        assert_eq!(
            confirmation(&anything, &digit, &json!("3")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&anything, &digit, &json!("٣")),
            Confirmation::RejectedByNarrow
        );
    }

    #[test]
    fn nothing_is_fetched() {
        let elsewhere = json!({"$ref": "https://example.com/schema.json"});
        assert!(matches!(
            confirmation(&json!(false), &elsewhere, &json!(null)),
            Confirmation::NotChecked(_)
        ));
    }

    #[test]
    fn a_confirmation_is_one_word_in_the_results() {
        let written = |confirmation: &Confirmation| serde_json::to_value(confirmation).unwrap();
        assert_eq!(written(&Confirmation::Confirmed), json!("confirmed"));
        assert_eq!(
            written(&Confirmation::RejectedByNarrow),
            json!("rejected_by_narrow")
        );
        assert_eq!(
            written(&Confirmation::AcceptedByWide),
            json!("accepted_by_wide")
        );
        let unchecked = Confirmation::NotChecked("why".to_owned());
        assert_eq!(written(&unchecked), json!({"not_checked": "why"}));
        for confirmation in [Confirmation::Confirmed, unchecked] {
            let read: Confirmation = serde_json::from_value(written(&confirmation)).unwrap();
            assert_eq!(read, confirmation);
        }
    }
}
