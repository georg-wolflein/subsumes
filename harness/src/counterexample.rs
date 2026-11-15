//! Whether a counterexample is one.
//!
//! The library returns the counterexample of a `No` unchecked: it holds no validator. Here a
//! validator is asked, the `jsonschema` crate. The counterexample must be valid under the
//! narrow schema, whose instances were to be accepted, and invalid under the wide schema,
//! which was to accept them.
//!
//! The validator reads the schemas as the library does: as draft 2020-12, with `format`
//! asserted, and with every pattern in the dialect of the `regex` crate, which the
//! [`patterns`] module sees to.
//!
//! What a format accepts, the validator works out with code of its own, and the library with
//! a pattern for each format that it models. So a counterexample that is a string holds the
//! two against each other. No string is known on which they differ. Whether a time with the
//! second 60 is one, the library leaves open and gives no such string.

use jsonschema::{Draft, PatternOptions, Validator};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::patterns;

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
        .build(&patterns::spelled_out(schema))
        .map_err(|error| format!("the validator does not take a schema: {error}"))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn the_validator_reads_a_large_float_as_the_whole_number_that_it_holds() {
        // 2^60 + 256, which a float holds and prints as a number that ends in 200. A whole
        // number between the two is less than the float.
        let least = validator(&json!({"minimum": 1.152_921_504_606_847_2e18})).unwrap();
        assert!(least.is_valid(&json!(1_152_921_504_606_847_232_u64)));
        assert!(!least.is_valid(&json!(1_152_921_504_606_847_210_u64)));
        // -2^63, which is printed as a number that ends in 000 and is less.
        let least = validator(&json!({"minimum": -9.223_372_036_854_776e18})).unwrap();
        assert!(least.is_valid(&json!(i64::MIN)));
        let most = validator(&json!({"maximum": i64::MIN})).unwrap();
        assert!(most.is_valid(&json!(-9.223_372_036_854_776e18)));
    }

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
    fn the_validator_reads_a_format_as_the_library_does() {
        let formats = [
            "date",
            "time",
            "date-time",
            "duration",
            "uuid",
            "ipv4",
            "ipv6",
            "uri",
            "uri-reference",
            "json-pointer",
            "relative-json-pointer",
        ];
        let nothing = json!(false);
        let mut of_the_format = 0;
        for format in formats {
            for least in [0, 1, 2, 5, 9, 10, 11, 20, 21, 36, 37, 45, 60] {
                // The shortest string of the format that is this long, if the format has one:
                // the validator must take it for one too.
                let narrow = json!({"type": "string", "format": format, "minLength": least});
                let verdict = subsumes::subsumes(&nothing, &narrow).unwrap();
                if let subsumes::Verdict::No { counterexample } = verdict {
                    assert_eq!(
                        confirmation(&nothing, &narrow, &counterexample),
                        Confirmation::Confirmed,
                        "{counterexample} for {format}"
                    );
                    of_the_format += 1;
                }
                // And a string this long that is not of the format.
                let (wide, narrow) = (
                    json!({"format": format}),
                    json!({"type": "string", "minLength": least}),
                );
                let subsumes::Verdict::No { counterexample } =
                    subsumes::subsumes(&wide, &narrow).unwrap()
                else {
                    panic!("every string of {least} characters is of the format {format}");
                };
                assert_eq!(
                    confirmation(&wide, &narrow, &counterexample),
                    Confirmation::Confirmed,
                    "{counterexample} against {format}"
                );
            }
        }
        // Most formats have a string of most of these lengths.
        assert!(of_the_format > 80, "{of_the_format}");
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
    fn a_pattern_matches_what_it_matches_in_the_regex_crate() {
        // Each of these says something else in ECMA 262, which the validator reads by itself:
        // the classes of Unicode, the line ends, the operations on classes, the flags.
        let patterns = [
            r"^\d$",
            r"^\D$",
            r"^\w+$",
            r"^\W$",
            r"^\s$",
            r"^\S*$",
            "^.$",
            "(?s)^.$",
            r"^[\d-]+$",
            r"^[a-z&&[^b]]$",
            r"^[\w--\d]$",
            r"^[a-c~~b-d]$",
            r"^[[:alpha:]&]$",
            r"[^\s\S]",
            r"\P{any}",
            r"^\a$",
            "(?i)^straße$",
            "(?x) ^ a b $ # and no more",
            r"^\p{Greek}+$",
            r"a\b",
        ];
        let strings = [
            "",
            "3",
            "٣",
            "a",
            "b",
            "d",
            "é",
            "_",
            "&",
            "-",
            "~",
            "[",
            " ",
            "\n",
            "\r",
            "\u{7}",
            "\u{85}",
            "\u{feff}",
            "\u{2028}",
            "ab",
            "a b",
            "a-",
            "3-٣",
            "STRASSE",
            "Straße",
            "λόγος",
        ];
        for pattern in patterns {
            let expected = regex::Regex::new(pattern).unwrap();
            let validator = validator(&json!({"pattern": pattern})).unwrap();
            let names = validator_of_names(pattern);
            for string in strings {
                let matches = expected.is_match(string);
                assert_eq!(
                    validator.is_valid(&json!(string)),
                    matches,
                    "{pattern:?} on {string:?}"
                );
                // The same pattern as a key of `patternProperties`, with the name as the string.
                assert_eq!(
                    names.is_valid(&json!({string: null})),
                    matches,
                    "{pattern:?} on the name {string:?}"
                );
            }
        }
    }

    /// Accepts an object whose names all match the pattern, by way of `patternProperties`.
    fn validator_of_names(pattern: &str) -> Validator {
        let schema = json!({"patternProperties": {pattern: true}, "additionalProperties": false});
        validator(&schema).unwrap()
    }

    #[test]
    fn a_pattern_is_read_so_wherever_a_reference_leads() {
        // To the `regex` crate, and so to the library, `\d` is any digit of Unicode.
        let digit = json!({
            "$ref": "#/types/digit",
            "types": {"digit": {"pattern": r"^\d$"}},
        });
        assert_eq!(
            confirmation(&json!(false), &digit, &json!("٣")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&json!({"pattern": "^[0-9]$"}), &digit, &json!("٣")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&digit, &json!(true), &json!("٣")),
            Confirmation::AcceptedByWide
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
