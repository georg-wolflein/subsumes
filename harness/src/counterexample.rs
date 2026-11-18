//! Whether a counterexample is one.
//!
//! The library returns the counterexample of a `No` unchecked: it holds no validator. Here a
//! validator is asked, the `jsonschema` crate. The counterexample must be valid under the
//! narrow schema, whose instances were to be accepted, and invalid under the wide schema,
//! which was to accept them.
//!
//! The validator reads the schemas as the library does by default: as draft 2020-12, with
//! `format` asserted, and with every pattern as one of ECMA-262.
//!
//! What a format accepts, the validator works out with code of its own, and the library with
//! a pattern for each format that it models. So a counterexample that is a string holds the
//! two against each other. No string is known on which they differ. Whether a time with the
//! second 60 is one, the library leaves open and gives no such string.

use jsonschema::{Draft, Validator};
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
        .should_validate_formats(true)
        .build(schema)
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
    fn the_validator_follows_the_dynamic_scope_as_the_library_does() {
        // A list whose items are what the schema that led to it says they are, in a
        // document that says what `root` says and has these definitions besides.
        let lists = |root: Value, more: Value| {
            let mut document = json!({
                "$id": "https://example.com/root",
                "$defs": {
                    "strings": {
                        "$id": "strings",
                        "$ref": "list",
                        "$defs": {"item": {"$dynamicAnchor": "item", "type": "string"}},
                    },
                    "list": {
                        "$id": "list",
                        "type": "array",
                        "items": {"$dynamicRef": "#item"},
                        "$defs": {"item": {"$dynamicAnchor": "item"}},
                    },
                },
            });
            for (keyword, value) in root.as_object().unwrap() {
                document[keyword] = value.clone();
            }
            for (name, schema) in more.as_object().unwrap() {
                document["$defs"][name] = schema.clone();
            }
            document
        };
        let (any, strings, nulls) = (
            json!({"type": "array"}),
            json!({"type": "array", "items": {"type": "string"}}),
            json!({"type": "array", "items": {"type": "null"}}),
        );
        let of_nulls = json!({"$dynamicAnchor": "item", "type": "null"});
        // Each schema with what it says, written without a reference.
        let pairs = [
            // The anchor of the outermost resource on the way that has one is meant.
            (lists(json!({"$ref": "strings"}), json!({})), &strings),
            (lists(json!({"$ref": "list"}), json!({})), &any),
            (
                lists(json!({"$ref": "strings"}), json!({"item": of_nulls})),
                &nulls,
            ),
            // A resource that was left is on the way no more. The list is reached twice:
            // by way of `strings`, and after that by itself, where it takes any item.
            (
                lists(
                    json!({"not": {"not": {"$ref": "strings"}}, "$ref": "list"}),
                    json!({}),
                ),
                &strings,
            ),
            (
                lists(
                    json!({"anyOf": [{"$ref": "strings"}, {"$ref": "list"}]}),
                    json!({}),
                ),
                &any,
            ),
            // The first target is in a resource that is not on the way.
            (
                lists(
                    json!({"type": "array", "items": {"$dynamicRef": "strings#item"}}),
                    json!({}),
                ),
                &strings,
            ),
            // A `$dynamicRef` to an `$anchor` is a `$ref`.
            (
                lists(
                    json!({"$ref": "inner"}),
                    json!({
                        "item": of_nulls,
                        "inner": {
                            "$id": "inner",
                            "type": "array",
                            "items": {"$dynamicRef": "#item"},
                            "$defs": {"item": {"$anchor": "item", "type": "string"}},
                        },
                    }),
                ),
                &strings,
            ),
        ];
        let instances = [
            json!([]),
            json!(["a"]),
            json!([null]),
            json!(["a", null]),
            json!(0),
        ];
        let same = |one: &Value, other: &Value| {
            let yes =
                |wide, narrow| subsumes::subsumes(wide, narrow).unwrap() == subsumes::Verdict::Yes;
            yes(one, other) && yes(other, one)
        };
        for (dynamic, plain) in &pairs {
            assert!(same(dynamic, plain), "{dynamic} and {plain}");
            let (of_dynamic, of_plain) = (validator(dynamic).unwrap(), validator(plain).unwrap());
            for instance in &instances {
                assert_eq!(
                    of_dynamic.is_valid(instance),
                    of_plain.is_valid(instance),
                    "{instance} under {dynamic}"
                );
            }
        }

        // The two differ on a `$ref` that names a dynamic anchor where another one of the
        // name is further out on the way. To the draft a `$ref` leads where it says, and
        // the library follows the draft. The validator looks for the anchor on the way, as
        // for a `$dynamicRef`. No schema of the corpus has such a `$ref`.
        let plain_reference = lists(
            json!({"$ref": "inner"}),
            json!({
                "item": of_nulls,
                "inner": {
                    "$id": "inner",
                    "type": "array",
                    "items": {"$ref": "#item"},
                    "$defs": {"item": {"$dynamicAnchor": "item", "type": "string"}},
                },
            }),
        );
        assert!(same(&plain_reference, &strings));
        let of_validator = validator(&plain_reference).unwrap();
        assert!(!of_validator.is_valid(&json!(["a"])));
        assert!(of_validator.is_valid(&json!([null])));
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
    fn a_pattern_is_one_of_ecma_262() {
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
        // The validator has look-around, which the library does not model.
        let look_ahead = json!({"pattern": "a(?=b)"});
        assert_eq!(
            confirmation(&anything, &look_ahead, &json!("ab")),
            Confirmation::Confirmed
        );
        assert_eq!(
            confirmation(&look_ahead, &json!(true), &json!("ac")),
            Confirmation::Confirmed
        );
    }

    #[test]
    fn a_pattern_matches_what_it_matches_in_ecma_262() {
        // Each of these says something else in the `regex` crate: the classes of ASCII, the
        // line terminators, the escapes.
        let patterns: [(&str, &[&str], &[&str]); 9] = [
            (r"^\d$", &["3"], &["٣", "a", ""]),
            (r"^\D$", &["٣", "a"], &["3"]),
            (r"^\w+$", &["a", "_", "a3"], &["é", "-", ""]),
            (r"^\W$", &["é", "-"], &["a"]),
            (
                r"^\s$",
                &[" ", "\n", "\u{a0}", "\u{2028}", "\u{feff}"],
                &["\u{85}", "a"],
            ),
            (r"^\S$", &["\u{85}", "a"], &[" ", "\u{feff}"]),
            (
                "^.$",
                &["a", "\u{85}", "😀"],
                &["\n", "\r", "\u{2028}", "\u{2029}", "ab"],
            ),
            (r"^\cC$", &["\u{3}"], &["C", "cC"]),
            (r"^\p{Script=Greek}+$", &["λόγος"], &["logos"]),
        ];
        for (pattern, matched, others) in patterns {
            let validator = validator(&json!({"pattern": pattern})).unwrap();
            // The same pattern as a key of `patternProperties`, with the name as the string.
            let names =
                json!({"patternProperties": {pattern: true}, "additionalProperties": false});
            let names = self::validator(&names).unwrap();
            let strings = matched.iter().map(|string| (string, true));
            for (string, matches) in strings.chain(others.iter().map(|string| (string, false))) {
                assert_eq!(
                    validator.is_valid(&json!(string)),
                    matches,
                    "{pattern:?} on {string:?}"
                );
                assert_eq!(
                    names.is_valid(&json!({*string: null})),
                    matches,
                    "{pattern:?} on the name {string:?}"
                );
            }
        }
    }

    #[test]
    fn the_validator_reads_a_pattern_as_the_library_does() {
        let patterns = [
            r"^\d{2}$",
            r"^\D\d$",
            r"^\w\W$",
            r"^\s\S$",
            r"^.\s$",
            r"^[^\s]\n$",
            r"^[\w-]+\.$",
            r"^\cJ\x41B$",
            r"^[a-c]{2,3}\/$",
            r"^(?:a|b)+?c$",
            r"^(?<year>\d{4})-(?<month>\d{2})$",
            r"^\p{Lu}\p{Ll}$",
            r"^[^\p{L}\d]$",
            r"\u{1F600}$",
            r"^😀$",
        ];
        for pattern in patterns {
            // A string that the pattern matches, and one that it does not.
            let (nothing, narrow) = (json!(false), json!({"pattern": pattern, "type": "string"}));
            let subsumes::Verdict::No { counterexample } =
                subsumes::subsumes(&nothing, &narrow).unwrap()
            else {
                panic!("the library finds no string for {pattern:?}");
            };
            assert_eq!(
                confirmation(&nothing, &narrow, &counterexample),
                Confirmation::Confirmed,
                "{counterexample} for {pattern:?}"
            );
            let (wide, narrow) = (json!({"pattern": pattern}), json!({"type": "string"}));
            let subsumes::Verdict::No { counterexample } =
                subsumes::subsumes(&wide, &narrow).unwrap()
            else {
                panic!("the library finds no string against {pattern:?}");
            };
            assert_eq!(
                confirmation(&wide, &narrow, &counterexample),
                Confirmation::Confirmed,
                "{counterexample} against {pattern:?}"
            );
        }
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
