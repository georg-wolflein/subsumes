//! Patterns for a validator that reads ECMA 262, in the dialect of the library.
//!
//! The library reads a pattern as the `regex` crate does. The `jsonschema` crate translates
//! every pattern from ECMA 262 first, whichever engine matches it afterwards, and has no
//! option against that. `\d` becomes `[0-9]`, `\w` and `\s` lose what Unicode adds to them,
//! `.` stops at three more line ends, and the set operations of a class become plain
//! characters.
//!
//! So each pattern of a schema is written anew before the validator sees it: parsed as the
//! `regex` crate parses it, and printed with every class as the ranges it stands for. The
//! translation finds nothing left to change, and the validator matches what the library means.

use std::collections::BTreeSet;

use percent_encoding::percent_decode_str;
use serde_json::Value;

/// The keywords of the draft that hold one schema.
const ONE: [&str; 11] = [
    "additionalProperties",
    "contains",
    "contentSchema",
    "else",
    "if",
    "items",
    "not",
    "propertyNames",
    "then",
    "unevaluatedItems",
    "unevaluatedProperties",
];

/// Those that hold a list of schemas.
const LISTED: [&str; 4] = ["allOf", "anyOf", "oneOf", "prefixItems"];

/// Those that hold schemas by name.
const NAMED: [&str; 5] = [
    "$defs",
    "definitions",
    "dependentSchemas",
    "patternProperties",
    "properties",
];

/// The schema with every `pattern` and every key of `patternProperties` written so that the
/// validator reads it as the library does.
///
/// A reference that leads through a key of `patternProperties` leads nowhere afterwards, and
/// the validator refuses the schema.
pub fn spelled_out(schema: &Value) -> Value {
    let mut schema = schema.clone();
    // From the deepest place up, so that a key which changes is on the way to no place that
    // is still to come.
    for place in places(&schema).iter().rev() {
        let Some(Value::Object(keywords)) = schema.pointer_mut(place) else {
            continue;
        };
        if let Some(Value::String(pattern)) = keywords.get_mut("pattern")
            && let Some(spelled) = pattern_spelled_out(pattern)
        {
            *pattern = spelled;
        }
        if let Some(Value::Object(schemas)) = keywords.get_mut("patternProperties") {
            for (pattern, schema) in std::mem::take(schemas) {
                let mut spelled = pattern_spelled_out(&pattern).unwrap_or(pattern);
                // Two patterns that say the same are spelled the same. A group around one
                // keeps both.
                while schemas.contains_key(&spelled) {
                    spelled = format!("(?:{spelled})");
                }
                schemas.insert(spelled, schema);
            }
        }
    }
    schema
}

/// The pattern as the `regex` crate reads it, with every class written as its ranges. `None`
/// for a pattern that the `regex` crate does not take, which stays as it is: the validator
/// reads it as ECMA 262 then, and takes the schema where it can make something of the pattern.
fn pattern_spelled_out(pattern: &str) -> Option<String> {
    let read = regex_syntax::Parser::new().parse(pattern).ok()?;
    // The printer writes the class of no character as `[a&&b]`, an intersection, which ECMA
    // 262 reads as a class of three characters. Every other `&` it escapes.
    Some(read.to_string().replace("[a&&b]", r"[^\x{0}-\x{10FFFF}]"))
}

/// Where the schemas of a document are, as JSON Pointers: the root, what the keywords of the
/// draft put below a schema, and what a reference points to. The library reads a value as a
/// schema wherever a reference leads, also where the draft puts none.
///
/// Only a pointer into the resource that the reference stands in is followed. An anchor or
/// the URI of a resource names a schema that the draft declares, which is found without the
/// reference. A pointer behind the URI of another resource is not followed, so a pattern that
/// only such a reference makes part of a schema stays as it is written.
fn places(document: &Value) -> BTreeSet<String> {
    let mut places = BTreeSet::new();
    // The places with an `$id`. A pointer in a reference starts at the nearest one above it.
    let mut resources = BTreeSet::new();
    let mut references = Vec::new();
    let mut pending = vec![String::new()];
    loop {
        // The schemas that the draft declares come first, so that every `$id` among them is
        // known when a pointer is followed.
        while let Some(place) = pending.pop() {
            let Some(Value::Object(keywords)) = document.pointer(&place) else {
                continue;
            };
            if !places.insert(place.clone()) {
                continue;
            }
            for (keyword, value) in keywords {
                let below = |name: &str| {
                    let name = name.replace('~', "~0").replace('/', "~1");
                    format!("{place}/{keyword}/{name}")
                };
                match (keyword.as_str(), value) {
                    ("$id", Value::String(_)) => {
                        resources.insert(place.clone());
                    }
                    ("$ref" | "$dynamicRef", Value::String(reference)) => {
                        references.push((place.clone(), reference));
                    }
                    (keyword, _) if ONE.contains(&keyword) => {
                        pending.push(format!("{place}/{keyword}"));
                    }
                    (keyword, Value::Array(schemas)) if LISTED.contains(&keyword) => {
                        let positions = 0..schemas.len();
                        pending.extend(positions.map(|position| below(&position.to_string())));
                    }
                    (keyword, Value::Object(schemas)) if NAMED.contains(&keyword) => {
                        pending.extend(schemas.keys().map(|name| below(name)));
                    }
                    _ => {}
                }
            }
        }
        let Some((from, reference)) = references.pop() else {
            return places;
        };
        let Some(pointer) = reference.strip_prefix("#/") else {
            continue;
        };
        let pointer = percent_decode_str(pointer).decode_utf8_lossy();
        let resource = above(&from)
            .find(|place| resources.contains(*place))
            .unwrap_or_default();
        pending.push(format!("{resource}/{pointer}"));
    }
}

/// A place and every place above it, from the nearest.
fn above(place: &str) -> impl Iterator<Item = &str> {
    std::iter::successors(Some(place), |place| {
        place.rfind('/').map(|end| &place[..end])
    })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// What a pattern is spelled as, so that no test depends on how the printer writes.
    fn spelled(pattern: &str) -> String {
        let spelled = pattern_spelled_out(pattern).unwrap();
        assert_ne!(spelled, pattern);
        spelled
    }

    #[test]
    fn a_pattern_is_written_anew_wherever_the_draft_puts_a_schema() {
        let (a, b) = (spelled("^a$"), spelled("^b$"));
        let schema = json!({
            "pattern": "^a$",
            "patternProperties": {"^a$": {"pattern": "^b$"}},
            "propertyNames": {"pattern": "^a$"},
            "anyOf": [true, {"items": {"pattern": "^b$"}}],
            "$defs": {"a/b~c": {"pattern": "^a$"}},
        });
        assert_eq!(
            spelled_out(&schema),
            json!({
                "pattern": a,
                "patternProperties": {a.as_str(): {"pattern": b}},
                "propertyNames": {"pattern": a},
                "anyOf": [true, {"items": {"pattern": b}}],
                "$defs": {"a/b~c": {"pattern": a}},
            })
        );
    }

    #[test]
    fn what_is_no_pattern_stays() {
        // Values, the names of properties and of definitions, and what the draft does not
        // know. None of them is a keyword here, whatever it is called.
        let schema = json!({
            "const": {"pattern": "^a$"},
            "enum": [{"patternProperties": {"^a$": true}}],
            "default": {"pattern": "^a$"},
            "properties": {
                "pattern": {"const": "^a$"},
                "patternProperties": {"const": 1},
            },
            "$defs": {"patternProperties": {"type": "object"}},
            "x-unknown": {"pattern": "^a$"},
        });
        assert_eq!(spelled_out(&schema), schema);
        // Neither does a pattern that the `regex` crate does not take.
        let look_ahead = json!({"pattern": "a(?=b)", "patternProperties": {"a(?=b)": true}});
        assert_eq!(spelled_out(&look_ahead), look_ahead);
    }

    #[test]
    fn a_reference_makes_a_schema_of_what_it_points_to() {
        let a = spelled("^a$");
        let schema = json!({
            "$ref": "#/types/a%20letter",
            "types": {
                "a letter": {"pattern": "^a$", "not": {"$ref": "#/types/other/0"}},
                "other": [{"pattern": "^a$"}, {"pattern": "^a$"}],
                "unused": {"pattern": "^a$"},
            },
            "not": {"$ref": "#/types/missing"},
        });
        assert_eq!(
            spelled_out(&schema),
            json!({
                "$ref": "#/types/a%20letter",
                "types": {
                    "a letter": {"pattern": a, "not": {"$ref": "#/types/other/0"}},
                    "other": [{"pattern": a}, {"pattern": "^a$"}],
                    "unused": {"pattern": "^a$"},
                },
                "not": {"$ref": "#/types/missing"},
            })
        );
    }

    #[test]
    fn a_pointer_starts_at_the_resource_of_its_reference() {
        let a = spelled("^a$");
        let inner = |pattern: &str| {
            json!({
                "$id": "https://example.com/inner",
                "$ref": "#/types/letter",
                "types": {"letter": {"pattern": pattern}},
            })
        };
        let schema = |pattern: &str| {
            json!({
                "$ref": "https://example.com/inner",
                "$defs": {"inner": inner(pattern)},
                "types": {"letter": {"pattern": "^a$"}},
            })
        };
        assert_eq!(spelled_out(&schema("^a$")), schema(&a));
    }

    #[test]
    fn two_keys_that_say_the_same_both_stay() {
        let schema = json!({"patternProperties": {
            r"^\d$": {"type": "integer"},
            r"^\p{Nd}$": {"minimum": 5},
            "^[0-9]$": {"maximum": 7},
        }});
        let rewritten = spelled_out(&schema);
        let schemas = rewritten["patternProperties"].as_object().unwrap();
        let mut kept: Vec<&Value> = schemas.values().collect();
        kept.sort_by_key(|schema| schema.to_string());
        assert_eq!(
            kept,
            [
                &json!({"maximum": 7}),
                &json!({"minimum": 5}),
                &json!({"type": "integer"})
            ]
        );
        // The two that say the same still do.
        let read = |pattern: &String| regex_syntax::Parser::new().parse(pattern).unwrap();
        let readings: Vec<_> = schemas.keys().map(read).collect();
        let repeated = (1..readings.len()).filter(|&at| readings[..at].contains(&readings[at]));
        assert_eq!(repeated.count(), 1, "{:?}", schemas.keys());
    }
}
