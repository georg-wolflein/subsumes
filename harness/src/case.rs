//! The cases of the corpus, read from their files.
//!
//! A case file holds two schemas, and the file after it often holds the same two the other
//! way round, or one of them next to another version of the other: half of the text of the
//! corpus is a schema that the case before had too. Such a schema is not read again. The
//! reader keeps the schemas of the last case, each with its text, and where the text of a
//! schema of the next case is that text, it is that schema: the value that was read then,
//! with the validator that was built for it.
//!
//! Nothing else is kept from one case to the next. The library is given the same two values
//! for a case as it would be without this, and is asked the same. A file is a case here
//! exactly when `serde_json` reads it as one, with the same labels and schemas: what the
//! reader does not follow, it leaves to `serde_json` to read as a whole.

use std::fs::File;
use std::io::Read;
use std::mem;
use std::ops::Range;
use std::path::Path;
use std::rc::Rc;

use serde::Deserialize;
use serde::de::IgnoredAny;
use serde_json::Value;

use crate::counterexample::Schema;

/// A case of the corpus: the two schemas and the labels. What else the file says about the
/// case is not read.
pub struct Case {
    pub a_subsumes_b: Option<bool>,
    pub b_subsumes_a: Option<bool>,
    pub a: Rc<Schema>,
    pub b: Rc<Schema>,
}

/// A case as `serde_json` reads it from the whole text of a file.
#[derive(Deserialize)]
struct Whole {
    a_subsumes_b: Option<bool>,
    b_subsumes_a: Option<bool>,
    a: Value,
    b: Value,
}

/// A schema of a case with where its text stands in the text of the file.
type Placed = (Range<usize>, Rc<Schema>);

/// How many objects and arrays `serde_json` reads inside one another in a value of a case. A
/// value on its own may have one more, since the case is an object too.
const LEVELS: usize = 126;

/// Reads the cases of a job, one after the other, and keeps the schemas of the last one.
#[derive(Default)]
pub struct Reader {
    /// The text of the file of the last case.
    text: String,
    /// The schemas of the last case.
    schemas: Vec<Placed>,
    /// The string that the next file is read into: that of the case before the last one,
    /// whose room is kept.
    spare: String,
}

impl Reader {
    /// The case in a file.
    pub fn read(&mut self, path: &Path) -> Result<Case, String> {
        let failed =
            |error: &dyn std::fmt::Display| format!("cannot read {}: {error}", path.display());
        let mut text = mem::take(&mut self.spare);
        text.clear();
        let read = File::open(path).and_then(|mut file| file.read_to_string(&mut text));
        read.map_err(|error| failed(&error))?;
        self.case(text).map_err(|error| failed(&error))
    }

    /// The case that a text holds. A text that is not taken apart here is read as a whole,
    /// so what is a case and what the error says is for `serde_json` to say.
    fn case(&mut self, text: String) -> Result<Case, serde_json::Error> {
        let (case, schemas) = match self.fields(&text) {
            Some(read) => read,
            None => {
                let whole: Whole = serde_json::from_str(&text)?;
                let case = Case {
                    a_subsumes_b: whole.a_subsumes_b,
                    b_subsumes_a: whole.b_subsumes_a,
                    a: Rc::new(Schema::new(whole.a)),
                    b: Rc::new(Schema::new(whole.b)),
                };
                (case, Vec::new())
            }
        };
        self.schemas = schemas;
        self.spare = mem::replace(&mut self.text, text);
        Ok(case)
    }

    /// Takes the text of a case file apart, and gives the case with where its schemas
    /// stand in the text. The text is an object. Only its braces, colons and commas are
    /// read here: each name and each value is read by `serde_json` from where it begins,
    /// which says where it ends. So a schema can be held against the text of one that is
    /// known before it is read.
    ///
    /// `None` is a text that is no case, or one that is written in a way that this does not
    /// follow, as with an escape in a name.
    fn fields(&self, text: &str) -> Option<(Case, Vec<Placed>)> {
        let (mut a, mut b, mut a_subsumes_b, mut b_subsumes_a) = (None, None, None, None);
        let mut schemas = Vec::new();
        let mut rest = past_space(past_space(text).strip_prefix('{')?);
        if let Some(after) = rest.strip_prefix('}') {
            rest = after;
        } else {
            loop {
                let (name, after) = value::<&str>(rest)?;
                rest = past_space(past_space(after).strip_prefix(':')?);
                rest = match name {
                    "a" => self.schema(text, rest, &mut schemas, &mut a)?,
                    "b" => self.schema(text, rest, &mut schemas, &mut b)?,
                    "a_subsumes_b" => label(rest, &mut a_subsumes_b)?,
                    "b_subsumes_a" => label(rest, &mut b_subsumes_a)?,
                    _ => value::<IgnoredAny>(rest)?.1,
                };
                rest = past_space(rest);
                match rest.strip_prefix(',') {
                    Some(after) => rest = after,
                    None => {
                        rest = rest.strip_prefix('}')?;
                        break;
                    }
                }
            }
        }
        if !past_space(rest).is_empty() {
            return None;
        }
        // A label that the file does not have is one that claims nothing, as a `null` is.
        let case = Case {
            a_subsumes_b: a_subsumes_b.flatten(),
            b_subsumes_a: b_subsumes_a.flatten(),
            a: a?,
            b: b?,
        };
        Some((case, schemas))
    }

    /// Reads the schema that `rest` begins with, where `rest` is the end of `text`, and
    /// gives the text after it. A schema that is known by its text is not read: one of the
    /// last case, or the other one of this case. A schema twice in a file is no case.
    ///
    /// A text that is known is the whole text of one value, as `serde_json` read it. An
    /// object, an array and a string end where they close, whatever comes after, so a text
    /// that begins with the text of one of those holds that value there, and the value ends
    /// where that text does. A number or a boolean ends where another character begins:
    /// `1` is where `12` begins. Those are read anew, which costs nothing.
    fn schema<'a>(
        &self,
        text: &'a str,
        rest: &'a str,
        schemas: &mut Vec<Placed>,
        slot: &mut Option<Rc<Schema>>,
    ) -> Option<&'a str> {
        if slot.is_some() {
            return None;
        }
        let of_last = self
            .schemas
            .iter()
            .map(|(place, schema)| (&self.text[place.clone()], schema));
        let of_this = schemas
            .iter()
            .map(|(place, schema)| (&text[place.clone()], schema));
        let known = of_last
            .chain(of_this)
            .find(|(known, _)| known.starts_with(['{', '[', '"']) && rest.starts_with(known))
            .map(|(known, schema)| (Rc::clone(schema), &rest[known.len()..]));
        let (schema, after) = match known {
            Some(known) => known,
            None => {
                let (value, after) = value(rest)?;
                // Read on its own, a value may be one level deeper than in a case.
                if is_deeper(&value, LEVELS) {
                    return None;
                }
                (Rc::new(Schema::new(value)), after)
            }
        };
        let place = text.len() - rest.len()..text.len() - after.len();
        schemas.push((place, Rc::clone(&schema)));
        *slot = Some(schema);
        Some(after)
    }
}

/// Reads the label that a text begins with, and gives the text after it. A label twice in a
/// file is no case.
fn label<'a>(rest: &'a str, slot: &mut Option<Option<bool>>) -> Option<&'a str> {
    if slot.is_some() {
        return None;
    }
    let (label, after) = value(rest)?;
    *slot = Some(label);
    Some(after)
}

/// The value that a text begins with, as `serde_json` reads it, and the text after it.
fn value<'a, T: Deserialize<'a>>(text: &'a str) -> Option<(T, &'a str)> {
    let mut values = serde_json::Deserializer::from_str(text).into_iter();
    let value = values.next()?.ok()?;
    Some((value, &text[values.byte_offset()..]))
}

/// A text from where the white space of JSON ends that it begins with.
fn past_space(text: &str) -> &str {
    text.trim_start_matches([' ', '\n', '\r', '\t'])
}

/// Whether a value has more than so many objects and arrays inside one another.
fn is_deeper(value: &Value, levels: usize) -> bool {
    match value {
        Value::Array(items) => levels == 0 || items.iter().any(|item| is_deeper(item, levels - 1)),
        Value::Object(members) => {
            levels == 0 || members.values().any(|member| is_deeper(member, levels - 1))
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// What a reader makes of a text, and what `serde_json` makes of the whole of it.
    fn read(reader: &mut Reader, text: &str) -> Option<Case> {
        let case = reader.case(text.to_owned()).ok();
        let whole = serde_json::from_str::<Whole>(text).ok();
        assert_eq!(case.is_some(), whole.is_some(), "{text}");
        if let (Some(case), Some(whole)) = (&case, &whole) {
            assert_eq!(case.a.value, whole.a, "{text}");
            assert_eq!(case.b.value, whole.b, "{text}");
            let labels = (case.a_subsumes_b, case.b_subsumes_a);
            assert_eq!(labels, (whole.a_subsumes_b, whole.b_subsumes_a), "{text}");
        }
        case
    }

    #[test]
    fn a_case_is_read_as_serde_json_reads_it() {
        let texts = [
            // As the corpus writes a case.
            "{\n  \"$schema\": \"../case.schema.json\",\n  \"a_subsumes_b\": false,\n  \
             \"b_subsumes_a\": null,\n  \"features\": [\n    \"type\"\n  ],\n  \"a\": {\n    \
             \"type\": \"string\"\n  },\n  \"b\": true\n}\n",
            // Without a space, with much of it, and in another order.
            r#"{"b":{"const":[1,{"x":"}"}]},"a":false,"b_subsumes_a":true}"#,
            " \t\r\n{ \"a\" \n:\t[ ] ,\r\n\"b\" : \"{\" , \"a_subsumes_b\" : true } \n",
            // A name with an escape is the name that it spells, to `serde_json`.
            r#"{"\u0061": 1, "b": 2, "a_subsumes\u005fb": false}"#,
            // What else a file says is not read, also where it says it twice.
            r#"{"note": {"a": 0}, "a": 1, "note": [], "b": 2, "upstream": null}"#,
            // Numbers and booleans end where something else begins.
            r#"{"a":1,"b":1.5e3}"#,
            r#"{"a":true,"b":null}"#,
            // No case: a schema or a label twice, one that is missing, a label that is none.
            r#"{"a": 1, "b": 2, "a": 1}"#,
            r#"{"a": 1, "b": 2, "b_subsumes_a": null, "b_subsumes_a": null}"#,
            r#"{"a": 1}"#,
            r#"{"a_subsumes_b": true, "b_subsumes_a": true}"#,
            r#"{"a": 1, "b": 2, "a_subsumes_b": 0}"#,
            "{}",
            // No JSON, or more than one value.
            "",
            "{",
            r#"{"a": 1, "b": 2"#,
            r#"{"a": 1, "b": 2,}"#,
            r#"{"a": 1 "b": 2}"#,
            r#"{"a": 1, "b": 2} {}"#,
            r#"{"a": 1, "b": 2}x"#,
            r#"{"a": 1, "b": tru}"#,
            r#"{"a": 1, "b": true1}"#,
            r#"{"a": 1, "b": 2x}"#,
            r#"{a: 1, "b": 2}"#,
            r#"{"a" 1, "b": 2}"#,
            r#"{"a": {"x": }, "b": 2}"#,
            "\u{feff}{\"a\": 1, \"b\": 2}",
            "{\"a\": 1,\u{a0}\"b\": 2}",
            // An array of the four fields is a case to `serde_json`, and so here.
            r#"[true, null, {"type": "string"}, {}]"#,
            "null",
        ];
        let mut reader = Reader::default();
        let read = texts.map(|text| read(&mut reader, text).is_some());
        assert_eq!(read.iter().filter(|read| **read).count(), 8);
        assert!(read[..7].iter().all(|read| *read));
    }

    #[test]
    fn a_schema_is_read_as_deep_as_serde_json_reads_it_in_a_case() {
        let arrays = |levels: usize| format!("{}{}", "[".repeat(levels), "]".repeat(levels));
        let objects = |levels: usize| {
            let inner = "{\"x\": ".repeat(levels - 1);
            format!("{inner}{{}}{}", "}".repeat(levels - 1))
        };
        let case = |a: &str| format!(r#"{{"a": {a}, "b": true}}"#);
        let mut reader = Reader::default();
        for nested in [arrays, objects] {
            // On its own `serde_json` reads one level more than in a case.
            assert!(serde_json::from_str::<Value>(&nested(LEVELS + 1)).is_ok());
            assert!(serde_json::from_str::<Value>(&nested(LEVELS + 2)).is_err());
            assert!(read(&mut reader, &case(&nested(LEVELS))).is_some());
            assert!(read(&mut reader, &case(&nested(LEVELS + 1))).is_none());
            assert!(read(&mut reader, &case(&nested(LEVELS + 2))).is_none());
        }
    }

    #[test]
    fn a_schema_of_the_last_case_is_not_read_again() {
        let (strings, numbers, both) = (
            r#"{"type": "string"}"#,
            r#"{"type": "number"}"#,
            r#"{"type": ["string", "number"]}"#,
        );
        let case = |a: &str, b: &str| format!(r#"{{"a_subsumes_b": null, "a": {a}, "b": {b}}}"#);
        let mut reader = Reader::default();
        let first = read(&mut reader, &case(strings, numbers)).unwrap();
        assert!(!Rc::ptr_eq(&first.a, &first.b));
        // The same two the other way round, written with other space around them.
        let turned = format!(" {{\"b\":{strings}  ,\n\"a\"  :  {numbers}}}");
        let second = read(&mut reader, &turned).unwrap();
        assert!(Rc::ptr_eq(&second.a, &first.b));
        assert!(Rc::ptr_eq(&second.b, &first.a));
        // One of them next to a new one.
        let third = read(&mut reader, &case(both, strings)).unwrap();
        assert!(Rc::ptr_eq(&third.b, &first.a));
        assert!(!Rc::ptr_eq(&third.a, &first.b));
        // Only the last case is kept.
        let fourth = read(&mut reader, &case(numbers, both)).unwrap();
        assert!(Rc::ptr_eq(&fourth.b, &third.a));
        assert!(!Rc::ptr_eq(&fourth.a, &first.b));
        // A case of one schema twice has it once.
        let fifth = read(&mut reader, &case(strings, strings)).unwrap();
        assert!(Rc::ptr_eq(&fifth.a, &fifth.b));
        assert!(!Rc::ptr_eq(&fifth.a, &first.a));
        // A text that is no case is none that was read, and a case that is read as a whole
        // leaves nothing to the next one.
        assert!(read(&mut reader, &case(strings, "")).is_none());
        let sixth = read(&mut reader, &case(strings, strings)).unwrap();
        assert!(Rc::ptr_eq(&sixth.a, &fifth.a));
        let array = format!("[null, null, {strings}, {numbers}]");
        let seventh = read(&mut reader, &array).unwrap();
        let eighth = read(&mut reader, &case(strings, numbers)).unwrap();
        assert!(!Rc::ptr_eq(&eighth.a, &seventh.a));
    }

    #[test]
    fn a_schema_is_known_by_its_whole_text() {
        let case = |a: &str, b: &str| format!(r#"{{"a": {a}, "b": {b}}}"#);
        let mut reader = Reader::default();
        // A schema that begins as another one does is another one: the text of the first
        // is where the second begins, and no more.
        let first = read(&mut reader, &case(r#"{"const": 1}"#, r#"{"const": 12}"#)).unwrap();
        assert_eq!(first.b.value, json!({"const": 12}));
        let second = read(&mut reader, &case(r#"{"const": 12}"#, r#"{"const": 123}"#)).unwrap();
        assert!(Rc::ptr_eq(&second.a, &first.b));
        assert_eq!(second.b.value, json!({"const": 123}));
        // A number is the beginning of a longer number, and a string of a longer text.
        let third = read(&mut reader, &case("1", "12")).unwrap();
        assert_eq!((&third.a.value, &third.b.value), (&json!(1), &json!(12)));
        let fourth = read(&mut reader, &case("123", "1")).unwrap();
        assert_eq!((&fourth.a.value, &fourth.b.value), (&json!(123), &json!(1)));
        let fifth = read(&mut reader, &case(r#""x""#, r#""x\"y""#)).unwrap();
        assert_eq!(fifth.b.value, json!("x\"y"));
        let sixth = read(&mut reader, &case(r#""x\"y""#, r#""x""#)).unwrap();
        assert!(Rc::ptr_eq(&sixth.a, &fifth.b));
        assert!(Rc::ptr_eq(&sixth.b, &fifth.a));
        // The same value in other words is read anew.
        let seventh = read(&mut reader, &case(r#""x\u0022y""#, r#"[1]"#)).unwrap();
        assert_eq!(seventh.a.value, sixth.a.value);
        assert!(!Rc::ptr_eq(&seventh.a, &sixth.a));
        let eighth = read(&mut reader, &case("[1 ]", "[1]")).unwrap();
        assert!(Rc::ptr_eq(&eighth.b, &seventh.b));
        assert!(!Rc::ptr_eq(&eighth.a, &seventh.b));
    }
}
