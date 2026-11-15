//! A test that holds the engine against every instance there could be.
//!
//! To the engine an instance matters only by its type, by which boolean, which number or
//! which string it is, by the properties it has if it is an object, and by which of the
//! leaves about its type it satisfies. A leaf may come out either way, since the engine
//! knows nothing of what it means. So the kinds of instance can be listed: a value, and an
//! answer for each leaf.
//!
//! A small evaluator here says for each kind whether a schema accepts it. It reads the JSON
//! and knows nothing of terms or branches, and it states again which keywords are about which
//! type and which of them are one leaf. The engine must agree with it:
//!
//! - `Yes` exactly when every kind that B accepts, A accepts.
//! - `No` only with an instance of which every kind is accepted by B and not by A.
//! - `Unknown` only when some kind is accepted by B and not by A, and no instance that
//!   holds no array is.
//!
//! The only leaves here are about arrays. An instance that holds no array is of one kind
//! only, and of an array the empty one stands for all, with every way of answering the
//! leaves.
//!
//! # Numbers
//!
//! No leaf is about numbers: the engine knows what every keyword about them means, and the
//! evaluator works it out again, in floats. There are more numbers than can be listed, but
//! not more kinds of them. The schemas here take their bounds, their constants and what a
//! number is to be a multiple of from a few numbers, all of them multiples of a half. A
//! number matters to such a schema only by where it lies among the bounds and by which of
//! the multiples it is. Every multiple of a half is its own kind, and the numbers between two
//! of them that are next to each other are all of one kind, which the quarter between them
//! is of too. Beyond the bounds everything repeats with the least number that all the
//! multiples divide. So the quarters from a little below the least bound to a little above
//! the greatest hold one number of every kind, and a float holds each of them exactly.
//!
//! A number that the engine gives may be any number, and is evaluated as it is.
//!
//! # Strings
//!
//! No leaf is about strings either, and the evaluator works out what a keyword about them
//! means: it counts the characters, and asks the `regex` crate whether a pattern matches. The
//! schemas here ask little of a string: to begin with an `a`, to end with a `b`, to hold a
//! `b`, to be made of the letters `a` and `b` only, to be shorter or longer than one, two or
//! three characters, or to be one of a few strings of up to two characters. To such a schema
//! every string is like one of up to three of the letters `a`, `b` and `c`, where `c` is as
//! good as any other character. So those strings hold one of every kind.
//!
//! A string that the engine gives is evaluated as it is too.
//!
//! A pattern that is one word between `^` and `$` never becomes a DFA: the store of
//! languages keeps it as that word. None of the patterns above is one, so one run makes
//! each of them one: `^a$`, `^b$`, `^ab$` or `^$`. The evaluator still asks the `regex`
//! crate, to which they are patterns like any other.
//!
//! # Objects
//!
//! Nor is a leaf about objects. The evaluator looks at the properties that an object has:
//! which names there are, which of them a pattern matches, how many there are, and whether
//! the schema of a property accepts its value, which it asks itself. The objects that are
//! listed have up to two of four names: `a` and `b`, which the schemas here name, `ab`,
//! which the patterns `^a` and `b$` both match, and `c` for any other. Their values are a
//! few that the schemas for values tell apart, with an object or two among them. That is
//! not one object of every kind: a schema can ask for three properties. So a `Yes` is held
//! against fewer objects than it could be. A `No` loses nothing by that, since the object
//! that the engine gives is evaluated as it is, and neither does an `Unknown`, since the
//! schemas for values hold no leaf.
//!
//! # Schemas that refer to themselves
//!
//! A definition that refers to itself, or to one that refers back, accepts what it can be
//! shown to accept in finitely many steps. The evaluator finds that by starting from
//! definitions that accept nothing and reading them again until nothing changes. A reference
//! under a negation cannot be read that way, since more accepted below is less accepted
//! above. So there are two readings: what a definition *surely* accepts and what it *possibly*
//! accepts, where a negated reference is read from the other of the two. Each is found from
//! the other in turns until both stand still. Where the two differ, as for a schema that is
//! its own negation, the definitions say nothing definite, and nothing is asked of the engine.
//! "Accepted by B and not by A" above is then: surely accepted by B, and not possibly by A.
//!
//! A definition may also hold itself in a property. What it accepts of a value then depends
//! on what the definitions accept of the values inside, which are smaller. So the evaluator
//! reads the definitions for the values inside first, and for each value once.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use serde_json::{Value, json};

use crate::testing::Random;
use crate::{Checker, Reason, Verdict};

/// The answers to the leaves, which are all about arrays, and those that were asked for
/// without an answer. Every array of an instance answers alike.
struct Leaves<'l> {
    satisfies: &'l BTreeMap<String, bool>,
    asked: &'l RefCell<Vec<String>>,
}

impl Leaves<'_> {
    /// Whether a value satisfies a leaf about arrays. What is no array satisfies it.
    fn hold(&self, value: &Value, key: String) -> bool {
        if !value.is_array() {
            return true;
        }
        let answer = self.satisfies.get(&key).copied();
        answer.unwrap_or_else(|| {
            self.asked.borrow_mut().push(key);
            false
        })
    }
}

/// Whether each definition of a document accepts a value, by the fragment that a reference
/// to it holds.
type Definitions<'d> = BTreeMap<&'d str, bool>;

/// What the definitions accept of a value: for a reference as it stands, and for a negated
/// one.
struct Readings<'r> {
    plain: &'r Definitions<'r>,
    negated: &'r Definitions<'r>,
}

/// Which of the two readings a reference as it stands reads.
#[derive(Clone, Copy)]
enum Which {
    Surely,
    Possibly,
}

/// What the definitions surely accept of a value, and what they possibly accept.
type Both<'d> = Rc<(Definitions<'d>, Definitions<'d>)>;

/// A schema with its definitions, by the fragment that a reference to each holds.
struct Document<'d> {
    schema: &'d Value,
    definitions: Vec<(&'d str, &'d Value)>,
    /// Whether no definition refers to one. Then a reference is read by reading the
    /// definition where the reference stands, and nothing is read until it stands still.
    without_cycles: bool,
    /// What the definitions accept of the values that were looked at and hold no array,
    /// by the value as text. Of a value that holds one, that depends on the leaves.
    known: RefCell<HashMap<String, Both<'d>>>,
}

fn type_of(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

/// Whether a value is this constant, which is no array and no object.
fn is(value: &Value, constant: &Value) -> bool {
    match (value, constant) {
        (Value::Number(value), Value::Number(constant)) => value.as_f64() == constant.as_f64(),
        (_, Value::Array(_) | Value::Object(_)) => {
            panic!("no schema here has the constant {constant}")
        }
        _ => value == constant,
    }
}

/// Whether a value is an array or holds one.
fn holds_an_array(value: &Value) -> bool {
    match value {
        Value::Array(_) => true,
        Value::Object(members) => members.values().any(holds_an_array),
        _ => false,
    }
}

impl<'d> Document<'d> {
    /// `fragments` holds the fragment of every definition that a schema here may have.
    fn new(schema: &'d Value, fragments: &'d BTreeMap<String, String>) -> Self {
        let definitions = schema.get("$defs").and_then(Value::as_object);
        let definitions = definitions.into_iter().flatten();
        let definitions = definitions.map(|(name, schema)| (fragments[name].as_str(), schema));
        let definitions: Vec<(&str, &Value)> = definitions.collect();
        let refers = |(_, schema): &(&str, &Value)| schema.to_string().contains("\"$ref\"");
        Self {
            schema,
            without_cycles: !definitions.iter().any(refers),
            definitions,
            known: RefCell::default(),
        }
    }

    fn accepting_nothing(&self) -> Definitions<'d> {
        let fragments = self.definitions.iter();
        fragments.map(|(fragment, _)| (*fragment, false)).collect()
    }

    /// Whether a schema accepts a value, given what the definitions accept of the value. A
    /// reference reads `plain`, and one that stands under a negation reads `negated`;
    /// `under_negation` says which of the two the schema itself stands under, and `which`
    /// what `plain` is. Every part is looked at, also where the answer is settled before,
    /// so that every leaf is asked for.
    fn accepts(
        &self,
        value: &Value,
        schema: &Value,
        under_negation: bool,
        read: &Readings,
        which: Which,
        leaves: &Leaves,
    ) -> bool {
        let keywords = match schema {
            Value::Bool(accepts) => return *accepts,
            other => other
                .as_object()
                .expect("a schema is an object or a boolean"),
        };
        let accepts =
            |schema: &Value| self.accepts(value, schema, under_negation, read, which, leaves);
        // The same schema where its negation is what counts.
        let rejects =
            |schema: &Value| !self.accepts(value, schema, !under_negation, read, which, leaves);
        // A schema that is asked of a value inside this one, with what the definitions
        // accept of that value.
        let inside = |inner: &Value, schema: &Value| {
            if self.without_cycles {
                return self.accepts(inner, schema, under_negation, read, which, leaves);
            }
            let both = self.definitions(inner, leaves);
            let read = match which {
                Which::Surely => Readings {
                    plain: &both.0,
                    negated: &both.1,
                },
                Which::Possibly => Readings {
                    plain: &both.1,
                    negated: &both.0,
                },
            };
            self.accepts(inner, schema, under_negation, &read, which, leaves)
        };
        let every = |schemas: &Value, accepts: &dyn Fn(&Value) -> bool| -> Vec<bool> {
            schemas.as_array().unwrap().iter().map(accepts).collect()
        };
        let all =
            |answers: &mut dyn Iterator<Item = bool>| answers.fold(true, |all, one| all & one);
        // The number that a keyword about numbers holds.
        let at = |value: &Value| value.as_f64().expect("the keyword holds a number");
        let count = |value: &Value| value.as_u64().expect("the keyword holds a count") as usize;
        let number = |holds: &dyn Fn(f64) -> bool| value.as_f64().is_none_or(holds);
        let string = |holds: &dyn Fn(&str) -> bool| value.as_str().is_none_or(holds);
        let members = value.as_object();
        let has = |name: &str| members.is_none_or(|members| members.contains_key(name));
        let named = |names: &Value| -> Vec<bool> {
            let names = names.as_array().unwrap().iter();
            names.map(|name| has(name.as_str().unwrap())).collect()
        };
        // The properties that neither `properties` nor `patternProperties` is about.
        let is_additional = |name: &str| {
            let listed = keywords.get("properties").and_then(Value::as_object);
            let patterns = keywords.get("patternProperties").and_then(Value::as_object);
            let patterns = patterns.into_iter().flatten();
            !listed.is_some_and(|listed| listed.contains_key(name))
                && !patterns.fold(false, |any, (pattern, _)| any | matches(pattern, name))
        };
        let mut accepted = true;
        for (keyword, held) in keywords {
            accepted &= match keyword.as_str() {
                "$defs" | "then" | "else" => true,
                "$ref" => {
                    let pointer = held.as_str().unwrap().trim_start_matches('#');
                    let definitions = if under_negation {
                        read.negated
                    } else {
                        read.plain
                    };
                    let is_it = |(at, _): &&(&str, &Value)| *at == pointer;
                    match self.definitions.iter().find(is_it) {
                        Some((_, definition)) if self.without_cycles => accepts(definition),
                        _ => definitions[pointer],
                    }
                }
                "type" => {
                    let names = held
                        .as_array()
                        .cloned()
                        .unwrap_or_else(|| vec![held.clone()]);
                    let any_number = names.contains(&json!("number"));
                    let named = names.iter().map(|name| match name.as_str().unwrap() {
                        // An integer is a number without a fraction.
                        "integer" => {
                            number(&|number| any_number || number.fract() == 0.0)
                                && value.is_number()
                        }
                        name => name == type_of(value),
                    });
                    named.fold(false, |any, named| any | named)
                }
                "const" => is(value, held),
                "enum" => {
                    let values = held.as_array().unwrap().iter();
                    values.fold(false, |any, constant| any | is(value, constant))
                }
                "allOf" => every(held, &accepts).into_iter().all(|accepted| accepted),
                "anyOf" => every(held, &accepts).into_iter().any(|accepted| accepted),
                // One is accepted and every other is rejected.
                "oneOf" => {
                    let (accepted, rejected) = (every(held, &accepts), every(held, &rejects));
                    (0..accepted.len()).any(|one| {
                        let others = (0..rejected.len()).filter(|other| *other != one);
                        accepted[one] && others.fold(true, |all, other| all & rejected[other])
                    })
                }
                "not" => rejects(held),
                // The condition is rejected or `then` holds, and it is accepted or `else` holds.
                "if" => {
                    let part = |name| keywords.get(name).is_none_or(accepts);
                    let (then, otherwise) = (part("then"), part("else"));
                    (rejects(held) | then) & (accepts(held) | otherwise)
                }
                "minLength" => string(&|string| string.chars().count() >= count(held)),
                "maxLength" => string(&|string| string.chars().count() <= count(held)),
                "pattern" => string(&|string| matches(held.as_str().unwrap(), string)),
                "minimum" => number(&|number| number >= at(held)),
                "maximum" => number(&|number| number <= at(held)),
                "exclusiveMinimum" => number(&|number| number > at(held)),
                "exclusiveMaximum" => number(&|number| number < at(held)),
                "multipleOf" => number(&|number| (number / at(held)).fract() == 0.0),
                "uniqueItems" => held == &json!(false) || leaves.hold(value, keyword.clone()),
                "minItems" => leaves.hold(value, format!("{keyword} {held}")),
                "required" => all(&mut named(held).into_iter()),
                "minProperties" => members.is_none_or(|members| members.len() >= count(held)),
                "maxProperties" => members.is_none_or(|members| members.len() <= count(held)),
                "properties" => {
                    let listed = held.as_object().unwrap().iter();
                    let mut there = listed
                        .filter_map(|(name, schema)| Some(inside(members?.get(name)?, schema)));
                    all(&mut there)
                }
                "patternProperties" => {
                    let patterns = held.as_object().unwrap().iter();
                    let mut matched = patterns.flat_map(|(pattern, schema)| {
                        let there = members.into_iter().flatten();
                        let matched = there.filter(move |(name, _)| matches(pattern, name));
                        matched.map(|(_, inner)| inside(inner, schema))
                    });
                    all(&mut matched)
                }
                "additionalProperties" => {
                    let there = members.into_iter().flatten();
                    let others = there.filter(|(name, _)| is_additional(name));
                    all(&mut others.map(|(_, inner)| inside(inner, held)))
                }
                "propertyNames" => {
                    let names = members.into_iter().flatten().map(|(name, _)| name);
                    all(&mut names.map(|name| inside(&json!(name), held)))
                }
                "dependentRequired" => {
                    let dependencies = held.as_object().unwrap().iter();
                    dependencies.fold(true, |all_hold, (name, needed)| {
                        let needed = all(&mut named(needed).into_iter());
                        all_hold & (members.is_none() || !has(name) || needed)
                    })
                }
                "dependentSchemas" => {
                    let dependencies = held.as_object().unwrap().iter();
                    dependencies.fold(true, |all_hold, (name, schema)| {
                        let accepted = accepts(schema);
                        all_hold & (members.is_none() || !has(name) || accepted)
                    })
                }
                other => panic!("no schema here has the keyword {other}"),
            };
        }
        accepted
    }

    /// What the definitions accept of a value when they are read until nothing changes,
    /// beginning with definitions that accept nothing. A negated reference reads `negated`,
    /// and `which` says what is being read.
    fn read_out(
        &self,
        value: &Value,
        which: Which,
        negated: &Definitions,
        leaves: &Leaves,
    ) -> Definitions<'d> {
        let mut plain = self.accepting_nothing();
        loop {
            let read = Readings {
                plain: &plain,
                negated,
            };
            let next: Definitions = self
                .definitions
                .iter()
                .map(|(at, schema)| {
                    (
                        *at,
                        self.accepts(value, schema, false, &read, which, leaves),
                    )
                })
                .collect();
            if next == plain {
                return plain;
            }
            plain = next;
        }
    }

    /// What the definitions surely accept of a value, and what they possibly accept. For
    /// the values inside the value that is asked again, and found as it was left.
    fn definitions(&self, value: &Value, leaves: &Leaves) -> Both<'d> {
        let text = (!holds_an_array(value)).then(|| value.to_string());
        if let Some(known) = text
            .as_ref()
            .and_then(|text| self.known.borrow().get(text).cloned())
        {
            return known;
        }
        let mut surely = self.accepting_nothing();
        let possibly = loop {
            let possibly = self.read_out(value, Which::Possibly, &surely, leaves);
            let next = self.read_out(value, Which::Surely, &possibly, leaves);
            if next == surely {
                break possibly;
            }
            surely = next;
        };
        let both = Rc::new((surely, possibly));
        if let Some(text) = text {
            self.known.borrow_mut().insert(text, Rc::clone(&both));
        }
        both
    }

    /// Whether the document surely accepts a value, and whether it possibly does.
    fn accepted(&self, value: &Value, leaves: &Leaves) -> (bool, bool) {
        if self.without_cycles {
            let none = Definitions::new();
            let read = Readings {
                plain: &none,
                negated: &none,
            };
            let accepted = self.accepts(value, self.schema, false, &read, Which::Surely, leaves);
            return (accepted, accepted);
        }
        let both = self.definitions(value, leaves);
        let read = |plain, negated, which| {
            let read = Readings { plain, negated };
            self.accepts(value, self.schema, false, &read, which, leaves)
        };
        (
            read(&both.0, &both.1, Which::Surely),
            read(&both.1, &both.0, Which::Possibly),
        )
    }
}

/// Whether a pattern matches a string, by the `regex` crate.
fn matches(pattern: &str, string: &str) -> bool {
    thread_local! {
        static READ: RefCell<HashMap<String, regex::Regex>> = RefCell::default();
    }
    READ.with_borrow_mut(|read| {
        if !read.contains_key(pattern) {
            let parsed = regex::Regex::new(pattern).expect("the pattern is one of the crate");
            read.insert(pattern.to_owned(), parsed);
        }
        read[pattern].is_match(string)
    })
}

/// The quarters that hold a number of every kind: from -8 to 9. The bounds and constants of
/// the schemas here are from -1.5 to 2.5, and the least number that 0.5, 1, 1.5 and 2 all
/// divide is 6.
const QUARTERS: std::ops::RangeInclusive<i16> = -32..=36;

/// The strings that hold one of every kind: those of up to three of the letters `a`, `b`
/// and `c`.
fn strings() -> Vec<String> {
    let mut strings = vec![String::new()];
    let mut from = 0;
    for _ in 0..3 {
        let end = strings.len();
        for at in from..end {
            strings.extend(['a', 'b', 'c'].map(|letter| format!("{}{letter}", strings[at])));
        }
        from = end;
    }
    strings
}

/// The objects of up to two of these names, each with one of these values.
fn objects(names: &[&str], values: &[Value]) -> Vec<Value> {
    let mut objects = vec![json!({})];
    for (place, first) in names.iter().enumerate() {
        for value in values {
            objects.push(json!({ *first: value }));
            for second in &names[place + 1..] {
                let both = values
                    .iter()
                    .map(|other| json!({ *first: value, *second: other }));
                objects.extend(both);
            }
        }
    }
    objects
}

/// What is no object, with both booleans, a number of every kind and a string of every
/// kind, and the empty array for all arrays.
fn plain_instances() -> Vec<Value> {
    let numbers = QUARTERS.map(|quarters| json!(f64::from(quarters) / 4.0));
    let strings = strings().into_iter().map(Value::String);
    let others = [json!(null), json!(true), json!(false), json!([])];
    others.into_iter().chain(numbers).chain(strings).collect()
}

/// What holds for an instance, with every way of answering the leaves about it.
struct Found {
    /// The instance holds no array, so that no leaf is about it.
    exact: bool,
    /// Some kind is surely accepted by B and not possibly by A.
    some_tells_apart: bool,
    /// Every kind is.
    all_tell_apart: bool,
}

/// Asks the evaluator about A and B, for an instance with every way of answering the
/// leaves about it.
fn found(a: &Document, b: &Document, instance: &Value) -> Found {
    let ask = |satisfies: &BTreeMap<String, bool>| {
        let asked = RefCell::new(Vec::new());
        let leaves = Leaves {
            satisfies,
            asked: &asked,
        };
        let (_, a_possibly) = a.accepted(instance, &leaves);
        let (b_surely, _) = b.accepted(instance, &leaves);
        (b_surely & !a_possibly, asked.into_inner())
    };
    // The first look finds the leaves that there are to answer. Without any, as for every
    // instance that holds no array, it is the answer.
    let (tells_apart, mut leaves) = ask(&BTreeMap::new());
    let exact = !holds_an_array(instance);
    if leaves.is_empty() {
        return Found {
            exact,
            some_tells_apart: tells_apart,
            all_tell_apart: tells_apart,
        };
    }
    leaves.sort();
    leaves.dedup();
    assert!(
        leaves.len() <= 14,
        "{} leaves are too many to list",
        leaves.len()
    );
    let mut found = Found {
        exact,
        some_tells_apart: false,
        all_tell_apart: true,
    };
    for answers in 0..1_u32 << leaves.len() {
        let answer = |place: usize| answers >> place & 1 == 1;
        let satisfies = leaves.iter().cloned().enumerate();
        let satisfies = satisfies
            .map(|(place, leaf)| (leaf, answer(place)))
            .collect();
        let (tells_apart, unanswered) = ask(&satisfies);
        assert_eq!(unanswered, Vec::<String>::new());
        found.some_tells_apart |= tells_apart;
        found.all_tell_apart &= tells_apart;
    }
    found
}

/// What the schemas of a pair are made of.
#[derive(Clone, Copy)]
struct Shape {
    /// The definitions that the schemas refer to, and that refer to each other. Every
    /// document has the definition `d` besides, which refers to nothing.
    definitions: &'static [&'static str],
    /// Whether only `allOf` and `anyOf` hold schemas, so that no reference is negated.
    never_negated: bool,
    /// Whether most of what the schemas say is about objects and about the values of
    /// their properties.
    of_objects: bool,
}

/// Schemas that refer to `d` only, so that none refers to itself.
const WITHOUT_CYCLES: Shape = Shape {
    definitions: &[],
    never_negated: false,
    of_objects: false,
};

/// A reference to one of the definitions of the shape.
fn reference(random: &mut Random, shape: Shape) -> Value {
    let name = shape.definitions[random.below(shape.definitions.len())];
    json!({"$ref": format!("#/$defs/{name}")})
}

/// A schema for the value of a property. It holds no leaf: what it asks of an array, every
/// array answers alike. Where the shape has definitions, it is often a reference to one,
/// which makes a cycle through the property.
fn for_a_value(random: &mut Random, depth: usize, shape: Shape) -> Value {
    if !shape.definitions.is_empty() && random.chance(50) {
        return reference(random, shape);
    }
    if depth > 0 && random.chance(30) {
        return about_objects(random, depth - 1, shape);
    }
    let plain = [
        json!(true),
        json!(false),
        json!({"type": "null"}),
        json!({"type": "string"}),
        json!({"type": "integer"}),
        json!({"type": ["number", "null"]}),
        json!({"type": "boolean"}),
        json!({"type": "object"}),
        json!({"type": "array"}),
        json!({"const": 1}),
        json!({"enum": [1, "a"]}),
        json!({"minimum": 1}),
        json!({"minLength": 1}),
        json!({"required": ["a"]}),
        json!({"maxProperties": 0}),
    ];
    plain[random.below(plain.len())].clone()
}

/// A schema that says something of objects, with schemas for the values of properties.
fn about_objects(random: &mut Random, depth: usize, shape: Shape) -> Value {
    let of = |random: &mut Random| for_a_value(random, depth, shape);
    match random.below(20) {
        0 => json!({"properties": {"a": of(random)}}),
        1 => json!({"properties": {"a": of(random), "b": of(random)}, "required": ["a"]}),
        2 => json!({"properties": {"a": of(random)}, "additionalProperties": false}),
        3 => json!({"properties": {"b": of(random)}, "additionalProperties": of(random)}),
        4 => json!({"additionalProperties": of(random)}),
        5 => json!({"patternProperties": {"^a": of(random)}}),
        6 => json!({"patternProperties": {"^a": of(random), "b$": of(random)}}),
        7 => json!({
            "properties": {"a": of(random)},
            "patternProperties": {"^a": of(random)},
            "additionalProperties": of(random),
        }),
        8 => {
            let names = [
                json!({"pattern": "^a"}),
                json!({"enum": ["a", "b"]}),
                json!({"maxLength": 1}),
                json!({"not": {"const": "a"}}),
                json!({"anyOf": [{"const": "c"}, {"pattern": "b$"}]}),
            ];
            json!({"propertyNames": names[random.below(names.len())]})
        }
        9 => json!({"minProperties": 1 + random.below(2)}),
        10 => json!({"maxProperties": random.below(3)}),
        11 => json!({"required": [random.pick(&["a", "b", "ab", "c"])]}),
        12 => json!({"required": ["a", "b"]}),
        13 => json!({"dependentRequired": {"a": ["b"]}}),
        14 => json!({"type": "object"}),
        15 => json!({"type": "object", "required": ["a"], "properties": {"a": of(random)}}),
        16 => json!({"type": "object", "required": ["b"], "additionalProperties": of(random)}),
        17 => json!({"minProperties": 2, "maxProperties": 2}),
        18 => json!({"type": ["object", "null"]}),
        _ => json!({"patternProperties": {"b$": of(random)}, "additionalProperties": false}),
    }
}

/// A schema without a schema below it that is asked of the same instance. More often than
/// not it is a reference to one of the definitions of the shape, so that cycles are common.
fn plain(random: &mut Random, shape: Shape) -> Value {
    let often = if shape.of_objects { 25 } else { 60 };
    if !shape.definitions.is_empty() && random.chance(often) {
        return reference(random, shape);
    }
    if shape.of_objects && random.chance(75) {
        return about_objects(random, 1, shape);
    }
    let plain = [
        json!(true),
        json!(false),
        json!({"type": "null"}),
        json!({"type": "boolean"}),
        json!({"type": "string"}),
        json!({"type": "number"}),
        json!({"type": "integer"}),
        json!({"type": ["integer", "string"]}),
        json!({"type": ["number", "integer", "null"]}),
        json!({"type": ["array", "object"]}),
        json!({"const": null}),
        json!({"const": true}),
        json!({"enum": [false, null]}),
        json!({"enum": [1, "a", true]}),
        json!({"const": 1}),
        json!({"const": "a"}),
        json!({"enum": ["ab", ""]}),
        json!({"minLength": 1}),
        json!({"minLength": 2, "type": "string"}),
        json!({"minLength": 3}),
        json!({"maxLength": 1}),
        json!({"maxLength": 2, "minLength": 1}),
        json!({"pattern": "^a"}),
        json!({"pattern": "b$", "type": "string"}),
        json!({"pattern": "b"}),
        json!({"pattern": "^[ab]*$"}),
        json!({"minimum": 0}),
        json!({"maximum": 0, "type": "number"}),
        json!({"multipleOf": 1}),
        json!({"minimum": 1}),
        json!({"exclusiveMinimum": 0}),
        json!({"maximum": 2.5}),
        json!({"exclusiveMaximum": 2.5, "type": "number"}),
        json!({"minimum": -1.5, "maximum": 1}),
        json!({"multipleOf": 0.5}),
        json!({"multipleOf": 1.5}),
        json!({"multipleOf": 2, "type": "number"}),
        json!({"type": "integer", "minimum": 1}),
        json!({"const": 1.0}),
        json!({"enum": [0, 2.5]}),
        json!({"uniqueItems": true}),
        json!({"minItems": 1, "type": "array"}),
        json!({"required": ["a"]}),
        json!({"required": ["a", "b"], "type": "object"}),
        json!({"dependentRequired": {"a": ["b"]}}),
        json!({"minProperties": 1}),
        json!({"maxProperties": 1, "type": "object"}),
        json!({"$ref": "#/$defs/d"}),
    ];
    plain[random.below(plain.len())].clone()
}

fn schema(random: &mut Random, depth: usize, shape: Shape) -> Value {
    if depth == 0 || random.chance(30) {
        return plain(random, shape);
    }
    let mut below = |random: &mut Random| schema(random, depth - 1, shape);
    let several = |random: &mut Random, below: &mut dyn FnMut(&mut Random) -> Value| {
        let count = 1 + random.below(3);
        Value::Array((0..count).map(|_| below(random)).collect())
    };
    let connectives = if shape.never_negated { 4 } else { 8 };
    let mut schema = match random.below(connectives) {
        0 | 1 => json!({"allOf": several(random, &mut below)}),
        2 | 3 => json!({"anyOf": several(random, &mut below)}),
        4 => json!({"oneOf": several(random, &mut below)}),
        5 => json!({"not": below(random)}),
        6 => {
            let mut condition = json!({"if": below(random)});
            for part in ["then", "else"] {
                if random.chance(70) {
                    condition[part] = below(random);
                }
            }
            condition
        }
        _ => json!({"dependentSchemas": {"a": below(random)}}),
    };
    // A keyword next to the connective, in the same schema.
    if random.chance(25) {
        let beside = [
            ("type", json!(["string", "null"])),
            ("minLength", json!(1)),
            ("pattern", json!("^a")),
            ("required", json!(["a"])),
            ("maximum", json!(1)),
        ];
        let about_objects = [
            ("type", json!("object")),
            ("required", json!(["a"])),
            ("maxProperties", json!(1)),
            ("additionalProperties", json!({"type": "null"})),
            ("propertyNames", json!({"pattern": "^a"})),
        ];
        let beside = if shape.of_objects {
            about_objects
        } else {
            beside
        };
        let (keyword, value) = beside[random.below(beside.len())].clone();
        schema[keyword] = value;
    }
    schema
}

/// The definitions of a document: `d`, which refers to nothing, and those of the shape,
/// which may refer to each other and to themselves. They are small, so that a reference is
/// a large part of what one says.
fn definitions(random: &mut Random, shape: Shape) -> Value {
    let without_reference = loop {
        let definition = plain(random, WITHOUT_CYCLES);
        if definition.get("$ref").is_none() {
            break definition;
        }
    };
    let mut definitions = json!({ "d": without_reference });
    for name in shape.definitions {
        definitions[name] = schema(random, 1, shape);
    }
    definitions
}

/// The schema as a document with these definitions.
fn document(mut schema: Value, definitions: &Value) -> Value {
    if schema.is_object() {
        schema["$defs"] = definitions.clone();
    }
    schema
}

/// What the engine made of a pair that the evaluator agrees with.
#[derive(Default)]
struct Tally {
    yes: usize,
    no: usize,
    /// The checks that ended in `No` with a number, those with a string, and those with
    /// an object that has a property.
    numbers: usize,
    strings: usize,
    objects: usize,
    unknown: usize,
    /// The checks that ended in `Unknown` although there was an instance to give.
    missed: usize,
}

impl Tally {
    /// Holds the verdict of the engine against the evaluator, which looks at these
    /// instances. `complete` says that the engine has to see everything that the evaluator
    /// sees, which it does where no schema refers to itself.
    fn compare(&mut self, a: &Value, b: &Value, instances: &[Value], complete: bool) {
        let names = ["d", "e", "f"].into_iter();
        let fragments = names.map(|name| (name.to_owned(), format!("/$defs/{name}")));
        let fragments = fragments.collect();
        let (of_a, of_b) = (&Document::new(a, &fragments), &Document::new(b, &fragments));
        let found: Vec<Found> = instances
            .iter()
            .map(|instance| found(of_a, of_b, instance))
            .collect();
        let subsumed = found.iter().all(|found| !found.some_tells_apart);
        // No leaf is about an instance that holds no array, so one of them that tells the
        // two apart is an instance to give.
        let mut exact = found.iter().filter(|found| found.exact);
        let one_tells_apart = exact.any(|found| found.some_tells_apart);
        let verdict = Checker::new().subsumes(a, b).unwrap();
        let context = format!("does {a} subsume {b}? {verdict:?}");
        match &verdict {
            Verdict::Yes => {
                assert!(subsumed, "{context}");
                self.yes += 1;
            }
            Verdict::No { counterexample } => {
                let found = self::found(of_a, of_b, counterexample);
                assert!(found.all_tell_apart, "{context}");
                self.no += 1;
                self.numbers += usize::from(counterexample.is_number());
                self.strings += usize::from(counterexample.is_string());
                let members = counterexample.as_object();
                self.objects += usize::from(members.is_some_and(|members| !members.is_empty()));
            }
            Verdict::Unknown {
                reason: Reason::Unsupported { .. },
            } => {
                assert!(!complete || !subsumed, "{context}");
                assert!(!complete || !one_tells_apart, "{context}");
                self.unknown += 1;
                // There was an instance to give, and the engine did not find a branch for it.
                self.missed += usize::from(found.iter().any(|found| found.all_tell_apart));
            }
            Verdict::Unknown { .. } => panic!("{context}"),
        }
    }
}

impl std::fmt::Display for Tally {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            yes,
            no,
            numbers,
            strings,
            objects,
            unknown,
            missed,
        } = self;
        write!(
            f,
            "{yes} Yes, {no} No, {numbers} of them with a number, {strings} with a string and {objects} with an object that has a property, {unknown} Unknown, {missed} of them with an instance to give"
        )
    }
}

/// The instances for schemas that say little of objects: everything that is no object, and
/// the objects that tell apart which of two properties there are.
fn mostly_plain() -> Vec<Value> {
    let mut instances = plain_instances();
    instances.extend(objects(&["a", "b"], &[json!(null)]));
    instances
}

/// The instances for schemas that are mostly about objects: a few that are no objects, and
/// the objects of up to two of four names with a few values.
fn mostly_objects() -> Vec<Value> {
    let values = [
        json!(null),
        json!(true),
        json!(1),
        json!(0.5),
        json!("a"),
        json!(""),
        json!([]),
        json!({}),
        json!({"a": null}),
    ];
    let mut instances = vec![json!(null), json!(0), json!("ab"), json!([])];
    instances.extend(values.iter().cloned());
    instances.extend(objects(&["a", "b", "ab", "c"], &values));
    instances
}

/// Makes each pattern of a schema one that is a word between `^` and `$`, which the store
/// of languages keeps as that word. The words are `a`, `b`, `ab` and the empty one.
fn with_patterns_of_one_word(schema: &mut Value) {
    let one_word = |pattern: &str| match pattern {
        "^a" => "^a$",
        "b$" => "^b$",
        "b" => "^ab$",
        _ => "^$",
    };
    match schema {
        Value::Object(keywords) => {
            if let Some(Value::String(pattern)) = keywords.get_mut("pattern") {
                *pattern = one_word(pattern).to_owned();
            }
            if let Some(Value::Object(patterns)) = keywords.get_mut("patternProperties") {
                let renamed = std::mem::take(patterns).into_iter();
                *patterns = renamed
                    .map(|(pattern, schema)| (one_word(&pattern).to_owned(), schema))
                    .collect();
            }
            keywords.values_mut().for_each(with_patterns_of_one_word);
        }
        Value::Array(items) => items.iter_mut().for_each(with_patterns_of_one_word),
        _ => {}
    }
}

#[test]
fn the_engine_agrees_with_every_instance_there_could_be() {
    let random = &mut Random(0);
    let shape = WITHOUT_CYCLES;
    let instances = mostly_plain();
    let mut tally = Tally::default();
    for pair in 0..4_000 {
        let (a, b) = (schema(random, 3, shape), schema(random, 3, shape));
        let (of_a, of_b) = (definitions(random, shape), definitions(random, shape));
        // Half of the time B is made out of A, so that the two share what they say. The
        // references in both parts then lead to the definition of A.
        let b = match pair % 4 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"anyOf": [a, b]}), &of_a),
            _ => document(b, &of_b),
        };
        let a = document(a, &of_a);
        tally.compare(&a, &b, &instances, true);
    }
    println!("{tally}");
    let Tally {
        yes,
        no,
        numbers,
        strings,
        unknown,
        ..
    } = tally;
    assert!(
        yes > 500 && no > 500 && numbers > 300 && strings > 300 && unknown > 20,
        "{yes} {no} {numbers} {strings} {unknown}"
    );
}

#[test]
fn the_engine_agrees_on_schemas_that_refer_to_themselves() {
    let random = &mut Random(1);
    let instances = mostly_plain();
    let mut tally = Tally::default();
    for pair in 0..3_000 {
        // In half of the pairs no reference is negated, so every definition says something
        // definite and a cycle accepts nothing by itself.
        let shape = Shape {
            definitions: &["e", "f"],
            never_negated: pair % 2 == 0,
            of_objects: false,
        };
        let (a, b) = (schema(random, 2, shape), schema(random, 2, shape));
        let of_a = definitions(random, shape);
        // B has the definitions of A, and in a third of the pairs its own under the same
        // names, which say something else. In another third it takes the two definitions
        // side by side, so that each is met before the other refers to it.
        let (e, f) = (json!({"$ref": "#/$defs/e"}), json!({"$ref": "#/$defs/f"}));
        let b = match pair % 3 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"allOf": [e, f, b]}), &of_a),
            _ => document(b, &definitions(random, shape)),
        };
        let a = document(a, &of_a);
        // The negation of a cycle is a leaf to the engine, and the evaluator knows it.
        tally.compare(&a, &b, &instances, false);
    }
    println!("{tally}");
    let Tally {
        yes,
        no,
        numbers,
        strings,
        unknown,
        ..
    } = tally;
    assert!(
        yes > 300 && no > 150 && numbers > 100 && strings > 100 && unknown > 100,
        "{yes} {no} {numbers} {strings} {unknown}"
    );
}

#[test]
fn the_engine_agrees_on_objects() {
    let random = &mut Random(2);
    let shape = Shape {
        definitions: &[],
        never_negated: false,
        of_objects: true,
    };
    let instances = mostly_objects();
    let mut tally = Tally::default();
    for pair in 0..1_500 {
        let (a, b) = (schema(random, 2, shape), schema(random, 2, shape));
        let (of_a, of_b) = (definitions(random, shape), definitions(random, shape));
        let b = match pair % 4 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"anyOf": [a, b]}), &of_a),
            _ => document(b, &of_b),
        };
        let a = document(a, &of_a);
        tally.compare(&a, &b, &instances, true);
    }
    println!("{tally}");
    let Tally {
        yes, no, objects, ..
    } = tally;
    assert!(
        yes > 200 && no > 500 && objects > 300,
        "{yes} {no} {objects}"
    );
}

#[test]
fn the_engine_agrees_on_patterns_of_one_word() {
    let random = &mut Random(4);
    let shape = Shape {
        definitions: &[],
        never_negated: false,
        of_objects: true,
    };
    // Every string of up to three letters as well, since a pattern is asked of strings too.
    let mut instances = mostly_objects();
    instances.extend(strings().into_iter().map(Value::String));
    let mut tally = Tally::default();
    for pair in 0..1_000 {
        let (a, b) = (schema(random, 2, shape), schema(random, 2, shape));
        let (of_a, of_b) = (definitions(random, shape), definitions(random, shape));
        let mut b = match pair % 4 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"anyOf": [a, b]}), &of_a),
            _ => document(b, &of_b),
        };
        let mut a = document(a, &of_a);
        with_patterns_of_one_word(&mut a);
        with_patterns_of_one_word(&mut b);
        tally.compare(&a, &b, &instances, true);
    }
    println!("{tally}");
    let Tally {
        yes, no, objects, ..
    } = tally;
    assert!(
        yes > 150 && no > 300 && objects > 200,
        "{yes} {no} {objects}"
    );
}

#[test]
fn the_engine_agrees_on_schemas_that_hold_themselves_in_a_property() {
    let random = &mut Random(3);
    // Objects in objects, three deep along the name `a`.
    let plain = [json!(null), json!(1)];
    let mut inner = plain.to_vec();
    inner.extend(objects(&["a", "b"], &plain));
    let mut instances = vec![json!("a"), json!([])];
    instances.extend(inner.iter().cloned());
    let deeper = objects(&["a", "b"], &inner);
    let deepest = deeper
        .iter()
        .filter(|object| object.as_object().unwrap().len() < 2);
    let deepest: Vec<Value> = deepest.map(|object| json!({"a": object})).collect();
    instances.extend(deeper);
    instances.extend(deepest);
    let mut tally = Tally::default();
    for pair in 0..700 {
        let shape = Shape {
            definitions: &["e", "f"],
            never_negated: pair % 2 == 0,
            of_objects: true,
        };
        let (a, b) = (schema(random, 2, shape), schema(random, 2, shape));
        let of_a = definitions(random, shape);
        let b = match pair % 3 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"anyOf": [a, b]}), &of_a),
            _ => document(b, &definitions(random, shape)),
        };
        let a = document(a, &of_a);
        tally.compare(&a, &b, &instances, false);
    }
    println!("{tally}");
    let Tally {
        yes, no, objects, ..
    } = tally;
    assert!(
        yes > 150 && no > 200 && objects > 100,
        "{yes} {no} {objects}"
    );
}
