//! A test that holds the engine against every instance there could be.
//!
//! To the engine an instance matters only by its type, by which boolean, which number or
//! which string it is, and by which of the leaves about its type it satisfies. A leaf may
//! come out either way, since the engine knows nothing of what it means. So the kinds of
//! instance can all be listed: a type, a boolean, a number or a string, and an answer for
//! each leaf.
//!
//! A small evaluator here says for each kind whether a schema accepts it. It reads the JSON
//! and knows nothing of terms or branches, and it states again which keywords are about which
//! type and which of them are one leaf. The engine must agree with it:
//!
//! - `Yes` exactly when every kind that B accepts, A accepts.
//! - `No` only with an instance of which every kind is accepted by B and not by A.
//! - `Unknown` only when some kind is accepted by B and not by A, and no number and no
//!   string is.
//!
//! The schemas are made at random from the keywords that hold no schema inside a leaf.
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

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use serde_json::{Value, json};

use crate::testing::Random;
use crate::{Checker, Reason, Verdict};

/// One kind of instance: its type, which boolean it is if it is one, which number if it is
/// one, which string if it is one, and the leaves that it satisfies. A leaf that was not
/// given an answer is asked for and noted.
struct Kind<'k> {
    of_type: &'static str,
    boolean: bool,
    number: f64,
    string: &'k str,
    satisfies: &'k BTreeMap<String, bool>,
    asked: &'k RefCell<Vec<String>>,
}

impl Kind<'_> {
    /// Whether the instance satisfies a leaf about the type `about`. An instance of another
    /// type satisfies every such leaf.
    fn leaf(&self, about: &str, key: String) -> bool {
        if self.of_type != about {
            return true;
        }
        let answer = self.satisfies.get(&key).copied();
        answer.unwrap_or_else(|| {
            self.asked.borrow_mut().push(key);
            false
        })
    }

    fn is(&self, value: &Value) -> bool {
        match value {
            Value::Null => self.of_type == "null",
            Value::Bool(value) => self.of_type == "boolean" && self.boolean == *value,
            Value::Number(value) => self.of_type == "number" && value.as_f64() == Some(self.number),
            Value::String(value) => self.of_type == "string" && self.string == value,
            other => panic!("no schema here has the constant {other}"),
        }
    }

    /// Whether the instance is no string, or a string of which this holds.
    fn string(&self, holds: impl Fn(&str) -> bool) -> bool {
        self.of_type != "string" || holds(self.string)
    }

    /// Whether the instance is no number, or a number of which this holds.
    fn number(&self, holds: impl Fn(f64) -> bool) -> bool {
        self.of_type != "number" || holds(self.number)
    }

    fn has(&self, name: &Value) -> bool {
        self.leaf("object", format!("required {name}"))
    }

    /// Whether a schema accepts the instance, given what the definitions accept. A reference
    /// reads `plain`, and one that stands under a negation reads `negated`; `under_negation`
    /// says which of the two the schema itself stands under. Every part is looked at, also
    /// where the answer is settled before, so that every leaf is asked for.
    fn accepted_by(&self, schema: &Value, under_negation: bool, read: &Readings) -> bool {
        let keywords = match schema {
            Value::Bool(accepts) => return *accepts,
            other => other
                .as_object()
                .expect("a schema is an object or a boolean"),
        };
        let accepts = |schema: &Value| self.accepted_by(schema, under_negation, read);
        // The same schema where its negation is what counts.
        let rejects = |schema: &Value| !self.accepted_by(schema, !under_negation, read);
        let every = |schemas: &Value, accepts: &dyn Fn(&Value) -> bool| -> Vec<bool> {
            schemas.as_array().unwrap().iter().map(accepts).collect()
        };
        // The number that a keyword about numbers holds.
        let at = |value: &Value| value.as_f64().expect("the keyword holds a number");
        let count = |value: &Value| value.as_u64().expect("the keyword holds a count") as usize;
        let mut accepted = true;
        for (keyword, value) in keywords {
            accepted &= match keyword.as_str() {
                "$defs" | "then" | "else" => true,
                "$ref" => {
                    let pointer = value.as_str().unwrap().trim_start_matches('#');
                    let definitions = if under_negation {
                        read.negated
                    } else {
                        read.plain
                    };
                    definitions[pointer]
                }
                "type" => {
                    let names = value
                        .as_array()
                        .cloned()
                        .unwrap_or_else(|| vec![value.clone()]);
                    let number = names.contains(&json!("number"));
                    let named = names.iter().map(|name| match name.as_str().unwrap() {
                        // An integer is a number without a fraction.
                        "integer" if self.of_type == "number" => {
                            number || self.number.fract() == 0.0
                        }
                        name => name == self.of_type,
                    });
                    named.fold(false, |any, named| any | named)
                }
                "const" => self.is(value),
                "enum" => {
                    let values = value.as_array().unwrap().iter();
                    values.fold(false, |any, value| any | self.is(value))
                }
                "allOf" => every(value, &accepts).into_iter().all(|accepted| accepted),
                "anyOf" => every(value, &accepts).into_iter().any(|accepted| accepted),
                // One is accepted and every other is rejected.
                "oneOf" => {
                    let (accepted, rejected) = (every(value, &accepts), every(value, &rejects));
                    (0..accepted.len()).any(|one| {
                        let others = (0..rejected.len()).filter(|other| *other != one);
                        accepted[one] && others.fold(true, |all, other| all & rejected[other])
                    })
                }
                "not" => rejects(value),
                // The condition is rejected or `then` holds, and it is accepted or `else` holds.
                "if" => {
                    let part = |name| keywords.get(name).is_none_or(accepts);
                    let (then, otherwise) = (part("then"), part("else"));
                    (rejects(value) | then) & (accepts(value) | otherwise)
                }
                "minLength" => self.string(|string| string.chars().count() >= count(value)),
                "maxLength" => self.string(|string| string.chars().count() <= count(value)),
                "pattern" => self.string(|string| matches(value.as_str().unwrap(), string)),
                "minimum" => self.number(|number| number >= at(value)),
                "maximum" => self.number(|number| number <= at(value)),
                "exclusiveMinimum" => self.number(|number| number > at(value)),
                "exclusiveMaximum" => self.number(|number| number < at(value)),
                "multipleOf" => self.number(|number| (number / at(value)).fract() == 0.0),
                "uniqueItems" => value == &json!(false) || self.leaf("array", keyword.clone()),
                "minItems" => self.leaf("array", format!("{keyword} {value}")),
                "required" => {
                    let names = value.as_array().unwrap().iter();
                    names.fold(true, |all, name| all & self.has(name))
                }
                "dependentRequired" => {
                    let dependencies = value.as_object().unwrap().iter();
                    dependencies.fold(true, |all, (name, needed)| {
                        let needed = needed.as_array().unwrap().iter();
                        let needed = needed.fold(true, |all, name| all & self.has(name));
                        all & (self.of_type != "object" || !self.has(&json!(name)) || needed)
                    })
                }
                "dependentSchemas" => {
                    let dependencies = value.as_object().unwrap().iter();
                    dependencies.fold(true, |all, (name, schema)| {
                        let accepted = accepts(schema);
                        all & (self.of_type != "object" || !self.has(&json!(name)) || accepted)
                    })
                }
                other => panic!("no schema here has the keyword {other}"),
            };
        }
        accepted
    }

    /// What the definitions of a document accept when they are read until nothing changes,
    /// beginning with definitions that accept nothing. A negated reference reads `negated`.
    fn read_out<'d>(&self, document: &Document<'d>, negated: &Definitions) -> Definitions<'d> {
        let mut plain = document.accepting_nothing();
        loop {
            let read = Readings {
                plain: &plain,
                negated,
            };
            let next: Definitions = document
                .definitions
                .iter()
                .map(|(at, schema)| (*at, self.accepted_by(schema, false, &read)))
                .collect();
            if next == plain {
                return plain;
            }
            plain = next;
        }
    }

    /// Whether a document surely accepts the instance, and whether it possibly does.
    fn accepted(&self, document: &Document) -> (bool, bool) {
        let mut surely = document.accepting_nothing();
        let possibly = loop {
            let possibly = self.read_out(document, &surely);
            let next = self.read_out(document, &possibly);
            if next == surely {
                break possibly;
            }
            surely = next;
        };
        let read = |plain, negated| {
            let read = Readings { plain, negated };
            self.accepted_by(document.schema, false, &read)
        };
        // Where the two readings are one, so is what the schema makes of them.
        if surely == possibly {
            let accepted = read(&surely, &surely);
            return (accepted, accepted);
        }
        (read(&surely, &possibly), read(&possibly, &surely))
    }
}

/// Whether each definition of a document accepts an instance, by the fragment that a
/// reference to it holds.
type Definitions<'d> = BTreeMap<&'d str, bool>;

/// What the definitions accept: for a reference as it stands, and for a negated one.
struct Readings<'r> {
    plain: &'r Definitions<'r>,
    negated: &'r Definitions<'r>,
}

/// A schema with its definitions, by the fragment that a reference to each holds.
struct Document<'d> {
    schema: &'d Value,
    definitions: Vec<(&'d str, &'d Value)>,
}

impl<'d> Document<'d> {
    /// `fragments` holds the fragment of every definition that a schema here may have.
    fn new(schema: &'d Value, fragments: &'d BTreeMap<String, String>) -> Self {
        let definitions = schema.get("$defs").and_then(Value::as_object);
        let definitions = definitions.into_iter().flatten();
        let definitions = definitions.map(|(name, schema)| (fragments[name].as_str(), schema));
        Self {
            schema,
            definitions: definitions.collect(),
        }
    }

    fn accepting_nothing(&self) -> Definitions<'d> {
        let fragments = self.definitions.iter();
        fragments.map(|(fragment, _)| (*fragment, false)).collect()
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

/// An instance apart from its leaves: its type, which boolean it is, which number, and which
/// string.
type Instance = (&'static str, bool, f64, String);

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

/// The types, with both booleans, with a number of every kind and with a string of every
/// kind.
fn instances() -> Vec<Instance> {
    let none = String::new;
    let others = ["null", "array", "object"].map(|of_type| (of_type, false, 0.0, none()));
    let booleans = [true, false].map(|boolean| ("boolean", boolean, 0.0, none()));
    let numbers = QUARTERS.map(|quarters| ("number", false, f64::from(quarters) / 4.0, none()));
    let strings = strings()
        .into_iter()
        .map(|string| ("string", false, 0.0, string));
    let listed = others.into_iter().chain(booleans).chain(numbers);
    listed.chain(strings).collect()
}

/// What a value is apart from its leaves. Of an array and an object, the engine gives the
/// empty one only.
fn instance_of(value: &Value) -> Instance {
    let none = String::new;
    match value {
        Value::Null => ("null", false, 0.0, none()),
        Value::Bool(boolean) => ("boolean", *boolean, 0.0, none()),
        Value::Number(number) => ("number", false, number.as_f64().expect("a float"), none()),
        Value::String(text) => ("string", false, 0.0, text.clone()),
        Value::Array(items) if items.is_empty() => ("array", false, 0.0, none()),
        Value::Object(members) if members.is_empty() => ("object", false, 0.0, none()),
        other => panic!("the engine does not give {other} yet"),
    }
}

/// What holds for the instances that are alike apart from their leaves.
struct Found {
    of_type: &'static str,
    /// Some kind is surely accepted by B and not possibly by A.
    some_tells_apart: bool,
    /// Every kind is.
    all_tell_apart: bool,
}

/// Asks the evaluator about A and B, for an instance with every way of answering the leaves
/// about it.
fn found(a: &Document, b: &Document, instance: &Instance) -> Found {
    let (of_type, boolean, number, string) = (instance.0, instance.1, instance.2, &instance.3);
    let ask = |satisfies: &BTreeMap<String, bool>| {
        let asked = RefCell::new(Vec::new());
        let kind = Kind {
            of_type,
            boolean,
            number,
            string,
            satisfies,
            asked: &asked,
        };
        let ((_, a_possibly), (b_surely, _)) = (kind.accepted(a), kind.accepted(b));
        (b_surely & !a_possibly, asked.into_inner())
    };
    // The first look finds the leaves that there are to answer. Without any, as for every
    // number and every string, it is the answer.
    let (tells_apart, mut leaves) = ask(&BTreeMap::new());
    if leaves.is_empty() {
        return Found {
            of_type,
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
        of_type,
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
}

/// Schemas that refer to `d` only, so that none refers to itself.
const WITHOUT_CYCLES: Shape = Shape {
    definitions: &[],
    never_negated: false,
};

/// A schema without a schema below it. More often than not it is a reference to one of
/// the definitions of the shape, so that cycles are common.
fn plain(random: &mut Random, shape: Shape) -> Value {
    if !shape.definitions.is_empty() && random.chance(60) {
        let name = shape.definitions[random.below(shape.definitions.len())];
        return json!({"$ref": format!("#/$defs/{name}")});
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
    /// The checks that ended in `No` with a number, and those with a string.
    numbers: usize,
    strings: usize,
    unknown: usize,
    /// The checks that ended in `Unknown` although there was an instance to give.
    missed: usize,
}

impl Tally {
    /// Holds the verdict of the engine against the evaluator. `complete` says that the
    /// engine has to see everything that the evaluator sees, which it does where no schema
    /// refers to itself.
    fn compare(&mut self, a: &Value, b: &Value, complete: bool) {
        let names = ["d", "e", "f"].into_iter();
        let fragments = names.map(|name| (name.to_owned(), format!("/$defs/{name}")));
        let fragments = fragments.collect();
        let (of_a, of_b) = (&Document::new(a, &fragments), &Document::new(b, &fragments));
        let instances = instances().into_iter();
        let found: Vec<Found> = instances
            .map(|instance| found(of_a, of_b, &instance))
            .collect();
        let subsumed = found.iter().all(|found| !found.some_tells_apart);
        // No leaf is about numbers or about strings, so one of them that tells the two apart
        // is an instance.
        let without_leaves = |found: &&Found| ["number", "string"].contains(&found.of_type);
        let mut exact = found.iter().filter(without_leaves);
        let one_tells_apart = exact.any(|found| found.some_tells_apart);
        let verdict = Checker::new().subsumes(a, b).unwrap();
        let context = format!("does {a} subsume {b}? {verdict:?}");
        match &verdict {
            Verdict::Yes => {
                assert!(subsumed, "{context}");
                self.yes += 1;
            }
            Verdict::No { counterexample } => {
                let found = self::found(of_a, of_b, &instance_of(counterexample));
                assert!(found.all_tell_apart, "{context}");
                self.no += 1;
                self.numbers += usize::from(counterexample.is_number());
                self.strings += usize::from(counterexample.is_string());
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
            unknown,
            missed,
        } = self;
        write!(
            f,
            "{yes} Yes, {no} No, {numbers} of them with a number and {strings} with a string, {unknown} Unknown, {missed} of them with an instance to give"
        )
    }
}

#[test]
fn the_engine_agrees_with_every_instance_there_could_be() {
    let random = &mut Random(0);
    let shape = WITHOUT_CYCLES;
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
        tally.compare(&a, &b, true);
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
        yes > 500 && no > 500 && numbers > 300 && strings > 300 && unknown > 100,
        "{yes} {no} {numbers} {strings} {unknown}"
    );
}

#[test]
fn the_engine_agrees_on_schemas_that_refer_to_themselves() {
    let random = &mut Random(1);
    let mut tally = Tally::default();
    for pair in 0..3_000 {
        // In half of the pairs no reference is negated, so every definition says something
        // definite and a cycle accepts nothing by itself.
        let shape = Shape {
            definitions: &["e", "f"],
            never_negated: pair % 2 == 0,
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
        tally.compare(&a, &b, false);
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
