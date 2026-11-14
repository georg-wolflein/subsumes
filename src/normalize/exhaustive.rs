//! A test that holds the engine against every instance there could be.
//!
//! To the engine an instance matters only by its type, by which boolean or which number it
//! is, and by which of the leaves about its type it satisfies. A leaf may come out either way,
//! since the engine knows nothing of what it means. So the kinds of instance can all be
//! listed: a type, a boolean or a number, and an answer for each leaf.
//!
//! A small evaluator here says for each kind whether a schema accepts it. It reads the JSON
//! and knows nothing of terms or branches, and it states again which keywords are about which
//! type and which of them are one leaf. The engine must agree with it:
//!
//! - `Yes` exactly when every kind that B accepts, A accepts.
//! - `No` only with an instance of which every kind is accepted by B and not by A.
//! - `Unknown` only when some kind is accepted by B and not by A, and that kind is no number:
//!   no leaf is about numbers, so a number that tells the two apart is a counterexample.
//!
//! The schemas are made at random from the keywords that hold no schema inside a leaf.
//!
//! # Numbers
//!
//! Every number in these schemas is a multiple of a half from -1.5 to 2.5, and `multipleOf`
//! holds 0.5, 1 or 3. A number matters by where it lies among those numbers and by which of
//! them it is a multiple of. Further out than the outermost, the multiples repeat every 3.
//! A number that is no multiple of a half is a multiple of none, and one such lies between
//! any two multiples of a half: the odd quarter. So the quarters from -5 to 6 hold a number
//! of every kind. The evaluator counts in thousandths, which holds them and whatever number
//! the engine gives.
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
use std::collections::BTreeMap;

use serde_json::{Value, json};

use crate::testing::Random;
use crate::{Checker, Reason, Verdict};

/// One kind of instance: its type, which boolean it is if it is one, which number, in
/// thousandths, if it is one, and the leaves that it satisfies. A leaf that was not given an
/// answer is asked for and noted.
struct Kind<'k> {
    of_type: &'static str,
    boolean: bool,
    number: i64,
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
            Value::Number(_) => self.of_type == "number" && self.number == thousandths(value),
            Value::String(_) => {
                self.of_type == "string" && self.leaf("string", format!("const {value}"))
            }
            other => panic!("no schema here has the constant {other}"),
        }
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
                        // An integer is a number that is a multiple of one.
                        "integer" if self.of_type == "number" => number || self.number % 1000 == 0,
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
                "minLength" | "maxLength" => self.leaf("string", format!("{keyword} {value}")),
                "minimum" | "maximum" | "exclusiveMinimum" | "exclusiveMaximum" | "multipleOf" => {
                    let (number, value) = (self.number, thousandths(value));
                    self.of_type != "number"
                        || match keyword.as_str() {
                            "minimum" => number >= value,
                            "maximum" => number <= value,
                            "exclusiveMinimum" => number > value,
                            "exclusiveMaximum" => number < value,
                            _ => number % value == 0,
                        }
                }
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

/// A number in thousandths. The numbers here have no more places than that.
fn thousandths(number: &Value) -> i64 {
    let scaled = number.as_f64().unwrap() * 1000.0;
    assert!(scaled.fract() == 0.0, "{number} has more than three places");
    scaled as i64
}

/// The types, with both booleans and a number of every kind, and an instance of each. The
/// number that the engine gave, if it gave one, is among them.
fn kinds(given: Option<&Value>) -> Vec<(&'static str, bool, i64, Value)> {
    let other = |of_type, instance| (of_type, false, 0, instance);
    let mut kinds = vec![
        other("null", json!(null)),
        ("boolean", true, 0, json!(true)),
        other("boolean", json!(false)),
        other("string", json!("")),
        other("array", json!([])),
        other("object", json!({})),
    ];
    // The engine writes a whole number as an integer.
    let quarters = (-20..=24).map(|quarters| match quarters % 4 {
        0 => json!(quarters / 4),
        _ => json!(f64::from(quarters) / 4.0),
    });
    let numbers = quarters.chain(given.filter(|given| given.is_number()).cloned());
    kinds.extend(numbers.map(|number| ("number", false, thousandths(&number), number)));
    kinds
}

/// What holds for the instances of one type that are one boolean or one number.
struct Found {
    instance: Value,
    /// Some kind is surely accepted by B and not possibly by A.
    some_tells_apart: bool,
    /// Every kind is.
    all_tell_apart: bool,
}

/// Lists every kind of instance and asks the evaluator about A and B. `given` is the
/// instance that the engine gave, if it gave one.
fn evaluated(a: &Value, b: &Value, given: Option<&Value>) -> Vec<Found> {
    let names = ["d", "e", "f"].into_iter();
    let fragments = names.map(|name| (name.to_owned(), format!("/$defs/{name}")));
    let fragments = fragments.collect();
    let (a, b) = (&Document::new(a, &fragments), &Document::new(b, &fragments));
    let ask = |of_type, boolean, number, satisfies: &BTreeMap<String, bool>| {
        let asked = RefCell::new(Vec::new());
        let kind = Kind {
            of_type,
            boolean,
            number,
            satisfies,
            asked: &asked,
        };
        let ((_, a_possibly), (b_surely, _)) = (kind.accepted(a), kind.accepted(b));
        (b_surely & !a_possibly, asked.into_inner())
    };
    let kinds = kinds(given).into_iter();
    let found = kinds.map(|(of_type, boolean, number, instance)| {
        // The first look finds the leaves that there are to answer.
        let (_, mut leaves) = ask(of_type, boolean, number, &BTreeMap::new());
        leaves.sort();
        leaves.dedup();
        assert!(
            leaves.len() <= 14,
            "{} leaves are too many to list",
            leaves.len()
        );
        let mut found = Found {
            instance,
            some_tells_apart: false,
            all_tell_apart: true,
        };
        for answers in 0..1_u32 << leaves.len() {
            let answer = |place: usize| answers >> place & 1 == 1;
            let satisfies = leaves.iter().cloned().enumerate();
            let satisfies = satisfies
                .map(|(place, leaf)| (leaf, answer(place)))
                .collect();
            let (tells_apart, unanswered) = ask(of_type, boolean, number, &satisfies);
            assert_eq!(unanswered, Vec::<String>::new());
            found.some_tells_apart |= tells_apart;
            found.all_tell_apart &= tells_apart;
        }
        found
    });
    found.collect()
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
        json!({"const": 2.5}),
        json!({"enum": [0, 1.0, "a"]}),
        json!({"const": "a"}),
        json!({"minLength": 1}),
        json!({"minLength": 2, "type": "string"}),
        json!({"maxLength": 1}),
        json!({"minimum": 0}),
        json!({"minimum": -1.5, "maximum": 1}),
        json!({"maximum": 0, "type": "number"}),
        json!({"maximum": 2.5}),
        json!({"exclusiveMinimum": 0}),
        json!({"exclusiveMinimum": 1, "type": "integer"}),
        json!({"exclusiveMaximum": 2.5}),
        json!({"exclusiveMaximum": 1, "minimum": 0}),
        json!({"multipleOf": 1}),
        json!({"multipleOf": 0.5}),
        json!({"multipleOf": 3, "type": "number"}),
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
            ("type", json!("number")),
            ("maximum", json!(1)),
            ("minLength", json!(1)),
            ("required", json!(["a"])),
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
    unknown: usize,
    /// The checks that ended in `Unknown` although there was an instance to give.
    missed: usize,
}

impl Tally {
    /// Holds the verdict of the engine against the evaluator. `complete` says that the
    /// engine has to see everything that the evaluator sees, which it does where no schema
    /// refers to itself.
    fn compare(&mut self, a: &Value, b: &Value, complete: bool) {
        let verdict = Checker::new().subsumes(a, b).unwrap();
        let given = match &verdict {
            Verdict::No { counterexample } => Some(counterexample),
            _ => None,
        };
        let found = evaluated(a, b, given);
        let subsumed = found.iter().all(|found| !found.some_tells_apart);
        let context = format!("does {a} subsume {b}? {verdict:?}");
        match &verdict {
            Verdict::Yes => {
                assert!(subsumed, "{context}");
                self.yes += 1;
            }
            Verdict::No { counterexample } => {
                let found = found.iter().find(|found| found.instance == *counterexample);
                let found = found.unwrap_or_else(|| panic!("{context}"));
                assert!(found.all_tell_apart, "{context}");
                self.no += 1;
            }
            Verdict::Unknown {
                reason: Reason::Unsupported { .. },
            } => {
                assert!(!complete || !subsumed, "{context}");
                // No leaf is about numbers, so one that tells the two apart is given.
                let mut numbers = found.iter().filter(|found| found.instance.is_number());
                assert!(
                    !complete || !numbers.any(|found| found.some_tells_apart),
                    "{context}"
                );
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
            unknown,
            missed,
        } = self;
        write!(
            f,
            "{yes} Yes, {no} No, {unknown} Unknown, {missed} of them with an instance to give"
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
        yes, no, unknown, ..
    } = tally;
    assert!(
        yes > 500 && no > 500 && unknown > 200,
        "{yes} {no} {unknown}"
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
        yes, no, unknown, ..
    } = tally;
    assert!(
        yes > 300 && no > 150 && unknown > 100,
        "{yes} {no} {unknown}"
    );
}
