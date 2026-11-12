//! A test that holds the engine against every instance there could be.
//!
//! To the engine an instance matters only by its type, by which boolean it is, and by which
//! of the leaves about its type it satisfies. A leaf may come out either way, since the engine
//! knows nothing of what it means. So the kinds of instance can all be listed: a type, a
//! boolean, and an answer for each leaf.
//!
//! A small evaluator here says for each kind whether a schema accepts it. It reads the JSON
//! and knows nothing of terms or branches, and it states again which keywords are about which
//! type and which of them are one leaf. The engine must agree with it:
//!
//! - `Yes` exactly when every kind that B accepts, A accepts.
//! - `No` only with an instance of which every kind is accepted by B and not by A.
//! - `Unknown` only when some kind is accepted by B and not by A.
//!
//! The schemas are made at random from the keywords that hold no schema inside a leaf.

use std::cell::RefCell;
use std::collections::BTreeMap;

use serde_json::{Value, json};

use crate::testing::Random;
use crate::{Checker, Reason, Verdict};

/// One kind of instance: its type, which boolean it is if it is one, and the leaves that it
/// satisfies. A leaf that was not given an answer is asked for and noted.
struct Kind<'k> {
    of_type: &'static str,
    boolean: bool,
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
            Value::Number(_) => {
                self.of_type == "number" && self.leaf("number", format!("const {value}"))
            }
            Value::String(_) => {
                self.of_type == "string" && self.leaf("string", format!("const {value}"))
            }
            other => panic!("no schema here has the constant {other}"),
        }
    }

    fn has(&self, name: &Value) -> bool {
        self.leaf("object", format!("required {name}"))
    }

    /// Whether a schema accepts the instance. Every part is looked at, also where the answer
    /// is settled before, so that every leaf is asked for.
    fn accepted_by(&self, root: &Value, schema: &Value) -> bool {
        let keywords = match schema {
            Value::Bool(accepts) => return *accepts,
            other => other
                .as_object()
                .expect("a schema is an object or a boolean"),
        };
        let every = |schemas: &Value| -> Vec<bool> {
            let schemas = schemas.as_array().unwrap().iter();
            schemas
                .map(|schema| self.accepted_by(root, schema))
                .collect()
        };
        let mut accepted = true;
        for (keyword, value) in keywords {
            accepted &= match keyword.as_str() {
                "$defs" | "then" | "else" => true,
                "$ref" => {
                    let pointer = value.as_str().unwrap().trim_start_matches('#');
                    self.accepted_by(root, root.pointer(pointer).unwrap())
                }
                "type" => {
                    let names = value
                        .as_array()
                        .cloned()
                        .unwrap_or_else(|| vec![value.clone()]);
                    let number = names.contains(&json!("number"));
                    let named = names.iter().map(|name| match name.as_str().unwrap() {
                        // An integer is a number that is a multiple of one.
                        "integer" if self.of_type == "number" => {
                            number || self.leaf("number", "multipleOf 1".to_owned())
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
                "allOf" => every(value).into_iter().all(|accepted| accepted),
                "anyOf" => every(value).into_iter().any(|accepted| accepted),
                "oneOf" => {
                    every(value)
                        .into_iter()
                        .filter(|accepted| *accepted)
                        .count()
                        == 1
                }
                "not" => !self.accepted_by(root, value),
                "if" => {
                    let part = |name| {
                        keywords
                            .get(name)
                            .is_none_or(|part| self.accepted_by(root, part))
                    };
                    let (then, otherwise) = (part("then"), part("else"));
                    if self.accepted_by(root, value) {
                        then
                    } else {
                        otherwise
                    }
                }
                "minLength" | "maxLength" => self.leaf("string", format!("{keyword} {value}")),
                "minimum" | "maximum" | "multipleOf" => {
                    self.leaf("number", format!("{keyword} {value}"))
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
                        let accepted = self.accepted_by(root, schema);
                        all & (self.of_type != "object" || !self.has(&json!(name)) || accepted)
                    })
                }
                other => panic!("no schema here has the keyword {other}"),
            };
        }
        accepted
    }
}

/// The types, with both booleans, and an instance of each.
fn kinds() -> [(&'static str, bool, Value); 7] {
    [
        ("null", false, json!(null)),
        ("boolean", true, json!(true)),
        ("boolean", false, json!(false)),
        ("number", false, json!(0)),
        ("string", false, json!("")),
        ("array", false, json!([])),
        ("object", false, json!({})),
    ]
}

/// What holds for the instances of one type that are one boolean.
struct Found {
    instance: Value,
    /// Some kind is accepted by B and not by A.
    some_tells_apart: bool,
    /// Every kind is.
    all_tell_apart: bool,
}

/// Lists every kind of instance and asks the evaluator about A and B.
fn evaluated(a: &Value, b: &Value) -> Vec<Found> {
    let ask = |of_type, boolean, satisfies: &BTreeMap<String, bool>| {
        let asked = RefCell::new(Vec::new());
        let kind = Kind {
            of_type,
            boolean,
            satisfies,
            asked: &asked,
        };
        let tells_apart = kind.accepted_by(b, b) & !kind.accepted_by(a, a);
        (tells_apart, asked.into_inner())
    };
    let found = kinds().into_iter().map(|(of_type, boolean, instance)| {
        // The first look finds the leaves that there are to answer.
        let (_, mut leaves) = ask(of_type, boolean, &BTreeMap::new());
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
            let (tells_apart, unanswered) = ask(of_type, boolean, &satisfies);
            assert_eq!(unanswered, Vec::<String>::new());
            found.some_tells_apart |= tells_apart;
            found.all_tell_apart &= tells_apart;
        }
        found
    });
    found.collect()
}

/// A schema without a schema below it.
fn plain(random: &mut Random) -> Value {
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
        json!({"minLength": 1}),
        json!({"minLength": 2, "type": "string"}),
        json!({"maxLength": 1}),
        json!({"minimum": 0}),
        json!({"maximum": 0, "type": "number"}),
        json!({"multipleOf": 1}),
        json!({"uniqueItems": true}),
        json!({"minItems": 1, "type": "array"}),
        json!({"required": ["a"]}),
        json!({"required": ["a", "b"], "type": "object"}),
        json!({"dependentRequired": {"a": ["b"]}}),
        json!({"$ref": "#/$defs/d"}),
    ];
    plain[random.below(plain.len())].clone()
}

fn schema(random: &mut Random, depth: usize) -> Value {
    if depth == 0 || random.chance(30) {
        return plain(random);
    }
    let mut below = |random: &mut Random| schema(random, depth - 1);
    let several = |random: &mut Random, below: &mut dyn FnMut(&mut Random) -> Value| {
        let count = 1 + random.below(3);
        Value::Array((0..count).map(|_| below(random)).collect())
    };
    let mut schema = match random.below(8) {
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
            ("required", json!(["a"])),
        ];
        let (keyword, value) = beside[random.below(beside.len())].clone();
        schema[keyword] = value;
    }
    schema
}

/// A schema without a reference, for the references of the others to lead to.
fn definition(random: &mut Random) -> Value {
    loop {
        let definition = plain(random);
        if definition.get("$ref").is_none() {
            return definition;
        }
    }
}

/// The schema as a document in which `#/$defs/d` is the definition.
fn document(mut schema: Value, definition: &Value) -> Value {
    if schema.is_object() {
        schema["$defs"] = json!({ "d": definition });
    }
    schema
}

#[test]
fn the_engine_agrees_with_every_instance_there_could_be() {
    let random = &mut Random(0);
    let (mut yes, mut no, mut unknown, mut missed) = (0, 0, 0, 0);
    for pair in 0..4_000 {
        let (a, b) = (schema(random, 3), schema(random, 3));
        let (of_a, of_b) = (definition(random), definition(random));
        // Half of the time B is made out of A, so that the two share what they say. The
        // references in both parts then lead to the definition of A.
        let b = match pair % 4 {
            0 => document(json!({"allOf": [a, b]}), &of_a),
            1 => document(json!({"anyOf": [a, b]}), &of_a),
            _ => document(b, &of_b),
        };
        let a = document(a, &of_a);
        let found = evaluated(&a, &b);
        let subsumed = found.iter().all(|found| !found.some_tells_apart);
        let verdict = Checker::new().subsumes(&a, &b).unwrap();
        let context = format!("does {a} subsume {b}? {verdict:?}");
        match &verdict {
            Verdict::Yes => {
                assert!(subsumed, "{context}");
                yes += 1;
            }
            Verdict::No { counterexample } => {
                let found = found.iter().find(|found| found.instance == *counterexample);
                let found = found.unwrap_or_else(|| panic!("{context}"));
                assert!(found.all_tell_apart, "{context}");
                no += 1;
            }
            Verdict::Unknown {
                reason: Reason::Unsupported { .. },
            } => {
                assert!(!subsumed, "{context}");
                unknown += 1;
                // There was an instance to give, and the engine did not find a branch for it.
                missed += usize::from(found.iter().any(|found| found.all_tell_apart));
            }
            Verdict::Unknown { .. } => panic!("{context}"),
        }
    }
    println!("{yes} Yes, {no} No, {unknown} Unknown, {missed} of them with an instance to give");
    assert!(
        yes > 500 && no > 500 && unknown > 200,
        "{yes} {no} {unknown}"
    );
}
