//! Which schemas say the same.
//!
//! Two schemas are of one class when they have the same keywords with the same values, and
//! the subschemas and reference targets in each place are of one class in turn. For schemas
//! that refer to themselves, that is read as far as it goes: two are of one class unless
//! following the same places from both leads to a difference. Schemas of one class accept
//! the same instances, so the engine gives them one variable, and `x` and `not x` cancel
//! without anything inside being opened. A and B are classed together, so what two versions
//! of a schema share is found here.
//!
//! A schema is classed as it is reached: once for each dynamic scope, since a `$dynamicRef`
//! below it may lead to one schema in one scope and to another in the next. Where it leads
//! to in a scope is a reference target like any other.

use std::collections::{HashMap, HashSet};
use std::convert::Infallible;
use std::hash::Hash;

use serde_json::{Number, Value};

use super::scopes::{Lists, Scopes};
use super::too_deep;
use crate::context::{Budget, Exhausted};
use crate::rational::exact;
use crate::schema::{Count, Graph, Keywords, Node, NodeId, Part, Schema};

/// A value as JSON text, which is equal for two values exactly when they are written alike.
macro_rules! written {
    ($value:expr) => {
        serde_json::to_string($value).expect("the value is written as JSON")
    };
}
pub(super) use written;

/// Writes a value as that text at the end of a buffer.
macro_rules! write_json {
    ($value:expr, $text:expr) => {
        serde_json::to_writer(&mut *$text, $value).expect("the value is written as JSON")
    };
}

/// The class of every schema as it is reached, in the order in which `scopes` has them, and
/// whether a schema leads back to itself.
///
/// # Errors
///
/// When schemas that refer to themselves take more rounds to tell apart than the budget
/// covers. Without such schemas the work is one pass and costs nothing.
pub(super) fn classes(
    graph: &Graph,
    scopes: &Scopes,
    budget: &mut Budget,
) -> Result<(Vec<u32>, bool), Exhausted> {
    let count = scopes.len();
    // What each schema says by itself, as a number. What it leads to is in `scopes`. Every
    // text is written into the one buffer, and only a new one is copied out of it.
    let mut texts: HashMap<Box<[u8]>, u32> = HashMap::with_capacity(count);
    let mut text = Vec::new();
    let mut own = Vec::with_capacity(count);
    for index in 0..count {
        let id = scopes.at(index).node;
        text.clear();
        describe(id, graph.node(id), &mut text);
        own.push(numbered(&mut texts, &text));
    }
    let successors = scopes.leads_to();
    let (order, cyclic) = components(successors);

    // A node that is on no cycle gets its class from the classes of the nodes it leads to,
    // which are known before it. The nodes on cycles are told apart in rounds: all are one
    // block at first, and each round separates those that differ one step further in. When a
    // round separates nothing, nothing will.
    //
    // A class is the number of a list: what a schema says by itself, and then the class of
    // each schema that it leads to.
    const UNTOLD: u32 = u32::MAX;
    let mut numbers: HashMap<Box<[u32]>, u32> = HashMap::with_capacity(count);
    let mut said = Vec::new();
    let mut previous = vec![UNTOLD; count];
    let mut blocks = usize::from(cyclic.contains(&true));
    loop {
        let mut current = vec![UNTOLD; count];
        for &node in &order {
            said.clear();
            said.push(own[node]);
            let places = successors.of(node).iter();
            said.extend(places.map(|&to| {
                if cyclic[to] {
                    previous[to]
                } else {
                    current[to]
                }
            }));
            current[node] = numbered(&mut numbers, &said);
        }
        let on_cycles = (0..count).filter(|&node| cyclic[node]);
        let told_apart: HashSet<u32> = on_cycles.map(|node| current[node]).collect();
        if told_apart.len() == blocks {
            return Ok((current, blocks > 0));
        }
        blocks = told_apart.len();
        previous = current;
        budget.charge(count as u64)?;
    }
}

/// The number of a key: the one that it has, or the next one if the key is new. Only a new
/// key is copied.
fn numbered<T: Clone + Eq + Hash>(numbers: &mut HashMap<Box<[T]>, u32>, key: &[T]) -> u32 {
    if let Some(known) = numbers.get(key) {
        return *known;
    }
    let next = u32::try_from(numbers.len()).expect("a check has fewer than 2^32 classes");
    numbers.insert(key.into(), next);
    next
}

/// Writes what a node says by itself, as text that is equal for two nodes exactly when they
/// say the same apart from the schemas they lead to. The text names those in the order in
/// which `Scopes` has them: the subschemas of the keywords, the target of `$ref`, and what
/// `$dynamicRef` leads to, which is a reference target as that of `$ref` is.
///
/// Every schema that is reached is described, so the text is written without the formatter
/// and without a string for each of its parts.
fn describe(id: NodeId, node: &Node, text: &mut Vec<u8>) {
    let keywords = match &node.schema {
        Schema::Bool(true) => return text.extend_from_slice(b"true"),
        Schema::Bool(false) => return text.extend_from_slice(b"false"),
        Schema::Object(keywords) => keywords,
    };
    let visited = keywords.visit_subschemas(|keyword, part, _| {
        text.extend_from_slice(keyword.as_bytes());
        match part {
            Part::Whole => {}
            Part::Name(name) => write_word(name, text),
            Part::Index(_) => text.extend_from_slice(b"[]"),
        }
        text.push(b';');
        Ok::<_, Infallible>(())
    });
    visited.unwrap_or_else(|never| match never {});
    let references = [
        keywords.reference.is_some(),
        keywords.dynamic_reference.is_some(),
    ];
    for _ in references.into_iter().filter(|there| *there) {
        text.extend_from_slice(b"$ref;");
    }
    assertions(id, keywords, text);
}

/// The keywords of a schema that hold no schema, each with its value.
fn assertions(id: NodeId, keywords: &Keywords, text: &mut Vec<u8>) {
    /// Writes a keyword with its value, if the schema has the keyword.
    fn put<T>(
        text: &mut Vec<u8>,
        keyword: &str,
        value: Option<T>,
        write: impl FnOnce(T, &mut Vec<u8>),
    ) {
        if let Some(value) = value {
            text.extend_from_slice(keyword.as_bytes());
            text.push(b'=');
            write(value, text);
            text.push(b';');
        }
    }
    // A count that was too large to keep is not known to equal another one.
    let unlike_any_other = |text: &mut Vec<u8>| {
        text.push(b'@');
        write_digits(id.index() as u64, text);
    };
    let count = |count: Count, text: &mut Vec<u8>| match count {
        Count::Of(count) => write_digits(count, text),
        Count::Beyond => unlike_any_other(text),
    };
    // A value that is nested deeper than an instance may be is not written out, and is like
    // no other.
    let constant = |value: &Value, text: &mut Vec<u8>| {
        if too_deep(value) {
            unlike_any_other(text);
        } else {
            write_value(value, text);
        }
    };
    let listed = |values: &[Value], text: &mut Vec<u8>| {
        for (place, value) in values.iter().enumerate() {
            if place > 0 {
                text.push(b',');
            }
            constant(value, text);
        }
    };
    let (required, dependent) = (&keywords.required, &keywords.dependent_required);

    // `$dynamicAnchor` says nothing of an instance: it is a name, as `$anchor` is.
    put(text, "type", keywords.types, |types, text| {
        write_digits(types.bits().into(), text);
    });
    put(text, "enum", keywords.enumeration, listed);
    put(text, "const", keywords.constant, constant);
    put(text, "minimum", keywords.minimum, write_number);
    put(text, "maximum", keywords.maximum, write_number);
    put(
        text,
        "exclusiveMinimum",
        keywords.exclusive_minimum,
        write_number,
    );
    put(
        text,
        "exclusiveMaximum",
        keywords.exclusive_maximum,
        write_number,
    );
    put(text, "multipleOf", keywords.multiple_of, write_number);
    put(text, "minLength", keywords.min_length, count);
    put(text, "maxLength", keywords.max_length, count);
    put(text, "pattern", keywords.pattern, write_word);
    put(text, "format", keywords.format, write_word);
    put(text, "minContains", keywords.min_contains, count);
    put(text, "maxContains", keywords.max_contains, count);
    put(text, "minItems", keywords.min_items, count);
    put(text, "maxItems", keywords.max_items, count);
    put(
        text,
        "uniqueItems",
        keywords.unique_items.then_some(()),
        |(), _| {},
    );
    let required = Some(required).filter(|names| !names.is_empty());
    put(text, "required", required, |names, text| {
        write_words(names, text)
    });
    let dependent = Some(dependent).filter(|names| !names.is_empty());
    put(text, "dependentRequired", dependent, |dependent, text| {
        write_length(dependent.len(), text);
        for (name, needed) in dependent {
            write_word(name, text);
            write_words(needed, text);
        }
    });
    put(text, "minProperties", keywords.min_properties, count);
    put(text, "maxProperties", keywords.max_properties, count);
}

/// Writes a word as its length and then its bytes, so that where it ends is known without a
/// look at the bytes, and no byte has to be escaped.
fn write_word(word: &str, text: &mut Vec<u8>) {
    write_length(word.len(), text);
    text.extend_from_slice(word.as_bytes());
}

/// Writes a list of words as their number and then each word.
fn write_words(words: &[&str], text: &mut Vec<u8>) {
    write_length(words.len(), text);
    for word in words {
        write_word(word, text);
    }
}

/// Writes a length seven bits to a byte, from the lowest on, with the highest bit of every
/// byte but the last set. So where the length ends is known.
fn write_length(mut length: usize, text: &mut Vec<u8>) {
    while length >= 0x80 {
        text.push(0x80 | (length & 0x7f) as u8);
        length >>= 7;
    }
    text.push(length as u8);
}

/// Writes a count in digits.
fn write_digits(mut count: u64, text: &mut Vec<u8>) {
    let start = text.len();
    loop {
        text.push(b'0' + (count % 10) as u8);
        count /= 10;
        if count == 0 {
            break;
        }
    }
    text[start..].reverse();
}

/// Writes a number as the number that it stands for, however it is written: `1.0` says
/// what `1` says. A whole number that 64 bits hold is its digits, as the ratio of such a
/// number is written, and any other number is written as its ratio.
fn write_number(number: &Number, text: &mut Vec<u8>) {
    if let Some(whole) = number.as_u64() {
        write_digits(whole, text);
    } else if let Some(whole) = number.as_i64() {
        if whole < 0 {
            text.push(b'-');
        }
        write_digits(whole.unsigned_abs(), text);
    } else {
        text.extend_from_slice(exact(number).to_string().as_bytes());
    }
}

/// Writes a value as text that is equal for two values exactly when they are one value: a
/// number is written as the number that it stands for, and the properties of an object in
/// the order of their names.
///
/// This goes as deep as the value does, which is no deeper than an instance may be.
fn write_value(value: &Value, text: &mut Vec<u8>) {
    match value {
        Value::Number(number) => write_number(number, text),
        Value::Array(items) => {
            text.push(b'[');
            for item in items {
                write_value(item, text);
                text.push(b',');
            }
            text.push(b']');
        }
        Value::Object(members) => {
            let mut members: Vec<(&String, &Value)> = members.iter().collect();
            members.sort_by_key(|(name, _)| *name);
            text.push(b'{');
            for (name, member) in members {
                write_json!(name, text);
                text.push(b':');
                write_value(member, text);
                text.push(b',');
            }
            text.push(b'}');
        }
        plain => write_json!(plain, text),
    }
}

/// The nodes in an order in which every node comes after the nodes it leads to, unless they
/// are on a cycle with it, and for every node whether it is on a cycle.
///
/// This is Tarjan's algorithm for strongly connected components, without recursion.
pub(super) fn components(successors: &impl Successors) -> (Vec<usize>, Vec<bool>) {
    const UNSEEN: usize = usize::MAX;
    let count = successors.len();
    let (mut found, mut lowest) = (vec![UNSEEN; count], vec![0; count]);
    let (mut open, mut is_open) = (Vec::new(), vec![false; count]);
    let (mut order, mut cyclic) = (Vec::with_capacity(count), vec![false; count]);
    let mut next = 0;
    // The nodes being visited, each with the place among its successors that comes next.
    let mut visiting: Vec<(usize, usize)> = Vec::new();
    for root in 0..count {
        if found[root] != UNSEEN {
            continue;
        }
        visiting.push((root, 0));
        while let Some((node, place)) = visiting.last_mut() {
            let node = *node;
            if found[node] == UNSEEN {
                (found[node], lowest[node]) = (next, next);
                next += 1;
                open.push(node);
                is_open[node] = true;
            }
            if let Some(&to) = successors.of(node).get(*place) {
                *place += 1;
                if found[to] == UNSEEN {
                    visiting.push((to, 0));
                } else if is_open[to] {
                    lowest[node] = lowest[node].min(found[to]);
                }
                continue;
            }
            visiting.pop();
            if let Some(&(parent, _)) = visiting.last() {
                lowest[parent] = lowest[parent].min(lowest[node]);
            }
            if lowest[node] == found[node] {
                // The node is the first of its component, which is what was opened after it.
                let start = order.len();
                while let Some(member) = open.pop() {
                    is_open[member] = false;
                    order.push(member);
                    if member == node {
                        break;
                    }
                }
                let alone = order.len() - start == 1;
                if !alone || successors.of(node).contains(&node) {
                    for &member in &order[start..] {
                        cyclic[member] = true;
                    }
                }
            }
        }
    }
    (order, cyclic)
}

/// The nodes that each node leads to, for [`components`]: those of a schema in a flat list,
/// those of a variable in a vector of their own.
pub(super) trait Successors {
    /// How many nodes there are.
    fn len(&self) -> usize;

    /// The nodes that a node leads to.
    fn of(&self, node: usize) -> &[usize];
}

impl Successors for Lists {
    fn len(&self) -> usize {
        Lists::len(self)
    }

    fn of(&self, node: usize) -> &[usize] {
        Lists::of(self, node)
    }
}

impl Successors for Vec<Vec<usize>> {
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn of(&self, node: usize) -> &[usize] {
        &self[node]
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, Value, json};

    use super::*;
    use crate::lower::scopes::ScopeId;
    use crate::schema::parse;

    /// The class of each node of one schema, by its location.
    type Classed = Vec<(String, u32)>;

    /// The schemas as they are reached, and the class of each.
    fn reached<'g>(
        graph: &'g Graph<'g>,
        budget: &mut Budget,
    ) -> Result<(Scopes<'g>, Vec<u32>), Exhausted> {
        let scopes = Scopes::of(graph, budget)?;
        let (classes, _) = classes(graph, &scopes, budget)?;
        Ok((scopes, classes))
    }

    /// The classes of the nodes of A, and those of the nodes of B. A node that is reached
    /// in several scopes is there once for each.
    fn classed(a: &Value, b: &Value) -> (Classed, Classed) {
        let graph = parse(a, b).unwrap().link().unwrap();
        let (scopes, classes) = reached(&graph, &mut Budget::new(u64::MAX)).unwrap();
        let of = |side| {
            let nodes = (0..scopes.len()).map(|index| (scopes.at(index).node, classes[index]));
            nodes
                .filter(|(id, _)| graph.node(*id).side == side)
                .map(|(id, class)| (graph.location(id), class))
                .collect()
        };
        (of(crate::Side::A), of(crate::Side::B))
    }

    /// The class of the node at a location.
    fn at(classes: &[(String, u32)], location: &str) -> u32 {
        let found = classes.iter().find(|(place, _)| place == location);
        found.unwrap_or_else(|| panic!("no node at {location}")).1
    }

    #[test]
    fn schemas_that_say_the_same_are_of_one_class() {
        let a = json!({
            "type": "object",
            "properties": {"name": {"type": "string", "minLength": 1}, "age": {"minimum": 0}},
            "allOf": [{"required": ["name"]}],
        });
        let b = json!({
            "type": "object",
            "properties": {"name": {"minLength": 1, "type": "string"}, "age": {"minimum": 1}},
            "allOf": [{"required": ["name"]}],
            "title": "what only annotates makes no difference",
        });
        let (of_a, of_b) = classed(&a, &b);
        for same in ["#/properties/name", "#/allOf/0"] {
            assert_eq!(at(&of_a, same), at(&of_b, same), "{same}");
        }
        // One property differs, and so does everything that holds it.
        for different in ["#/properties/age", "#"] {
            assert_ne!(at(&of_a, different), at(&of_b, different), "{different}");
        }
        // Inside one schema too: the place of a schema is no part of what it says.
        let twice = json!({"items": {"type": "null"}, "not": {"type": "null"}, "contains": {}});
        let (of_a, of_b) = classed(&twice, &json!({}));
        assert_eq!(at(&of_a, "#/items"), at(&of_a, "#/not"));
        assert_eq!(at(&of_a, "#/contains"), at(&of_b, "#"));
        assert_ne!(at(&of_a, "#"), at(&of_b, "#"));
    }

    #[test]
    fn what_a_keyword_holds_and_where_tells_schemas_apart() {
        let apart = [
            (json!(true), json!(false)),
            (json!(true), json!({})),
            (json!({"minLength": 1}), json!({"maxLength": 1})),
            (json!({"minLength": 1}), json!({"minLength": 2})),
            (json!({"type": "integer"}), json!({"type": "number"})),
            (json!({"enum": [1]}), json!({"const": 1})),
            (json!({"allOf": [{}]}), json!({"anyOf": [{}]})),
            (json!({"allOf": [{}, {}]}), json!({"allOf": [{}]})),
            (
                json!({"allOf": [true, false]}),
                json!({"allOf": [false, true]}),
            ),
            (
                json!({"properties": {"a": {}}}),
                json!({"properties": {"b": {}}}),
            ),
            (json!({"items": {}}), json!({"contains": {}})),
            (json!({"required": ["a"]}), json!({"required": ["a", "b"]})),
            (json!({"uniqueItems": true}), json!({})),
            (json!({"minimum": 1}), json!({"minimum": 1.5})),
            (json!({"minimum": 1}), json!({"exclusiveMinimum": 1})),
            (json!({"const": 1}), json!({"const": "1"})),
            (json!({"enum": [1, 2]}), json!({"enum": ["1,2"]})),
            (json!({"enum": [1, 2]}), json!({"enum": [2, 1]})),
            // An array or an object is the values that it holds, each where it is.
            (json!({"const": [1, 2]}), json!({"const": [2, 1]})),
            (json!({"const": [1, 2]}), json!({"const": ["1,2"]})),
            (json!({"const": [1, 2]}), json!({"const": [12]})),
            (json!({"const": [1, 2.5]}), json!({"const": [12.5]})),
            (json!({"const": ["a", "b"]}), json!({"const": ["a\",\"b"]})),
            (json!({"const": [1, [2]]}), json!({"const": [[1], 2]})),
            (json!({"const": [[]]}), json!({"const": [{}]})),
            (json!({"const": []}), json!({"const": {}})),
            (json!({"const": {"a": 1}}), json!({"const": {"b": 1}})),
            (
                json!({"const": {"a": 1}}),
                json!({"const": {"a": 1, "b": 1}}),
            ),
            (json!({"const": {"a": [1]}}), json!({"const": {"a": 1}})),
            // A number is told from the one next to it, also where a float holds neither.
            (json!({"minimum": 1}), json!({"minimum": -1})),
            (
                json!({"minimum": u64::MAX}),
                json!({"minimum": 1.8446744073709552e19}),
            ),
            (
                json!({"const": i64::MIN}),
                json!({"const": -9.223372036854778e18}),
            ),
            (json!({"minItems": 1}), json!({"minItems": 10})),
            (json!({"type": "null"}), json!({"type": "boolean"})),
            (json!({"type": ["null", "array"]}), json!({"type": "array"})),
            (
                json!({"required": ["a", "b"]}),
                json!({"required": ["a,b"]}),
            ),
            (
                json!({"dependentRequired": {"a": ["b"]}}),
                json!({"dependentRequired": {"b": ["a"]}}),
            ),
            (json!({"pattern": "a"}), json!({"format": "a"})),
            (json!({"pattern": "a\""}), json!({"pattern": "a"})),
            // A name is told from names that are written alike in part, and from what follows
            // it, however long it is.
            (json!({"required": ["ab"]}), json!({"required": ["a", "b"]})),
            (
                json!({"required": [""]}),
                json!({"required": ["", "\u{0}"]}),
            ),
            (
                json!({"properties": {"a": {}, "b": {}}}),
                json!({"properties": {"a\u{1}\u{1}b": {}}}),
            ),
            (
                json!({"properties": {"a": {}}}),
                json!({"properties": {"a;properties\u{1}a": {}}}),
            ),
            (
                json!({"properties": {"a".repeat(130): {}}}),
                json!({"properties": {"a".repeat(2): {}}}),
            ),
            (
                json!({"dependentRequired": {"a": ["b", "c"]}}),
                json!({"dependentRequired": {"a": ["b"], "c": []}}),
            ),
            (
                json!({"dependentRequired": {"a": [], "b": []}}),
                json!({"dependentRequired": {"a": ["b"]}}),
            ),
            (json!({"pattern": "a;"}), json!({"pattern": "a"})),
            (
                json!({"pattern": "a", "format": "b"}),
                json!({"pattern": "a\u{1}\u{1}b"}),
            ),
        ];
        for (a, b) in apart {
            let (of_a, of_b) = classed(&a, &b);
            assert_ne!(at(&of_a, "#"), at(&of_b, "#"), "{a} and {b}");
        }
        let alike = [
            (
                json!({}),
                json!({"title": "a", "$comment": "b", "$id": "c"}),
            ),
            (json!({"uniqueItems": false}), json!({})),
            (json!({"$defs": {"a": {}}, "$anchor": "x"}), json!({})),
            // A number is the number that it stands for, however it is written.
            (json!({"minimum": 1}), json!({"minimum": 1.0})),
            (json!({"multipleOf": 0.5}), json!({"multipleOf": 5e-1})),
            (json!({"const": 1}), json!({"const": 1.0})),
            (json!({"const": 0}), json!({"const": -0.0})),
            (json!({"maximum": -12}), json!({"maximum": -1.2e1})),
            (json!({"minimum": u64::MAX}), json!({"minimum": u64::MAX})),
            (
                json!({"const": i64::MIN}),
                json!({"const": -9.223372036854776e18}),
            ),
            (
                json!({"type": ["null", "array"]}),
                json!({"type": ["array", "null"]}),
            ),
            (
                json!({"enum": [1, "a", null]}),
                json!({"enum": [1.0, "a", null]}),
            ),
            // Also inside an array or an object.
            (json!({"const": [1]}), json!({"const": [1.0]})),
            (
                json!({"const": {"a": [1, {"b": 2.0}], "c": null}}),
                json!({"const": {"c": null, "a": [1.0, {"b": 2}]}}),
            ),
        ];
        for (a, b) in alike {
            let (of_a, of_b) = classed(&a, &b);
            assert_eq!(at(&of_a, "#"), at(&of_b, "#"), "{a} and {b}");
        }
    }

    #[test]
    fn schemas_that_refer_to_themselves_are_read_as_far_as_they_go() {
        // A list of lists, written once with one turn of the cycle and once with two.
        let short = json!({"type": "array", "items": {"$ref": "#"}});
        let long = json!({
            "type": "array",
            "items": {"$ref": "#/$defs/again"},
            "$defs": {"again": {"type": "array", "items": {"$ref": "#"}}},
        });
        let (of_a, of_b) = classed(&short, &long);
        assert_eq!(at(&of_a, "#"), at(&of_b, "#"));
        assert_eq!(at(&of_a, "#"), at(&of_b, "#/$defs/again"));
        assert_eq!(at(&of_a, "#/items"), at(&of_b, "#/$defs/again/items"));
        // A schema that only refers to another is a schema of its own.
        assert_ne!(at(&of_a, "#"), at(&of_a, "#/items"));

        // A difference that only shows after a turn of the cycle still tells them apart.
        let other = json!({
            "type": "array",
            "items": {"$ref": "#/$defs/again"},
            "$defs": {"again": {"type": "array", "items": {"$ref": "#"}, "minItems": 1}},
        });
        let (of_a, of_b) = classed(&short, &other);
        assert_ne!(at(&of_a, "#"), at(&of_b, "#"));
        assert_ne!(at(&of_a, "#/items"), at(&of_b, "#/items"));
        assert_ne!(at(&of_a, "#"), at(&of_b, "#/$defs/again"));

        // Two cycles that take turns say the same as each of them.
        let pair = json!({
            "$ref": "#/$defs/even",
            "$defs": {
                "even": {"anyOf": [{"type": "null"}, {"$ref": "#/$defs/odd"}]},
                "odd": {"anyOf": [{"type": "null"}, {"$ref": "#/$defs/even"}]},
            },
        });
        let (of_a, _) = classed(&pair, &json!(true));
        assert_eq!(at(&of_a, "#/$defs/even"), at(&of_a, "#/$defs/odd"));
    }

    #[test]
    fn some_schemas_are_like_no_other() {
        // A count that was too large to keep is not known to equal another.
        let huge = json!({"properties": {"a": {"minLength": 1e30}, "b": {"minLength": 1e30}}});
        let (of_a, _) = classed(&huge, &json!(true));
        assert_ne!(at(&of_a, "#/properties/a"), at(&of_a, "#/properties/b"));
    }

    #[test]
    fn a_dynamic_reference_is_classed_by_what_it_leads_to() {
        // An anchor is a name and says nothing, and a `$dynamicRef` says what a `$ref` to
        // the schema that it leads to says.
        let dynamic = json!({"$dynamicAnchor": "x", "items": {"$dynamicRef": "#x"}});
        let plain = json!({"items": {"$ref": "#"}});
        let (of_a, of_b) = classed(&dynamic, &plain);
        assert_eq!(at(&of_a, "#"), at(&of_b, "#"));
        assert_eq!(at(&of_a, "#/items"), at(&of_b, "#/items"));

        // `list` is reached from `strings` and from `numbers`, and its items are what the
        // one that led to it says they are. So it is of two classes, one for each way.
        let lists = |of_strings: &str, of_numbers: &str| {
            json!({
                "$id": "https://example.com/root",
                "properties": {"a": {"$ref": "strings"}, "b": {"$ref": "numbers"}},
                "$defs": {
                    "strings": {
                        "$id": "strings",
                        "$ref": "list",
                        "$defs": {"item": {"$dynamicAnchor": "item", "type": of_strings}},
                    },
                    "numbers": {
                        "$id": "numbers",
                        "$ref": "list",
                        "$defs": {"item": {"$dynamicAnchor": "item", "type": of_numbers}},
                    },
                    "list": {
                        "$id": "list",
                        "items": {"$dynamicRef": "#item"},
                        "$defs": {"item": {"$dynamicAnchor": "item"}},
                    },
                },
            })
        };
        let every = |classes: &Classed, location: &str| -> Vec<u32> {
            let there = classes.iter().filter(|(place, _)| place == location);
            there.map(|(_, class)| *class).collect()
        };
        let (of_a, of_b) = classed(&lists("string", "number"), &lists("string", "string"));
        let list = "#/$defs/list";
        let (in_a, in_b) = (every(&of_a, list), every(&of_b, list));
        assert_eq!((in_a.len(), in_b.len()), (2, 2));
        assert_ne!(in_a[0], in_a[1]);
        // Where both ways say the same of the items, the list is of one class, and it is
        // the class of the list of strings in the other schema.
        assert_eq!(in_b[0], in_b[1]);
        assert_eq!(in_a[0], in_b[0]);
        let (strings, numbers) = ("#/$defs/strings", "#/$defs/numbers");
        assert_ne!(at(&of_a, strings), at(&of_a, numbers));
        assert_eq!(at(&of_b, strings), at(&of_b, numbers));
        assert_eq!(at(&of_a, strings), at(&of_b, strings));
        // The list by itself, with nothing that led to it, takes any item.
        let alone = json!({"$ref": "#/$defs/list", "$defs": lists("null", "null")["$defs"]});
        let (of_a, _) = classed(&alone, &json!({"items": {}}));
        assert_eq!(every(&of_a, "#/$defs/list").len(), 1);
    }

    #[test]
    fn only_cycles_cost_steps() {
        // How many schemas are classed, where that costs no step.
        let classed = |schema: &Value| {
            let truth = json!(true);
            let graph = parse(schema, &truth).unwrap().link().unwrap();
            reached(&graph, &mut Budget::new(0)).map(|(scopes, _)| scopes.len())
        };
        let plain = json!({"properties": {"a": {"items": {"not": {}}}}});
        assert!(classed(&plain).is_ok());

        // Three of the four schemas on the cycle say the same by themselves. Each round tells
        // one more of them apart, by what it leads to, and a round that tells nothing apart
        // ends the work. Every round but the first costs a step for each schema that is
        // classed.
        let cycle = json!({"not": {"not": {"not": {"$ref": "#"}}}});
        assert_eq!(classed(&cycle), Err(Exhausted));
        // Schemas that nothing leads to are not classed. Here the root and `true` are, and
        // the four on the cycle are not.
        let unused = json!({
            "$defs": {"cycle": {"not": {"not": {"not": {"$ref": "#/$defs/cycle"}}}}},
        });
        assert_eq!(classed(&unused), Ok(2));
    }

    #[test]
    fn a_deep_schema_is_classed_in_one_pass() {
        let deep = |last: Value| {
            let mut schema = last;
            for _ in 0..100_000 {
                schema = Value::Object(Map::from_iter([("not".to_owned(), schema)]));
            }
            schema
        };
        let (a, b, c) = (deep(json!({})), deep(json!({})), deep(json!(false)));
        let roots = |a: &Value, b: &Value| {
            let graph = parse(a, b).unwrap().link().unwrap();
            let (scopes, classes) = reached(&graph, &mut Budget::new(0)).unwrap();
            let of = |root| classes[scopes.from(root, ScopeId::NOTHING)];
            (of(graph.a), of(graph.b))
        };
        let (of_a, of_b) = roots(&a, &b);
        assert_eq!(of_a, of_b);
        let (of_a, of_c) = roots(&a, &c);
        assert_ne!(of_a, of_c);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget((a, b, c));
    }

    #[test]
    fn the_nodes_on_cycles_are_found() {
        // 0 leads to 1 and 4; 1, 2 and 3 are a cycle; 4 leads to itself; 5 stands alone.
        let successors = Lists::from([&[1, 4][..], &[2], &[3], &[1], &[4], &[]]);
        let (order, cyclic) = components(&successors);
        assert_eq!(cyclic, [false, true, true, true, true, false]);
        let place = |node| order.iter().position(|&other| other == node).unwrap();
        assert_eq!(order.len(), 6);
        // What a node leads to comes before it, unless both are on one cycle.
        assert!(place(1) < place(0) && place(4) < place(0));
        let mut cycle = [place(1), place(2), place(3)];
        cycle.sort_unstable();
        assert_eq!(cycle[2] - cycle[0], 2);
    }
}
