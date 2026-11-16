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
use std::fmt::Write;

use serde_json::{Number, Value};

use super::scopes::Scopes;
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

/// The class of every schema as it is reached, in the order in which `scopes` has them.
///
/// # Errors
///
/// When schemas that refer to themselves take more rounds to tell apart than the budget
/// covers. Without such schemas the work is one pass and costs nothing.
pub(super) fn classes(
    graph: &Graph,
    scopes: &Scopes,
    budget: &mut Budget,
) -> Result<Vec<u32>, Exhausted> {
    let count = scopes.len();
    // What each schema says by itself, as a number. What it leads to is in `scopes`.
    let mut texts: HashMap<String, u32> = HashMap::new();
    let mut own = Vec::with_capacity(count);
    for index in 0..count {
        let id = scopes.at(index).node;
        let text = described(id, graph.node(id));
        let next = number(texts.len());
        own.push(*texts.entry(text).or_insert(next));
    }
    let successors = scopes.leads_to();
    let (order, cyclic) = components(successors);

    // A node that is on no cycle gets its class from the classes of the nodes it leads to,
    // which are known before it. The nodes on cycles are told apart in rounds: all are one
    // block at first, and each round separates those that differ one step further in. When a
    // round separates nothing, nothing will.
    const UNTOLD: u32 = u32::MAX;
    let mut numbers: HashMap<(u32, Vec<u32>), u32> = HashMap::new();
    let mut previous = vec![UNTOLD; count];
    let mut blocks = usize::from(cyclic.contains(&true));
    loop {
        let mut current = vec![UNTOLD; count];
        for &node in &order {
            let places = successors[node].iter();
            let leads_to = places.map(|&to| {
                if cyclic[to] {
                    previous[to]
                } else {
                    current[to]
                }
            });
            let next = number(numbers.len());
            let class = numbers
                .entry((own[node], leads_to.collect()))
                .or_insert(next);
            current[node] = *class;
        }
        let on_cycles = (0..count).filter(|&node| cyclic[node]);
        let told_apart: HashSet<u32> = on_cycles.map(|node| current[node]).collect();
        if told_apart.len() == blocks {
            return Ok(current);
        }
        blocks = told_apart.len();
        previous = current;
        budget.charge(count as u64)?;
    }
}

fn number(count: usize) -> u32 {
    u32::try_from(count).expect("a check has fewer than 2^32 classes")
}

/// What a node says by itself, as text that is equal for two nodes exactly when they say the
/// same apart from the schemas they lead to. The text names those in the order in which
/// `Scopes` has them: the subschemas of the keywords, the target of `$ref`, and what
/// `$dynamicRef` leads to, which is a reference target as that of `$ref` is.
fn described(id: NodeId, node: &Node) -> String {
    let keywords = match &node.schema {
        Schema::Bool(value) => return value.to_string(),
        Schema::Object(keywords) => keywords,
    };
    let mut text = String::new();
    for (keyword, part, _) in keywords.subschemas() {
        match part {
            Part::Whole => write!(text, "{keyword};"),
            Part::Name(name) => write!(text, "{keyword}{};", quoted(name)),
            Part::Index(_) => write!(text, "{keyword}[];"),
        }
        .expect("a string takes any text");
    }
    let references = [
        keywords.reference.is_some(),
        keywords.dynamic_reference.is_some(),
    ];
    for _ in references.into_iter().filter(|there| *there) {
        text.push_str("$ref;");
    }
    assertions(id, keywords, &mut text);
    text
}

/// The keywords of a schema that hold no schema, each with its value.
fn assertions(id: NodeId, keywords: &Keywords, text: &mut String) {
    let mut put = |keyword: &str, value: Option<String>| {
        if let Some(value) = value {
            write!(text, "{keyword}={value};").expect("a string takes any text");
        }
    };
    // A count that was too large to keep is not known to equal another one.
    let unlike_any_other = || format!("@{}", id.index());
    let count = |count: Option<Count>| {
        count.map(|count| match count {
            Count::Of(count) => count.to_string(),
            Count::Beyond => unlike_any_other(),
        })
    };

    // `$dynamicAnchor` says nothing of an instance: it is a name, as `$anchor` is.
    put("type", keywords.types.map(|types| format!("{types:?}")));
    // A number is the number that it stands for, however it is written: `1.0` says what `1`
    // says, also inside an array or an object. A value that is nested deeper than an
    // instance may be is not written out, and is like no other.
    let number = |number: &Number| exact(number).to_string();
    let constant = |value: &Value| {
        if too_deep(value) {
            return unlike_any_other();
        }
        let mut text = String::new();
        write_value(value, &mut text);
        text
    };
    let listed = |values: &[Value]| values.iter().map(constant).collect::<Vec<_>>().join(",");
    put("enum", keywords.enumeration.map(listed));
    put("const", keywords.constant.map(constant));
    put("minimum", keywords.minimum.map(number));
    put("maximum", keywords.maximum.map(number));
    put("exclusiveMinimum", keywords.exclusive_minimum.map(number));
    put("exclusiveMaximum", keywords.exclusive_maximum.map(number));
    put("multipleOf", keywords.multiple_of.map(number));
    put("minLength", count(keywords.min_length));
    put("maxLength", count(keywords.max_length));
    put("pattern", keywords.pattern.map(quoted));
    put("format", keywords.format.map(quoted));
    put("minContains", count(keywords.min_contains));
    put("maxContains", count(keywords.max_contains));
    put("minItems", count(keywords.min_items));
    put("maxItems", count(keywords.max_items));
    put("uniqueItems", keywords.unique_items.then(String::new));
    let required = &keywords.required;
    put(
        "required",
        (!required.is_empty()).then(|| written!(required)),
    );
    let dependent = &keywords.dependent_required;
    put(
        "dependentRequired",
        (!dependent.is_empty()).then(|| written!(dependent)),
    );
    put("minProperties", count(keywords.min_properties));
    put("maxProperties", count(keywords.max_properties));
}

fn quoted(text: &str) -> String {
    written!(text)
}

/// Writes a value as text that is equal for two values exactly when they are one value: a
/// number is written as the number that it stands for, and the properties of an object in
/// the order of their names.
///
/// This goes as deep as the value does, which is no deeper than an instance may be.
fn write_value(value: &Value, text: &mut String) {
    match value {
        Value::Number(number) => text.push_str(&exact(number).to_string()),
        Value::Array(items) => {
            text.push('[');
            for item in items {
                write_value(item, text);
                text.push(',');
            }
            text.push(']');
        }
        Value::Object(members) => {
            let mut members: Vec<(&String, &Value)> = members.iter().collect();
            members.sort_by_key(|(name, _)| *name);
            text.push('{');
            for (name, member) in members {
                text.push_str(&quoted(name));
                text.push(':');
                write_value(member, text);
                text.push(',');
            }
            text.push('}');
        }
        plain => text.push_str(&written!(plain)),
    }
}

/// The nodes in an order in which every node comes after the nodes it leads to, unless they
/// are on a cycle with it, and for every node whether it is on a cycle.
///
/// This is Tarjan's algorithm for strongly connected components, without recursion.
fn components(successors: &[Vec<usize>]) -> (Vec<usize>, Vec<bool>) {
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
            if let Some(&to) = successors[node].get(*place) {
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
                if !alone || successors[node].contains(&node) {
                    for &member in &order[start..] {
                        cyclic[member] = true;
                    }
                }
            }
        }
    }
    (order, cyclic)
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
        let classes = classes(graph, &scopes, budget)?;
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
        let rounds = |schema: &Value| {
            let truth = json!(true);
            let graph = parse(schema, &truth).unwrap().link().unwrap();
            let mut budget = Budget::new(u64::MAX);
            let (scopes, _) = reached(&graph, &mut budget).unwrap();
            (budget.spent(), scopes.len() as u64)
        };
        let plain = json!({"properties": {"a": {"items": {"not": {}}}}});
        assert_eq!(rounds(&plain).0, 0);

        // Three of the four schemas on the cycle say the same by themselves. Each round tells
        // one more of them apart, by what it leads to, and a round that tells nothing apart
        // ends the work. Every round but the first costs a step for each schema that is
        // classed: the four on the cycle and `true`.
        let cycle = json!({"not": {"not": {"not": {"$ref": "#"}}}});
        assert_eq!(rounds(&cycle), (3 * 5, 5));
        // Schemas that nothing leads to are not classed. Here the root and `true` are, and
        // the four on the cycle are not.
        let unused = json!({
            "$defs": {"cycle": {"not": {"not": {"not": {"$ref": "#/$defs/cycle"}}}}},
        });
        assert_eq!(rounds(&unused), (0, 2));

        let truth = json!(true);
        let graph = parse(&cycle, &truth).unwrap().link().unwrap();
        assert_eq!(reached(&graph, &mut Budget::new(14)).err(), Some(Exhausted));
        assert!(reached(&graph, &mut Budget::new(15)).is_ok());
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
        let successors = vec![vec![1, 4], vec![2], vec![3], vec![1], vec![4], vec![]];
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
