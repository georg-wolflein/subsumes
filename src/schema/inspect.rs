//! The schema graph as JSON, for a tool that shows it.
//!
//! The value is a list of nodes, each with what it says by itself, and a list of the edges
//! between them. Its shape follows the needs of the viewer and is not stable.

use serde_json::{Map, Value, json};

use super::{Count, Graph, Keywords, NodeId, Origin, Part, Schema, Type};
use crate::Side;

/// The keywords whose schemas apply nowhere by themselves. A node has no field for them, so
/// the edge to such a schema comes from where the schema was found.
const HELD: [&str; 4] = ["$defs", "definitions", "contentSchema", "dependencies"];

impl Graph<'_> {
    pub(crate) fn to_json(&self) -> Value {
        let ids = || (0..self.len()).map(NodeId::new);
        let nodes: Vec<Value> = ids().map(|id| self.described(id)).collect();
        let mut edges = Vec::new();
        for id in ids() {
            self.edges_of(id, &mut edges);
        }
        json!({
            "a": self.a.index(),
            "b": self.b.index(),
            "nodes": nodes,
            "edges": edges,
        })
    }

    /// A node without its edges.
    fn described(&self, id: NodeId) -> Value {
        let node = self.node(id);
        let mut described = Map::new();
        described.insert("id".to_owned(), json!(id.index()));
        let side = match node.side {
            Side::A => "A",
            Side::B => "B",
        };
        described.insert("side".to_owned(), json!(side));
        described.insert("location".to_owned(), json!(self.location(id)));
        described.insert("resource".to_owned(), json!(node.resource.index()));
        match &node.schema {
            Schema::Bool(value) => described.insert("boolean".to_owned(), json!(value)),
            Schema::Object(keywords) => {
                described.insert("keywords".to_owned(), json!(assertions(keywords)))
            }
        };
        Value::Object(described)
    }

    /// The edges that begin at a node, and the one that leads to it if no keyword applies it.
    fn edges_of(&self, id: NodeId, edges: &mut Vec<Value>) {
        let node = self.node(id);
        if let Origin::Child {
            parent,
            keyword,
            part,
        } = node.origin
            && HELD.contains(&keyword)
        {
            edges.push(edge("holds", parent, id, keyword, part));
        }
        let Schema::Object(keywords) = &node.schema else {
            return;
        };
        let mut applies = |keyword, part, to| edges.push(edge("applies", id, to, keyword, part));
        let one = [
            ("not", keywords.not),
            ("if", keywords.if_),
            ("then", keywords.then),
            ("else", keywords.else_),
            ("items", keywords.items),
            ("contains", keywords.contains),
            ("unevaluatedItems", keywords.unevaluated_items),
            ("additionalProperties", keywords.additional_properties),
            ("propertyNames", keywords.property_names),
            ("unevaluatedProperties", keywords.unevaluated_properties),
        ];
        for (keyword, to) in one {
            if let Some(to) = to {
                applies(keyword, Part::Whole, to);
            }
        }
        let listed = [
            ("allOf", &keywords.all_of),
            ("anyOf", &keywords.any_of),
            ("oneOf", &keywords.one_of),
            ("prefixItems", &keywords.prefix_items),
        ];
        for (keyword, schemas) in listed {
            for (position, to) in schemas.iter().enumerate() {
                applies(keyword, Part::Index(position), *to);
            }
        }
        let named = [
            ("properties", &keywords.properties),
            ("patternProperties", &keywords.pattern_properties),
            ("dependentSchemas", &keywords.dependent_schemas),
        ];
        for (keyword, schemas) in named {
            for (name, to) in schemas {
                applies(keyword, Part::Name(name), *to);
            }
        }
        if let Some(to) = keywords.reference {
            edges.push(edge("reference", id, to, "$ref", Part::Whole));
        }
        if let Some(dynamic) = keywords.dynamic_reference {
            // The text says which dynamic anchor the engine will look for.
            let text = Part::Name(dynamic.reference);
            edges.push(edge("reference", id, dynamic.target, "$dynamicRef", text));
        }
    }
}

fn edge(kind: &str, from: NodeId, to: NodeId, keyword: &str, part: Part) -> Value {
    let mut edge = json!({
        "kind": kind,
        "from": from.index(),
        "to": to.index(),
        "keyword": keyword,
    });
    match part {
        Part::Whole => {}
        Part::Name(name) => edge["name"] = json!(name),
        Part::Index(index) => edge["index"] = json!(index),
    }
    edge
}

/// What a schema object says without another schema: each keyword with its value, in the
/// order in which a reader expects them.
fn assertions(keywords: &Keywords) -> Vec<(&'static str, Value)> {
    let count = |count: Option<Count>| {
        count.map(|count| match count {
            Count::Of(count) => json!(count),
            Count::Beyond => json!("too large to keep exactly"),
        })
    };
    let types = keywords.types.map(|types| {
        let held = Type::ALL.into_iter().filter(|kind| types.contains(*kind));
        json!(held.map(Type::name).collect::<Vec<_>>())
    });
    let all = [
        (
            "$dynamicAnchor",
            keywords.dynamic_anchor.map(|name| json!(name)),
        ),
        ("type", types),
        ("enum", keywords.enumeration.map(|values| json!(values))),
        ("const", keywords.constant.cloned()),
        ("minimum", keywords.minimum.map(|number| json!(number))),
        ("maximum", keywords.maximum.map(|number| json!(number))),
        (
            "exclusiveMinimum",
            keywords.exclusive_minimum.map(|number| json!(number)),
        ),
        (
            "exclusiveMaximum",
            keywords.exclusive_maximum.map(|number| json!(number)),
        ),
        (
            "multipleOf",
            keywords.multiple_of.map(|number| json!(number)),
        ),
        ("minLength", count(keywords.min_length)),
        ("maxLength", count(keywords.max_length)),
        ("pattern", keywords.pattern.map(|pattern| json!(pattern))),
        ("format", keywords.format.map(|format| json!(format))),
        ("minItems", count(keywords.min_items)),
        ("maxItems", count(keywords.max_items)),
        (
            "uniqueItems",
            keywords.unique_items.then_some(Value::Bool(true)),
        ),
        ("minContains", count(keywords.min_contains)),
        ("maxContains", count(keywords.max_contains)),
        (
            "required",
            (!keywords.required.is_empty()).then(|| json!(keywords.required)),
        ),
        (
            "dependentRequired",
            (!keywords.dependent_required.is_empty()).then(|| {
                let names = keywords.dependent_required.iter();
                Value::Object(
                    names
                        .map(|(name, needs)| ((*name).to_owned(), json!(needs)))
                        .collect(),
                )
            }),
        ),
        ("minProperties", count(keywords.min_properties)),
        ("maxProperties", count(keywords.max_properties)),
    ];
    all.into_iter()
        .filter_map(|(keyword, value)| Some((keyword, value?)))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::super::parse;
    use super::*;

    fn graph(a: &Value, b: &Value) -> Value {
        parse(a, b).unwrap().link().unwrap().to_json()
    }

    #[test]
    fn a_node_says_where_it_is_and_what_it_asserts() {
        let a = json!({
            "type": ["string", "null"],
            "minLength": 1,
            "maxLength": 1e30,
            "pattern": "^a",
            "required": ["x"],
            "title": "not kept",
        });
        let described = graph(&a, &json!(false));
        assert_eq!((&described["a"], &described["b"]), (&json!(0), &json!(1)));
        assert_eq!(
            described["nodes"],
            json!([
                {
                    "id": 0,
                    "side": "A",
                    "location": "#",
                    "resource": 0,
                    "keywords": [
                        ["type", ["null", "string"]],
                        ["minLength", 1],
                        ["maxLength", "too large to keep exactly"],
                        ["pattern", "^a"],
                        ["required", ["x"]],
                    ],
                },
                {"id": 1, "side": "B", "location": "#", "resource": 1, "boolean": false},
            ])
        );
        assert_eq!(described["edges"], json!([]));
    }

    #[test]
    fn an_edge_says_which_keyword_leads_where() {
        let a = json!({
            "$dynamicAnchor": "node",
            "allOf": [{"$ref": "#/$defs/a b"}],
            "properties": {"child": {"$dynamicRef": "#node"}},
            "not": false,
            "$defs": {"a b": true},
        });
        let described = graph(&a, &json!(true));
        let locations: Vec<&str> = described["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|node| node["location"].as_str().unwrap())
            .collect();
        assert_eq!(
            locations,
            [
                "#",
                "#/$defs/a%20b",
                "#/allOf/0",
                "#/not",
                "#/properties/child",
                "#"
            ]
        );
        assert_eq!(
            described["edges"],
            json!([
                {"kind": "applies", "from": 0, "to": 3, "keyword": "not"},
                {"kind": "applies", "from": 0, "to": 2, "keyword": "allOf", "index": 0},
                {"kind": "applies", "from": 0, "to": 4, "keyword": "properties", "name": "child"},
                {"kind": "holds", "from": 0, "to": 1, "keyword": "$defs", "name": "a b"},
                {"kind": "reference", "from": 2, "to": 1, "keyword": "$ref"},
                {"kind": "reference", "from": 4, "to": 0, "keyword": "$dynamicRef", "name": "#node"},
            ])
        );
    }
}
