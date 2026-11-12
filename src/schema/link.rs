//! The second step of loading: every reference resolved to a node.
//!
//! A reference names a resource and a place in it. The resource is the one that the reference
//! stands in, another one of the same schema, named by its URI, or a meta-schema of the draft.
//! The place is the fragment: nothing for the resource itself, a JSON Pointer, or the name of
//! an anchor.
//!
//! Resolution is static. A `$dynamicRef` gets the target that a `$ref` would have, and what
//! the dynamic scope makes of it is for the engine to say.

use std::borrow::Cow;

use serde_json::Value;

use super::parse::{Builder, Reference, ReferenceKeyword, Unlinked, index, resolve};
use super::{DynamicReference, Graph, NodeId, Origin, Schema, meta, push_token};
use crate::{Error, Side};

impl<'a> Unlinked<'a> {
    /// Resolves every reference, and parses every meta-schema that a reference leads to.
    ///
    /// # Errors
    ///
    /// When a reference resolves to nothing, or when it points to a value that is no schema.
    pub(crate) fn link(self) -> Result<Graph<'a>, Error> {
        let mut builder = self.builder;
        // Parsing a meta-schema adds its references to the end of the list.
        let mut next = 0;
        while let Some(&reference) = builder.references.get(next) {
            next += 1;
            let Some(target) = builder.target(reference)? else {
                let mut location = builder.location(reference.node);
                push_token(&mut location, reference.keyword.name());
                return Err(Error::UnresolvedReference {
                    schema: builder.nodes[reference.node.index()].side,
                    location,
                    reference: reference.reference.to_owned(),
                });
            };
            let node = &mut builder.nodes[reference.node.index()];
            if let Schema::Object(keywords) = &mut node.schema {
                match reference.keyword {
                    ReferenceKeyword::Ref => keywords.reference = Some(target),
                    ReferenceKeyword::DynamicRef => {
                        keywords.dynamic_reference = Some(DynamicReference {
                            reference: reference.reference,
                            target,
                        });
                    }
                }
            }
        }
        Ok(Graph {
            nodes: builder.nodes,
            a: self.a,
            b: self.b,
        })
    }
}

impl<'a> Builder<'a> {
    /// The node that a reference points to, or `None` if it points to nothing.
    pub(super) fn target(&mut self, reference: Reference<'a>) -> Result<Option<NodeId>, Error> {
        let node = &self.nodes[reference.node.index()];
        let (side, own) = (node.side, node.resource);
        let (resource, fragment) = reference
            .reference
            .split_once('#')
            .unwrap_or((reference.reference, ""));
        let resource = if resource.is_empty() {
            own
        } else {
            let Some(resource) = self.resource(side, own, resource)? else {
                return Ok(None);
            };
            resource
        };
        let Some(fragment) = percent_decoded(fragment) else {
            return Ok(None);
        };
        if fragment.is_empty() {
            Ok(Some(resource))
        } else if fragment.starts_with('/') {
            self.at_pointer(side, resource, &fragment)
        } else {
            Ok(self.anchors.get(&(resource, &*fragment)).copied())
        }
    }

    /// The node that begins the resource which a URI reference names, where the reference
    /// stands in the resource `own`.
    fn resource(
        &mut self,
        side: Side,
        own: NodeId,
        reference: &str,
    ) -> Result<Option<NodeId>, Error> {
        let base = &self.bases[&own];
        let Some(uri) = resolve(base, reference) else {
            return Ok(None);
        };
        // A resource in a place where the draft puts no schema is in no map, but a reference
        // inside it can still name it.
        if uri.as_str() == base.as_str() {
            return Ok(Some(own));
        }
        if let Some(&resource) = self.resources[index(side)].get(uri.as_str()) {
            return Ok(Some(resource));
        }
        let Some(document) = meta::document(uri.as_str()) else {
            return Ok(None);
        };
        let origin = Origin::Reference(uri.as_str().to_owned());
        self.document(side, document, origin, uri).map(Some)
    }

    /// The node at a JSON Pointer inside a resource, or `None` if the pointer leads nowhere.
    fn at_pointer(
        &mut self,
        side: Side,
        resource: NodeId,
        pointer: &str,
    ) -> Result<Option<NodeId>, Error> {
        let tokens = || pointer[1..].split('/');
        let mut value = self.values[resource.index()];
        // The nearest node on the way, and whether the way ends at it.
        let (mut above, mut ends_there) = (resource, false);
        for token in tokens() {
            let Some(next) = step(value, token) else {
                return Ok(None);
            };
            value = next;
            let node = self.known(side, value);
            (above, ends_there) = (node.unwrap_or(above), node.is_some());
        }
        if ends_there {
            return Ok(Some(above));
        }

        // The target is in a place where the draft puts no schema, so it is parsed only now.
        // An `$id` between the nearest node and the target does not count either.
        let mut location = self.location(resource);
        for token in tokens() {
            // Every token was taken a moment ago, so it has no escape that is none.
            push_token(&mut location, &unescaped(token).unwrap_or_default());
        }
        let around = self.nodes[above.index()].resource;
        self.subtree(side, value, Origin::Reference(location), around)
            .map(Some)
    }
}

/// One step of a JSON Pointer, as RFC 6901 reads it.
fn step<'a>(value: &'a Value, token: &str) -> Option<&'a Value> {
    match value {
        Value::Object(map) => map.get(&*unescaped(token)?),
        Value::Array(items) => {
            // An index is `0` or a number without a leading zero, and it has no sign.
            let digits = token.bytes().all(|byte| byte.is_ascii_digit());
            if !digits || (token.starts_with('0') && token != "0") {
                return None;
            }
            items.get(token.parse::<usize>().ok()?)
        }
        _ => None,
    }
}

/// A token of a JSON Pointer without its escapes: `~1` is `/` and `~0` is `~`. `None` if a
/// `~` begins neither.
fn unescaped(token: &str) -> Option<Cow<'_, str>> {
    if !token.contains('~') {
        return Some(Cow::Borrowed(token));
    }
    let mut plain = String::with_capacity(token.len());
    let mut characters = token.chars();
    while let Some(character) = characters.next() {
        plain.push(match character {
            '~' => match characters.next()? {
                '0' => '~',
                '1' => '/',
                _ => return None,
            },
            other => other,
        });
    }
    Some(Cow::Owned(plain))
}

/// A fragment with its percent-encoded bytes decoded, or `None` if they are not UTF-8. A `%`
/// that begins no encoded byte stands for itself, as in the many references that are written
/// without any encoding.
fn percent_decoded(fragment: &str) -> Option<Cow<'_, str>> {
    if !fragment.contains('%') {
        return Some(Cow::Borrowed(fragment));
    }
    let digit = |byte: Option<&u8>| char::from(*byte?).to_digit(16);
    let bytes = fragment.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut position = 0;
    while let Some(&byte) = bytes.get(position) {
        let digits = (
            digit(bytes.get(position + 1)),
            digit(bytes.get(position + 2)),
        );
        if let (b'%', (Some(high), Some(low))) = (byte, digits) {
            decoded.push(u8::try_from(high * 16 + low).expect("two hex digits are one byte"));
            position += 3;
        } else {
            decoded.push(byte);
            position += 1;
        }
    }
    String::from_utf8(decoded).ok().map(Cow::Owned)
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, json};

    use super::super::oracle::compared;
    use super::super::parse::parse;
    use super::super::{Keywords, Type};
    use super::*;

    /// Loads A and B, and hands the graph to `inspect`.
    fn load<R>(a: &Value, b: &Value, inspect: impl FnOnce(&Graph) -> R) -> Result<R, Error> {
        let graph = parse(a, b)?.link()?;
        Ok(inspect(&graph))
    }

    fn object<'a, 'g>(graph: &'g Graph<'a>, node: NodeId) -> &'g Keywords<'a> {
        match &graph.node(node).schema {
            Schema::Object(keywords) => keywords,
            Schema::Bool(_) => panic!("the node is a boolean schema"),
        }
    }

    /// Where the `$ref` of a node leads.
    fn target(graph: &Graph, node: NodeId) -> String {
        graph.location(object(graph, node).reference.expect("the node has a $ref"))
    }

    /// Where the `$ref` of the property `name` of A leads.
    fn property_target(graph: &Graph, name: &str) -> String {
        let properties = &object(graph, graph.a).properties;
        let (_, property) = properties.iter().find(|(key, _)| *key == name).unwrap();
        target(graph, *property)
    }

    /// Where the `$ref` of A leads.
    fn root_target(schema: &Value) -> Result<String, Error> {
        load(schema, &json!(true), |graph| target(graph, graph.a))
    }

    fn unresolved(a: &Value) -> (Side, String, String) {
        match load(a, &json!(true), |_| ()) {
            Err(Error::UnresolvedReference {
                schema,
                location,
                reference,
            }) => (schema, location, reference),
            other => panic!("{a} gave {other:?}"),
        }
    }

    fn pointers_and_anchors() -> Value {
        json!({
            "properties": {
                "root": {"$ref": "#"},
                "later": {"$ref": "#/$defs/later"},
                "nested": {"$ref": "#/$defs/later/items"},
                "escaped": {"$ref": "#/$defs/a~1b%20c"},
                "anchor": {"$ref": "#here"},
            },
            "$defs": {
                "later": {"items": {"$anchor": "here"}},
                "a/b c": {},
            },
        })
    }

    #[test]
    fn a_reference_leads_to_the_node_of_its_target() {
        load(&pointers_and_anchors(), &json!(true), |graph| {
            assert_eq!(property_target(graph, "root"), "#");
            assert_eq!(property_target(graph, "later"), "#/$defs/later");
            assert_eq!(property_target(graph, "nested"), "#/$defs/later/items");
            assert_eq!(property_target(graph, "escaped"), "#/$defs/a~1b%20c");
            assert_eq!(property_target(graph, "anchor"), "#/$defs/later/items");
            // The reference to the root closes a cycle.
            let root = object(graph, graph.a).properties[4].1;
            assert_eq!(object(graph, root).reference, Some(graph.a));
        })
        .unwrap();
    }

    fn resources_in_one_schema() -> Value {
        json!({
            "$id": "https://example.com/root.json",
            "properties": {
                "by_id": {"$ref": "https://example.com/root.json#/$defs/a"},
                "relative": {"$ref": "inner.json"},
                "into": {"$ref": "inner.json#/$defs/b"},
                "anchor": {"$ref": "inner.json#here"},
                "itself": {"$ref": ""},
            },
            "$defs": {
                "a": {},
                "inner": {
                    "$id": "inner.json",
                    "$ref": "#/$defs/b",
                    "$defs": {"b": {"$anchor": "here"}},
                },
            },
        })
    }

    #[test]
    fn a_reference_resolves_against_the_id_in_scope() {
        load(&resources_in_one_schema(), &json!(true), |graph| {
            assert_eq!(property_target(graph, "by_id"), "#/$defs/a");
            assert_eq!(property_target(graph, "relative"), "#/$defs/inner");
            assert_eq!(property_target(graph, "into"), "#/$defs/inner/$defs/b");
            assert_eq!(property_target(graph, "anchor"), "#/$defs/inner/$defs/b");
            assert_eq!(property_target(graph, "itself"), "#");
            // Inside the inner resource a pointer starts at its root.
            let inner = object(graph, object(graph, graph.a).properties[4].1).reference;
            assert_eq!(target(graph, inner.unwrap()), "#/$defs/inner/$defs/b");
        })
        .unwrap();
    }

    #[test]
    fn a_and_b_each_resolve_within_themselves() {
        let id = "https://example.com/schema.json";
        let a = json!({"$id": id, "$ref": format!("{id}#/$defs/x"), "$defs": {"x": {"type": "string"}}});
        let b =
            json!({"$id": id, "$ref": format!("{id}#/$defs/x"), "$defs": {"x": {"type": "null"}}});
        load(&a, &b, |graph| {
            let of_a = object(graph, graph.a).reference.unwrap();
            let of_b = object(graph, graph.b).reference.unwrap();
            assert_eq!(
                (graph.node(of_a).side, graph.node(of_b).side),
                (Side::A, Side::B)
            );
            assert!(object(graph, of_a).types.unwrap().contains(Type::String));
            assert!(object(graph, of_b).types.unwrap().contains(Type::Null));
        })
        .unwrap();
    }

    /// A schema that carries the documents it references, as bundling leaves it.
    fn bundled() -> Value {
        json!({
            "properties": {
                "other": {"$ref": "https://example.com/defs.json#/$defs/other"},
                "directory": {"$ref": "https://example.com/retrieved.json"},
            },
            "$defs": {
                "defs": {
                    "$id": "https://example.com/defs.json",
                    "$defs": {"name": {"type": "string"}, "other": {"$ref": "#/$defs/name"}},
                },
                // The URI that a document gives itself is the base of its references.
                "retrieved": {"$id": "https://example.com/retrieved.json", "$ref": "base/"},
                "base": {"$id": "https://example.com/base/", "$ref": "child"},
                "child": {"$id": "https://example.com/base/child"},
                "decoy": {"$id": "https://example.com/child"},
            },
        })
    }

    #[test]
    fn a_bundled_document_is_found_by_its_uri() {
        load(&bundled(), &json!(true), |graph| {
            assert_eq!(property_target(graph, "other"), "#/$defs/defs/$defs/other");
            let other = object(graph, graph.a).properties[1].1;
            let other = object(graph, other).reference.unwrap();
            assert_eq!(target(graph, other), "#/$defs/defs/$defs/name");

            assert_eq!(property_target(graph, "directory"), "#/$defs/retrieved");
            let directory = object(graph, graph.a).properties[0].1;
            let retrieved = object(graph, directory).reference.unwrap();
            assert_eq!(target(graph, retrieved), "#/$defs/base");
            let base = object(graph, retrieved).reference.unwrap();
            assert_eq!(target(graph, base), "#/$defs/child");
        })
        .unwrap();
    }

    #[test]
    fn a_reference_that_resolves_to_nothing_is_an_error_where_it_stands() {
        let cases = [
            (
                json!({"$ref": "https://example.com/missing.json"}),
                "#/$ref",
            ),
            (
                json!({"$ref": "https://example.com/missing.json#/$defs/a"}),
                "#/$ref",
            ),
            (json!({"$ref": "missing.json"}), "#/$ref"),
            (
                json!({"items": {"$ref": "#/$defs/missing"}}),
                "#/items/$ref",
            ),
            (json!({"$ref": "#missing"}), "#/$ref"),
            (json!({"$dynamicRef": "#missing"}), "#/$dynamicRef"),
            (
                json!({"$defs": {"unused": {"$ref": "#/nowhere"}}}),
                "#/$defs/unused/$ref",
            ),
            (
                json!({"$id": "https://example.com/a.json", "$ref": "b.json"}),
                "#/$ref",
            ),
            (
                json!({"$ref": "https://json-schema.org/draft/2019-09/schema"}),
                "#/$ref",
            ),
            // An anchor belongs to its resource and to no other.
            (
                json!({"$ref": "#here", "$defs": {"a": {"$id": "a.json", "$anchor": "here"}}}),
                "#/$ref",
            ),
            (json!({"$ref": "urn:example:a#/x", "x": {}}), "#/$ref"),
        ];
        for (schema, location) in cases {
            let (side, found, _) = unresolved(&schema);
            assert_eq!((side, found.as_str()), (Side::A, location), "{schema}");
        }
        let (_, _, reference) = unresolved(&json!({"$ref": "missing.json#/a"}));
        assert_eq!(reference, "missing.json#/a");
    }

    #[test]
    fn the_meta_schema_of_the_draft_is_known() {
        let schema = json!({"$ref": "https://json-schema.org/draft/2020-12/schema"});
        load(&schema, &schema, |graph| {
            let meta = object(graph, graph.a).reference.unwrap();
            assert_eq!(
                graph.location(meta),
                "https://json-schema.org/draft/2020-12/schema#"
            );
            assert_eq!(object(graph, meta).dynamic_anchor, Some("meta"));
            // It pulls in the meta-schemas of its vocabularies.
            let applicator = object(graph, meta).all_of[1];
            assert_eq!(
                target(graph, applicator),
                "https://json-schema.org/draft/2020-12/meta/applicator#"
            );
            // B has nodes of its own for it.
            let of_b = object(graph, graph.b).reference.unwrap();
            assert_ne!(of_b, meta);
            assert_eq!(
                (graph.node(meta).side, graph.node(of_b).side),
                (Side::A, Side::B)
            );
            assert_eq!(graph.location(of_b), graph.location(meta));
        })
        .unwrap();
    }

    #[test]
    fn a_dynamic_reference_keeps_its_text_and_its_first_target() {
        let schema = json!({
            "$dynamicAnchor": "node",
            "items": {"$dynamicRef": "#node"},
        });
        load(&schema, &json!(true), |graph| {
            let items = object(graph, object(graph, graph.a).items.unwrap());
            assert_eq!(
                items.dynamic_reference,
                Some(DynamicReference {
                    reference: "#node",
                    target: graph.a,
                })
            );
            assert_eq!(items.reference, None);
        })
        .unwrap();
    }

    /// Both resources have a dynamic anchor of the same name, and the reference names one.
    fn dynamic_anchors() -> Value {
        json!({
            "$id": "https://example.com/root",
            "$dynamicAnchor": "node",
            "$ref": "https://example.com/list#node",
            "items": {"$dynamicRef": "list#node"},
            "$defs": {
                "list": {"$id": "https://example.com/list", "$dynamicAnchor": "node"},
            },
        })
    }

    #[test]
    fn a_reference_to_a_dynamic_anchor_is_resolved_like_any_other() {
        // The dynamic scope would lead both references back to the root.
        load(&dynamic_anchors(), &json!(true), |graph| {
            assert_eq!(target(graph, graph.a), "#/$defs/list");
            let items = object(graph, object(graph, graph.a).items.unwrap());
            let first = items.dynamic_reference.unwrap().target;
            assert_eq!(graph.location(first), "#/$defs/list");
        })
        .unwrap();
    }

    fn targets_that_are_no_subschemas() -> Value {
        json!({
            "$ref": "#/x-shared/name",
            "x-shared": {
                "name": {"properties": {"first": {"$ref": "#/x-shared/text"}}},
                "text": {},
            },
            "$defs": {
                "inner": {
                    "$id": "https://example.com/inner",
                    "$ref": "#/x-inner/0",
                    "x-inner": [{"$ref": "#/x-inner/1"}, {"$anchor": "unseen"}],
                },
            },
        })
    }

    #[test]
    fn a_target_where_the_draft_puts_no_schema_is_parsed_when_referenced() {
        load(&targets_that_are_no_subschemas(), &json!(true), |graph| {
            let name = object(graph, graph.a).reference.unwrap();
            assert_eq!(graph.location(name), "#/x-shared/name");
            assert_eq!(graph.node(name).resource, graph.a);
            let first = object(graph, name).properties[0].1;
            assert_eq!(graph.location(first), "#/x-shared/name/properties/first");
            // A pointer in it still starts at the root of the resource.
            assert_eq!(target(graph, first), "#/x-shared/text");

            let mut nodes = (0..graph.len()).map(NodeId::new);
            let inner = nodes
                .find(|&node| graph.location(node) == "#/$defs/inner")
                .unwrap();
            let first = object(graph, inner).reference.unwrap();
            assert_eq!(graph.location(first), "#/$defs/inner/x-inner/0");
            assert_eq!(graph.node(first).resource, inner);
            assert_eq!(target(graph, first), "#/$defs/inner/x-inner/1");
        })
        .unwrap();

        let bad = json!({"$ref": "#/x-shared", "x-shared": 1});
        assert_eq!(
            load(&bad, &json!(true), |_| ()).unwrap_err(),
            Error::InvalidKeyword {
                schema: Side::A,
                location: "#/x-shared".to_owned(),
                message: "must be a schema: an object or a boolean".to_owned(),
            }
        );
        // What such a value declares is not looked for, so no reference can name it.
        let unseen = json!({"$ref": "#/x/0", "x": [{"$ref": "#unseen"}, {"$anchor": "unseen"}]});
        assert_eq!(unresolved(&unseen).1, "#/x/0/$ref");
    }

    #[test]
    fn an_id_on_such_a_target_is_the_base_of_what_is_inside() {
        let schema = json!({
            "$ref": "#/x/pet",
            "x": {
                "pet": {
                    "$id": "https://example.com/pet",
                    "properties": {
                        "pointer": {"$ref": "#/properties/name"},
                        "by_uri": {"$ref": "pet#/properties/name"},
                        "name": {},
                    },
                },
            },
            "properties": {"name": {}},
        });
        load(&schema, &json!(true), |graph| {
            let pet = object(graph, graph.a).reference.unwrap();
            assert_eq!(graph.node(pet).resource, pet);
            for (name, property) in &object(graph, pet).properties {
                if *name != "name" {
                    assert_eq!(target(graph, *property), "#/x/pet/properties/name");
                }
            }
        })
        .unwrap();
        // No other reference can name it by that URI.
        let outside = json!({
            "allOf": [{"$ref": "#/x/pet"}, {"$ref": "https://example.com/pet"}],
            "x": {"pet": {"$id": "https://example.com/pet"}},
        });
        assert_eq!(unresolved(&outside).1, "#/allOf/1/$ref");
    }

    #[test]
    fn a_fragment_is_decoded_before_it_is_read() {
        let anchor = json!({"$ref": "#%78", "$defs": {"a": {"$anchor": "x"}}});
        assert_eq!(root_target(&anchor).unwrap(), "#/$defs/a");
        let pointer = json!({"$ref": "#%2F$defs%2Fx", "$defs": {"x": false}});
        assert_eq!(root_target(&pointer).unwrap(), "#/$defs/x");
        // `%25` is a percent sign, and what follows it is not decoded again.
        let percent = json!({"$ref": "#/$defs/100%2541", "$defs": {"100%41": {}, "100A": {}}});
        assert_eq!(root_target(&percent).unwrap(), "#/$defs/100%2541");
        let tilde = json!({"$ref": "#/$defs/a~1b~0c", "$defs": {"a/b~c": {}}});
        assert_eq!(root_target(&tilde).unwrap(), "#/$defs/a~1b~0c");
    }

    #[test]
    fn a_pointer_is_read_as_strictly_as_it_is_defined() {
        let cases = [
            json!({"$ref": "#/allOf/00", "allOf": [false]}),
            json!({"$ref": "#/allOf/+0", "allOf": [false]}),
            json!({"$ref": "#/allOf/1", "allOf": [false]}),
            json!({"$ref": "#/allOf/-", "allOf": [false]}),
            json!({"$ref": "#/allOf/", "allOf": [false]}),
            json!({"$ref": "#/$defs/~2", "$defs": {"~2": false}}),
            json!({"$ref": "#/$defs/a~", "$defs": {"a~": false}}),
            json!({"$ref": "#/type/x", "type": "string"}),
            json!({"$ref": "#/$defs/%FF", "$defs": {"a": false}}),
        ];
        for schema in cases {
            assert_eq!(unresolved(&schema).1, "#/$ref", "{schema}");
        }
        let mut branches = vec![json!(true); 10];
        branches.push(json!({}));
        let index = json!({"$ref": "#/allOf/10", "allOf": branches});
        assert_eq!(root_target(&index).unwrap(), "#/allOf/10");
        let empty_name = json!({"$ref": "#/$defs/", "$defs": {"": {}}});
        assert_eq!(root_target(&empty_name).unwrap(), "#/$defs/");
    }

    #[test]
    fn a_fragment_may_hold_what_a_uri_does_not_allow() {
        let schema = json!({
            "properties": {
                "space": {"$ref": "#/$defs/item array"},
                "letters": {"$ref": "#/$defs/Größe"},
                "percent": {"$ref": "#/$defs/50%"},
            },
            "$defs": {"item array": {}, "Größe": {}, "50%": {}},
        });
        load(&schema, &json!(true), |graph| {
            assert_eq!(property_target(graph, "space"), "#/$defs/item%20array");
            assert_eq!(property_target(graph, "letters"), "#/$defs/Gr%C3%B6%C3%9Fe");
            assert_eq!(property_target(graph, "percent"), "#/$defs/50%25");
        })
        .unwrap();
    }

    #[test]
    fn a_referenced_value_may_be_nested_deeply() {
        let mut deep = json!({});
        for _ in 0..100_000 {
            deep = Value::Object(Map::from_iter([("not".to_owned(), deep)]));
        }
        let schema = Value::Object(Map::from_iter([
            ("$ref".to_owned(), json!("#/x")),
            ("x".to_owned(), deep),
        ]));
        let nodes = load(&schema, &json!(true), |graph| graph.len()).unwrap();
        assert_eq!(nodes, 100_003);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget(schema);
    }

    #[test]
    fn the_parts_of_a_fragment_are_read_as_their_rules_say() {
        assert_eq!(unescaped("a~1b~0c~01").unwrap(), "a/b~c~1");
        assert_eq!(unescaped("plain").unwrap(), "plain");
        assert_eq!(unescaped("~"), None);
        assert_eq!(unescaped("~x"), None);
        assert_eq!(percent_decoded("a%20b%C3%A9").unwrap(), "a b\u{e9}");
        assert_eq!(percent_decoded("100%").unwrap(), "100%");
        assert_eq!(percent_decoded("%zz%4").unwrap(), "%zz%4");
        assert_eq!(percent_decoded("%2541").unwrap(), "%41");
        assert_eq!(percent_decoded("%FF"), None);
    }

    #[test]
    fn referencing_finds_the_same_targets() {
        let schemas = [
            (pointers_and_anchors(), 5),
            (resources_in_one_schema(), 6),
            (bundled(), 5),
            (dynamic_anchors(), 2),
            (targets_that_are_no_subschemas(), 4),
        ];
        for (schema, references) in schemas {
            let comparison = compared(&schema).unwrap();
            assert_eq!(comparison.differences, Vec::<String>::new(), "{schema}");
            assert_eq!(
                (comparison.same, comparison.unresolved),
                (references, 0),
                "{schema}"
            );
        }
        // The meta-schema of the draft and the eight that it draws in.
        let meta = json!({"$ref": "https://json-schema.org/draft/2020-12/schema"});
        let comparison = compared(&meta).unwrap();
        assert_eq!(comparison.differences, Vec::<String>::new());
        assert!(comparison.same > 40, "{}", comparison.same);
    }
}
