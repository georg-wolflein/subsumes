//! The second step of loading: every reference resolved to a node.
//!
//! Resolution is the work of the `referencing` crate, and this module is the only one that
//! uses it for that.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, PoisonError};

use referencing::{Draft, Registry, RegistryBuilder, Resolver, ResourceRef, Retrieve, Uri};
use serde_json::Value;

use super::parse::{Builder, Reference, ReferenceKeyword, Unlinked};
use super::{DynamicReference, Graph, NodeId, Origin, Schema, location, push_token};
use crate::{Error, Side};

/// The URI of A and of B during a check. A schema without an `$id` has no URI of its own, and
/// each of the two has its own registry, so both can have this one.
const ROOT: &str = "json-schema:///";

/// The documents given to a checker, indexed once for all its checks.
#[derive(Debug, Clone)]
pub(crate) struct Documents {
    /// The documents, on top of the meta-schemas that `referencing` ships.
    registry: Registry<'static>,
    /// The documents that the given ones reference and that nobody gave.
    missing: Vec<String>,
}

impl Documents {
    /// # Errors
    ///
    /// When a URI is not one, or `referencing` cannot index a document.
    pub(crate) fn new(documents: &BTreeMap<String, Arc<Value>>) -> Result<Self, Error> {
        let asked = Asked::default();
        let pairs = documents
            .iter()
            .map(|(uri, document)| (uri, Arc::clone(document)));
        let registry = referencing::SPECIFICATIONS
            .extend(pairs)
            .and_then(|builder| prepare(builder, &asked))
            .map_err(|error| Error::InvalidDocuments {
                message: error.to_string(),
            })?;
        Ok(Self {
            registry,
            missing: asked.take(),
        })
    }

    /// What `schema` can refer to as one of the two schemas of a check.
    ///
    /// # Errors
    ///
    /// When `referencing` cannot index the schema. [`parse`](super::parse) catches what is
    /// known to cause that, with its location, so it should run first.
    pub(crate) fn scope<'x>(&'x self, side: Side, schema: &'x Value) -> Result<Scope<'x>, Error> {
        let asked = Asked::default();
        let registry = self
            .registry
            .add(ROOT, schema)
            .and_then(|builder| prepare(builder, &asked))
            .map_err(|error| Error::InvalidKeyword {
                schema: side,
                location: "#".to_owned(),
                message: error.to_string(),
            })?;
        Ok(Scope {
            registry,
            missing: asked.take(),
            documents: self,
        })
    }
}

/// What one of the two schemas can refer to: itself, the documents of the checker and the
/// meta-schemas. A and B each have their own, because two versions of a schema usually share
/// an `$id`.
#[derive(Debug)]
pub(crate) struct Scope<'x> {
    registry: Registry<'x>,
    /// The documents that the schema references and that nobody gave.
    missing: Vec<String>,
    documents: &'x Documents,
}

impl Scope<'_> {
    /// Whether nobody gave the document with this URI.
    fn lacks(&self, uri: &str) -> bool {
        let mut missing = self.missing.iter().chain(&self.documents.missing);
        missing.any(|missing| missing == uri)
    }
}

/// Nothing is fetched. `referencing` asks for every document that is referenced and not given;
/// each gets `true` in its place and its URI is noted, so that a reference to it can be
/// reported where it stands.
#[derive(Debug, Default, Clone)]
struct Asked(Arc<Mutex<Vec<String>>>);

impl Asked {
    fn take(&self) -> Vec<String> {
        std::mem::take(&mut self.0.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

impl Retrieve for Asked {
    fn retrieve(
        &self,
        uri: &Uri<String>,
    ) -> Result<Value, Box<dyn std::error::Error + Send + Sync>> {
        let mut asked = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        asked.push(uri.as_str().to_owned());
        Ok(Value::Bool(true))
    }
}

fn prepare<'x>(
    builder: RegistryBuilder<'x>,
    asked: &Asked,
) -> Result<Registry<'x>, referencing::Error> {
    builder
        .draft(Draft::Draft202012)
        .retrieve_known_draft_meta_schemas(false)
        .retriever(asked.clone())
        .prepare()
}

impl<'a> Unlinked<'a> {
    /// Resolves every reference, and parses every document that a reference leads to.
    ///
    /// A schema needs its scope only if it [has references](Self::has_references).
    ///
    /// # Errors
    ///
    /// When a reference resolves to nothing, or a document it leads to is not a valid schema.
    pub(crate) fn link<'g>(
        self,
        a: Option<&'g Scope<'g>>,
        b: Option<&'g Scope<'g>>,
    ) -> Result<Graph<'g>, Error>
    where
        'a: 'g,
    {
        let mut linker = Linker {
            builder: self.builder,
            scopes: [a, b],
            resolvers: HashMap::new(),
        };
        // Parsing a document adds its references to the end of the list.
        let mut next = 0;
        while let Some(&reference) = linker.builder.references.get(next) {
            next += 1;
            let target = linker.resolve(reference)?;
            let node = &mut linker.builder.nodes[reference.node.index()];
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
            nodes: linker.builder.nodes,
            a: self.a,
            b: self.b,
        })
    }
}

struct Linker<'g> {
    builder: Builder<'g>,
    /// The scope of A and that of B.
    scopes: [Option<&'g Scope<'g>>; 2],
    /// The resolver of every node that begins a resource, once it was needed.
    resolvers: HashMap<NodeId, Resolver<'g>>,
}

impl<'g> Linker<'g> {
    /// The scope of a side. Without one, none of its references resolves.
    fn scope(&self, reference: Reference) -> Result<&'g Scope<'g>, Error> {
        let side = self.builder.nodes[reference.node.index()].side;
        let scope = match side {
            Side::A => self.scopes[0],
            Side::B => self.scopes[1],
        };
        scope.ok_or_else(|| Error::UnresolvedReference {
            schema: side,
            location: self.location(reference.node, reference.keyword.name()),
            reference: reference.reference.to_owned(),
        })
    }

    /// The node that a reference points to.
    fn resolve(&mut self, reference: Reference<'g>) -> Result<NodeId, Error> {
        let node = &self.builder.nodes[reference.node.index()];
        let (side, resource) = (node.side, node.resource);
        let scope = self.scope(reference)?;
        let resolver = self.resolver(scope, resource)?;
        let resolved = resolver
            .lookup(reference.reference)
            .ok()
            .filter(|resolved| !scope.lacks(resolved.resolver().base_uri().as_str()));
        let Some(resolved) = resolved else {
            return Err(Error::UnresolvedReference {
                schema: side,
                location: self.location(reference.node, reference.keyword.name()),
                reference: reference.reference.to_owned(),
            });
        };
        let target = resolved.contents();
        if let Some(node) = self.builder.known(side, target) {
            return Ok(node);
        }

        // The target is in a document that is not parsed yet, or in a place where the draft
        // puts no schema. First parse the resource around it, as a whole.
        let base = resolved.resolver().base_uri();
        let within = scope.registry.resolver(Uri::clone(&base));
        if let Ok(resource) = within.lookup("")
            && self.builder.known(side, resource.contents()).is_none()
        {
            let origin = Origin::Reference(base.as_str().to_owned());
            let root = self.builder.tree(side, resource.contents(), origin)?;
            self.resolvers.insert(root, within.clone());
            if let Some(node) = self.builder.known(side, target) {
                return Ok(node);
            }
        }
        let origin = Origin::Reference(absolute(&resolver, reference.reference));
        let node = self.builder.tree(side, target, origin)?;
        self.resolvers.insert(node, within);
        Ok(node)
    }

    /// The resolver for the references of a resource: its base URI is that of the resource.
    fn resolver(&mut self, scope: &'g Scope<'g>, resource: NodeId) -> Result<Resolver<'g>, Error> {
        // The resources around this one that have no resolver yet, from the inside out.
        let mut pending = Vec::new();
        let mut current = resource;
        let mut resolver = loop {
            if let Some(resolver) = self.resolvers.get(&current) {
                break resolver.clone();
            }
            pending.push(current);
            let node = &self.builder.nodes[current.index()];
            match node.origin {
                Origin::Child { parent, .. } => {
                    current = self.builder.nodes[parent.index()].resource;
                }
                // The root of A or of B. The target of a reference gets its resolver when
                // it is parsed.
                Origin::Root | Origin::Reference(_) => {
                    let root = referencing::uri::from_str(ROOT).expect("the root URI is valid");
                    break scope.registry.resolver(root);
                }
            }
        };
        for resource in pending.into_iter().rev() {
            let value = self.builder.values[resource.index()];
            resolver = resolver
                .in_subresource(ResourceRef::new(value, Draft::Draft202012))
                .map_err(|error| Error::InvalidKeyword {
                    schema: self.builder.nodes[resource.index()].side,
                    location: self.location(resource, "$id"),
                    message: error.to_string(),
                })?;
            self.resolvers.insert(resource, resolver.clone());
        }
        Ok(resolver)
    }

    /// The location of a keyword of a node.
    fn location(&self, node: NodeId, keyword: &str) -> String {
        let nodes = &self.builder.nodes;
        let mut location = location(nodes, &nodes[node.index()].origin);
        push_token(&mut location, keyword);
        location
    }
}

/// The URI that a reference names, for the location of a target that no node holds yet.
fn absolute(resolver: &Resolver, reference: &str) -> String {
    let (document, fragment) = match reference.strip_prefix('#') {
        Some(fragment) => ("", fragment),
        None => reference.rsplit_once('#').unwrap_or((reference, "")),
    };
    let base = resolver.base_uri();
    let document = if document.is_empty() {
        base.as_str().to_owned()
    } else {
        resolver
            .resolve_uri(&base.borrow(), document)
            .map_or_else(|_| document.to_owned(), |uri| uri.as_str().to_owned())
    };
    if document == ROOT {
        format!("#{fragment}")
    } else {
        format!("{document}#{fragment}")
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::super::{Keywords, Type, parse};
    use super::*;

    /// Loads A and B with the given documents, and hands the graph to `inspect`.
    fn load<R>(
        a: &Value,
        b: &Value,
        documents: &[(&str, Value)],
        inspect: impl FnOnce(&Graph) -> R,
    ) -> Result<R, Error> {
        let documents = documents
            .iter()
            .map(|(uri, document)| ((*uri).to_owned(), Arc::new(document.clone())))
            .collect();
        let documents = Documents::new(&documents)?;
        let unlinked = parse(a, b)?;
        let scope_a = documents.scope(Side::A, a)?;
        let scope_b = documents.scope(Side::B, b)?;
        let graph = unlinked.link(Some(&scope_a), Some(&scope_b))?;
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

    fn unresolved(a: &Value, documents: &[(&str, Value)]) -> (Side, String, String) {
        match load(a, &json!(true), documents, |_| ()) {
            Err(Error::UnresolvedReference {
                schema,
                location,
                reference,
            }) => (schema, location, reference),
            other => panic!("{a} gave {other:?}"),
        }
    }

    #[test]
    fn a_reference_leads_to_the_node_of_its_target() {
        let schema = json!({
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
        });
        load(&schema, &json!(true), &[], |graph| {
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

    #[test]
    fn a_reference_resolves_against_the_id_in_scope() {
        let schema = json!({
            "$id": "https://example.com/root.json",
            "properties": {
                "by_id": {"$ref": "https://example.com/root.json#/$defs/a"},
                "relative": {"$ref": "inner.json"},
                "into": {"$ref": "inner.json#/$defs/b"},
                "anchor": {"$ref": "inner.json#here"},
            },
            "$defs": {
                "a": {},
                "inner": {
                    "$id": "inner.json",
                    "$ref": "#/$defs/b",
                    "$defs": {"b": {"$anchor": "here"}},
                },
            },
        });
        load(&schema, &json!(true), &[], |graph| {
            assert_eq!(property_target(graph, "by_id"), "#/$defs/a");
            assert_eq!(property_target(graph, "relative"), "#/$defs/inner");
            assert_eq!(property_target(graph, "into"), "#/$defs/inner/$defs/b");
            assert_eq!(property_target(graph, "anchor"), "#/$defs/inner/$defs/b");
            // Inside the inner resource a pointer starts at its root.
            let inner = object(graph, object(graph, graph.a).properties[3].1).reference;
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
        load(&a, &b, &[], |graph| {
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

    #[test]
    fn a_reference_to_a_document_of_the_checker_parses_that_document() {
        let documents = [(
            "https://example.com/defs.json",
            json!({"$defs": {"name": {"type": "string"}, "other": {"$ref": "#/$defs/name"}}}),
        )];
        let a = json!({"$ref": "https://example.com/defs.json#/$defs/other"});
        let b = json!({"items": {"$ref": "https://example.com/defs.json"}});
        load(&a, &b, &documents, |graph| {
            let other = object(graph, graph.a).reference.unwrap();
            assert_eq!(
                graph.location(other),
                "https://example.com/defs.json#/$defs/other"
            );
            assert_eq!(
                target(graph, other),
                "https://example.com/defs.json#/$defs/name"
            );
            // B reaches the same document and gets nodes of its own for it.
            let items = object(graph, graph.b).items.unwrap();
            let document = object(graph, items).reference.unwrap();
            assert_eq!(graph.location(document), "https://example.com/defs.json#");
            assert_eq!(graph.node(document).side, Side::B);
            assert_ne!(graph.node(other).resource, document);
            // A, its document with two definitions, B with its items, and the document again.
            assert_eq!(graph.len(), 1 + 3 + 2 + 3);
        })
        .unwrap();
    }

    #[test]
    fn a_part_of_a_document_that_was_reached_before_is_not_parsed_again() {
        let documents = [(
            "https://example.com/outer.json",
            json!({"$defs": {"inner": {"$id": "inner.json", "type": "string"}}}),
        )];
        let schema = json!({"allOf": [
            {"$ref": "https://example.com/inner.json"},
            {"$ref": "https://example.com/outer.json"},
        ]});
        load(&schema, &json!(true), &documents, |graph| {
            let branches = &object(graph, graph.a).all_of;
            assert_eq!(
                target(graph, branches[0]),
                "https://example.com/inner.json#"
            );
            assert_eq!(
                target(graph, branches[1]),
                "https://example.com/outer.json#"
            );
            // A, its two branches, the inner resource, the outer document, and B.
            assert_eq!(graph.len(), 6);
        })
        .unwrap();
    }

    #[test]
    fn a_document_is_read_only_when_a_reference_leads_to_it() {
        let draft_07 = "http://json-schema.org/draft-07/schema#";
        let documents = [
            (
                "https://example.com/broken.json",
                json!({"$defs": {"a": {"minLength": "1"}}}),
            ),
            ("https://example.com/old.json", json!({"$schema": draft_07})),
            (
                "https://example.com/dangling.json",
                json!({"$ref": "nowhere.json"}),
            ),
        ];
        assert!(load(&json!({}), &json!({}), &documents, |_| ()).is_ok());

        let broken = json!({"$ref": "https://example.com/broken.json"});
        assert_eq!(
            load(&json!(true), &broken, &documents, |_| ()).unwrap_err(),
            Error::InvalidKeyword {
                schema: Side::B,
                location: "https://example.com/broken.json#/$defs/a/minLength".to_owned(),
                message: "must be a non-negative integer".to_owned(),
            }
        );
        let old = json!({"$ref": "https://example.com/old.json"});
        assert_eq!(
            load(&old, &json!(true), &documents, |_| ()).unwrap_err(),
            Error::UnsupportedDialect {
                schema: Side::A,
                location: "https://example.com/old.json#/$schema".to_owned(),
                dialect: draft_07.to_owned(),
            }
        );
        let dangling = json!({"$ref": "https://example.com/dangling.json"});
        assert_eq!(
            unresolved(&dangling, &documents),
            (
                Side::A,
                "https://example.com/dangling.json#/$ref".to_owned(),
                "nowhere.json".to_owned()
            )
        );
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
        ];
        for (schema, location) in cases {
            let (side, found, _) = unresolved(&schema, &[]);
            assert_eq!((side, found.as_str()), (Side::A, location), "{schema}");
        }
        let (_, _, reference) = unresolved(&json!({"$ref": "missing.json#/a"}), &[]);
        assert_eq!(reference, "missing.json#/a");
    }

    #[test]
    fn the_meta_schema_of_the_draft_is_known() {
        let schema = json!({"$ref": "https://json-schema.org/draft/2020-12/schema"});
        load(&schema, &json!(true), &[], |graph| {
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
        })
        .unwrap();
    }

    #[test]
    fn a_dynamic_reference_keeps_its_text_and_its_first_target() {
        let schema = json!({
            "$dynamicAnchor": "node",
            "items": {"$dynamicRef": "#node"},
        });
        load(&schema, &json!(true), &[], |graph| {
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

    #[test]
    fn a_target_where_the_draft_puts_no_schema_is_parsed_when_referenced() {
        let schema = json!({
            "$ref": "#/x-shared/name",
            "x-shared": {"name": {"properties": {"first": {"$ref": "#/x-shared/text"}}}, "text": {}},
        });
        load(&schema, &json!(true), &[], |graph| {
            let name = object(graph, graph.a).reference.unwrap();
            assert_eq!(graph.location(name), "#/x-shared/name");
            let first = object(graph, name).properties[0].1;
            assert_eq!(graph.location(first), "#/x-shared/name/properties/first");
            assert_eq!(target(graph, first), "#/x-shared/text");
        })
        .unwrap();

        let bad = json!({"$ref": "#/x-shared", "x-shared": 1});
        assert_eq!(
            load(&bad, &json!(true), &[], |_| ()).unwrap_err(),
            Error::InvalidKeyword {
                schema: Side::A,
                location: "#/x-shared".to_owned(),
                message: "must be a schema: an object or a boolean".to_owned(),
            }
        );
    }

    #[test]
    fn a_uri_that_is_none_makes_the_documents_unusable() {
        let error = load(&json!({}), &json!({}), &[("not a uri", json!({}))], |_| ()).unwrap_err();
        assert!(matches!(error, Error::InvalidDocuments { .. }), "{error:?}");
    }
}
