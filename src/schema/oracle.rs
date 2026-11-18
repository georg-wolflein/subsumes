//! Tests that hold the resolution of references against the `referencing` crate, which resolves
//! them for the validator `jsonschema`: on the corpus, and on schemas made at random.
//!
//! The two differ on purpose in a few places, and the comparison and the random schemas stay
//! clear of them:
//!
//! - The crate's lookup follows the dynamic scope. The comparison looks a fragment up from the
//!   resource that the reference names, where the scope holds nothing else.
//! - The crate decides between pointer and anchor before it decodes a fragment, takes `00` and
//!   `+0` for array indexes and `~2` for a name, and rejects a reference with a URI whose
//!   fragment holds a character that a URI does not allow.
//! - The crate does not find a pointer inside a resource whose `$id` stands where the draft
//!   puts no schema. This library does.
//!
//! The comparison does not ask this library where the references of a schema are, or which
//! resource each stands in. It walks the JSON itself and lets `referencing` work out the base
//! of every schema on the way, so a mistake of the parser shows as a difference and is not
//! shared. Only for what the draft does not take for a schema, such as the target of a
//! pointer into an unknown keyword, does it take the place from this library.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::Path;
use std::sync::{Arc, Mutex};

use referencing::{Draft, Registry, Resolver, ResourceRef, Retrieve, Uri};
use serde_json::{Map, Value, json};

use super::parse::{Builder, ROOT, Reference, parse};
use super::{NodeId, Origin, push_token};
use crate::testing::{Random, corpus_cases, schemas_of};
use crate::{Error, Side, meta_schemas};

/// How this library and `referencing` resolved the references of one schema.
#[derive(Debug, Default, PartialEq, Eq)]
pub(super) struct Comparison {
    /// The references that both resolved to the same value.
    pub same: usize,
    /// Those of them that stand in the schema itself, not in a meta-schema, and name their
    /// resource by a URI.
    pub same_by_uri: usize,
    /// Those of them that stand in the schema itself and name their target by an anchor.
    pub same_by_anchor: usize,
    /// The references that neither resolved.
    pub unresolved: usize,
    /// The references, of both kinds above, whose place the comparison took from this library.
    pub placed_by_the_library: usize,
    /// Each reference on which the two differ.
    pub differences: Vec<String>,
}

impl Comparison {
    fn add(&mut self, other: Self) {
        self.same += other.same;
        self.same_by_uri += other.same_by_uri;
        self.same_by_anchor += other.same_by_anchor;
        self.unresolved += other.unresolved;
        self.placed_by_the_library += other.placed_by_the_library;
        self.differences.extend(other.differences);
    }
}

/// The crate asks for every document that is referenced and not there. Each gets `true` in
/// its place and its URI is noted, so that a reference to it counts as unresolved.
#[derive(Debug, Default, Clone)]
struct Asked(Arc<Mutex<Vec<String>>>);

impl Retrieve for Asked {
    fn retrieve(
        &self,
        uri: &Uri<String>,
    ) -> Result<Value, Box<dyn std::error::Error + Send + Sync>> {
        self.0.lock().unwrap().push(uri.as_str().to_owned());
        Ok(Value::Bool(true))
    }
}

/// The keywords of the draft that hold one schema, a list of schemas, and schemas under names.
/// The parser knows the same, and the two are written apart so that one checks the other.
const ONE: [&str; 11] = [
    "additionalProperties",
    "contains",
    "contentSchema",
    "else",
    "if",
    "items",
    "not",
    "propertyNames",
    "then",
    "unevaluatedItems",
    "unevaluatedProperties",
];
const LISTED: [&str; 4] = ["allOf", "anyOf", "oneOf", "prefixItems"];
const NAMED: [&str; 5] = [
    "$defs",
    "definitions",
    "dependentSchemas",
    "patternProperties",
    "properties",
];

/// A reference as the comparison finds it in the JSON.
struct Found<'r> {
    /// The schema that has the keyword.
    holder: &'r Value,
    keyword: &'static str,
    text: &'r str,
    /// The resolver of `referencing` for that schema.
    resolver: Resolver<'r>,
}

/// Every reference of a document that stands where the draft puts a schema. `at` is the
/// resolver for the root of the document.
fn references_in<'r>(document: &'r Value, at: Resolver<'r>) -> Vec<Found<'r>> {
    let mut found = Vec::new();
    let mut pending = vec![(document, at)];
    while let Some((schema, resolver)) = pending.pop() {
        let Value::Object(keywords) = schema else {
            continue;
        };
        // The crate takes the `$id` of the schema, if it has one, as the base of what follows.
        let subresource = ResourceRef::new(schema, Draft::Draft202012);
        let Ok(resolver) = resolver.in_subresource(subresource) else {
            continue;
        };
        for keyword in ["$ref", "$dynamicRef"] {
            if let Some(Value::String(text)) = keywords.get(keyword) {
                found.push(Found {
                    holder: schema,
                    keyword,
                    text,
                    resolver: resolver.clone(),
                });
            }
        }
        for (keyword, held) in keywords {
            let keyword = keyword.as_str();
            let schemas: Vec<&Value> = match held {
                _ if ONE.contains(&keyword) => vec![held],
                Value::Array(schemas) if LISTED.contains(&keyword) => schemas.iter().collect(),
                Value::Object(schemas) if NAMED.contains(&keyword) => schemas.values().collect(),
                _ => Vec::new(),
            };
            pending.extend(schemas.into_iter().map(|schema| (schema, resolver.clone())));
        }
    }
    found
}

/// The resolver of `referencing` for the references of a resource, placed as this library
/// places the resource. It serves only where the crate sees no schema.
fn resolver<'r>(
    builder: &Builder<'r>,
    registry: &'r Registry<'r>,
    resource: NodeId,
) -> Option<Resolver<'r>> {
    let root = |uri: &str| registry.resolver(referencing::uri::from_str(uri).unwrap());
    let outer = match &builder.nodes[resource.index()].origin {
        Origin::Root => root(ROOT),
        Origin::Child { parent, .. } => {
            resolver(builder, registry, builder.nodes[parent.index()].resource)?
        }
        Origin::Reference(uri) if !uri.contains('#') => root(uri),
        // A resource in a place where the draft puts no schema, which the crate never enters.
        Origin::Reference(_) => return None,
    };
    let value = builder.values[resource.index()];
    outer
        .in_subresource(ResourceRef::new(value, Draft::Draft202012))
        .ok()
}

/// What `referencing` finds for a reference, looked up statically.
fn found_by_referencing<'r>(
    registry: &'r Registry<'r>,
    resolver: &Resolver<'r>,
    missing: &[String],
    reference: &str,
) -> Option<&'r Value> {
    let (resource, fragment) = reference.split_once('#').unwrap_or((reference, ""));
    let base = resolver.base_uri();
    let uri = if resource.is_empty() {
        (*base).clone()
    } else {
        (*resolver.resolve_uri(&base.borrow(), resource).ok()?).clone()
    };
    if missing.iter().any(|missing| missing == uri.as_str()) {
        return None;
    }
    let resolved = registry.resolver(uri).lookup(&format!("#{fragment}"));
    resolved.ok().map(|resolved| resolved.contents())
}

/// The crate's copies of the meta-schemas declare a `$vocabulary` where the ones that
/// json-schema.org serves declare none. Nothing else differs.
fn without_vocabulary(meta_schema: &Value) -> Value {
    let mut meta_schema = meta_schema.clone();
    if let Value::Object(keywords) = &mut meta_schema {
        keywords.remove("$vocabulary");
    }
    meta_schema
}

impl Comparison {
    /// Resolves one reference with this library and holds the result against what
    /// `referencing` found. Returns `false` once the library began to parse a value that is
    /// no schema, after which what it built is not fit for another reference.
    fn settle<'r>(
        &mut self,
        builder: &mut Builder<'r>,
        reference: Reference<'r>,
        theirs: Option<&Value>,
    ) -> bool {
        let text = reference.reference;
        let place = format!("{} to {text}", builder.location(reference.node));
        match (builder.target(reference), theirs) {
            (Ok(Some(ours)), Some(theirs)) => {
                let ours = builder.values[ours.index()];
                // Each of the two has its own copy of a meta-schema.
                let equal = std::ptr::eq(ours, theirs)
                    || (builder.known(Side::A, theirs).is_none()
                        && without_vocabulary(ours) == without_vocabulary(theirs));
                if equal {
                    let (resource, fragment) = text.split_once('#').unwrap_or((text, ""));
                    let own = place.starts_with('#');
                    let anchor = !fragment.is_empty() && !fragment.starts_with(['/', '%']);
                    self.same += 1;
                    self.same_by_uri += usize::from(own && !resource.is_empty());
                    self.same_by_anchor += usize::from(own && anchor);
                } else {
                    self.differences.push(format!("{place}: another value"));
                }
            }
            (Ok(None), None) => self.unresolved += 1,
            (Ok(Some(ours)), None) => {
                let ours = builder.location(ours);
                self.differences
                    .push(format!("{place}: only this library, {ours}"));
            }
            (Ok(None), Some(_)) => self.differences.push(format!("{place}: only referencing")),
            // The crate hands out any value, and this library wants a schema.
            (Err(Error::InvalidKeyword { .. }), Some(theirs))
                if !theirs.is_object() && !theirs.is_boolean() =>
            {
                return false;
            }
            (Err(error), _) => {
                self.differences.push(format!("{place}: {error}"));
                return false;
            }
        }
        true
    }
}

/// Resolves every reference of a schema with this library and with `referencing`.
///
/// # Errors
///
/// When one of the two does not take the schema at all, with what it says.
pub(super) fn compared(schema: &Value) -> Result<Comparison, String> {
    let truth = Value::Bool(true);
    let mut builder = parse(schema, &truth)
        .map_err(|error| format!("is not parsed: {error}"))?
        .builder;
    let asked = Asked::default();
    let registry = referencing::SPECIFICATIONS
        .add(ROOT, schema)
        .and_then(|registry| {
            registry
                .draft(Draft::Draft202012)
                .retrieve_known_draft_meta_schemas(false)
                .retriever(asked.clone())
                .prepare()
        })
        .map_err(|error| format!("is not indexed by referencing: {error}"))?;
    let missing = std::mem::take(&mut *asked.0.lock().unwrap());
    let mut comparison = Comparison::default();

    // First the references that the comparison finds by itself: those of the schema, then
    // those of every meta-schema that a reference has led to by then.
    let mut documents = vec![(schema, ROOT)];
    // What this library noted, by the schema that holds it and the keyword.
    let mut noted: HashMap<(NodeId, &str), Reference> = HashMap::new();
    let mut settled = HashSet::new();
    let mut walked = 0;
    while let Some(&(document, uri)) = documents.get(walked) {
        walked += 1;
        let at = registry.resolver(referencing::uri::from_str(uri).unwrap());
        for found in references_in(document, at) {
            let theirs = found_by_referencing(&registry, &found.resolver, &missing, found.text);
            for reference in &builder.references[noted.len()..] {
                noted.insert((reference.node, reference.keyword.name()), *reference);
            }
            let node = builder.known(Side::A, found.holder);
            let noted = node.and_then(|node| noted.get(&(node, found.keyword)));
            let Some(&reference) = noted else {
                let Found { keyword, text, .. } = found;
                let difference = format!("{keyword} to {text} in {uri}: not seen by this library");
                comparison.differences.push(difference);
                continue;
            };
            settled.insert((reference.node, found.keyword));
            if !comparison.settle(&mut builder, reference, theirs) {
                return Ok(comparison);
            }
        }
        for (uri, _) in meta_schemas::SOURCES {
            let document = meta_schemas::document(uri).expect("the table has the URI");
            let reached = builder.known(Side::A, document).is_some();
            if reached && documents.iter().all(|(_, known)| *known != uri) {
                documents.push((document, uri));
            }
        }
    }

    // Then the references that only this library has, in what the draft takes for no schema.
    let mut next = 0;
    while let Some(&reference) = builder.references.get(next) {
        next += 1;
        if settled.contains(&(reference.node, reference.keyword.name())) {
            continue;
        }
        let node = &builder.nodes[reference.node.index()];
        let Some(resolver) = resolver(&builder, &registry, node.resource) else {
            continue;
        };
        let theirs = found_by_referencing(&registry, &resolver, &missing, reference.reference);
        comparison.placed_by_the_library += 1;
        if !comparison.settle(&mut builder, reference, theirs) {
            break;
        }
    }
    Ok(comparison)
}

#[test]
#[ignore = "needs the corpus in benchmark/, which `make corpus` downloads"]
fn referencing_finds_the_same_targets_in_the_corpus() {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmark");
    let cases = corpus_cases();
    assert!(cases.len() > 10_000, "{} cases", cases.len());
    let mut total = Comparison::default();
    let mut refused = BTreeMap::new();
    for case in &cases {
        for (key, schema) in schemas_of(case) {
            // The schema `a` of `rb-testset/s87.json` is `rb-testset/s87.json#/a`.
            let name = format!("{}#/{key}", case.strip_prefix(&corpus).unwrap().display());
            match compared(&schema) {
                Ok(mut comparison) => {
                    for difference in &mut comparison.differences {
                        *difference = format!("{name}: {difference}");
                    }
                    total.add(comparison);
                }
                Err(error) => {
                    refused.insert(name, error);
                }
            }
        }
    }
    println!(
        "{} schemas, {} references with the same target, {} of them placed by this library",
        2 * cases.len(),
        total.same,
        total.placed_by_the_library
    );
    assert_eq!(refused, BTreeMap::new());
    assert_eq!(total.differences, Vec::<String>::new());
    assert_eq!(total.unresolved, 0);
    assert!(total.same > 100_000, "{} references", total.same);
}

// Schemas made at random. They are dense in what the corpus has little of: resources inside
// resources, relative references, anchors, and names that need an escape.

/// Names of properties and definitions. Some need an escape in a JSON Pointer, some in a URI.
const NAMES: [&str; 8] = ["a", "b", "c/d", "e~f", "g h", "i%j", "k\u{f6}", ""];
const ANCHORS: [&str; 3] = ["x", "y", "z"];
/// What an `$id` may say. A relative one resolves against the `$id` around it.
const IDS: [&str; 12] = [
    "https://example.com/a.json",
    "https://example.com/dir/",
    "https://example.com/dir/b.json",
    "HTTPS://EXAMPLE.COM/%7Ec.json",
    "https://example.com/d.json#",
    "e.json",
    "dir/f.json",
    "./g.json",
    "../h.json",
    "/i.json",
    "//other.example/j.json",
    "urn:example:k",
];
const ROOT_ID: &str = "https://example.com/schemas/root.json";
const META_SCHEMA: &str = "https://json-schema.org/draft/2020-12/schema";
/// Places where the draft puts no schema. A reference may still point into them.
const ELSEWHERE: [&str; 2] = ["x-data", "dependencies"];

/// A schema that the generator made.
struct Place {
    /// The tokens that lead to it from the root of the document.
    absolute: Vec<String>,
    /// The resource it is in, and the tokens that lead to it from there.
    resource: usize,
    relative: Vec<String>,
    /// Whether it is an object, which can hold a reference.
    object: bool,
}

struct Generator {
    random: Random,
    places: Vec<Place>,
    /// What the `$id` of each resource says, if it has one. The first resource is the root.
    ids: Vec<Option<&'static str>>,
    unused_ids: Vec<&'static str>,
    /// The anchors that each resource has, since a name may be used once in a resource.
    anchors: Vec<Vec<&'static str>>,
}

fn absolute(id: &str) -> bool {
    id.contains(':')
}

impl Generator {
    fn schema(seed: u64) -> Value {
        let mut generator = Self {
            random: Random(seed),
            places: Vec::new(),
            ids: vec![None],
            unused_ids: IDS.to_vec(),
            anchors: vec![Vec::new()],
        };
        let mut root = generator.subschema(0, 0, Vec::new(), Vec::new(), true);
        if generator.random.chance(50) {
            root["$id"] = json!(ROOT_ID);
            generator.ids[0] = Some(ROOT_ID);
        }
        for place in 0..generator.places.len() {
            if generator.places[place].object && generator.random.chance(60) {
                let keyword = if generator.random.chance(12) {
                    "$dynamicRef"
                } else {
                    "$ref"
                };
                let reference = generator.reference(place);
                let mut target = &mut root;
                for token in &generator.places[place].absolute {
                    target = match target {
                        Value::Array(items) => &mut items[token.parse::<usize>().unwrap()],
                        other => &mut other[token.as_str()],
                    };
                }
                target[keyword] = json!(reference);
            }
        }
        root
    }

    /// A schema at `absolute`, with what is below it. `named` says whether the draft puts a
    /// schema there, so that its `$id` and its anchors count.
    fn subschema(
        &mut self,
        depth: usize,
        mut resource: usize,
        absolute: Vec<String>,
        mut relative: Vec<String>,
        named: bool,
    ) -> Value {
        if depth > 0 && self.random.chance(8) {
            self.places.push(Place {
                absolute,
                resource,
                relative,
                object: false,
            });
            return json!(self.random.chance(50));
        }
        let mut schema = Map::new();
        let mut leaf = depth == 4;
        if named && depth > 0 && !self.unused_ids.is_empty() && self.random.chance(22) {
            let id = self
                .unused_ids
                .swap_remove(self.random.below(self.unused_ids.len()));
            schema.insert("$id".to_owned(), json!(id));
            self.ids.push(Some(id));
            self.anchors.push(Vec::new());
            (resource, relative) = (self.ids.len() - 1, Vec::new());
            // Nothing relative resolves against a URI without a hierarchy.
            leaf |= id.starts_with("urn:");
        }
        self.places.push(Place {
            absolute: absolute.clone(),
            resource,
            relative: relative.clone(),
            object: true,
        });
        for keyword in ["$anchor", "$dynamicAnchor"] {
            if self.random.chance(12) {
                let name = self.random.pick(&ANCHORS);
                // Where the draft puts no schema an anchor names nothing, however often.
                if !named || !self.anchors[resource].contains(&name) {
                    schema.insert(keyword.to_owned(), json!(name));
                    if named {
                        self.anchors[resource].push(name);
                    }
                }
            }
        }
        if self.random.chance(10) {
            // Data that looks like a schema is none.
            schema.insert("enum".to_owned(), json!([1, {"$anchor": "x"}]));
        }
        let below = |tokens: &[&str], path: &[String]| {
            let mut path = path.to_vec();
            path.extend(tokens.iter().map(|token| (*token).to_owned()));
            path
        };
        let children = if leaf { 0 } else { self.random.below(4) };
        for _ in 0..children {
            match self.random.below(10) {
                0..=2 => {
                    let keyword = self.random.pick(&ONE);
                    if !schema.contains_key(keyword) {
                        let child = self.subschema(
                            depth + 1,
                            resource,
                            below(&[keyword], &absolute),
                            below(&[keyword], &relative),
                            named,
                        );
                        schema.insert(keyword.to_owned(), child);
                    }
                }
                3..=4 => {
                    let keyword = self.random.pick(&LISTED);
                    if !schema.contains_key(keyword) {
                        let children: Vec<Value> = (0..1 + self.random.below(2))
                            .map(|position| {
                                let position = position.to_string();
                                self.subschema(
                                    depth + 1,
                                    resource,
                                    below(&[keyword, &position], &absolute),
                                    below(&[keyword, &position], &relative),
                                    named,
                                )
                            })
                            .collect();
                        schema.insert(keyword.to_owned(), json!(children));
                    }
                }
                choice => {
                    let (keyword, named) = if choice == 9 {
                        (self.random.pick(&ELSEWHERE), false)
                    } else {
                        (self.random.pick(&NAMED), named)
                    };
                    let name = self.random.pick(&NAMES);
                    let known = schema.get(keyword).and_then(|names| names.get(name));
                    if known.is_none() {
                        let child = self.subschema(
                            depth + 1,
                            resource,
                            below(&[keyword, name], &absolute),
                            below(&[keyword, name], &relative),
                            named,
                        );
                        let names = schema.entry(keyword).or_insert_with(|| json!({}));
                        names[name] = child;
                    }
                }
            }
        }
        Value::Object(schema)
    }

    /// A reference to write at a place. Many lead to a schema that the generator made, the
    /// others are pieces put together blindly: what counts is that both resolve them alike.
    fn reference(&mut self, from: usize) -> String {
        let own = self.places[from].resource;
        // A relative reference has no meaning under a URI without a hierarchy.
        let opaque = self.ids[own].is_some_and(|id| id.starts_with("urn:"));
        let id = |random: &mut Random| loop {
            let id = random.pick(&IDS);
            if !opaque || absolute(id) {
                return id.strip_suffix('#').unwrap_or(id);
            }
        };
        match self.random.below(20) {
            0..=9 => {
                let to = self.random.below(self.places.len());
                let (resource, tokens) = (self.places[to].resource, &self.places[to].relative);
                let mut reference = String::new();
                if resource != own {
                    let id = self.ids[resource].unwrap_or("");
                    if opaque && !absolute(id) {
                        return "#".to_owned();
                    }
                    reference.push_str(id.strip_suffix('#').unwrap_or(id));
                }
                if tokens.is_empty() && !reference.is_empty() && self.random.chance(50) {
                    return reference;
                }
                reference.push('#');
                // Without a URI before it, a fragment is often written without encoding.
                let encoded = !reference.starts_with('#') || self.random.chance(50);
                for token in tokens {
                    if encoded {
                        push_token(&mut reference, token);
                    } else {
                        reference.push('/');
                        reference.push_str(&token.replace('~', "~0").replace('/', "~1"));
                    }
                }
                reference
            }
            10..=12 => {
                let resource = if self.random.chance(50) {
                    ""
                } else {
                    id(&mut self.random)
                };
                format!("{resource}#{}", self.random.pick(&ANCHORS))
            }
            13..=14 => {
                let mut reference = format!("{}#", id(&mut self.random));
                for _ in 0..self.random.below(3) {
                    let token = self
                        .random
                        .pick(&["$defs", "properties", "items", "a", "b", "0"]);
                    push_token(&mut reference, token);
                }
                reference
            }
            15..=16 => {
                let mut reference = "#".to_owned();
                for _ in 0..1 + self.random.below(3) {
                    let tokens = [
                        "$defs",
                        "properties",
                        "not",
                        "allOf",
                        "x-data",
                        "a",
                        "c/d",
                        "1",
                    ];
                    push_token(&mut reference, self.random.pick(&tokens));
                }
                reference
            }
            17 => {
                let fragment = self
                    .random
                    .pick(&["", "#", "#meta", "#/properties/definitions"]);
                format!("{META_SCHEMA}{fragment}")
            }
            18 => self.random.pick(&["", "#"]).to_owned(),
            _ if opaque => "https://example.com/missing#/a".to_owned(),
            _ => self
                .random
                .pick(&["missing.json", "https://example.com/missing#/a"])
                .to_owned(),
        }
    }
}

#[test]
fn referencing_finds_the_same_targets_in_random_schemas() {
    const SCHEMAS: u64 = 3_000;
    let mut total = Comparison::default();
    let mut refused = Vec::new();
    for seed in 0..SCHEMAS {
        let schema = Generator::schema(seed);
        match compared(&schema) {
            Ok(mut comparison) => {
                for difference in &mut comparison.differences {
                    *difference = format!("seed {seed}: {difference} in {schema}");
                }
                total.add(comparison);
            }
            Err(error) => refused.push(format!("seed {seed}: {error}")),
        }
    }
    for difference in total.differences.iter().take(5) {
        println!("{difference}\n");
    }
    assert_eq!(total.differences.len(), 0);
    println!(
        "{SCHEMAS} schemas, {} refused, and references: {} the same ({} by a URI, {} by an anchor), {} unresolved, {} of them placed by this library",
        refused.len(),
        total.same,
        total.same_by_uri,
        total.same_by_anchor,
        total.unresolved,
        total.placed_by_the_library,
    );
    assert_eq!(refused, Vec::<String>::new());
    // Enough of every kind, so that the agreement means something.
    assert!(total.same > 10_000, "{}", total.same);
    assert!(total.same_by_uri > 1_000, "{}", total.same_by_uri);
    assert!(total.same_by_anchor > 100, "{}", total.same_by_anchor);
    assert!(total.unresolved > 1_000, "{}", total.unresolved);
}
