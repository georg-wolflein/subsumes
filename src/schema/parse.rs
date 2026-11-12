//! The first step of loading: a schema document as nodes, with its references still open.

use std::collections::{HashMap, VecDeque};

use referencing::UriRef;
use serde_json::{Map, Number, Value};

use super::{Keywords, Node, NodeId, Origin, Part, Schema, Type, Types, location, push_token};
use crate::{Error, Side};

const DRAFT_2020_12: &str = "https://json-schema.org/draft/2020-12/schema";

/// A and B as nodes, with their references not yet resolved.
#[derive(Debug)]
pub(crate) struct Unlinked<'a> {
    pub(super) builder: Builder<'a>,
    pub(super) a: NodeId,
    pub(super) b: NodeId,
}

impl Unlinked<'_> {
    /// Whether one of the two schemas has a reference to resolve. One that has none needs
    /// no [`Scope`](super::link::Scope).
    pub(crate) fn has_references(&self, side: Side) -> bool {
        let nodes = &self.builder.nodes;
        let mut references = self.builder.references.iter();
        references.any(|reference| nodes[reference.node.index()].side == side)
    }
}

/// Parses every subschema of A and of B.
///
/// # Errors
///
/// When a root is no schema, when a schema declares another dialect, or when a keyword has a
/// value that the draft does not allow, wherever in the document it stands.
pub(crate) fn parse<'a>(a: &'a Value, b: &'a Value) -> Result<Unlinked<'a>, Error> {
    let mut builder = Builder::default();
    let a = builder.tree(Side::A, a, Origin::Root)?;
    let b = builder.tree(Side::B, b, Origin::Root)?;
    Ok(Unlinked { builder, a, b })
}

/// The nodes parsed so far, and what is left to do about them.
#[derive(Debug, Default)]
pub(super) struct Builder<'a> {
    pub nodes: Vec<Node<'a>>,
    /// The JSON value of each node, by node id.
    pub values: Vec<&'a Value>,
    /// The nodes of A and of B, by the address of their JSON value.
    known: [HashMap<usize, NodeId>; 2],
    /// Every `$ref` and `$dynamicRef` met, in the order of the nodes.
    pub references: Vec<Reference<'a>>,
}

/// A `$ref` or `$dynamicRef` as written.
#[derive(Debug, Clone, Copy)]
pub(super) struct Reference<'a> {
    /// The node that has the keyword.
    pub node: NodeId,
    pub keyword: ReferenceKeyword,
    pub reference: &'a str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ReferenceKeyword {
    Ref,
    DynamicRef,
}

impl ReferenceKeyword {
    pub fn name(self) -> &'static str {
        match self {
            Self::Ref => "$ref",
            Self::DynamicRef => "$dynamicRef",
        }
    }
}

/// A value waiting to be parsed. Its node id follows from its place in the queue.
struct Entry<'a> {
    value: &'a Value,
    origin: Origin<'a>,
    /// The resource of the parent; `None` for the first entry of a tree.
    resource: Option<NodeId>,
}

/// What is wrong with the value of a keyword.
enum Problem<'a> {
    /// The draft does not allow the value.
    Shape(&'static str),
    /// `$schema` names another dialect.
    Dialect(&'a str),
}

impl From<&'static str> for Problem<'_> {
    fn from(message: &'static str) -> Self {
        Self::Shape(message)
    }
}

impl<'a> Builder<'a> {
    /// The node of a JSON value, if the value was parsed as a schema of this side.
    pub fn known(&self, side: Side, value: &Value) -> Option<NodeId> {
        self.known[index(side)].get(&address(value)).copied()
    }

    /// Parses `root` and every subschema below it, breadth first, and returns the node of
    /// `root`. Nothing recurses, so the depth of a document does not matter.
    pub fn tree(
        &mut self,
        side: Side,
        root: &'a Value,
        origin: Origin<'a>,
    ) -> Result<NodeId, Error> {
        let first = NodeId::new(self.nodes.len());
        self.known[index(side)].insert(address(root), first);
        let mut queue = VecDeque::from([Entry {
            value: root,
            origin,
            resource: None,
        }]);
        while let Some(entry) = queue.pop_front() {
            let id = NodeId::new(self.nodes.len());
            let mut resource = entry.resource.unwrap_or(id);
            let schema = match entry.value {
                Value::Bool(value) => Schema::Bool(*value),
                Value::Object(map) => {
                    if map.contains_key("$id") {
                        resource = id;
                    }
                    let known = &mut self.known[index(side)];
                    let references = &mut self.references;
                    let mut child = |keyword: &'a str, part: Part<'a>, value: &'a Value| {
                        // A reference may have led into this document before, and what was
                        // parsed then is not parsed again.
                        if let Some(&child) = known.get(&address(value)) {
                            return child;
                        }
                        // The entries still queued have the ids after this one, and a new
                        // child gets the id after theirs.
                        let child = NodeId::new(id.index() + 1 + queue.len());
                        known.insert(address(value), child);
                        queue.push_back(Entry {
                            value,
                            origin: Origin::Child {
                                parent: id,
                                keyword,
                                part,
                            },
                            resource: Some(resource),
                        });
                        child
                    };
                    let mut reference = |keyword, reference| {
                        references.push(Reference {
                            node: id,
                            keyword,
                            reference,
                        });
                    };
                    match keywords(map, &mut child, &mut reference) {
                        Ok(keywords) => Schema::Object(Box::new(keywords)),
                        Err((keyword, problem)) => {
                            return Err(self.error(side, &entry.origin, keyword, problem));
                        }
                    }
                }
                _ if matches!(entry.origin, Origin::Root) => {
                    return Err(Error::NotASchema { schema: side });
                }
                _ => {
                    return Err(Error::InvalidKeyword {
                        schema: side,
                        location: location(&self.nodes, &entry.origin),
                        message: "must be a schema: an object or a boolean".to_owned(),
                    });
                }
            };
            self.nodes.push(Node {
                side,
                origin: entry.origin,
                resource,
                schema,
            });
            self.values.push(entry.value);
        }
        Ok(first)
    }

    fn error(&self, side: Side, origin: &Origin, keyword: &str, problem: Problem) -> Error {
        let mut location = location(&self.nodes, origin);
        push_token(&mut location, keyword);
        match problem {
            Problem::Shape(message) => Error::InvalidKeyword {
                schema: side,
                location,
                message: message.to_owned(),
            },
            Problem::Dialect(dialect) => Error::UnsupportedDialect {
                schema: side,
                location,
                dialect: dialect.to_owned(),
            },
        }
    }
}

fn index(side: Side) -> usize {
    match side {
        Side::A => 0,
        Side::B => 1,
    }
}

/// What tells two JSON values of a document apart: where they are in memory.
fn address(value: &Value) -> usize {
    std::ptr::from_ref(value) as usize
}

/// Reads the keywords of a schema object. `child` is called for every subschema and returns
/// its node; `reference` is called for `$ref` and `$dynamicRef`. An error names the keyword.
fn keywords<'a>(
    map: &'a Map<String, Value>,
    child: &mut impl FnMut(&'a str, Part<'a>, &'a Value) -> NodeId,
    reference: &mut impl FnMut(ReferenceKeyword, &'a str),
) -> Result<Keywords<'a>, (&'a str, Problem<'a>)> {
    let mut keywords = Keywords::default();
    for (key, value) in map {
        keyword(key, value, &mut keywords, child, reference)
            .map_err(|problem| (key.as_str(), problem))?;
    }
    Ok(keywords)
}

/// Reads one keyword into `keywords`.
fn keyword<'a>(
    key: &'a str,
    value: &'a Value,
    keywords: &mut Keywords<'a>,
    child: &mut impl FnMut(&'a str, Part<'a>, &'a Value) -> NodeId,
    reference: &mut impl FnMut(ReferenceKeyword, &'a str),
) -> Result<(), Problem<'a>> {
    match key {
        "$schema" => {
            let dialect = string(value)?;
            if dialect.trim_end_matches('#') != DRAFT_2020_12 {
                return Err(Problem::Dialect(dialect));
            }
        }
        "$id" => {
            let id = uri_reference(value)?;
            if id
                .split_once('#')
                .is_some_and(|(_, fragment)| !fragment.is_empty())
            {
                return Err("must not have a fragment".into());
            }
        }
        "$anchor" => {
            anchor(value)?;
        }
        "$dynamicAnchor" => keywords.dynamic_anchor = Some(anchor(value)?),
        "$ref" => reference(ReferenceKeyword::Ref, reference_to(value)?),
        "$dynamicRef" => reference(ReferenceKeyword::DynamicRef, reference_to(value)?),

        // These hold schemas that apply nowhere by themselves. They are parsed like every
        // other subschema, so that a reference into them finds a node.
        "$defs" | "definitions" => {
            named(key, value, child)?;
        }
        "contentSchema" => {
            child(key, Part::Whole, value);
        }

        "allOf" => keywords.all_of = listed(key, value, child)?,
        "anyOf" => keywords.any_of = listed(key, value, child)?,
        "oneOf" => keywords.one_of = listed(key, value, child)?,
        "not" => keywords.not = Some(child(key, Part::Whole, value)),
        "if" => keywords.if_ = Some(child(key, Part::Whole, value)),
        "then" => keywords.then = Some(child(key, Part::Whole, value)),
        "else" => keywords.else_ = Some(child(key, Part::Whole, value)),
        "dependentSchemas" => keywords.dependent_schemas = named(key, value, child)?,

        "type" => keywords.types = Some(types(value)?),
        "enum" => keywords.enumeration = Some(value.as_array().ok_or("must be an array")?),
        "const" => keywords.constant = Some(value),

        "minimum" => keywords.minimum = Some(number(value)?),
        "maximum" => keywords.maximum = Some(number(value)?),
        "exclusiveMinimum" => keywords.exclusive_minimum = Some(number(value)?),
        "exclusiveMaximum" => keywords.exclusive_maximum = Some(number(value)?),
        "multipleOf" => {
            let divisor = number(value)?;
            if !divisor.as_f64().is_some_and(|divisor| divisor > 0.0) {
                return Err("must be greater than 0".into());
            }
            keywords.multiple_of = Some(divisor);
        }

        "minLength" => keywords.min_length = Some(count(value)?),
        "maxLength" => keywords.max_length = Some(count(value)?),
        "pattern" => keywords.pattern = Some(string(value)?),
        "format" => keywords.format = Some(string(value)?),

        "prefixItems" => keywords.prefix_items = listed(key, value, child)?,
        "items" => keywords.items = Some(child(key, Part::Whole, value)),
        "contains" => keywords.contains = Some(child(key, Part::Whole, value)),
        "minContains" => keywords.min_contains = Some(count(value)?),
        "maxContains" => keywords.max_contains = Some(count(value)?),
        "minItems" => keywords.min_items = Some(count(value)?),
        "maxItems" => keywords.max_items = Some(count(value)?),
        "uniqueItems" => keywords.unique_items = value.as_bool().ok_or("must be a boolean")?,
        "unevaluatedItems" => keywords.unevaluated_items = Some(child(key, Part::Whole, value)),

        "properties" => keywords.properties = named(key, value, child)?,
        "patternProperties" => keywords.pattern_properties = named(key, value, child)?,
        "additionalProperties" => {
            keywords.additional_properties = Some(child(key, Part::Whole, value));
        }
        "propertyNames" => keywords.property_names = Some(child(key, Part::Whole, value)),
        "required" => keywords.required = strings(value)?,
        "dependentRequired" => {
            const MESSAGE: &str =
                "must be an object whose values are arrays of strings without repetition";
            keywords.dependent_required = value
                .as_object()
                .ok_or(MESSAGE)?
                .iter()
                .map(|(name, names)| Ok((name.as_str(), strings(names)?)))
                .collect::<Result<_, &'static str>>()
                .map_err(|_| MESSAGE)?;
        }
        "minProperties" => keywords.min_properties = Some(count(value)?),
        "maxProperties" => keywords.max_properties = Some(count(value)?),
        "unevaluatedProperties" => {
            keywords.unevaluated_properties = Some(child(key, Part::Whole, value));
        }

        // A keyword that only annotates, or one that the draft does not define.
        _ => {}
    }
    Ok(())
}

fn string(value: &Value) -> Result<&str, &'static str> {
    value.as_str().ok_or("must be a string")
}

fn number(value: &Value) -> Result<&Number, &'static str> {
    value.as_number().ok_or("must be a number")
}

/// A non-negative integer. The draft counts `2.0` as an integer, and a count beyond what a
/// machine can hold stands for the largest one that it can.
fn count(value: &Value) -> Result<u64, &'static str> {
    const MESSAGE: &str = "must be a non-negative integer";
    let number = value.as_number().ok_or(MESSAGE)?;
    if let Some(count) = number.as_u64() {
        return Ok(count);
    }
    match number.as_f64() {
        // The cast saturates, which is the rounding wanted here.
        Some(count) if count >= 0.0 && count.fract() == 0.0 => Ok(count as u64),
        _ => Err(MESSAGE),
    }
}

const URI_REFERENCE: &str = "must be a URI reference";

fn uri_reference(value: &Value) -> Result<&str, &'static str> {
    let reference = value.as_str().ok_or(URI_REFERENCE)?;
    UriRef::parse(reference).map_err(|_| URI_REFERENCE)?;
    Ok(reference)
}

/// The value of `$ref` or `$dynamicRef`. Only the part that names a document has to be a URI
/// reference; whether the fragment leads anywhere is for the resolution to say.
fn reference_to(value: &Value) -> Result<&str, &'static str> {
    let reference = value.as_str().ok_or(URI_REFERENCE)?;
    if !reference.starts_with('#') {
        let document = reference
            .rsplit_once('#')
            .map_or(reference, |(document, _)| document);
        UriRef::parse(document).map_err(|_| URI_REFERENCE)?;
    }
    Ok(reference)
}

fn anchor(value: &Value) -> Result<&str, &'static str> {
    const MESSAGE: &str =
        "must start with a letter or `_`, followed by letters, digits, `_`, `-` and `.`";
    let name = value.as_str().ok_or(MESSAGE)?;
    let mut bytes = name.bytes();
    let starts = bytes
        .next()
        .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_');
    let continues =
        bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.'));
    if starts && continues {
        Ok(name)
    } else {
        Err(MESSAGE)
    }
}

fn types(value: &Value) -> Result<Types, &'static str> {
    const MESSAGE: &str =
        "must be one of the seven type names, or a non-empty array of them without repetition";
    let mut types = Types::default();
    let mut add = |name: &Value| match name.as_str().and_then(Type::named) {
        Some(kind) if types.insert(kind) => Ok(()),
        _ => Err(MESSAGE),
    };
    match value {
        Value::String(_) => add(value)?,
        Value::Array(names) if !names.is_empty() => names.iter().try_for_each(add)?,
        _ => return Err(MESSAGE),
    }
    Ok(types)
}

/// An array of strings without repetition.
fn strings(value: &Value) -> Result<Vec<&str>, &'static str> {
    const MESSAGE: &str = "must be an array of strings without repetition";
    let mut names = Vec::new();
    for name in value.as_array().ok_or(MESSAGE)? {
        let name = name.as_str().ok_or(MESSAGE)?;
        if names.contains(&name) {
            return Err(MESSAGE);
        }
        names.push(name);
    }
    Ok(names)
}

/// The subschemas of a keyword that holds a non-empty array of them.
fn listed<'a>(
    keyword: &'a str,
    value: &'a Value,
    child: &mut impl FnMut(&'a str, Part<'a>, &'a Value) -> NodeId,
) -> Result<Vec<NodeId>, &'static str> {
    let schemas = value.as_array().filter(|schemas| !schemas.is_empty());
    Ok(schemas
        .ok_or("must be a non-empty array of schemas")?
        .iter()
        .enumerate()
        .map(|(position, schema)| child(keyword, Part::Index(position), schema))
        .collect())
}

/// The subschemas of a keyword that holds them under names.
fn named<'a>(
    keyword: &'a str,
    value: &'a Value,
    child: &mut impl FnMut(&'a str, Part<'a>, &'a Value) -> NodeId,
) -> Result<Vec<(&'a str, NodeId)>, &'static str> {
    let schemas = value.as_object().ok_or("must be an object of schemas")?;
    Ok(schemas
        .iter()
        .map(|(name, schema)| (name.as_str(), child(keyword, Part::Name(name), schema)))
        .collect())
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    /// The root of A when it is parsed next to `true`.
    fn parsed(schema: &Value) -> Result<Unlinked<'_>, Error> {
        parse(schema, &Value::Bool(true))
    }

    fn object<'a, 'b>(unlinked: &'b Unlinked<'a>, node: NodeId) -> &'b Keywords<'a> {
        match &unlinked.builder.nodes[node.index()].schema {
            Schema::Object(keywords) => keywords,
            Schema::Bool(_) => panic!("the node is a boolean schema"),
        }
    }

    fn location_of(unlinked: &Unlinked, node: NodeId) -> String {
        let nodes = &unlinked.builder.nodes;
        location(nodes, &nodes[node.index()].origin)
    }

    fn invalid(schema: Value) -> (String, String) {
        match parsed(&schema) {
            Err(Error::InvalidKeyword {
                schema: Side::A,
                location,
                message,
            }) => (location, message),
            other => panic!("{schema} gave {other:?}"),
        }
    }

    #[test]
    fn every_keyword_gets_its_typed_field() {
        let schema = json!({
            "type": ["integer", "null"],
            "enum": [1, null],
            "const": 1,
            "minimum": 0,
            "maximum": 10.5,
            "exclusiveMinimum": -1,
            "exclusiveMaximum": 11,
            "multipleOf": 0.5,
            "minLength": 1,
            "maxLength": 2,
            "pattern": "^a",
            "format": "date",
            "minItems": 3,
            "maxItems": 4,
            "minContains": 5,
            "maxContains": 6,
            "uniqueItems": true,
            "minProperties": 7,
            "maxProperties": 8,
            "required": ["a", "b"],
            "dependentRequired": {"a": ["b"]},
            "$dynamicAnchor": "node",
        });
        let unlinked = parsed(&schema).unwrap();
        let keywords = object(&unlinked, unlinked.a);
        let types = keywords.types.unwrap();
        assert!(types.contains(Type::Integer) && types.contains(Type::Null));
        assert!(!types.contains(Type::Number));
        assert_eq!(
            keywords.enumeration,
            Some([json!(1), json!(null)].as_slice())
        );
        assert_eq!(keywords.constant, Some(&json!(1)));
        assert_eq!(keywords.minimum.unwrap().as_i64(), Some(0));
        assert_eq!(keywords.maximum.unwrap().as_f64(), Some(10.5));
        assert_eq!(keywords.exclusive_minimum.unwrap().as_i64(), Some(-1));
        assert_eq!(keywords.exclusive_maximum.unwrap().as_i64(), Some(11));
        assert_eq!(keywords.multiple_of.unwrap().as_f64(), Some(0.5));
        assert_eq!(
            (keywords.min_length, keywords.max_length),
            (Some(1), Some(2))
        );
        assert_eq!(
            (keywords.pattern, keywords.format),
            (Some("^a"), Some("date"))
        );
        assert_eq!((keywords.min_items, keywords.max_items), (Some(3), Some(4)));
        assert_eq!(
            (keywords.min_contains, keywords.max_contains),
            (Some(5), Some(6))
        );
        assert!(keywords.unique_items);
        assert_eq!(
            (keywords.min_properties, keywords.max_properties),
            (Some(7), Some(8))
        );
        assert_eq!(keywords.required, ["a", "b"]);
        assert_eq!(keywords.dependent_required, [("a", vec!["b"])]);
        assert_eq!(keywords.dynamic_anchor, Some("node"));
    }

    #[test]
    fn every_subschema_is_a_node_with_its_location() {
        let schema = json!({
            "allOf": [true, {"not": false}],
            "anyOf": [{}],
            "oneOf": [{}],
            "if": {},
            "then": {},
            "else": {},
            "dependentSchemas": {"a": {}},
            "prefixItems": [{}],
            "items": {},
            "contains": {},
            "unevaluatedItems": {},
            "properties": {"a/b": {"properties": {"c~d": {}}}},
            "patternProperties": {"^x ": {}},
            "additionalProperties": {},
            "propertyNames": {},
            "unevaluatedProperties": {},
        });
        let unlinked = parsed(&schema).unwrap();
        let root = object(&unlinked, unlinked.a);
        let at = |node| location_of(&unlinked, node);
        assert_eq!(at(unlinked.a), "#");
        assert_eq!(at(root.all_of[0]), "#/allOf/0");
        assert_eq!(
            at(object(&unlinked, root.all_of[1]).not.unwrap()),
            "#/allOf/1/not"
        );
        assert_eq!(at(root.any_of[0]), "#/anyOf/0");
        assert_eq!(at(root.one_of[0]), "#/oneOf/0");
        assert_eq!(at(root.if_.unwrap()), "#/if");
        assert_eq!(at(root.then.unwrap()), "#/then");
        assert_eq!(at(root.else_.unwrap()), "#/else");
        assert_eq!(root.dependent_schemas[0].0, "a");
        assert_eq!(at(root.dependent_schemas[0].1), "#/dependentSchemas/a");
        assert_eq!(at(root.prefix_items[0]), "#/prefixItems/0");
        assert_eq!(at(root.items.unwrap()), "#/items");
        assert_eq!(at(root.contains.unwrap()), "#/contains");
        assert_eq!(at(root.unevaluated_items.unwrap()), "#/unevaluatedItems");
        let (name, property) = root.properties[0];
        assert_eq!(
            (name, at(property)),
            ("a/b", "#/properties/a~1b".to_owned())
        );
        let nested = object(&unlinked, property).properties[0].1;
        assert_eq!(at(nested), "#/properties/a~1b/properties/c~0d");
        assert_eq!(
            at(root.pattern_properties[0].1),
            "#/patternProperties/%5Ex%20"
        );
        assert_eq!(
            at(root.additional_properties.unwrap()),
            "#/additionalProperties"
        );
        assert_eq!(at(root.property_names.unwrap()), "#/propertyNames");
        assert_eq!(
            at(root.unevaluated_properties.unwrap()),
            "#/unevaluatedProperties"
        );

        let nodes = &unlinked.builder.nodes;
        assert!(matches!(
            nodes[root.all_of[0].index()].schema,
            Schema::Bool(true)
        ));
        // A and its 19 subschemas, then B.
        assert_eq!(unlinked.b.index(), 20);
        assert!(nodes.iter().take(20).all(|node| node.side == Side::A));
        assert_eq!(nodes[20].side, Side::B);
    }

    #[test]
    fn definitions_are_parsed_although_nothing_applies_them() {
        let schema = json!({
            "$defs": {"a": {"minLength": 1}},
            "definitions": {"b": false},
            "contentSchema": {"type": "string"},
        });
        let unlinked = parsed(&schema).unwrap();
        let locations: Vec<String> = (0..3)
            .map(|index| location_of(&unlinked, NodeId::new(index + 1)))
            .collect();
        assert_eq!(
            locations,
            ["#/$defs/a", "#/contentSchema", "#/definitions/b"]
        );

        let unused = json!({"$defs": {"unused": {"minLength": "1"}}});
        assert_eq!(invalid(unused).0, "#/$defs/unused/minLength");
    }

    #[test]
    fn a_keyword_of_the_wrong_shape_is_an_error_at_its_location() {
        let cases = [
            (json!({"type": "text"}), "#/type"),
            (json!({"type": []}), "#/type"),
            (json!({"type": ["array", "array"]}), "#/type"),
            (json!({"enum": {}}), "#/enum"),
            (json!({"minimum": "0"}), "#/minimum"),
            (json!({"multipleOf": 0}), "#/multipleOf"),
            (json!({"multipleOf": -2}), "#/multipleOf"),
            (json!({"minLength": -1}), "#/minLength"),
            (json!({"maxItems": 1.5}), "#/maxItems"),
            (json!({"pattern": 1}), "#/pattern"),
            (json!({"format": []}), "#/format"),
            (json!({"uniqueItems": "yes"}), "#/uniqueItems"),
            (json!({"required": ["a", "a"]}), "#/required"),
            (json!({"required": "a"}), "#/required"),
            (
                json!({"dependentRequired": {"a": "b"}}),
                "#/dependentRequired",
            ),
            (json!({"allOf": []}), "#/allOf"),
            (json!({"oneOf": {}}), "#/oneOf"),
            (json!({"prefixItems": []}), "#/prefixItems"),
            (json!({"properties": []}), "#/properties"),
            (json!({"$defs": 1}), "#/$defs"),
            (json!({"$ref": 1}), "#/$ref"),
            (json!({"$ref": "ht tp://example.com"}), "#/$ref"),
            (json!({"$id": "http://example.com/a#b"}), "#/$id"),
            (json!({"$id": "a b"}), "#/$id"),
            (json!({"$anchor": "1a"}), "#/$anchor"),
            (json!({"$dynamicAnchor": ""}), "#/$dynamicAnchor"),
            (json!({"$schema": 2020}), "#/$schema"),
            (json!({"items": 1}), "#/items"),
            (
                json!({"properties": {"a": {"not": []}}}),
                "#/properties/a/not",
            ),
            (json!({"allOf": [{}, {"if": null}]}), "#/allOf/1/if"),
        ];
        for (schema, location) in cases {
            assert_eq!(invalid(schema.clone()).0, location, "{schema}");
        }
        assert_eq!(
            invalid(json!({"minLength": "3"})),
            (
                "#/minLength".to_owned(),
                "must be a non-negative integer".to_owned()
            )
        );
    }

    #[test]
    fn a_count_may_be_written_as_a_float() {
        let schema = json!({"minLength": 2.0, "maxLength": 1e300});
        let unlinked = parsed(&schema).unwrap();
        let keywords = object(&unlinked, unlinked.a);
        assert_eq!(
            (keywords.min_length, keywords.max_length),
            (Some(2), Some(u64::MAX))
        );
    }

    #[test]
    fn annotations_and_unknown_keywords_are_not_read() {
        let schema = json!({
            "title": 1,
            "deprecated": "use another",
            "examples": {},
            "$comment": [],
            "dependencies": {"a": 1},
            "x-custom": {"$ref": 1, "type": "text"},
            "enum": [{"$ref": 1, "type": "text"}],
            "const": {"minLength": "1"},
            "fragment": {"$ref": "#/a b"},
        });
        let unlinked = parsed(&schema).unwrap();
        assert_eq!(unlinked.b.index(), 1);
        assert!(unlinked.builder.references.is_empty());
    }

    #[test]
    fn only_draft_2020_12_is_accepted_wherever_a_dialect_is_declared() {
        let draft_2020_12 = json!({"$defs": {"a": {"$schema": format!("{DRAFT_2020_12}#")}}});
        assert!(parsed(&draft_2020_12).is_ok());

        let draft_07 = "http://json-schema.org/draft-07/schema#";
        let schema = json!({"$defs": {"a": {"$id": "a.json", "$schema": draft_07}}});
        assert_eq!(
            parsed(&schema).unwrap_err(),
            Error::UnsupportedDialect {
                schema: Side::A,
                location: "#/$defs/a/$schema".to_owned(),
                dialect: draft_07.to_owned(),
            }
        );
    }

    #[test]
    fn a_root_that_is_no_schema_is_named_by_its_side() {
        let error = parse(&json!(true), &json!([])).unwrap_err();
        assert_eq!(error, Error::NotASchema { schema: Side::B });
    }

    #[test]
    fn a_node_names_the_resource_it_belongs_to() {
        let schema = json!({
            "properties": {
                "plain": {"items": {}},
                "named": {"$id": "https://example.com/named", "items": {"not": {}}},
            },
        });
        let unlinked = parsed(&schema).unwrap();
        let root = object(&unlinked, unlinked.a);
        let resource_of = |node: NodeId| unlinked.builder.nodes[node.index()].resource;
        let named = root.properties[0].1;
        let plain = root.properties[1].1;
        assert_eq!(location_of(&unlinked, named), "#/properties/named");
        assert_eq!(resource_of(unlinked.a), unlinked.a);
        assert_eq!(resource_of(plain), unlinked.a);
        assert_eq!(
            resource_of(object(&unlinked, plain).items.unwrap()),
            unlinked.a
        );
        assert_eq!(resource_of(named), named);
        let items = object(&unlinked, named).items.unwrap();
        assert_eq!(resource_of(items), named);
        assert_eq!(resource_of(object(&unlinked, items).not.unwrap()), named);
        // B is a tree of its own.
        assert_eq!(resource_of(unlinked.b), unlinked.b);
    }

    #[test]
    fn references_are_noted_in_the_order_of_the_nodes() {
        let schema = json!({
            "$ref": "#/$defs/a",
            "$defs": {"a": {"$dynamicRef": "#node"}},
        });
        let unlinked = parsed(&schema).unwrap();
        let noted: Vec<_> = unlinked
            .builder
            .references
            .iter()
            .map(|reference| {
                (
                    reference.node.index(),
                    reference.keyword.name(),
                    reference.reference,
                )
            })
            .collect();
        assert_eq!(
            noted,
            [(0, "$ref", "#/$defs/a"), (1, "$dynamicRef", "#node")]
        );
    }

    #[test]
    fn a_deep_document_does_not_overflow_the_stack() {
        let mut schema = json!({});
        for _ in 0..100_000 {
            schema = Value::Object(Map::from_iter([("not".to_owned(), schema)]));
        }
        let nodes = parsed(&schema).unwrap().builder.nodes.len();
        assert_eq!(nodes, 100_002);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget(schema);
    }
}
