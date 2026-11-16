//! The schema graph: what the load stage makes of the two schemas of a check.
//!
//! Every subschema is a [`Node`]: a boolean, or the keywords of an object, with one typed
//! field for each keyword that says what a schema accepts. A subschema and the target of a
//! reference are [`NodeId`]s, so a recursive schema is a cycle in the graph.
//!
//! Loading has two steps. [`parse`] reads A and B from top to bottom. [`Unlinked::link`] then
//! resolves every reference. A schema stands on its own: a reference leads to a place inside
//! it or to a meta-schema of the draft, which the library carries.
//!
//! [`Unlinked::link`]: parse::Unlinked::link

// Only the inspection reads the graph until the lowering stage exists, and it does not need
// everything.
#![cfg_attr(not(test), expect(dead_code))]
#![cfg_attr(test, allow(dead_code))]

mod inspect;
mod link;
#[cfg(test)]
mod oracle;
mod parse;

use std::fmt::Write;

use serde_json::{Number, Value};

use crate::Side;

pub(crate) use parse::parse;

/// The two schemas of a check and every meta-schema they reference, as nodes.
#[derive(Debug)]
pub(crate) struct Graph<'a> {
    nodes: Vec<Node<'a>>,
    /// The root of A.
    pub a: NodeId,
    /// The root of B.
    pub b: NodeId,
}

impl<'a> Graph<'a> {
    pub fn node(&self, id: NodeId) -> &Node<'a> {
        &self.nodes[id.index()]
    }

    /// How many nodes the graph has.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Where a node is: a URI reference whose fragment is a JSON Pointer.
    pub fn location(&self, id: NodeId) -> String {
        location(&self.nodes, &self.node(id).origin)
    }

    /// Where a keyword of a node is.
    pub fn keyword_location(&self, id: NodeId, keyword: &str) -> String {
        let mut location = self.location(id);
        push_token(&mut location, keyword);
        location
    }
}

/// The id of a node of the graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct NodeId(u32);

impl NodeId {
    pub fn new(index: usize) -> Self {
        Self(u32::try_from(index).expect("a graph has fewer than 2^32 nodes"))
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// One subschema.
#[derive(Debug)]
pub(crate) struct Node<'a> {
    /// The schema that the node is part of. A meta-schema that both schemas reference has a
    /// node for each.
    pub side: Side,
    pub origin: Origin<'a>,
    /// The node that begins the resource of this one: the nearest node above it that has an
    /// `$id`, or else the root of its document. A node that begins a resource names itself.
    pub resource: NodeId,
    pub schema: Schema<'a>,
}

/// How a node was reached, which says where it is.
#[derive(Debug)]
pub(crate) enum Origin<'a> {
    /// The root of A or of B.
    Root,
    /// The target of a reference that is not a subschema of a node known before: the root of
    /// a meta-schema, or a value in a place where the draft puts no schema. The string is the
    /// location of the target.
    Reference(String),
    /// A subschema of `parent`: the value of `keyword`, or one of several values in it.
    Child {
        parent: NodeId,
        keyword: &'a str,
        part: Part<'a>,
    },
}

/// Which of the subschemas of a keyword a node is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Part<'a> {
    /// The keyword holds one schema, as `not` does.
    Whole,
    /// The schema under a name, as in `properties`.
    Name(&'a str),
    /// The schema at a position, as in `allOf`.
    Index(usize),
}

#[derive(Debug)]
pub(crate) enum Schema<'a> {
    Bool(bool),
    Object(Box<Keywords<'a>>),
}

/// The keywords of a schema object that say what it accepts.
///
/// A keyword that is absent is `None`, `false` or empty. Keywords that only annotate, such as
/// `title`, and keywords that the draft does not define are not read. `$id`, `$anchor` and
/// `$defs` are not here either: they only say where a reference can point, and every reference
/// is already resolved.
#[derive(Debug, Default)]
pub(crate) struct Keywords<'a> {
    /// The target of `$ref`.
    pub reference: Option<NodeId>,
    pub dynamic_reference: Option<DynamicReference<'a>>,
    /// The name of its `$dynamicAnchor`, if a reference can name the schema by it: not where
    /// the schema stands in a place where the draft puts none.
    pub dynamic_anchor: Option<&'a str>,

    pub all_of: Vec<NodeId>,
    pub any_of: Vec<NodeId>,
    pub one_of: Vec<NodeId>,
    pub not: Option<NodeId>,
    pub if_: Option<NodeId>,
    pub then: Option<NodeId>,
    pub else_: Option<NodeId>,
    pub dependent_schemas: Vec<(&'a str, NodeId)>,

    pub types: Option<Types>,
    pub enumeration: Option<&'a [Value]>,
    pub constant: Option<&'a Value>,

    pub minimum: Option<&'a Number>,
    pub maximum: Option<&'a Number>,
    pub exclusive_minimum: Option<&'a Number>,
    pub exclusive_maximum: Option<&'a Number>,
    pub multiple_of: Option<&'a Number>,

    pub min_length: Option<Count>,
    pub max_length: Option<Count>,
    pub pattern: Option<&'a str>,
    pub format: Option<&'a str>,

    pub prefix_items: Vec<NodeId>,
    pub items: Option<NodeId>,
    pub contains: Option<NodeId>,
    pub min_contains: Option<Count>,
    pub max_contains: Option<Count>,
    pub min_items: Option<Count>,
    pub max_items: Option<Count>,
    pub unique_items: bool,
    pub unevaluated_items: Option<NodeId>,

    pub properties: Vec<(&'a str, NodeId)>,
    pub pattern_properties: Vec<(&'a str, NodeId)>,
    pub additional_properties: Option<NodeId>,
    pub property_names: Option<NodeId>,
    pub required: Vec<&'a str>,
    pub dependent_required: Vec<(&'a str, Vec<&'a str>)>,
    pub min_properties: Option<Count>,
    pub max_properties: Option<Count>,
    pub unevaluated_properties: Option<NodeId>,
}

/// How many characters, items or properties a keyword such as `minItems` asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Count {
    Of(u64),
    /// Too large to be kept as the number that was written: more than a `u64` holds, as
    /// `1e30` is, or a float from 2^53 on, which does not hold every integer. Two such counts
    /// are not known to be equal, so nothing may be concluded from one.
    Beyond,
}

impl<'a> Keywords<'a> {
    /// Every subschema that a keyword applies, with the keyword and its place in it, in an
    /// order that depends on nothing but the keywords. The targets of `$ref` and `$dynamicRef`
    /// are not among them.
    pub fn subschemas(&self) -> Vec<(&'static str, Part<'a>, NodeId)> {
        let one = [
            ("not", self.not),
            ("if", self.if_),
            ("then", self.then),
            ("else", self.else_),
            ("items", self.items),
            ("contains", self.contains),
            ("unevaluatedItems", self.unevaluated_items),
            ("additionalProperties", self.additional_properties),
            ("propertyNames", self.property_names),
            ("unevaluatedProperties", self.unevaluated_properties),
        ];
        let listed = [
            ("allOf", &self.all_of),
            ("anyOf", &self.any_of),
            ("oneOf", &self.one_of),
            ("prefixItems", &self.prefix_items),
        ];
        let named = [
            ("properties", &self.properties),
            ("patternProperties", &self.pattern_properties),
            ("dependentSchemas", &self.dependent_schemas),
        ];
        let one = one
            .into_iter()
            .filter_map(|(keyword, schema)| Some((keyword, Part::Whole, schema?)));
        let listed = listed.into_iter().flat_map(|(keyword, schemas)| {
            let places = schemas.iter().enumerate();
            places.map(move |(position, schema)| (keyword, Part::Index(position), *schema))
        });
        let named = named.into_iter().flat_map(|(keyword, schemas)| {
            let places = schemas.iter();
            places.map(move |(name, schema)| (keyword, Part::Name(name), *schema))
        });
        one.chain(listed).chain(named).collect()
    }
}

/// A `$dynamicRef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct DynamicReference<'a> {
    /// The reference as written.
    pub reference: &'a str,
    /// What it resolves to before any dynamic scope is taken into account.
    pub target: NodeId,
    /// The dynamic anchor that it looks for in the dynamic scope: the name in its fragment,
    /// if that is the `$dynamicAnchor` of the target. Without one it is a `$ref`, as the
    /// draft has it.
    pub anchor: Option<&'a str>,
}

/// One of the seven names that `type` takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Type {
    Null,
    Boolean,
    Object,
    Array,
    Number,
    String,
    Integer,
}

impl Type {
    const ALL: [Self; 7] = [
        Self::Null,
        Self::Boolean,
        Self::Object,
        Self::Array,
        Self::Number,
        Self::String,
        Self::Integer,
    ];

    fn name(self) -> &'static str {
        match self {
            Self::Null => "null",
            Self::Boolean => "boolean",
            Self::Object => "object",
            Self::Array => "array",
            Self::Number => "number",
            Self::String => "string",
            Self::Integer => "integer",
        }
    }

    fn named(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|kind| kind.name() == name)
    }
}

/// A set of types: the value of `type`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Types(u8);

impl Types {
    pub fn contains(self, kind: Type) -> bool {
        self.0 & (1 << kind as u8) != 0
    }

    /// Adds a type; `false` if it was there already.
    fn insert(&mut self, kind: Type) -> bool {
        let added = !self.contains(kind);
        self.0 |= 1 << kind as u8;
        added
    }
}

/// The location of the node with this origin.
fn location(nodes: &[Node], origin: &Origin) -> String {
    let mut steps = Vec::new();
    let mut origin = origin;
    let mut location = loop {
        match origin {
            Origin::Root => break "#".to_owned(),
            Origin::Reference(uri) if uri.contains('#') => break uri.clone(),
            Origin::Reference(uri) => break format!("{uri}#"),
            Origin::Child {
                parent,
                keyword,
                part,
            } => {
                steps.push((*keyword, *part));
                origin = &nodes[parent.index()].origin;
            }
        }
    };
    for (keyword, part) in steps.into_iter().rev() {
        push_step(&mut location, keyword, part);
    }
    location
}

/// Appends the place of a subschema to the location of its parent.
fn push_step(location: &mut String, keyword: &str, part: Part) {
    push_token(location, keyword);
    match part {
        Part::Whole => {}
        Part::Name(name) => push_token(location, name),
        Part::Index(index) => write!(location, "/{index}").expect("a string takes any text"),
    }
}

/// Appends one token of a JSON Pointer, escaped for the pointer and for a URI fragment.
fn push_token(location: &mut String, token: &str) {
    location.push('/');
    for byte in token.bytes() {
        match byte {
            b'~' => location.push_str("~0"),
            b'/' => location.push_str("~1"),
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' => location.push(char::from(byte)),
            b'-' | b'.' | b'_' | b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b','
            | b';' | b'=' | b':' | b'@' | b'?' => location.push(char::from(byte)),
            _ => write!(location, "%{byte:02X}").expect("a string takes any text"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_token_is_escaped_for_the_pointer_and_for_the_fragment() {
        let mut location = "#".to_owned();
        push_token(&mut location, "$defs");
        push_token(&mut location, "a/b~c");
        push_token(&mut location, "x y#é");
        assert_eq!(location, "#/$defs/a~1b~0c/x%20y%23%C3%A9");
    }

    #[test]
    fn a_set_of_types_knows_what_it_holds() {
        let mut types = Types::default();
        assert!(types.insert(Type::Integer));
        assert!(types.insert(Type::Null));
        assert!(!types.insert(Type::Integer));
        assert!(types.contains(Type::Null));
        assert!(!types.contains(Type::Number));
    }
}
