//! From the schema graph to terms.
//!
//! Every schema that the check can reach in place, through a connective or a reference, gets
//! a variable, and the term of the variable says what its keywords say. Schemas that say the
//! same share a variable, also between A and B.
//!
//! The engine models the types, `null`, the booleans, the connectives and references. Every
//! other keyword becomes a predicate that it does not model, a leaf, which keeps the place
//! where it stands. A leaf says something only about the instances its keyword is about:
//! `minLength` about strings, and so a number satisfies it.

mod classes;

use std::collections::{HashMap, VecDeque};

use serde_json::Value;

use self::classes::written;
use crate::context::{Context, Exhausted};
use crate::schema::{Count, Graph, Keywords, NodeId, Schema, Type};
use crate::term::{InstanceType, TermId, TypeSet, VarId};

/// Gives A and B their terms, and returns the variables of the two.
///
/// # Errors
///
/// When the budget does not cover the work.
pub(crate) fn lower(graph: &Graph, context: &mut Context) -> Result<(VarId, VarId), Exhausted> {
    let classes = classes::classes(graph, &mut context.budget)?;
    let mut lowering = Lowering {
        graph,
        classes: &classes,
        context,
        variables: HashMap::new(),
        pending: VecDeque::new(),
    };
    let a = lowering.variable(graph.a);
    let b = lowering.variable(graph.b);
    while let Some(variable) = lowering.pending.pop_front() {
        let node = lowering.context.terms.variable(variable).node;
        let body = lowering.body(node);
        lowering.context.terms.variable_mut(variable).body = body;
    }

    // A variable stands for every schema of its class, on whichever side it is.
    for (index, class) in classes.iter().enumerate() {
        if let Some(&variable) = lowering.variables.get(class) {
            let side = graph.node(NodeId::new(index)).side as usize;
            lowering.context.terms.variable_mut(variable).sides[side] = true;
        }
    }
    Ok((a, b))
}

struct Lowering<'g, 'c> {
    graph: &'g Graph<'g>,
    classes: &'c [u32],
    context: &'c mut Context,
    /// The variable of each class that has one.
    variables: HashMap<u32, VarId>,
    /// The variables that have no term yet, in the order in which they were made.
    pending: VecDeque<VarId>,
}

const NULL: TypeSet = TypeSet::of(InstanceType::Null);
const NUMBER: TypeSet = TypeSet::of(InstanceType::Number);
const STRING: TypeSet = TypeSet::of(InstanceType::String);
const ARRAY: TypeSet = TypeSet::of(InstanceType::Array);
const OBJECT: TypeSet = TypeSet::of(InstanceType::Object);

impl Lowering<'_, '_> {
    /// The variable of a schema. The first schema of a class to ask gives the variable its
    /// term, and every schema of a class would give the same.
    fn variable(&mut self, node: NodeId) -> VarId {
        let class = self.classes[node.index()];
        if let Some(&variable) = self.variables.get(&class) {
            return variable;
        }
        let variable = self.context.terms.new_variable(node);
        self.variables.insert(class, variable);
        self.pending.push_back(variable);
        variable
    }

    /// The term that refers to a schema.
    fn refer(&mut self, node: NodeId) -> TermId {
        let variable = self.variable(node);
        self.context.terms.reference(variable)
    }

    /// The name of the class of a schema, for the key of a leaf that holds the schema.
    fn class(&self, node: NodeId) -> String {
        format!("#{}", self.classes[node.index()])
    }

    /// The term of a schema: the conjunction of what its keywords say.
    fn body(&mut self, id: NodeId) -> TermId {
        let graph = self.graph;
        let keywords = match &graph.node(id).schema {
            Schema::Bool(true) => return self.context.terms.truth(),
            Schema::Bool(false) => return self.context.terms.falsity(),
            Schema::Object(keywords) => keywords,
        };
        let mut parts = Vec::new();
        self.connectives(id, keywords, &mut parts);
        self.any_type(id, keywords, &mut parts);
        self.numbers(id, keywords, &mut parts);
        self.strings(id, keywords, &mut parts);
        self.arrays(id, keywords, &mut parts);
        self.objects(id, keywords, &mut parts);
        self.context.terms.all_of(parts)
    }

    /// A predicate that the engine does not model. `key` is the keyword with what it holds;
    /// two leaves with one key over the same types are one predicate.
    fn leaf(&mut self, domain: TypeSet, id: NodeId, keyword: &'static str, key: String) -> TermId {
        self.context.terms.unknown(domain, key, id, keyword)
    }

    /// A leaf that is unlike every other, for a keyword whose meaning is not in its value.
    fn leaf_of_its_own(&mut self, domain: TypeSet, id: NodeId, keyword: &'static str) -> TermId {
        let key = format!("{keyword} @{}", id.index());
        self.leaf(domain, id, keyword, key)
    }

    /// The leaf of a keyword that holds a count.
    fn count(
        &mut self,
        domain: TypeSet,
        id: NodeId,
        keyword: &'static str,
        count: Option<Count>,
        parts: &mut Vec<TermId>,
    ) {
        match count {
            None => {}
            Some(Count::Of(count)) => {
                parts.push(self.leaf(domain, id, keyword, format!("{keyword} {count}")));
            }
            // Two counts that were too large to keep are not known to be equal.
            Some(Count::Beyond) => parts.push(self.leaf_of_its_own(domain, id, keyword)),
        }
    }

    fn connectives(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        if let Some(target) = keywords.reference {
            parts.push(self.refer(target));
        }
        if keywords.dynamic_reference.is_some() {
            parts.push(self.leaf_of_its_own(TypeSet::ALL, id, "$dynamicRef"));
        }
        for schema in &keywords.all_of {
            parts.push(self.refer(*schema));
        }
        if !keywords.any_of.is_empty() {
            let branches: Vec<TermId> = keywords.any_of.iter().map(|s| self.refer(*s)).collect();
            parts.push(self.context.terms.any_of(branches));
        }
        if !keywords.one_of.is_empty() {
            let branches: Vec<TermId> = keywords.one_of.iter().map(|s| self.refer(*s)).collect();
            parts.push(self.context.terms.one_of(branches));
        }
        if let Some(schema) = keywords.not {
            let schema = self.refer(schema);
            parts.push(self.context.terms.not(schema));
        }
        // Without `if`, `then` and `else` say nothing.
        if let Some(condition) = keywords.if_ {
            let condition = self.refer(condition);
            if let Some(then) = keywords.then {
                let (unmet, then) = (self.context.terms.not(condition), self.refer(then));
                parts.push(self.context.terms.any_of([unmet, then]));
            }
            if let Some(otherwise) = keywords.else_ {
                let otherwise = self.refer(otherwise);
                parts.push(self.context.terms.any_of([condition, otherwise]));
            }
        }
        // An instance that is no object, or has no such property, or satisfies the schema.
        for (name, schema) in &keywords.dependent_schemas {
            let absent = self.absent(id, "dependentSchemas", name);
            let schema = self.refer(*schema);
            parts.push(self.context.terms.any_of([absent, schema]));
        }
    }

    /// The leaf for "an object has this property". An instance that is no object satisfies
    /// it, as it satisfies `required`.
    fn has_property(&mut self, id: NodeId, keyword: &'static str, name: &str) -> TermId {
        self.leaf(OBJECT, id, keyword, format!("required {}", written!(name)))
    }

    /// The term for "no object, or an object without this property".
    fn absent(&mut self, id: NodeId, keyword: &'static str, name: &str) -> TermId {
        let present = self.has_property(id, keyword, name);
        let (other, lacks) = (
            self.context.terms.type_is(OBJECT.complement()),
            self.context.terms.not(present),
        );
        self.context.terms.any_of([other, lacks])
    }

    fn any_type(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        if let Some(types) = keywords.types {
            let named = [
                (Type::Null, InstanceType::Null),
                (Type::Boolean, InstanceType::Boolean),
                (Type::Number, InstanceType::Number),
                (Type::String, InstanceType::String),
                (Type::Array, InstanceType::Array),
                (Type::Object, InstanceType::Object),
            ];
            let mut set = TypeSet::NONE;
            for (name, kind) in named {
                if types.contains(name) {
                    set = set.union(TypeSet::of(kind));
                }
            }
            if types.contains(Type::Integer) && !types.contains(Type::Number) {
                // An integer is a number that is a multiple of one.
                parts.push(self.context.terms.type_is(set.union(NUMBER)));
                parts.push(self.leaf(NUMBER, id, "type", "multipleOf 1".to_owned()));
            } else {
                parts.push(self.context.terms.type_is(set));
            }
        }
        if let Some(values) = keywords.enumeration {
            let values: Vec<TermId> = values
                .iter()
                .map(|value| self.constant(id, "enum", value))
                .collect();
            parts.push(self.context.terms.any_of(values));
        }
        if let Some(value) = keywords.constant {
            parts.push(self.constant(id, "const", value));
        }
    }

    /// The term for "the instance is this value". `null` and the booleans are terms of the
    /// engine; any other value is of one type and a leaf over that type.
    fn constant(&mut self, id: NodeId, keyword: &'static str, value: &Value) -> TermId {
        let kind = match value {
            Value::Null => return self.context.terms.type_is(NULL),
            Value::Bool(value) => return self.context.terms.bool_const(*value),
            Value::Number(_) => NUMBER,
            Value::String(_) => STRING,
            Value::Array(_) => ARRAY,
            Value::Object(_) => OBJECT,
        };
        let is_it = self.leaf(kind, id, keyword, format!("const {value}"));
        let of_type = self.context.terms.type_is(kind);
        self.context.terms.all_of([of_type, is_it])
    }

    fn numbers(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        let bounds = [
            ("minimum", keywords.minimum),
            ("maximum", keywords.maximum),
            ("exclusiveMinimum", keywords.exclusive_minimum),
            ("exclusiveMaximum", keywords.exclusive_maximum),
            ("multipleOf", keywords.multiple_of),
        ];
        for (keyword, number) in bounds {
            if let Some(number) = number {
                parts.push(self.leaf(NUMBER, id, keyword, format!("{keyword} {number}")));
            }
        }
    }

    fn strings(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        self.count(STRING, id, "minLength", keywords.min_length, parts);
        self.count(STRING, id, "maxLength", keywords.max_length, parts);
        if let Some(pattern) = keywords.pattern {
            parts.push(self.leaf(
                STRING,
                id,
                "pattern",
                format!("pattern {}", written!(pattern)),
            ));
        }
        if let Some(format) = keywords.format {
            parts.push(self.leaf(STRING, id, "format", format!("format {}", written!(format))));
        }
    }

    fn arrays(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        // `items` is about the items after those that `prefixItems` names, so the two are
        // one predicate.
        if !keywords.prefix_items.is_empty() || keywords.items.is_some() {
            let prefix: Vec<String> = keywords
                .prefix_items
                .iter()
                .map(|s| self.class(*s))
                .collect();
            let rest = keywords
                .items
                .map_or_else(|| "any".to_owned(), |s| self.class(s));
            let keyword = if keywords.items.is_some() {
                "items"
            } else {
                "prefixItems"
            };
            let key = format!("items [{}] then {rest}", prefix.join(", "));
            parts.push(self.leaf(ARRAY, id, keyword, key));
        }
        // `minContains` and `maxContains` say how many items `contains` is about, and
        // nothing without it.
        if let Some(schema) = keywords.contains {
            let bounds = [keywords.min_contains, keywords.max_contains];
            if bounds.contains(&Some(Count::Beyond)) {
                parts.push(self.leaf_of_its_own(ARRAY, id, "contains"));
            } else {
                let bound = |count| match count {
                    Some(Count::Of(count)) => count.to_string(),
                    _ => "unset".to_owned(),
                };
                let (least, most) = (bound(bounds[0]), bound(bounds[1]));
                let key = format!("contains {} from {least} to {most}", self.class(schema));
                parts.push(self.leaf(ARRAY, id, "contains", key));
            }
        }
        self.count(ARRAY, id, "minItems", keywords.min_items, parts);
        self.count(ARRAY, id, "maxItems", keywords.max_items, parts);
        if keywords.unique_items {
            parts.push(self.leaf(ARRAY, id, "uniqueItems", "uniqueItems".to_owned()));
        }
        // What `unevaluatedItems` is about depends on everything else in the schema, so it
        // is a predicate of the schema as a whole.
        if keywords.unevaluated_items.is_some() {
            let key = format!("unevaluatedItems of {}", self.class(id));
            parts.push(self.leaf(ARRAY, id, "unevaluatedItems", key));
        }
    }

    fn objects(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        let named = |lowering: &Self, schemas: &[(&str, NodeId)]| -> Vec<String> {
            let named = schemas.iter();
            named
                .map(|(name, schema)| format!("{} {}", written!(name), lowering.class(*schema)))
                .collect()
        };
        let properties = named(self, &keywords.properties);
        let patterns = named(self, &keywords.pattern_properties);
        if let Some(schema) = keywords.additional_properties {
            // `additionalProperties` is about the properties that the other two do not
            // name, so the three are one predicate.
            let key = format!(
                "properties {{{}}} patternProperties {{{}}} additionalProperties {}",
                properties.join(", "),
                patterns.join(", "),
                self.class(schema)
            );
            parts.push(self.leaf(OBJECT, id, "additionalProperties", key));
        } else {
            for property in properties {
                parts.push(self.leaf(OBJECT, id, "properties", format!("properties {property}")));
            }
            for pattern in patterns {
                let key = format!("patternProperties {pattern}");
                parts.push(self.leaf(OBJECT, id, "patternProperties", key));
            }
        }
        if let Some(schema) = keywords.property_names {
            let key = format!("propertyNames {}", self.class(schema));
            parts.push(self.leaf(OBJECT, id, "propertyNames", key));
        }
        for name in &keywords.required {
            parts.push(self.has_property(id, "required", name));
        }
        // An instance that is no object, or has no such property, or has all the others.
        for (name, needed) in &keywords.dependent_required {
            let absent = self.absent(id, "dependentRequired", name);
            let needed: Vec<TermId> = needed
                .iter()
                .map(|name| self.has_property(id, "dependentRequired", name))
                .collect();
            let all = self.context.terms.all_of(needed);
            parts.push(self.context.terms.any_of([absent, all]));
        }
        self.count(OBJECT, id, "minProperties", keywords.min_properties, parts);
        self.count(OBJECT, id, "maxProperties", keywords.max_properties, parts);
        if keywords.unevaluated_properties.is_some() {
            let key = format!("unevaluatedProperties of {}", self.class(id));
            parts.push(self.leaf(OBJECT, id, "unevaluatedProperties", key));
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, json};

    use super::*;
    use crate::Side;
    use crate::schema::parse;
    use crate::term::Terms;

    /// A and B lowered: the terms, and the variables of the two.
    fn lowered(a: &Value, b: &Value) -> (Terms, VarId, VarId) {
        let graph = parse(a, b).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX);
        let (a, b) = lower(&graph, &mut context).unwrap();
        (context.terms, a, b)
    }

    /// The term of a schema, as text.
    fn term(schema: &Value) -> String {
        let (terms, a, _) = lowered(schema, &json!(true));
        terms.show(terms.variable(a).body)
    }

    /// The terms of the first variables, as text. A is `x0`, B is `x1`, and the others
    /// follow in the order in which the terms name them.
    fn terms(a: &Value, b: &Value) -> Vec<String> {
        let (terms, ..) = lowered(a, b);
        let bodies = terms.variables().map(|(_, variable)| variable.body);
        bodies.map(|body| terms.show(body)).collect()
    }

    #[test]
    fn a_type_is_a_term_and_an_integer_is_a_number_with_a_leaf() {
        assert_eq!(term(&json!(true)), "true");
        assert_eq!(term(&json!({})), "true");
        assert_eq!(term(&json!(false)), "false");
        assert_eq!(term(&json!({"type": "string"})), "type(string)");
        assert_eq!(
            term(&json!({"type": ["boolean", "null"]})),
            "type(null | boolean)"
        );
        assert_eq!(
            term(&json!({"type": "integer"})),
            "all(type(number), ?[multipleOf 1])"
        );
        assert_eq!(
            term(&json!({"type": ["integer", "null"]})),
            "all(type(null | number), ?[multipleOf 1])"
        );
        // A number may be anything that an integer may be.
        assert_eq!(
            term(&json!({"type": ["integer", "number"]})),
            "type(number)"
        );
        // The leaf is the one of the keyword that says the same.
        assert_eq!(term(&json!({"multipleOf": 1})), "?[multipleOf 1]");
    }

    #[test]
    fn a_constant_is_a_term_if_it_is_null_or_a_boolean() {
        assert_eq!(term(&json!({"const": null})), "type(null)");
        assert_eq!(term(&json!({"const": true})), "is(true)");
        assert_eq!(
            term(&json!({"enum": [null, false, 1, "a"]})),
            r#"any(type(null), is(false), all(type(number), ?[const 1]), all(type(string), ?[const "a"]))"#
        );
        assert_eq!(term(&json!({"enum": []})), "false");
        assert_eq!(
            term(&json!({"const": [1, {"a": null}]})),
            r#"all(type(array), ?[const [1,{"a":null}]])"#
        );
        // One value is one leaf, whichever keyword holds it.
        assert_eq!(term(&json!({"enum": [1]})), term(&json!({"const": 1})));
    }

    #[test]
    fn a_connective_refers_to_the_variables_of_its_schemas() {
        let schema = json!({
            "allOf": [{"type": "string"}],
            "anyOf": [{"type": "null"}, {"type": "number"}],
            "oneOf": [{"type": "null"}, {"type": "array"}],
            "not": {"type": "object"},
        });
        // `{"type": "null"}` stands twice and is one variable.
        assert_eq!(
            terms(&schema, &json!(true)),
            [
                "all(x2, any(x3, x4), one(x3, x5), not x6)",
                "true",
                "type(string)",
                "type(null)",
                "type(number)",
                "type(array)",
                "type(object)",
            ]
        );
        // With one schema in it, a connective is that schema.
        let single = json!({"anyOf": [{"type": "null"}], "oneOf": [{"type": "string"}]});
        assert_eq!(terms(&single, &json!(true))[0], "all(x2, x3)");
    }

    #[test]
    fn a_condition_is_two_disjunctions() {
        let schema = json!({
            "if": {"type": "string"},
            "then": {"type": "null"},
            "else": {"type": "number"},
        });
        assert_eq!(
            terms(&schema, &json!(true))[0],
            "all(any(not x2, x3), any(x2, x4))"
        );
        // Without `if`, the other two say nothing, and `if` alone says nothing either.
        assert_eq!(term(&json!({"then": false, "else": false})), "true");
        assert_eq!(term(&json!({"if": false})), "true");
        assert_eq!(term(&json!({"if": {}, "then": false})), "any(not x2, x3)");
    }

    #[test]
    fn a_dependency_holds_for_what_is_no_object_or_lacks_the_property() {
        let no_object = "type(null | boolean | number | string | array)";
        assert_eq!(
            term(&json!({"dependentSchemas": {"a": {"type": "null"}}})),
            format!(r#"any({no_object}, not ?[required "a"], x2)"#)
        );
        assert_eq!(
            term(&json!({"dependentRequired": {"a": ["b", "c"]}})),
            format!(
                r#"any({no_object}, not ?[required "a"], all(?[required "b"], ?[required "c"]))"#
            )
        );
        // The leaf is the one that `required` has.
        assert_eq!(
            term(&json!({"required": ["a", "b"]})),
            r#"all(?[required "a"], ?[required "b"])"#
        );
    }

    #[test]
    fn every_other_keyword_is_a_leaf_with_what_it_holds() {
        let schema = json!({
            "minimum": 1,
            "exclusiveMaximum": 2.5,
            "maxLength": 3,
            "pattern": "^a",
            "format": "date",
            "minItems": 4,
            "uniqueItems": true,
            "required": ["a"],
            "minProperties": 5,
        });
        assert_eq!(
            term(&schema),
            r#"all(?[minimum 1], ?[exclusiveMaximum 2.5], ?[maxLength 3], ?[pattern "^a"], ?[format "date"], ?[minItems 4], ?[uniqueItems], ?[required "a"], ?[minProperties 5])"#
        );
        assert_eq!(term(&json!({"uniqueItems": false})), "true");
        // `minContains` says nothing without `contains`.
        assert_eq!(term(&json!({"minContains": 2, "maxContains": 3})), "true");
    }

    #[test]
    fn a_leaf_says_which_types_it_is_about_and_where_it_was_first() {
        let a = json!({"type": "string", "minLength": 1});
        let b = json!({"minLength": 1, "$dynamicRef": "#here", "$dynamicAnchor": "here"});
        let graph = parse(&a, &b).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX);
        let (_, of_b) = lower(&graph, &mut context).unwrap();
        let terms = &context.terms;
        let crate::term::Term::AllOf(parts) = terms.term(terms.variable(of_b).body) else {
            panic!("B has two keywords");
        };
        let leaves: Vec<_> = parts
            .iter()
            .map(|part| match terms.term(*part) {
                crate::term::Term::Unknown(leaf) => terms.leaf(*leaf),
                other => panic!("{other:?} is no leaf"),
            })
            .collect();
        let place = |leaf: &crate::term::Leaf| {
            let side = graph.node(leaf.node).side;
            (side, graph.keyword_location(leaf.node, leaf.keyword))
        };
        // A dynamic reference may be about any instance, and no other is like it.
        assert_eq!(leaves[0].domain, TypeSet::ALL);
        assert_eq!(place(leaves[0]), (Side::B, "#/$dynamicRef".to_owned()));
        // The leaf of `minLength` is about strings. A has it too, and A is lowered first.
        assert_eq!(leaves[1].domain, STRING);
        assert_eq!(place(leaves[1]), (Side::A, "#/minLength".to_owned()));
    }

    #[test]
    fn keywords_that_depend_on_each_other_are_one_leaf() {
        let count = |text: &str| text.matches("?[").count();
        // `items` is about what `prefixItems` leaves.
        let items = term(&json!({"prefixItems": [{}, false], "items": {"type": "null"}}));
        assert!(
            items.starts_with("?[items [#") && count(&items) == 1,
            "{items}"
        );
        let prefix = term(&json!({"prefixItems": [{}]}));
        assert!(prefix.ends_with("then any]"), "{prefix}");
        // `additionalProperties` is about what the other two leave.
        let closed = json!({
            "properties": {"a": {}},
            "patternProperties": {"^b": {}},
            "additionalProperties": false,
        });
        let closed = term(&closed);
        assert!(closed.starts_with(r#"?[properties {"a" #"#), "{closed}");
        assert!(closed.contains("additionalProperties #") && count(&closed) == 1);
        // Without it, every property is a leaf of its own.
        let open =
            term(&json!({"properties": {"a": {}, "b": {}}, "patternProperties": {"^c": {}}}));
        assert_eq!(count(&open), 3, "{open}");
        // The bounds of `contains` belong to it.
        let contains = term(&json!({"contains": {}, "minContains": 2}));
        assert!(contains.ends_with("from 2 to unset]"), "{contains}");
    }

    #[test]
    fn schemas_that_say_the_same_have_one_variable_and_one_leaf() {
        let a = json!({
            "type": "object",
            "properties": {"name": {"type": "string"}, "age": {"minimum": 0}},
            "items": {"type": "null"},
        });
        let mut b = a.clone();
        let (terms, of_a, of_b) = lowered(&a, &b);
        assert_eq!(of_a, of_b);
        assert_eq!(terms.variable(of_a).sides, [true, true]);
        assert_eq!(terms.variables().count(), 1);

        // One property changes. The variables of A and B differ, and so does that leaf, but
        // the leaves of what stayed are shared.
        b["properties"]["age"] = json!({"minimum": 1});
        let (terms, of_a, of_b) = lowered(&a, &b);
        assert_ne!(of_a, of_b);
        assert_eq!(terms.variable(of_a).sides, [true, false]);
        assert_eq!(terms.variable(of_b).sides, [false, true]);
        let parts = |variable| match terms.term(terms.variable(variable).body) {
            crate::term::Term::AllOf(parts) => parts.to_vec(),
            other => panic!("{other:?} is no conjunction"),
        };
        let (of_a, of_b) = (parts(of_a), parts(of_b));
        // The type, the two properties and the items.
        assert_eq!((of_a.len(), of_b.len()), (4, 4));
        let shared = of_a.iter().filter(|part| of_b.contains(part)).count();
        assert_eq!(shared, 3);
    }

    #[test]
    fn some_leaves_are_like_no_other() {
        // What `unevaluatedProperties` is about depends on the rest of its schema.
        let a = json!({"properties": {"a": {}}, "unevaluatedProperties": false});
        let b = json!({"properties": {"b": {}}, "unevaluatedProperties": false});
        let (terms, of_a, of_b) = lowered(&a, &b);
        let last = |variable| match terms.term(terms.variable(variable).body) {
            crate::term::Term::AllOf(parts) => *parts.last().unwrap(),
            other => panic!("{other:?} is no conjunction"),
        };
        assert_ne!(last(of_a), last(of_b));
        assert!(
            terms
                .show(last(of_a))
                .starts_with("?[unevaluatedProperties of #")
        );
        // In two schemas that say the same, it is the same.
        let (_, of_a, of_b) = lowered(&a, &a);
        assert_eq!(of_a, of_b);

        // A count that was too large to keep is not known to equal another.
        let huge = json!({"minLength": 1e30});
        let (terms, of_a, of_b) = lowered(&huge, &huge);
        assert_ne!(of_a, of_b);
        let (of_a, of_b) = (terms.variable(of_a).body, terms.variable(of_b).body);
        assert_ne!(terms.show(of_a), terms.show(of_b));
        assert!(terms.show(of_a).starts_with("?[minLength @"));
    }

    #[test]
    fn a_schema_that_refers_to_itself_has_a_term() {
        let list = json!({"anyOf": [{"type": "null"}, {"$ref": "#"}]});
        assert_eq!(
            terms(&list, &json!(true)),
            ["any(x2, x3)", "true", "type(null)", "x0"]
        );
        // What a leaf holds is not opened, so the cycle through `items` ends in the leaf.
        let tree = json!({"items": {"$ref": "#"}});
        assert_eq!(terms(&tree, &json!(true)).len(), 2);
    }

    #[test]
    fn a_deep_schema_is_lowered_without_recursion() {
        let mut deep = json!({"type": "null"});
        for _ in 0..100_000 {
            deep = Value::Object(Map::from_iter([("not".to_owned(), deep)]));
        }
        let (terms, of_a, of_b) = lowered(&deep, &deep);
        assert_eq!(of_a, of_b);
        assert_eq!(terms.variables().count(), 100_001);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget(deep);
    }

    #[test]
    fn the_budget_may_end_the_lowering() {
        let cycle = json!({"not": {"not": {"not": {"$ref": "#"}}}});
        let truth = json!(true);
        let graph = parse(&cycle, &truth).unwrap().link().unwrap();
        let mut context = Context::new(1);
        assert_eq!(lower(&graph, &mut context), Err(Exhausted));
        assert_eq!(context.budget.spent(), 1);
    }
}
