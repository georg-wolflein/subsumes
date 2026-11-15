//! From the schema graph to terms.
//!
//! Every schema that the check can reach in place, through a connective or a reference, gets
//! a variable, and the term of the variable says what its keywords say. Schemas that say the
//! same share a variable, also between A and B.
//!
//! The engine models the types, `null`, the booleans, numbers, strings, objects, the
//! connectives and references. Every other keyword becomes a predicate that it does not
//! model, a leaf, which keeps the place where it stands. A leaf says something only about
//! the instances its keyword is about: `minItems` about arrays, and so a number satisfies
//! it. The terms about numbers, about strings and about objects are the same in that: a
//! string satisfies `minimum`, and a number satisfies `minLength` and `required`.
//!
//! A schema that is the value of a property is not reached in place: it is asked of a
//! value inside the instance. It has a variable too, which the term about the property
//! names.

mod classes;

use std::collections::{HashMap, VecDeque};

use serde_json::Value;

use self::classes::written;
use crate::context::{Context, Exhausted};
use crate::formats;
use crate::rational::{Rational, exact};
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

/// The first `$dynamicRef` that A or B leads to, if either leads to one.
///
/// What a `$dynamicRef` accepts depends on the schemas that led to it, and a term says the
/// same wherever it stands. So the terms of a schema that leads to one are not to be trusted:
/// the same schema, reached in two ways, would cancel against its own negation. That holds
/// wherever in the schema the reference is, because a leaf holds schemas too.
pub(crate) fn dynamic_reference(graph: &Graph) -> Option<NodeId> {
    let mut seen = vec![false; graph.len()];
    let mut pending = VecDeque::from([graph.a, graph.b]);
    while let Some(id) = pending.pop_front() {
        if std::mem::replace(&mut seen[id.index()], true) {
            continue;
        }
        let Schema::Object(keywords) = &graph.node(id).schema else {
            continue;
        };
        if keywords.dynamic_reference.is_some() {
            return Some(id);
        }
        let applied = keywords.subschemas().into_iter().map(|(_, _, to)| to);
        pending.extend(applied.chain(keywords.reference));
    }
    None
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
        self.numbers(keywords, &mut parts);
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
        // No check gets this far with one; see `dynamic_reference`. The leaf is what a
        // picture of the terms shows in its place.
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
            let present = self.has_property(name);
            let schema = self.refer(*schema);
            let terms = &mut self.context.terms;
            let (other, lacks) = (terms.type_is(OBJECT.complement()), terms.not(present));
            parts.push(terms.any_of([other, lacks, schema]));
        }
    }

    /// The term for "no object, or an object with this property".
    fn has_property(&mut self, name: &str) -> TermId {
        let named = self.context.languages.words([name]);
        self.context.terms.p_req(named)
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
                parts.push(self.context.terms.mof(Rational::from_integer(1.into())));
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

    /// The term for "the instance is this value". `null`, the booleans, the numbers and the
    /// strings are terms of the engine; an array or an object is of one type and a leaf over
    /// that type.
    fn constant(&mut self, id: NodeId, keyword: &'static str, value: &Value) -> TermId {
        let kind = match value {
            Value::Null => return self.context.terms.type_is(NULL),
            Value::Bool(value) => return self.context.terms.bool_const(*value),
            Value::Number(number) => return self.context.terms.num_const(exact(number)),
            Value::String(word) => return self.context.terms.str_const(word),
            Value::Array(_) => ARRAY,
            Value::Object(_) => OBJECT,
        };
        let is_it = self.leaf(kind, id, keyword, format!("const {value}"));
        let of_type = self.context.terms.type_is(kind);
        self.context.terms.all_of([of_type, is_it])
    }

    fn numbers(&mut self, keywords: &Keywords, parts: &mut Vec<TermId>) {
        let terms = &mut self.context.terms;
        if let Some(at) = keywords.minimum {
            parts.push(terms.min(exact(at)));
        }
        if let Some(at) = keywords.maximum {
            parts.push(terms.max(exact(at)));
        }
        if let Some(at) = keywords.exclusive_minimum {
            parts.push(terms.ex_min(exact(at)));
        }
        if let Some(at) = keywords.exclusive_maximum {
            parts.push(terms.ex_max(exact(at)));
        }
        if let Some(step) = keywords.multiple_of {
            parts.push(terms.mof(exact(step)));
        }
    }

    fn strings(&mut self, id: NodeId, keywords: &Keywords, parts: &mut Vec<TermId>) {
        // A count that was too large to keep stays a leaf.
        match keywords.min_length {
            Some(Count::Of(least)) => parts.push(self.context.terms.min_len(least)),
            beyond => self.count(STRING, id, "minLength", beyond, parts),
        }
        match keywords.max_length {
            Some(Count::Of(most)) => parts.push(self.context.terms.max_len(most)),
            beyond => self.count(STRING, id, "maxLength", beyond, parts),
        }
        if let Some(pattern) = keywords.pattern {
            // A pattern that is not read as a language is a leaf.
            parts.push(match self.context.languages.pattern(pattern) {
                Ok(language) => self.context.terms.patt(language),
                Err(_) => {
                    let key = format!("pattern {}", written!(pattern));
                    self.leaf(STRING, id, "pattern", key)
                }
            });
        }
        if let Some(format) = keywords.format {
            parts.push(self.format(id, format));
        }
    }

    /// The term of a format. A format that is not modelled is a leaf. One that is modelled
    /// in part is the strings that it accepts, or one of those that it leaves open if a
    /// leaf holds, which stands for what the format makes of them.
    fn format(&mut self, id: NodeId, format: &str) -> TermId {
        let Some(modelled) = formats::modelled(format) else {
            let key = format!("format {}", written!(format));
            return self.leaf(STRING, id, "format", key);
        };
        let Context {
            terms, languages, ..
        } = &mut *self.context;
        let accepted = terms.patt(languages.format(format, modelled.accepted));
        let Some(open) = modelled.open else {
            return accepted;
        };
        let name = format!("{format}, where it is open");
        let open = terms.patt(languages.format(&name, open));
        let key = format!("format {} where it is open", written!(format));
        let holds = self.leaf(STRING, id, "format", key);
        let terms = &mut self.context.terms;
        let may_be = terms.all_of([open, holds]);
        terms.any_of([accepted, may_be])
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
        // A property with this name satisfies the schema.
        for (name, schema) in &keywords.properties {
            let variable = self.variable(*schema);
            let named = self.context.languages.words([*name]);
            parts.push(self.context.terms.p_prop(named, variable));
        }
        // So does one whose name the pattern matches. A pattern that is not read as a
        // language is a leaf.
        let mut patterns = Vec::with_capacity(keywords.pattern_properties.len());
        let mut all_read = true;
        for (pattern, schema) in &keywords.pattern_properties {
            let variable = self.variable(*schema);
            match self.context.languages.pattern(pattern) {
                Ok(matched) => {
                    patterns.push(matched);
                    parts.push(self.context.terms.p_prop(matched, variable));
                }
                Err(_) => {
                    all_read = false;
                    let (pattern, schema) = (written!(pattern), self.class(*schema));
                    let key = format!("patternProperties {pattern} {schema}");
                    parts.push(self.leaf(OBJECT, id, "patternProperties", key));
                }
            }
        }
        // `additionalProperties` is about the properties that the other two do not name:
        // those whose name is none of the names and in none of the languages. With a
        // pattern that is not read, which properties those are is not known, and the
        // keyword is a leaf together with what it depends on.
        if let Some(schema) = keywords.additional_properties {
            let names: Vec<&str> = keywords.properties.iter().map(|(name, _)| *name).collect();
            if all_read {
                let variable = self.variable(schema);
                let languages = &mut self.context.languages;
                let named = languages.words(names);
                let others = languages.outside(patterns.into_iter().chain([named]));
                parts.push(self.context.terms.p_prop(others, variable));
            } else {
                let patterns = keywords.pattern_properties.iter();
                let patterns: Vec<&str> = patterns.map(|(pattern, _)| *pattern).collect();
                let key = format!(
                    "additionalProperties {} but for {} and {}",
                    self.class(schema),
                    written!(&names),
                    written!(&patterns),
                );
                parts.push(self.leaf(OBJECT, id, "additionalProperties", key));
            }
        }
        if let Some(schema) = keywords.property_names {
            let variable = self.variable(schema);
            parts.push(self.context.terms.p_names(variable));
        }
        for name in &keywords.required {
            parts.push(self.has_property(name));
        }
        // An object without such a property, or an instance that has all the others if it
        // is an object, which also what is no object does.
        for (name, needed) in &keywords.dependent_required {
            let present = self.has_property(name);
            let needed: Vec<TermId> = needed.iter().map(|name| self.has_property(name)).collect();
            let terms = &mut self.context.terms;
            let (lacks, all) = (terms.not(present), terms.all_of(needed));
            parts.push(terms.any_of([lacks, all]));
        }
        // A count that was too large to keep stays a leaf.
        match keywords.min_properties {
            Some(Count::Of(least)) => parts.push(self.context.terms.min_props(least)),
            beyond => self.count(OBJECT, id, "minProperties", beyond, parts),
        }
        match keywords.max_properties {
            Some(Count::Of(most)) => parts.push(self.context.terms.max_props(most)),
            beyond => self.count(OBJECT, id, "maxProperties", beyond, parts),
        }
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
    fn a_type_is_a_term_and_an_integer_is_a_number_that_is_a_multiple_of_one() {
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
            "all(type(number), mof(1))"
        );
        assert_eq!(
            term(&json!({"type": ["integer", "null"]})),
            "all(type(null | number), mof(1))"
        );
        // A number may be anything that an integer may be.
        assert_eq!(
            term(&json!({"type": ["integer", "number"]})),
            "type(number)"
        );
        // The term is the one of the keyword that says the same.
        assert_eq!(term(&json!({"multipleOf": 1})), "mof(1)");
    }

    #[test]
    fn a_keyword_about_numbers_is_a_term_with_the_number_itself() {
        let schema = json!({
            "minimum": 1,
            "maximum": 1e30,
            "exclusiveMinimum": -0.5,
            "exclusiveMaximum": 2.50,
            "multipleOf": 0.01,
        });
        assert_eq!(
            term(&schema),
            "all(min(1), max(1e+30), exmin(-0.5), exmax(2.5), mof(0.01))"
        );
        // One number is one term, however it is written, and the two schemas are one class.
        assert_eq!(term(&json!({"minimum": 2.0})), "min(2)");
        let (_, of_a, of_b) = lowered(&json!({"minimum": 2.0}), &json!({"minimum": 2}));
        assert_eq!(of_a, of_b);
    }

    #[test]
    fn a_constant_is_a_term_unless_it_is_an_array_or_an_object() {
        assert_eq!(term(&json!({"const": null})), "type(null)");
        assert_eq!(term(&json!({"const": true})), "is(true)");
        assert_eq!(term(&json!({"const": "a"})), r#"is("a")"#);
        assert_eq!(
            term(&json!({"enum": [null, false, 1, "a", {}]})),
            r#"any(type(null), is(false), is(1), is("a"), all(type(object), ?[const {}]))"#
        );
        assert_eq!(term(&json!({"enum": []})), "false");
        assert_eq!(
            term(&json!({"const": [1, {"a": null}]})),
            r#"all(type(array), ?[const [1,{"a":null}]])"#
        );
        // One value is one term, whichever keyword holds it and however it is written.
        assert_eq!(term(&json!({"enum": [1]})), term(&json!({"const": 1})));
        assert_eq!(term(&json!({"const": 1.0})), term(&json!({"const": 1})));
        assert_eq!(term(&json!({"const": 0.5})), "is(0.5)");
        assert_eq!(term(&json!({"enum": ["a"]})), term(&json!({"const": "a"})));
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
            format!("any({no_object}, not preq(l2), x2)")
        );
        // What is no object has every property that is asked for, as far as `required`
        // goes, so it needs no alternative of its own here.
        assert_eq!(
            term(&json!({"dependentRequired": {"a": ["b", "c"]}})),
            "any(not preq(l2), all(preq(l3), preq(l4)))"
        );
        assert_eq!(term(&json!({"dependentRequired": {"a": []}})), "true");
        // The term is the one that `required` has.
        assert_eq!(
            term(&json!({"required": ["a", "b"]})),
            "all(preq(l2), preq(l3))"
        );
        assert_eq!(
            term(&json!({"required": ["a"], "dependentRequired": {"b": ["a"]}})),
            "all(preq(l2), any(not preq(l3), preq(l2)))"
        );
    }

    #[test]
    fn a_keyword_about_objects_is_a_term() {
        let schema = json!({
            "properties": {"a": {"type": "null"}, "b": {"type": "null"}},
            "patternProperties": {"^c": {"type": "string"}},
            "additionalProperties": false,
            "propertyNames": {"maxLength": 3},
            "required": ["a"],
            "minProperties": 1,
            "maxProperties": 2,
        });
        // The two properties are one class, and so one variable.
        assert_eq!(
            terms(&schema, &json!(true))[0],
            "all(pprop(l2: x2), pprop(l3: x2), pprop(l4: x3), pprop(l6: x4), pnames(x5), \
             preq(l2), minprops(1), maxprops(2))"
        );
        assert_eq!(
            languages(&schema),
            [
                r#"one of ["a"]"#,
                r#"one of ["b"]"#,
                r#""^c""#,
                r#"none of ["^c", one of ["a", "b"]]"#,
            ]
        );
        // Without a pattern, what `additionalProperties` is about is every name but a few.
        let closed = json!({"properties": {"a": {}, "b": {}}, "additionalProperties": false});
        assert_eq!(languages(&closed)[2], r#"any string but "a", "b""#);
        assert_eq!(
            languages(&json!({"additionalProperties": false})),
            ["any string"]
        );
        // At least no property is what every object has.
        assert_eq!(term(&json!({"minProperties": 0})), "true");
        assert_eq!(term(&json!({"maxProperties": 0})), "maxprops(0)");
    }

    #[test]
    fn a_pattern_of_names_that_is_not_read_is_a_leaf_and_so_is_what_depends_on_it() {
        let schema = json!({
            "properties": {"a": {"type": "null"}},
            "patternProperties": {r"\bb": {"type": "null"}, "^c": {"type": "null"}},
            "additionalProperties": false,
        });
        let term = term(&schema);
        assert!(
            term.starts_with(r#"all(pprop(l2: x2), ?[patternProperties "\\bb" #"#),
            "{term}"
        );
        assert!(
            term.contains(r#"], pprop(l3: x2), ?[additionalProperties #"#),
            "{term}"
        );
        assert!(
            term.ends_with(r#" but for ["a"] and ["\\bb","^c"]])"#),
            "{term}"
        );
        // A count that was too large to keep is a leaf too.
        let huge = self::term(&json!({"minProperties": 1e30}));
        assert!(huge.starts_with("?[minProperties @"), "{huge}");
    }

    /// What the terms of a schema that are about a language are about, as text.
    fn languages(schema: &Value) -> Vec<String> {
        let truth = json!(true);
        let graph = parse(schema, &truth).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX);
        let (a, _) = lower(&graph, &mut context).unwrap();
        let body = context.terms.variable(a).body;
        let parts = match context.terms.term(body) {
            crate::term::Term::AllOf(parts) => parts.to_vec(),
            _ => vec![body],
        };
        let shown = parts
            .iter()
            .filter_map(|part| match context.terms.term(*part) {
                crate::term::Term::Patt(language) | crate::term::Term::PProp(language, _) => {
                    Some(context.languages.show(*language))
                }
                _ => None,
            });
        shown.collect()
    }

    #[test]
    fn a_keyword_about_strings_is_a_term() {
        let schema = json!({"minLength": 2, "maxLength": 3, "pattern": "^a", "format": "date"});
        assert_eq!(
            term(&schema),
            "all(minlen(2), maxlen(3), patt(l2), patt(l3))"
        );
        assert_eq!(languages(&schema), [r#""^a""#, "format date"]);
        // At least no character is what every string has.
        assert_eq!(term(&json!({"minLength": 0})), "true");
        assert_eq!(term(&json!({"maxLength": 0})), "maxlen(0)");
        // One pattern is one language wherever it stands, and so is one format.
        let twice =
            json!({"pattern": "a", "format": "uuid", "not": {"pattern": "a", "format": "uuid"}});
        assert_eq!(
            terms(&twice, &json!(true)),
            [
                "all(not x2, patt(l2), patt(l3))",
                "true",
                "all(patt(l2), patt(l3))"
            ]
        );
        // What is not read as a language stays a leaf: a pattern that asks where a word
        // ends, one that the `regex` crate does not take, and a format that is not modelled.
        assert_eq!(
            term(&json!({"pattern": r"a\b", "format": "hostname"})),
            r#"all(?[pattern "a\\b"], ?[format "hostname"])"#
        );
        assert_eq!(
            term(&json!({"pattern": "a(?=b)"})),
            r#"?[pattern "a(?=b)"]"#
        );
        assert_eq!(
            term(&json!({"format": "no format"})),
            r#"?[format "no format"]"#
        );
    }

    #[test]
    fn every_other_keyword_is_a_leaf_with_what_it_holds() {
        let schema = json!({
            "minItems": 4,
            "uniqueItems": true,
            "maxItems": 5,
        });
        assert_eq!(
            term(&schema),
            "all(?[minItems 4], ?[maxItems 5], ?[uniqueItems])"
        );
        assert_eq!(term(&json!({"uniqueItems": false})), "true");
        // `minContains` says nothing without `contains`.
        assert_eq!(term(&json!({"minContains": 2, "maxContains": 3})), "true");
    }

    #[test]
    fn a_leaf_says_which_types_it_is_about_and_where_it_was_first() {
        let a = json!({"type": "array", "minItems": 1});
        let b = json!({"minItems": 1, "$dynamicRef": "#here", "$dynamicAnchor": "here"});
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
            (side, leaf.location(&graph))
        };
        // A dynamic reference may be about any instance, and no other is like it.
        assert_eq!(leaves[0].domain, TypeSet::ALL);
        assert_eq!(place(leaves[0]), (Side::B, "#/$dynamicRef".to_owned()));
        // The leaf of `minItems` is about arrays. A has it too, and A is lowered first.
        assert_eq!(leaves[1].domain, ARRAY);
        assert_eq!(place(leaves[1]), (Side::A, "#/minItems".to_owned()));
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
        // The schema and its two properties. What `items` holds is inside a leaf.
        assert_eq!(terms.variables().count(), 3);

        // One property changes. The variables of A and B differ, and so does the term of
        // that property, but the terms of what stayed are shared.
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
        // A and B, the name, which they share, and the two ages.
        assert_eq!(terms.variables().count(), 5);
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
        // The schema of a property has a variable, and a cycle through it is one of terms.
        let chain = json!({"properties": {"next": {"$ref": "#"}}});
        assert_eq!(terms(&chain, &json!(true)), ["pprop(l2: x2)", "true", "x0"]);
    }

    #[test]
    fn a_dynamic_reference_is_found_wherever_a_schema_leads_to_it() {
        let found = |a: &Value, b: &Value| {
            let graph = parse(a, b).unwrap().link().unwrap();
            let node = dynamic_reference(&graph)?;
            let location = graph.keyword_location(node, "$dynamicRef");
            Some((graph.node(node).side, location))
        };
        let at = |side, location: &str| Some((side, location.to_owned()));
        let plain = json!({"type": "null"});
        assert_eq!(found(&plain, &plain), None);

        // Under a keyword that is a leaf, and behind a reference.
        let inside = json!({
            "$dynamicAnchor": "node",
            "properties": {"child": {"items": {"$dynamicRef": "#node"}}},
        });
        let place = "#/properties/child/items/$dynamicRef";
        assert_eq!(found(&plain, &inside), at(Side::B, place));
        let behind = json!({
            "$ref": "#/$defs/tree",
            "$defs": {"tree": {"$dynamicAnchor": "node", "not": {"$dynamicRef": "#node"}}},
        });
        let place = "#/$defs/tree/not/$dynamicRef";
        assert_eq!(found(&behind, &plain), at(Side::A, place));
        // The one of A comes first.
        assert_eq!(found(&behind, &inside), at(Side::A, place));

        // A definition that nothing leads to is not in the way, and neither is an anchor.
        let unused = json!({
            "$dynamicAnchor": "node",
            "$defs": {"tree": {"$dynamicRef": "#node"}},
        });
        assert_eq!(found(&unused, &plain), None);
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
