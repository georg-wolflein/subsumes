//! From the schema graph to terms.
//!
//! Every schema that the check can reach in place, through a connective or a reference, gets
//! a variable, and the term of the variable says what its keywords say. Schemas that say the
//! same share a variable, also between A and B.
//!
//! The engine models the types, `null`, the booleans, numbers, strings, objects, arrays, the
//! connectives and references. Every other keyword becomes a predicate that it does not
//! model, a leaf, which keeps the place where it stands. A leaf says something only about
//! the instances its keyword is about: `uniqueItems` about arrays, and so a number
//! satisfies it. The terms about numbers, about strings, about objects and about arrays
//! are the same in that: a string satisfies `minimum`, and a number satisfies `minLength`,
//! `required` and `minItems`.
//!
//! A schema that is the value of a property or an item of an array is not reached in
//! place: it is asked of a value inside the instance. It has a variable too, which the
//! term about the property or the item names.
//!
//! A constant that is an array or an object is taken apart in the same way: the term says
//! how many items or which properties there are, and names a variable for each value
//! inside, whose term is that the instance is that value.

mod classes;

use std::collections::{HashMap, VecDeque};

use serde_json::Value;

use self::classes::written;
use crate::context::{Context, Exhausted};
use crate::formats;
use crate::normalize::DEEPEST;
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
        constants: HashMap::new(),
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
    /// The variable of each value inside a constant, by the term that says "the instance
    /// is this value".
    constants: HashMap<TermId, VarId>,
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

    /// The term for "the instance is this value", for a value of `const` or `enum`.
    ///
    /// A value that is nested deeper than an instance may be is not taken apart: it is of
    /// one type and a leaf over that type, which is unlike every other.
    fn constant(&mut self, id: NodeId, keyword: &'static str, value: &Value) -> TermId {
        if too_deep(value) {
            let kind = if value.is_array() { ARRAY } else { OBJECT };
            let is_it = self.leaf_of_its_own(kind, id, keyword);
            let of_type = self.context.terms.type_is(kind);
            return self.context.terms.all_of([of_type, is_it]);
        }
        self.value(id, value)
    }

    /// The term for "the instance is this value". `null`, the booleans, the numbers and the
    /// strings are terms of their own. An array is an array of so many items, each of them
    /// the value at its position, and an object is an object with these properties and no
    /// other, each of them the value of its name.
    ///
    /// This goes as deep as the value does, which is no deeper than an instance may be.
    fn value(&mut self, id: NodeId, value: &Value) -> TermId {
        match value {
            Value::Null => self.context.terms.type_is(NULL),
            Value::Bool(value) => self.context.terms.bool_const(*value),
            Value::Number(number) => self.context.terms.num_const(exact(number)),
            Value::String(word) => self.context.terms.str_const(word),
            Value::Array(items) => {
                let mut parts = vec![self.context.terms.type_is(ARRAY)];
                for (position, item) in items.iter().enumerate() {
                    let variable = self.inside_a_constant(id, item);
                    parts.push(self.context.terms.item(position as u64, variable));
                }
                let count = items.len() as u64;
                parts.push(self.context.terms.min_its(count));
                parts.push(self.context.terms.max_its(count));
                self.context.terms.all_of(parts)
            }
            Value::Object(members) => {
                let mut parts = vec![self.context.terms.type_is(OBJECT)];
                for (name, member) in members {
                    let variable = self.inside_a_constant(id, member);
                    let named = self.context.languages.words([name.as_str()]);
                    parts.push(self.context.terms.p_prop(named, variable));
                    parts.push(self.context.terms.p_req(named));
                }
                // Every name is there, so with no more properties than names there is no
                // other.
                parts.push(self.context.terms.max_props(members.len() as u64));
                self.context.terms.all_of(parts)
            }
        }
    }

    /// The variable of a value inside a constant. Its term is "the instance is this
    /// value", and a value that is met again has the variable that it had before. It
    /// stands where the constant does.
    fn inside_a_constant(&mut self, id: NodeId, value: &Value) -> VarId {
        let body = self.value(id, value);
        let terms = &mut self.context.terms;
        let variable = *self.constants.entry(body).or_insert_with(|| {
            let variable = terms.new_variable(id);
            terms.variable_mut(variable).body = body;
            variable
        });
        let side = self.graph.node(id).side as usize;
        terms.variable_mut(variable).sides[side] = true;
        variable
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
        // The item at each of the first positions satisfies the schema of its position,
        // and every item after those the schema of `items`.
        for (position, schema) in keywords.prefix_items.iter().enumerate() {
            let variable = self.variable(*schema);
            parts.push(self.context.terms.item(position as u64, variable));
        }
        if let Some(schema) = keywords.items {
            let variable = self.variable(schema);
            let from = keywords.prefix_items.len() as u64;
            parts.push(self.context.terms.add_its(from, variable));
        }
        // `contains` asks for an item that satisfies its schema. `minContains` and
        // `maxContains` say how many such items there are to be, and nothing without it.
        // At least one is what it asks by itself, and at least none is nothing asked. Any
        // other number is not modelled: then the three are one predicate.
        if let Some(schema) = keywords.contains {
            match (keywords.min_contains, keywords.max_contains) {
                (None | Some(Count::Of(1)), None) => {
                    let variable = self.variable(schema);
                    parts.push(self.context.terms.contains(variable));
                }
                (Some(Count::Of(0)), None) => {}
                (Some(Count::Beyond), _) | (_, Some(Count::Beyond)) => {
                    parts.push(self.leaf_of_its_own(ARRAY, id, "contains"));
                }
                (least, most) => {
                    let bound = |count| match count {
                        Some(Count::Of(count)) => count.to_string(),
                        _ => "unset".to_owned(),
                    };
                    let (least, most) = (bound(least), bound(most));
                    let key = format!("contains {} from {least} to {most}", self.class(schema));
                    // The leaf stands at the bound that makes it one.
                    let keyword = if keywords.max_contains.is_some() {
                        "maxContains"
                    } else {
                        "minContains"
                    };
                    parts.push(self.leaf(ARRAY, id, keyword, key));
                }
            }
        }
        // A count that was too large to keep stays a leaf.
        match keywords.min_items {
            Some(Count::Of(least)) => parts.push(self.context.terms.min_its(least)),
            beyond => self.count(ARRAY, id, "minItems", beyond, parts),
        }
        match keywords.max_items {
            Some(Count::Of(most)) => parts.push(self.context.terms.max_its(most)),
            beyond => self.count(ARRAY, id, "maxItems", beyond, parts),
        }
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

/// Whether a value holds more arrays and objects inside one another than an instance may:
/// more than [`DEEPEST`], itself among them. This goes no deeper than that.
fn too_deep(value: &Value) -> bool {
    let mut pending = vec![(value, 1_u32)];
    while let Some((value, depth)) = pending.pop() {
        let inside: Box<dyn Iterator<Item = &Value>> = match value {
            Value::Array(items) => Box::new(items.iter()),
            Value::Object(members) => Box::new(members.values()),
            _ => continue,
        };
        if depth > DEEPEST {
            return true;
        }
        pending.extend(inside.map(|value| (value, depth + 1)));
    }
    false
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
    fn a_constant_is_a_term() {
        assert_eq!(term(&json!({"const": null})), "type(null)");
        assert_eq!(term(&json!({"const": true})), "is(true)");
        assert_eq!(term(&json!({"const": "a"})), r#"is("a")"#);
        assert_eq!(
            term(&json!({"enum": [null, false, 1, "a", {}, []]})),
            r#"any(type(null), is(false), is(1), is("a"), all(type(object), maxprops(0)), all(type(array), maxits(0)))"#
        );
        assert_eq!(term(&json!({"enum": []})), "false");
        // One value is one term, whichever keyword holds it and however it is written.
        assert_eq!(term(&json!({"enum": [1]})), term(&json!({"const": 1})));
        assert_eq!(term(&json!({"const": 1.0})), term(&json!({"const": 1})));
        assert_eq!(term(&json!({"const": 0.5})), "is(0.5)");
        assert_eq!(term(&json!({"enum": ["a"]})), term(&json!({"const": "a"})));
    }

    #[test]
    fn a_constant_that_is_an_array_or_an_object_names_a_variable_for_each_value_inside() {
        // So many items, each the value at its position. A value that is met again has
        // the variable that it had before.
        let list = json!({"const": [1, "a", 1.0]});
        assert_eq!(
            terms(&list, &json!(true)),
            [
                "all(type(array), item(0: x2), item(1: x3), item(2: x2), minits(3), maxits(3))",
                "true",
                "is(1)",
                r#"is("a")"#,
            ]
        );
        // These properties and no other, each the value of its name.
        let record = json!({"const": {"a": null, "b": [null]}});
        assert_eq!(
            terms(&record, &json!(true)),
            [
                "all(type(object), pprop(l2: x2), preq(l2), pprop(l3: x3), preq(l3), maxprops(2))",
                "true",
                "type(null)",
                "all(type(array), item(0: x2), minits(1), maxits(1))",
            ]
        );
        // One value is one term, however the numbers in it are written, and a variable of
        // A is one of B too.
        let (a, b) = (json!({"const": [[1.0]]}), json!({"enum": [[[1]]]}));
        let (terms, of_a, of_b) = lowered(&a, &b);
        assert_eq!(terms.variable(of_a).body, terms.variable(of_b).body);
        let inside: Vec<[bool; 2]> = terms.variables().map(|(_, inside)| inside.sides).collect();
        assert_eq!(
            inside,
            [[true, false], [false, true], [true, true], [true, true]]
        );
    }

    #[test]
    fn a_constant_that_is_nested_too_deep_is_a_leaf() {
        let nested = |levels: u32| {
            let mut value = json!(null);
            for _ in 0..levels {
                value = json!([value]);
            }
            value
        };
        // As deep as an instance may be, it is taken apart.
        let deepest = term(&json!({"const": nested(DEEPEST)}));
        assert!(
            deepest.starts_with("all(type(array), item(0: x") && !deepest.contains("?["),
            "{deepest}"
        );
        // One level more and it is a leaf, which is like no other: not the same value
        // elsewhere either.
        let too_deep = json!({"const": nested(DEEPEST + 1)});
        let (terms, of_a, of_b) = lowered(&too_deep, &too_deep);
        assert_ne!(of_a, of_b);
        let shown = terms.show(terms.variable(of_a).body);
        assert!(shown.starts_with("all(type(array), ?[const @"), "{shown}");
        // A value that is very much deeper is not gone through to its end.
        // It is built by hand: `json!` copies what it is given, level by level.
        let mut endless = json!(null);
        for _ in 0..100_000 {
            endless = Value::Object([("a".to_owned(), endless)].into_iter().collect());
        }
        let schema = Value::Object(
            [("enum".to_owned(), Value::Array(vec![json!(1), endless]))]
                .into_iter()
                .collect(),
        );
        let shown = term(&schema);
        assert!(
            shown.starts_with("any(is(1), all(type(object), ?[enum @"),
            "{shown}"
        );
        // Dropping the value takes a level of the stack for each of its own.
        std::mem::forget(schema);
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
        // A pattern that is one word between `^` and `$` is that word.
        let (pattern, property) = (
            json!({"patternProperties": {"^a$": {"type": "null"}}}),
            json!({"properties": {"a": {"type": "null"}}}),
        );
        assert_eq!(term(&pattern), term(&property));
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
    fn a_keyword_about_arrays_is_a_term() {
        let schema = json!({
            "prefixItems": [{"type": "null"}, false],
            "items": {"type": "string"},
            "contains": {"minimum": 1},
            "minItems": 4,
            "maxItems": 5,
        });
        assert_eq!(
            terms(&schema, &json!(true)),
            [
                "all(item(0: x2), item(1: x3), addits(2: x4), contains(x5), minits(4), maxits(5))",
                "true",
                "type(null)",
                "false",
                "type(string)",
                "min(1)",
            ]
        );
        // Without `prefixItems`, `items` is about every item.
        assert_eq!(term(&json!({"items": {}})), "addits(0: x2)");
        // At least no item is what every array has.
        assert_eq!(term(&json!({"minItems": 0})), "true");
        assert_eq!(term(&json!({"maxItems": 0})), "maxits(0)");
        // `contains` asks for one item, also when `minContains` says so, and for nothing
        // when `minContains` asks for none. The bounds say nothing without it.
        let one = json!({"contains": {}, "minContains": 1});
        assert_eq!(term(&one), "contains(x2)");
        assert_eq!(term(&json!({"contains": {}, "minContains": 0})), "true");
        assert_eq!(term(&json!({"minContains": 2, "maxContains": 3})), "true");
    }

    #[test]
    fn every_other_keyword_is_a_leaf_with_what_it_holds() {
        let schema = json!({
            "format": "hostname",
            "uniqueItems": true,
            "minItems": 1e30,
        });
        let shown = term(&schema);
        assert!(
            shown.starts_with(r#"all(?[format "hostname"], ?[minItems @"#),
            "{shown}"
        );
        assert!(shown.ends_with("?[uniqueItems])"), "{shown}");
        assert_eq!(term(&json!({"uniqueItems": false})), "true");
    }

    #[test]
    fn a_leaf_says_which_types_it_is_about_and_where_it_was_first() {
        let a = json!({"type": "array", "uniqueItems": true});
        let b = json!({"uniqueItems": true, "$dynamicRef": "#here", "$dynamicAnchor": "here"});
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
        // The leaf of `uniqueItems` is about arrays. A has it too, and A is lowered first.
        assert_eq!(leaves[1].domain, ARRAY);
        assert_eq!(place(leaves[1]), (Side::A, "#/uniqueItems".to_owned()));
    }

    #[test]
    fn keywords_that_depend_on_each_other_are_one_leaf() {
        let count = |text: &str| text.matches("?[").count();
        // The bounds of `contains` belong to it. More than one item, or a most, is not
        // modelled, and the leaf stands at the bound.
        let contains = term(&json!({"contains": {}, "minContains": 2}));
        assert!(
            contains.starts_with("?[contains #") && contains.ends_with("from 2 to unset]"),
            "{contains}"
        );
        let most = json!({"contains": {}, "minContains": 1, "maxContains": 3});
        let (terms, of_a, _) = lowered(&most, &json!(true));
        let shown = terms.show(terms.variable(of_a).body);
        assert!(
            shown.ends_with("from 1 to 3]") && count(&shown) == 1,
            "{shown}"
        );
        let crate::term::Term::Unknown(leaf) = terms.term(terms.variable(of_a).body) else {
            panic!("{shown} is no leaf");
        };
        assert_eq!(terms.leaf(*leaf).keyword, Some("maxContains"));
        // What the leaf holds is not opened: its schema has no variable.
        assert_eq!(terms.variables().count(), 2);
        // A most is not modelled with a least of none either, where `contains` by itself
        // would ask for nothing.
        let none_or_few = term(&json!({"contains": {}, "minContains": 0, "maxContains": 3}));
        assert!(none_or_few.ends_with("from 0 to 3]"), "{none_or_few}");
    }

    #[test]
    fn schemas_that_say_the_same_have_one_variable_and_one_leaf() {
        let a = json!({
            "type": "object",
            "properties": {"name": {"type": "string"}, "age": {"minimum": 0}},
            "uniqueItems": true,
        });
        let mut b = a.clone();
        let (terms, of_a, of_b) = lowered(&a, &b);
        assert_eq!(of_a, of_b);
        assert_eq!(terms.variable(of_a).sides, [true, true]);
        // The schema and its two properties.
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
        // The type, the two properties and the leaf of `uniqueItems`.
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
        // What a leaf holds is not opened, so the cycle through a `contains` that is
        // counted ends in the leaf.
        let counted = json!({"contains": {"$ref": "#"}, "maxContains": 1});
        assert_eq!(terms(&counted, &json!(true)).len(), 2);
        // The schema of a property has a variable, and a cycle through it is one of terms.
        // So has the schema of an item.
        let chain = json!({"properties": {"next": {"$ref": "#"}}});
        assert_eq!(terms(&chain, &json!(true)), ["pprop(l2: x2)", "true", "x0"]);
        let tree = json!({"items": {"$ref": "#"}});
        assert_eq!(terms(&tree, &json!(true)), ["addits(0: x2)", "true", "x0"]);
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
