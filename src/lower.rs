//! From the schema graph to terms.
//!
//! Every schema that the check can reach in place, through a connective or a reference, gets
//! a variable, and the term of the variable says what its keywords say. Schemas that say the
//! same share a variable, also between A and B.
//!
//! A `$dynamicRef` is a reference to the schema that it leads to in the dynamic scope that
//! it is reached in. A schema that is reached in two scopes has a variable for each, unless
//! it says the same in both.
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
mod scopes;

use std::collections::{BTreeSet, HashMap, VecDeque};

use serde_json::Value;

use self::classes::written;
use self::scopes::{Reached, ScopeId, Scopes};
use crate::context::{Context, Exhausted};
use crate::formats;
use crate::language::LanguageId;
use crate::normalize::DEEPEST;
use crate::rational::{Rational, exact};
use crate::schema::{Count, Graph, Keywords, NodeId, Schema, Type};
use crate::term::{InstanceType, TermId, TypeSet, VarId};

/// Gives A and B their terms, and returns the variables of the two.
///
/// # Errors
///
/// When the budget does not cover the work.
pub(crate) fn lower<'g>(
    graph: &'g Graph<'g>,
    context: &mut Context,
) -> Result<(VarId, VarId), Exhausted> {
    let scopes = Scopes::of(graph, &mut context.budget)?;
    let classes = classes::classes(graph, &scopes, &mut context.budget)?;
    // The classes are numbered from zero on, so an array holds the variable of each.
    let numbers = classes.iter().max().map_or(0, |last| *last as usize + 1);
    context.terms.reserve(scopes.len());
    let mut lowering = Lowering {
        graph,
        scopes: &scopes,
        classes: &classes,
        context,
        variables: vec![None; numbers],
        constants: HashMap::new(),
        pending: VecDeque::new(),
        scope: ScopeId::NOTHING,
        parts: Vec::new(),
    };
    let a = lowering.variable(graph.a);
    let b = lowering.variable(graph.b);
    while let Some((variable, reached)) = lowering.pending.pop_front() {
        let Reached { node, scope } = scopes.at(reached);
        lowering.scope = scope;
        let body = lowering.body(node)?;
        lowering.context.terms.variable_mut(variable).body = body;
    }

    // A variable stands for every schema of its class, on whichever side it is.
    for (index, class) in classes.iter().enumerate() {
        if let Some(variable) = lowering.variables[*class as usize] {
            let side = graph.node(scopes.at(index).node).side as usize;
            lowering.context.terms.variable_mut(variable).sides[side] = true;
        }
    }
    Ok((a, b))
}

struct Lowering<'g, 'c> {
    graph: &'g Graph<'g>,
    scopes: &'c Scopes<'g>,
    /// The class of each schema as it is reached, in the order of `scopes`.
    classes: &'c [u32],
    context: &'c mut Context,
    /// The variable of each class that has one, by the number of the class.
    variables: Vec<Option<VarId>>,
    /// The variable of each term that has one without being the term of a schema: of a
    /// value inside a constant, by the term that says "the instance is this value", and of
    /// what an item is to satisfy unless it is evaluated.
    constants: HashMap<TermId, VarId>,
    /// The variables that have no term yet, in the order in which they were made, each
    /// with the schema that gives it its term, as it is reached.
    pending: VecDeque<(VarId, usize)>,
    /// The dynamic scope of the schema whose term is being made. Every schema that the
    /// term names is reached from it.
    scope: ScopeId,
    /// What the keywords of the schema whose term is being made say, each a term. The one
    /// list serves every schema in turn.
    parts: Vec<TermId>,
}

const NULL: TypeSet = TypeSet::of(InstanceType::Null);
const NUMBER: TypeSet = TypeSet::of(InstanceType::Number);
const STRING: TypeSet = TypeSet::of(InstanceType::String);
const ARRAY: TypeSet = TypeSet::of(InstanceType::Array);
const OBJECT: TypeSet = TypeSet::of(InstanceType::Object);

impl<'g, 'c> Lowering<'g, 'c> {
    /// The variable of a schema, as it is reached from the schema whose term is being
    /// made.
    fn variable(&mut self, node: NodeId) -> VarId {
        self.variable_of(self.scopes.from(node, self.scope))
    }

    /// The variable of a schema as it is reached. The first schema of a class to ask gives
    /// the variable its term, and every schema of a class would give the same.
    fn variable_of(&mut self, reached: usize) -> VarId {
        let class = self.classes[reached] as usize;
        if let Some(variable) = self.variables[class] {
            return variable;
        }
        let variable = self
            .context
            .terms
            .new_variable(self.scopes.at(reached).node);
        self.variables[class] = Some(variable);
        self.pending.push_back((variable, reached));
        variable
    }

    /// The term that refers to a schema.
    fn refer(&mut self, node: NodeId) -> TermId {
        let variable = self.variable(node);
        self.context.terms.reference(variable)
    }

    /// The name of the class of a schema, for the key of a leaf that holds the schema.
    fn class(&self, node: NodeId) -> String {
        format!("#{}", self.classes[self.scopes.from(node, self.scope)])
    }

    /// The term of a schema: the conjunction of what its keywords say.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the ways in which the properties of an instance may
    /// be evaluated.
    fn body(&mut self, id: NodeId) -> Result<TermId, Exhausted> {
        let graph = self.graph;
        let keywords = match &graph.node(id).schema {
            Schema::Bool(true) => return Ok(self.context.terms.truth()),
            Schema::Bool(false) => return Ok(self.context.terms.falsity()),
            Schema::Object(keywords) => keywords,
        };
        let mut parts = std::mem::take(&mut self.parts);
        parts.clear();
        self.connectives(keywords, &mut parts);
        self.any_type(id, keywords, &mut parts);
        self.numbers(keywords, &mut parts);
        self.strings(id, keywords, &mut parts);
        self.arrays(id, keywords, &mut parts)?;
        self.objects(id, keywords, &mut parts)?;
        let body = self.context.terms.all_of(parts.iter().copied());
        self.parts = parts;
        Ok(body)
    }

    /// A predicate that the engine does not model. `key` is the keyword with what it holds;
    /// two leaves with one key over the same types are one predicate.
    fn leaf(&mut self, domain: TypeSet, id: NodeId, keyword: &'static str, key: String) -> TermId {
        self.context.terms.unknown(domain, key, id, keyword)
    }

    /// A leaf that is unlike every other, for a keyword whose meaning is not in its value.
    /// It is one leaf for each class that the schema is of: a schema that says one thing in
    /// one dynamic scope and another in the next may hold a schema in the keyword that does
    /// so too.
    fn leaf_of_its_own(&mut self, domain: TypeSet, id: NodeId, keyword: &'static str) -> TermId {
        let key = format!("{keyword} @{} of {}", id.index(), self.class(id));
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

    fn connectives(&mut self, keywords: &Keywords, parts: &mut Vec<TermId>) {
        if let Some(target) = keywords.reference {
            parts.push(self.refer(target));
        }
        if let Some(dynamic) = keywords.dynamic_reference {
            let target = self.scopes.resolved(dynamic, self.scope);
            parts.push(self.refer(target));
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
        let named = self.context.languages.word(name);
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
                    let named = self.context.languages.word(name);
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
        self.standing_for(id, body)
    }

    /// The variable that stands for a term and for no schema, such as a value inside a
    /// constant. A term that is met again has the variable that it had before. The variable
    /// stands where the schema `id` does.
    fn standing_for(&mut self, id: NodeId, body: TermId) -> VarId {
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

    fn arrays(
        &mut self,
        id: NodeId,
        keywords: &Keywords,
        parts: &mut Vec<TermId>,
    ) -> Result<(), Exhausted> {
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
        if let Some(schema) = keywords.unevaluated_items {
            parts.push(self.unevaluated_items(id, schema)?);
        }
        Ok(())
    }

    fn objects(
        &mut self,
        id: NodeId,
        keywords: &Keywords,
        parts: &mut Vec<TermId>,
    ) -> Result<(), Exhausted> {
        // A property with this name satisfies the schema.
        for (name, schema) in &keywords.properties {
            let variable = self.variable(*schema);
            let named = self.context.languages.word(name);
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
        if let Some(schema) = keywords.unevaluated_properties {
            parts.push(self.unevaluated_properties(id, schema)?);
        }
        Ok(())
    }

    /// What `unevaluatedProperties` says: every property that the schema around it has not
    /// evaluated satisfies its schema.
    ///
    /// Which properties are evaluated depends on the instance: a branch of `anyOf` that
    /// the instance satisfies evaluates the properties that it names, and one that it does
    /// not satisfy evaluates none. So the term is one of several ways: in each, the
    /// instance satisfies some of the schemas in place, and every property that those do
    /// not evaluate satisfies the schema of the keyword. The schemas that it does not
    /// satisfy are not named: with more of them satisfied, more is evaluated and less is
    /// asked, so the way that names all of them holds whenever one that names fewer does.
    ///
    /// Where the ways are not to be found, the keyword is a leaf of the class of the schema
    /// around it, on which everything that it says depends.
    fn unevaluated_properties(&mut self, id: NodeId, schema: NodeId) -> Result<TermId, Exhausted> {
        let here = self.scopes.from(id, self.scope);
        let Some(ways) = self.evaluated(here, true, &mut Vec::new(), Self::names)? else {
            let key = format!("unevaluatedProperties of {}", self.class(id));
            return Ok(self.leaf(OBJECT, id, "unevaluatedProperties", key));
        };
        let variable = self.variable(schema);
        let mut terms = Vec::with_capacity(ways.len());
        for way in ways {
            let mut parts: Vec<TermId> = way.given.into_iter().collect();
            // As `additionalProperties` is about the names that `properties` and
            // `patternProperties` leave.
            if let Some(names) = way.evaluated {
                let languages = &mut self.context.languages;
                let named = languages.words(names.words);
                let others = languages.outside(names.patterns.into_iter().chain([named]));
                parts.push(self.context.terms.p_prop(others, variable));
            }
            terms.push(self.context.terms.all_of(parts));
        }
        Ok(self.context.terms.any_of(terms))
    }

    /// What `unevaluatedItems` says: every item that the schema around it has not evaluated
    /// satisfies its schema. It is one of several ways, as `unevaluatedProperties` is.
    ///
    /// The schemas that the instance satisfies evaluate the items before a position, by
    /// `prefixItems`, and each item that the schema of a `contains` accepts. So every item
    /// from the position on satisfies the schema of the keyword or one of those of
    /// `contains`.
    fn unevaluated_items(&mut self, id: NodeId, schema: NodeId) -> Result<TermId, Exhausted> {
        let here = self.scopes.from(id, self.scope);
        let Some(ways) = self.evaluated(here, true, &mut Vec::new(), Self::positions)? else {
            let key = format!("unevaluatedItems of {}", self.class(id));
            return Ok(self.leaf(ARRAY, id, "unevaluatedItems", key));
        };
        let variable = self.variable(schema);
        let mut terms = Vec::with_capacity(ways.len());
        for way in ways {
            let mut parts: Vec<TermId> = way.given.into_iter().collect();
            if let Some(positions) = way.evaluated {
                let of = if positions.contained.is_empty() {
                    variable
                } else {
                    let either = std::iter::once(variable).chain(positions.contained);
                    let either: Vec<TermId> = either
                        .map(|variable| self.context.terms.reference(variable))
                        .collect();
                    let either = self.context.terms.any_of(either);
                    self.standing_for(id, either)
                };
                parts.push(self.context.terms.add_its(positions.from, of));
            }
            terms.push(self.context.terms.all_of(parts));
        }
        Ok(self.context.terms.any_of(terms))
    }

    /// The names of the properties that the keywords of a schema evaluate: `Some(None)` for
    /// every name, and `None` with a pattern that is not read as a language.
    /// `additionalProperties` is about every property that the other two keywords leave,
    /// and so is `unevaluatedProperties` about every one that anything leaves. In
    /// `outermost`, the schema whose `unevaluatedProperties` is being lowered, that keyword
    /// does not count.
    fn names(
        &mut self,
        keywords: &Keywords<'g>,
        _: ScopeId,
        outermost: bool,
    ) -> Option<Option<Names<'g>>> {
        if keywords.additional_properties.is_some()
            || (!outermost && keywords.unevaluated_properties.is_some())
        {
            return Some(None);
        }
        let mut names = Names {
            words: keywords.properties.iter().map(|(name, _)| *name).collect(),
            patterns: BTreeSet::new(),
        };
        for (pattern, _) in &keywords.pattern_properties {
            let matched = self.context.languages.pattern(pattern).ok()?;
            names.patterns.insert(matched);
        }
        Some(Some(names))
    }

    /// The positions of the items that the keywords of a schema evaluate: `Some(None)` for
    /// every position, with `items` and with an `unevaluatedItems` that is not the one
    /// being lowered. Otherwise those that `prefixItems` names, and each one that holds an
    /// item which the schema of `contains` accepts, however many `contains` asks for.
    fn positions(
        &mut self,
        keywords: &Keywords<'g>,
        scope: ScopeId,
        outermost: bool,
    ) -> Option<Option<Positions>> {
        if keywords.items.is_some() || (!outermost && keywords.unevaluated_items.is_some()) {
            return Some(None);
        }
        let contained = keywords.contains;
        let contained = contained.map(|schema| self.variable_of(self.scopes.from(schema, scope)));
        Some(Some(Positions {
            from: keywords.prefix_items.len() as u64,
            contained: contained.into_iter().collect(),
        }))
    }

    /// The ways in which a schema that an instance satisfies evaluates the properties or
    /// the items of the instance, or `None` if they are not to be found: where `own` does
    /// not say what the keywords of a schema evaluate, with a schema that leads back to
    /// itself in place, and deeper in place than [`IN_PLACE`].
    ///
    /// `outermost` is the schema whose `unevaluated` keyword is being lowered. `above`
    /// holds the schemas on the way down to this one.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the schemas that are looked at, or the ways. A
    /// schema costs a step each time it is looked at, which is once for every way in place
    /// that leads to it. And a way that joins a list is held against every way of the
    /// list, which costs a step for each.
    fn evaluated<E: Evaluates>(
        &mut self,
        reached: usize,
        outermost: bool,
        above: &mut Vec<usize>,
        own: Own<'g, 'c, E>,
    ) -> Result<Option<Vec<Way<E>>>, Exhausted> {
        self.context.budget.charge(1)?;
        let graph = self.graph;
        let Reached { node, scope } = self.scopes.at(reached);
        let Schema::Object(keywords) = &graph.node(node).schema else {
            return Ok(Some(vec![Way::nothing()]));
        };
        if above.contains(&reached) || above.len() >= IN_PLACE {
            return Ok(None);
        }
        let Some(evaluated) = own(self, keywords, scope, outermost) else {
            return Ok(None);
        };
        let mut ways = vec![Way {
            given: BTreeSet::new(),
            evaluated,
        }];

        above.push(reached);
        // The term that says that the instance satisfies a schema in place, and the ways
        // of that schema.
        let below = |lowering: &mut Self, schema: NodeId, above: &mut Vec<usize>| {
            let reached = lowering.scopes.from(schema, scope);
            let variable = lowering.variable_of(reached);
            let satisfied = lowering.context.terms.reference(variable);
            let ways = lowering.evaluated(reached, false, above, own)?;
            Ok::<_, Exhausted>((satisfied, ways))
        };
        // Whatever the instance satisfies, nothing more is evaluated.
        let nothing = || vec![Way::nothing()];
        macro_rules! found {
            ($ways:expr) => {
                match $ways {
                    Some(ways) => ways,
                    None => {
                        above.pop();
                        return Ok(None);
                    }
                }
            };
        }

        // What an instance that satisfies the schema satisfies in any case.
        let dynamic = keywords.dynamic_reference;
        let dynamic = dynamic.map(|dynamic| self.scopes.resolved(dynamic, scope));
        let always = keywords.all_of.iter().copied();
        for schema in always.chain(keywords.reference).chain(dynamic) {
            let (_, of_schema) = below(self, schema, above)?;
            ways = self.together(ways, found!(of_schema))?;
        }
        // A branch of `anyOf` that the instance satisfies or not. Of `oneOf` it satisfies
        // one, so the ways of two of its branches are never put together.
        for schema in &keywords.any_of {
            let (satisfied, of_schema) = below(self, *schema, above)?;
            let either = self.or(nothing(), found!(of_schema), satisfied)?;
            ways = self.together(ways, either)?;
        }
        if !keywords.one_of.is_empty() {
            let mut either = nothing();
            for schema in &keywords.one_of {
                let (satisfied, of_schema) = below(self, *schema, above)?;
                either = self.or(either, found!(of_schema), satisfied)?;
            }
            ways = self.together(ways, either)?;
        }
        // The condition evaluates what it does where the instance satisfies it, and
        // `then` with it. Where the instance does not, `else` does.
        if let Some(condition) = keywords.if_ {
            let (satisfied, of_condition) = below(self, condition, above)?;
            let mut met = found!(of_condition);
            if let Some(then) = keywords.then {
                let (_, of_then) = below(self, then, above)?;
                met = self.together(met, found!(of_then))?;
            }
            let mut either = self.or(nothing(), met, satisfied)?;
            if let Some(otherwise) = keywords.else_ {
                let (_, of_else) = below(self, otherwise, above)?;
                let unmet = self.context.terms.not(satisfied);
                either = self.or(either, found!(of_else), unmet)?;
            }
            ways = self.together(ways, either)?;
        }
        // A schema of `dependentSchemas` is asked of an object that has the property, and
        // so of no array: for the items of an instance it evaluates nothing.
        let dependent = keywords.dependent_schemas.iter();
        for (name, schema) in dependent.filter(|_| E::OF_OBJECTS) {
            let present = self.has_property(name);
            let (_, of_schema) = below(self, *schema, above)?;
            let either = self.or(nothing(), found!(of_schema), present)?;
            ways = self.together(ways, either)?;
        }
        above.pop();
        Ok(Some(ways))
    }

    /// Every way of the one list with every way of the other.
    fn together<E: Evaluates>(
        &mut self,
        one: Vec<Way<E>>,
        other: Vec<Way<E>>,
    ) -> Result<Vec<Way<E>>, Exhausted> {
        let mut ways = Vec::new();
        for first in &one {
            for second in &other {
                self.add(&mut ways, first.with(second))?;
            }
        }
        Ok(ways)
    }

    /// The ways of `either`, or else those of `ways` where the instance satisfies `term`.
    fn or<E: Evaluates>(
        &mut self,
        mut either: Vec<Way<E>>,
        ways: Vec<Way<E>>,
        term: TermId,
    ) -> Result<Vec<Way<E>>, Exhausted> {
        for way in ways {
            self.add(&mut either, way.given(term))?;
        }
        Ok(either)
    }

    /// Adds a way to a list, unless a way of the list says as much. The ways of the list
    /// that say no more than the new one go. Each way that the new one is held against
    /// costs a step.
    fn add<E: Evaluates>(&mut self, ways: &mut Vec<Way<E>>, way: Way<E>) -> Result<(), Exhausted> {
        self.context.budget.charge(ways.len() as u64)?;
        if ways.iter().any(|other| way.says_no_more_than(other)) {
            return Ok(());
        }
        ways.retain(|other| !other.says_no_more_than(&way));
        ways.push(way);
        Ok(())
    }
}

/// How many schemas deep in place what a schema evaluates is looked for.
const IN_PLACE: usize = 64;

/// What the keywords of a schema evaluate, by the scope that the schema is reached in and
/// by whether it is the schema whose `unevaluated` keyword is being lowered: `Some(None)`
/// for everything, and `None` if that is not to be said.
type Own<'g, 'c, E> = fn(&mut Lowering<'g, 'c>, &Keywords<'g>, ScopeId, bool) -> Option<Option<E>>;

/// What a schema evaluates of an instance: properties by their names, or items by their
/// positions.
trait Evaluates: Clone + Default {
    /// Whether it is the properties of an object that are evaluated, and not the items of
    /// an array.
    const OF_OBJECTS: bool;

    /// What this and the other evaluate together.
    fn with(&self, other: &Self) -> Self;

    /// Whether the other evaluates all of this.
    fn within(&self, other: &Self) -> bool;
}

/// The names of the properties that a schema evaluates: these words, and what these
/// patterns match.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Names<'g> {
    words: BTreeSet<&'g str>,
    patterns: BTreeSet<LanguageId>,
}

impl Evaluates for Names<'_> {
    const OF_OBJECTS: bool = true;

    fn with(&self, other: &Self) -> Self {
        Self {
            words: self.words.union(&other.words).copied().collect(),
            patterns: self.patterns.union(&other.patterns).copied().collect(),
        }
    }

    fn within(&self, other: &Self) -> bool {
        self.words.is_subset(&other.words) && self.patterns.is_subset(&other.patterns)
    }
}

/// The positions of the items that a schema evaluates: those before `from`, and each one
/// with an item that the schema of one of these variables accepts.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Positions {
    from: u64,
    contained: BTreeSet<VarId>,
}

impl Evaluates for Positions {
    const OF_OBJECTS: bool = false;

    fn with(&self, other: &Self) -> Self {
        Self {
            from: self.from.max(other.from),
            contained: self.contained.union(&other.contained).copied().collect(),
        }
    }

    fn within(&self, other: &Self) -> bool {
        self.from <= other.from && self.contained.is_subset(&other.contained)
    }
}

/// One way in which a schema evaluates the properties or the items of an instance that it
/// accepts: where the instance satisfies every term of `given`, this much is evaluated, or
/// everything where it is `None`.
#[derive(Debug, Clone)]
struct Way<E> {
    given: BTreeSet<TermId>,
    evaluated: Option<E>,
}

impl<E: Evaluates> Way<E> {
    /// Whatever the instance satisfies, nothing is evaluated.
    fn nothing() -> Self {
        Self {
            given: BTreeSet::new(),
            evaluated: Some(E::default()),
        }
    }

    fn given(mut self, term: TermId) -> Self {
        self.given.insert(term);
        self
    }

    /// Both ways at once: the instance satisfies what both ask, and what either evaluates
    /// is evaluated.
    fn with(&self, other: &Self) -> Self {
        let evaluated = match (&self.evaluated, &other.evaluated) {
            (Some(one), Some(other)) => Some(one.with(other)),
            _ => None,
        };
        Self {
            given: self.given.union(&other.given).copied().collect(),
            evaluated,
        }
    }

    /// Whether the other way asks no more of the instance and evaluates no less. Then
    /// this one adds nothing to a list that has the other.
    fn says_no_more_than(&self, other: &Self) -> bool {
        let evaluates_no_more = match (&self.evaluated, &other.evaluated) {
            (_, None) => true,
            (None, Some(_)) => false,
            (Some(one), Some(other)) => one.within(other),
        };
        other.given.is_subset(&self.given) && evaluates_no_more
    }
}

/// Whether a value holds more arrays and objects inside one another than an instance may:
/// more than [`DEEPEST`], itself among them. This goes no deeper than that.
fn too_deep(value: &Value) -> bool {
    // Most values hold no other.
    if !(value.is_array() || value.is_object()) {
        return false;
    }
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
        let mut context = Context::new(u64::MAX, crate::RegexDialect::default());
        let (a, b) = lower(&graph, &mut context).unwrap();
        (context.terms, a, b)
    }

    /// Whether a schema is lowered within a budget, against `true`.
    fn lowers(schema: &Value, budget: u64) -> bool {
        let truth = json!(true);
        let graph = parse(schema, &truth).unwrap().link().unwrap();
        lower(
            &graph,
            &mut Context::new(budget, crate::RegexDialect::default()),
        )
        .is_ok()
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
        let mut context = Context::new(u64::MAX, crate::RegexDialect::default());
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
        let b = json!({"uniqueItems": true, "format": "hostname"});
        let graph = parse(&a, &b).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX, crate::RegexDialect::default());
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
        // A format that is not modelled is about strings.
        assert_eq!(leaves[0].domain, STRING);
        assert_eq!(place(leaves[0]), (Side::B, "#/format".to_owned()));
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
        // What `unevaluatedItems` is about depends on the rest of its schema. It is a leaf
        // where the schema leads back to itself in place.
        let round = |first: Value| json!({"allOf": [{"$ref": "#"}], "prefixItems": first, "unevaluatedItems": false});
        let (a, b) = (round(json!([{}])), round(json!([{}, {}])));
        let (terms, of_a, of_b) = lowered(&a, &b);
        let last = |variable| match terms.term(terms.variable(variable).body) {
            crate::term::Term::AllOf(parts) => *parts.last().unwrap(),
            other => panic!("{other:?} is no conjunction"),
        };
        assert_ne!(last(of_a), last(of_b));
        assert!(
            terms
                .show(last(of_a))
                .starts_with("?[unevaluatedItems of #")
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
    fn unevaluated_properties_is_about_the_properties_that_nothing_evaluates() {
        // Next to nothing in place it says what `additionalProperties` says, in the same
        // term.
        let beside = |keyword: &str| {
            let mut schema = json!({"properties": {"a": {}}, "patternProperties": {"^b": {}}});
            schema[keyword] = json!(false);
            term(&schema)
        };
        assert_eq!(
            beside("unevaluatedProperties"),
            beside("additionalProperties")
        );
        assert_eq!(
            beside("unevaluatedProperties"),
            "all(pprop(l2: x2), pprop(l3: x2), pprop(l4: x3))"
        );
        // `additionalProperties` evaluates every property, so nothing is left to say.
        let both = json!({
            "properties": {"a": {}},
            "additionalProperties": {"type": "null"},
            "unevaluatedProperties": false,
        });
        assert_eq!(term(&both), "all(pprop(l2: x2), pprop(l3: x3))");
        // What a schema of `allOf` or the target of a reference evaluates is evaluated
        // whatever the instance is: `l4` is every name but `a` and `b`.
        let always = json!({
            "allOf": [{"properties": {"a": {}}}],
            "properties": {"b": {}},
            "unevaluatedProperties": false,
        });
        assert_eq!(term(&always), "all(x2, pprop(l2: x3), pprop(l4: x4))");
        let referred = json!({
            "$ref": "#/$defs/d",
            "unevaluatedProperties": false,
            "$defs": {"d": {"properties": {"a": {}}}},
        });
        assert_eq!(term(&referred), "all(x2, pprop(l3: x3))");
        // Neither a negated schema nor one beside it evaluates anything: `l1` is every
        // name.
        let negated = json!({"not": {"properties": {"a": {}}}, "unevaluatedProperties": false});
        assert_eq!(term(&negated), "all(not x2, pprop(l1: x3))");
        let cousins =
            json!({"allOf": [{"properties": {"a": {}}}, {"unevaluatedProperties": false}]});
        assert_eq!(terms(&cousins, &json!(true))[3], "pprop(l1: x5)");
    }

    #[test]
    fn what_is_evaluated_depends_on_the_schemas_that_the_instance_satisfies() {
        // The last part of the term: one way for each choice of schemas in place that
        // evaluate something. `l1` is every name, so the first way is an object of which
        // every property satisfies the schema of the keyword.
        let ways = |mut schema: Value| {
            schema["unevaluatedProperties"] = json!(false);
            let shown = term(&schema);
            let (_, ways) = shown.split_once(", any(pprop(l1: ").expect(&shown);
            ways.strip_suffix("))").expect(&shown).to_owned()
        };
        // A branch of `anyOf` that the instance satisfies. One that evaluates nothing is no
        // way of its own.
        let any = json!({"anyOf": [{"properties": {"a": {}}}, {"required": ["b"]}]});
        assert_eq!(ways(any), "x4), all(x2, pprop(l3: x4))");
        // Two that are both satisfied evaluate no more than the second of these does, so
        // that is no way of its own either.
        let within = json!({
            "anyOf": [{"properties": {"a": {}}}, {"properties": {"a": {}, "b": {}}}],
        });
        assert_eq!(
            ways(within),
            "x4), all(x3, pprop(l3: x4)), all(x2, pprop(l5: x4))"
        );
        // Two with other names are a way together.
        let apart = json!({"anyOf": [{"properties": {"a": {}}}, {"properties": {"b": {}}}]});
        assert_eq!(
            ways(apart),
            "x4), all(x3, pprop(l3: x4)), all(x2, pprop(l5: x4)), all(x2, x3, pprop(l7: x4))"
        );
        // Of `oneOf` an instance satisfies one.
        let one = json!({"oneOf": [{"properties": {"a": {}}}, {"properties": {"b": {}}}]});
        assert_eq!(
            ways(one),
            "x4), all(x2, pprop(l3: x4)), all(x3, pprop(l5: x4))"
        );
        // The condition and `then` where it is met, and `else` where it is not.
        let condition = json!({
            "if": {"properties": {"a": {"type": "null"}}},
            "then": {"properties": {"b": {}}},
            "else": {"properties": {"c": {}}},
        });
        assert_eq!(
            ways(condition),
            "x5), all(x2, pprop(l3: x5)), all(not x2, pprop(l5: x5))"
        );
        // A schema of `dependentSchemas` where the object has the property.
        let dependent = json!({"dependentSchemas": {"a": {"properties": {"b": {}}}}});
        assert_eq!(ways(dependent), "x3), all(preq(l2), pprop(l4: x3))");
        // A branch with an `unevaluatedProperties` of its own evaluates everything.
        let inner = json!({"anyOf": [{"properties": {"a": {}}, "unevaluatedProperties": {}}]});
        assert_eq!(ways(inner), "x3), x2");
        let inner = json!({"allOf": [{"unevaluatedProperties": true}]});
        assert_eq!(
            term(&json!({"allOf": inner["allOf"], "unevaluatedProperties": false})),
            "x2"
        );
    }

    #[test]
    fn unevaluated_properties_is_a_leaf_where_what_is_evaluated_is_not_found() {
        let leaf = |schema: &Value| {
            let shown = term(schema);
            assert!(shown.contains("?[unevaluatedProperties of #"), "{shown}");
        };
        // A schema that leads back to itself in place.
        leaf(&json!({"allOf": [{"$ref": "#"}], "unevaluatedProperties": false}));
        // A pattern that is not read as a language, here or in a schema in place.
        leaf(&json!({"patternProperties": {"\\bword": {}}, "unevaluatedProperties": false}));
        leaf(&json!({
            "anyOf": [{"patternProperties": {"\\bword": {}}}],
            "unevaluatedProperties": false,
        }));
        // Schemas in place, one in the other, deeper than they are followed.
        let nested = |depth: usize| {
            let mut schema = json!({"properties": {"a": {}}});
            for _ in 0..depth {
                schema = json!({"allOf": [schema]});
            }
            schema["unevaluatedProperties"] = json!(false);
            schema
        };
        leaf(&nested(IN_PLACE));
        assert!(!term(&nested(IN_PLACE - 1)).contains('?'));
    }

    #[test]
    fn an_unevaluated_keyword_that_is_a_leaf_is_about_its_own_type() {
        // Schemas in place, one in the other, deeper than they are followed.
        let deep = |keyword: &str| {
            let mut schema = json!({});
            for _ in 0..IN_PLACE {
                schema = json!({"allOf": [schema]});
            }
            schema[keyword] = json!(false);
            schema
        };
        let verdict = |a: &Value, b: &Value| crate::Checker::new().subsumes(a, b).unwrap();
        let depends =
            |a: &Value, b: &Value| matches!(verdict(a, b), crate::Verdict::Unknown { .. });
        let (objects, arrays) = (json!({"type": "object"}), json!({"type": "array"}));
        // What the keyword says of arrays is not known, and it says nothing of objects.
        assert_eq!(
            verdict(&deep("unevaluatedItems"), &objects),
            crate::Verdict::Yes
        );
        assert!(depends(&deep("unevaluatedItems"), &arrays));
        assert_eq!(
            verdict(&deep("unevaluatedProperties"), &arrays),
            crate::Verdict::Yes
        );
        assert!(depends(&deep("unevaluatedProperties"), &objects));
    }

    #[test]
    fn the_ways_of_evaluating_cost_steps_where_they_multiply() {
        // So many schemas of `anyOf`, each with a property of its own, in one `allOf`.
        let choices = |count: usize| {
            let choice = |name: usize| json!({"anyOf": [{"properties": {format!("p{name}"): {}}}, {"type": "object"}]});
            json!({
                "allOf": (0..count).map(choice).collect::<Vec<_>>(),
                "unevaluatedProperties": false,
            })
        };
        // A way that joins a list is held against every way of the list, at a step each, and
        // each choice doubles the ways. So eight choices cost far more than a thousand steps,
        // and forty more than any budget has.
        assert!(lowers(&choices(2), 1_000));
        assert!(!lowers(&choices(8), 1_000));
        assert!(!lowers(&choices(40), 100_000));
        // Without a choice there is one way, which is held against nothing, however many
        // schemas there are in place.
        let property = |name: usize| json!({"properties": {format!("p{name}"): {}}});
        let plain = json!({
            "allOf": (0..30).map(property).collect::<Vec<_>>(),
            "unevaluatedProperties": false,
        });
        assert!(lowers(&plain, 1_000));

        // A schema is looked at once for every way in place that leads to it, at a step
        // each. Each definition here is two references to the one before, so the first is
        // reached in two ways, in four, in eight: twelve definitions are thousands of looks,
        // and thirty are more than any budget has. More of them are deeper in place than is
        // followed.
        let doubled = |levels: usize| {
            let mut definitions = Map::new();
            definitions.insert("d0".to_owned(), json!({"properties": {"a": {}}}));
            for level in 1..=levels {
                let before = json!({"$ref": format!("#/$defs/d{}", level - 1)});
                definitions.insert(format!("d{level}"), json!({"allOf": [before, before]}));
            }
            json!({
                "$ref": format!("#/$defs/d{levels}"),
                "unevaluatedProperties": false,
                "$defs": definitions,
            })
        };
        assert!(lowers(&doubled(3), 1_000));
        assert!(!lowers(&doubled(12), 1_000));
        assert!(!lowers(&doubled(30), 100_000));
        // The walk for `unevaluatedItems` is the same one.
        let mut items = doubled(12);
        items["$defs"]["d0"] = json!({"prefixItems": [{}]});
        let keywords = items.as_object_mut().unwrap();
        let schema = keywords.remove("unevaluatedProperties").unwrap();
        keywords.insert("unevaluatedItems".to_owned(), schema);
        assert!(!lowers(&items, 1_000));
    }

    #[test]
    fn unevaluated_items_is_about_the_items_that_nothing_evaluates() {
        // Next to nothing in place it says what `items` says, in the same term.
        let after_one = |keyword: &str| {
            let mut schema = json!({"prefixItems": [{}]});
            schema[keyword] = json!(false);
            term(&schema)
        };
        assert_eq!(after_one("unevaluatedItems"), after_one("items"));
        assert_eq!(after_one("items"), "all(item(0: x2), addits(1: x3))");
        // `items` evaluates every item, and so does an `unevaluatedItems` in place.
        let both = json!({"items": {"type": "null"}, "unevaluatedItems": false});
        assert_eq!(term(&both), "addits(0: x2)");
        let inner = json!({"allOf": [{"unevaluatedItems": true}], "unevaluatedItems": false});
        assert_eq!(term(&inner), "x2");
        // The longest list of first items counts, here or in a schema of `allOf`.
        let longer = json!({
            "allOf": [{"prefixItems": [{}, {}]}],
            "prefixItems": [{}],
            "unevaluatedItems": false,
        });
        assert_eq!(term(&longer), "all(x2, item(0: x3), addits(2: x4))");
        // A schema beside the one with the keyword evaluates nothing for it.
        let cousins = json!({"allOf": [{"prefixItems": [{}]}, {"unevaluatedItems": false}]});
        assert_eq!(terms(&cousins, &json!(true))[3], "addits(0: x5)");

        // An item that the schema of `contains` accepts is evaluated, wherever it is. So
        // every item satisfies that schema or the one of the keyword: `x4` is either.
        let contained = json!({"contains": {"type": "null"}, "unevaluatedItems": false});
        assert_eq!(
            terms(&contained, &json!(true)),
            [
                "all(contains(x2), addits(0: x4))",
                "true",
                "type(null)",
                "false",
                "any(x3, x2)"
            ]
        );
        // That is so however many such items `contains` asks for, which is a leaf.
        let counted = json!({
            "prefixItems": [{}],
            "contains": {"type": "null"},
            "maxContains": 2,
            "unevaluatedItems": {"type": "string"},
        });
        let shown = terms(&counted, &json!(true));
        assert_eq!(
            shown[0],
            "all(item(0: x2), ?[contains #0 from unset to 2], addits(1: x5))"
        );
        assert_eq!(shown[5], "any(x4, x3)");
        // Two schemas of `contains` in place are either of them.
        let two = json!({
            "allOf": [{"contains": {"type": "null"}}, {"contains": {"type": "string"}}],
            "unevaluatedItems": false,
        });
        let shown = terms(&two, &json!(true));
        assert_eq!(shown[0], "all(x2, x3, addits(0: x7))");
        assert_eq!(shown[7], "any(x6, x4, x5)");
    }

    #[test]
    fn which_items_are_evaluated_depends_on_the_schemas_that_the_instance_satisfies() {
        // A branch that names the first item, and one that asks for a null. With neither
        // satisfied every item is unevaluated, with the second every item but a null, with
        // the first every one after the first, and with both every one after it but a
        // null. `x5` is the schema of the keyword, and `x6` is that or a null.
        let either = json!({
            "anyOf": [{"prefixItems": [{}]}, {"contains": {"type": "null"}}],
            "unevaluatedItems": false,
        });
        let shown = terms(&either, &json!(true));
        let ways = "any(addits(0: x5), all(x3, addits(0: x6)), all(x2, addits(1: x5)), all(x2, x3, addits(1: x6)))";
        assert_eq!(shown[0], format!("all(any(x2, x3), {ways})"));
        assert_eq!(shown[6], "any(x5, x4)");
        // Where the condition is met it evaluates with `then`, and the longer of the two
        // lists counts. Where it is not, `else` evaluates every item here.
        let condition = json!({
            "if": {"prefixItems": [{"type": "null"}]},
            "then": {"prefixItems": [{}, {}]},
            "else": {"items": {}},
            "unevaluatedItems": false,
        });
        let ways = "any(addits(0: x5), all(x2, addits(2: x5)), not x2)";
        assert_eq!(
            term(&condition),
            format!("all(any(not x2, x3), any(x2, x4), {ways})")
        );
        // A schema of `dependentSchemas` is asked of objects, so there is one way, in
        // which no item is evaluated.
        let dependent = json!({
            "dependentSchemas": {"a": {"items": {}}},
            "unevaluatedItems": false,
        });
        let shown = term(&dependent);
        assert!(
            shown.ends_with("not preq(l2), x2), addits(0: x3))"),
            "{shown}"
        );
        // The keyword is a leaf where a schema leads back to itself in place.
        let round = json!({"allOf": [{"$ref": "#"}], "unevaluatedItems": false});
        assert!(term(&round).contains("?[unevaluatedItems of #"));
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

    /// A list whose items are what the schema that led to it says they are: by way of
    /// `strings` they are strings, and by itself it takes any item.
    fn lists() -> Value {
        json!({
            "$id": "https://example.com/root",
            "properties": {"a": {"$ref": "strings"}, "b": {"$ref": "list"}},
            "$defs": {
                "strings": {
                    "$id": "strings",
                    "$ref": "list",
                    "$defs": {"item": {"$dynamicAnchor": "item", "type": "string"}},
                },
                "list": {
                    "$id": "list",
                    "items": {"$dynamicRef": "#item"},
                    "$defs": {"item": {"$dynamicAnchor": "item"}},
                },
            },
        })
    }

    #[test]
    fn a_dynamic_reference_is_a_reference_to_what_it_leads_to_in_its_scope() {
        // The list has a variable for each of the two ways to it. `x2` and `x3` are the
        // schemas of the two properties, and `x4` is `strings`. `x6` is the list by way of
        // `strings`: its items are `x8`, which refers to the anchor of `strings`, `x10`.
        // `x5` is the list by itself: its items are `x7`, which refers to its own anchor.
        assert_eq!(
            terms(&lists(), &json!(true)),
            [
                "all(pprop(l2: x2), pprop(l3: x3))",
                "true",
                "x4",
                "x5",
                "x6",
                "addits(0: x7)",
                "addits(0: x8)",
                "x9",
                "x10",
                "true",
                "type(string)",
            ]
        );

        // Where both ways lead to schemas that say the same, the list is one variable,
        // `x4`. `strings` is `x3` together with the schema of `b`: both refer to the list
        // and say nothing else.
        let mut alike = lists();
        alike["$defs"]["strings"]["$defs"]["item"] = json!({"$dynamicAnchor": "item"});
        assert_eq!(
            terms(&alike, &json!(true)),
            [
                "all(pprop(l2: x2), pprop(l3: x3))",
                "true",
                "x3",
                "x4",
                "addits(0: x5)",
                "x6",
                "true",
            ]
        );

        // A name that is bound stays bound: the outermost resource with the anchor is the
        // one that is meant, not the last one. Here that is the root, by either way.
        let mut outermost = lists();
        outermost["$defs"]["item"] = json!({"$dynamicAnchor": "item", "type": "null"});
        assert_eq!(
            terms(&outermost, &json!(true)),
            [
                "all(pprop(l2: x2), pprop(l3: x3))",
                "true",
                "x3",
                "x4",
                "addits(0: x5)",
                "x6",
                "type(null)",
            ]
        );
    }

    #[test]
    fn a_dynamic_reference_that_names_no_dynamic_anchor_is_a_reference() {
        // The fragment names an `$anchor`, is a JSON Pointer, or is not there. The dynamic
        // anchor of the same name in the resource around is not looked for then.
        for reference in ["inner#item", "inner#/$defs/item", "inner"] {
            let schema = json!({
                "$id": "https://example.com/root",
                "$ref": "inner",
                "$defs": {
                    "item": {"$dynamicAnchor": "item", "type": "null"},
                    "inner": {
                        "$id": "inner",
                        "$anchor": "item",
                        "items": {"$dynamicRef": reference},
                        "$defs": {"item": {"type": "string"}},
                    },
                },
            });
            let shown = terms(&schema, &json!(true));
            let last = shown.last().unwrap();
            let expected = if reference == "inner#/$defs/item" {
                "type(string)"
            } else {
                // The resource itself. Its items refer to it, as the root does, and so
                // they are the variable of the root.
                "addits(0: x0)"
            };
            assert_eq!(last, expected, "{reference}: {shown:?}");
            assert!(!shown.contains(&"type(null)".to_owned()), "{shown:?}");
        }
    }

    #[test]
    fn a_schema_in_a_second_scope_costs_a_step() {
        // Without a `$dynamicRef` that looks for an anchor, nothing is bound and nothing
        // costs a step, whatever anchors there are.
        let mut unused = lists();
        unused["$defs"]["list"]["items"] = json!({"$ref": "#item"});
        assert!(lowers(&unused, 0));
        // With one, a schema costs a step for each scope that it is reached in beyond its
        // first: the list and what is in it are reached in two. And each of the two scopes
        // costs one for the name that it binds.
        assert!(!lowers(&lists(), 0));
        // So a list of a thousand schemas costs a thousand steps, with the same two names.
        let mut wide = lists();
        wide["$defs"]["list"]["prefixItems"] = json!(vec![json!({}); 1_000]);
        assert!(!lowers(&wide, 100));

        // Twelve names, each bound by one of two resources on the way, are 4,096 scopes
        // for the last resource to be reached in.
        let mut definitions = Map::new();
        let names: Vec<String> = (0..12).map(|level| format!("n{level}")).collect();
        for (level, name) in names.iter().enumerate() {
            for side in ["a", "b"] {
                let next = |side: &str| json!({"$ref": format!("r{}{side}", level + 1)});
                let resource = json!({
                    "$id": format!("r{level}{side}"),
                    "anyOf": [next("a"), next("b")],
                    "$defs": {"anchor": {"$dynamicAnchor": name}},
                });
                definitions.insert(format!("r{level}{side}"), resource);
            }
        }
        for side in ["a", "b"] {
            let anchors = names.iter().map(|name| json!({"$dynamicAnchor": name}));
            let references = names
                .iter()
                .map(|name| json!({"$dynamicRef": format!("#{name}")}));
            let last = json!({
                "$id": format!("r12{side}"),
                "allOf": references.collect::<Vec<_>>(),
                "$defs": {"anchors": {"allOf": anchors.collect::<Vec<_>>()}},
            });
            definitions.insert(format!("r12{side}"), last);
        }
        let many = json!({
            "$id": "https://example.com/root",
            "$ref": "r0a",
            "$defs": definitions,
        });
        assert!(lowers(&many, u64::MAX));
        assert!(!lowers(&many, 1_000));
    }

    #[test]
    fn a_scope_costs_a_step_for_each_name_that_it_binds() {
        // Each resource binds a name of its own and leads to the next, so the scope of
        // the last binds all of them. No schema is reached in a second scope.
        let chain = |resources: u64| {
            let mut definitions = Map::new();
            for index in 0..resources {
                let mut resource = json!({
                    "$id": format!("r{index}"),
                    "$dynamicRef": format!("#n{index}"),
                    "$defs": {"anchor": {"$dynamicAnchor": format!("n{index}")}},
                });
                if index + 1 < resources {
                    resource["$ref"] = json!(format!("r{}", index + 1));
                }
                definitions.insert(format!("r{index}"), resource);
            }
            json!({"$id": "https://example.com/root", "$ref": "r0", "$defs": definitions})
        };
        // The scopes of four resources bind one name, two, three and four. So a long chain
        // ends at the budget before its scopes take the memory: they would hold two million
        // names here.
        assert!(lowers(&chain(4), 1_000));
        assert!(!lowers(&chain(2_000), 10_000));
        // A scope is worked out once, however many references lead into its resource.
        let mut references = vec![json!({"$ref": "list"}); 1_000];
        references.push(json!({"$ref": "list#/items"}));
        let often = json!({
            "$id": "https://example.com/root",
            "allOf": references,
            "$defs": {"list": {
                "$id": "list",
                "items": {"$dynamicRef": "#item"},
                "$defs": {"item": {"$dynamicAnchor": "item"}},
            }},
        });
        assert!(lowers(&often, 100));
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
        // Telling the schemas of a cycle apart costs steps, and here there are none.
        assert_eq!(
            lower(&graph, &mut Context::new(0, crate::RegexDialect::default())),
            Err(Exhausted)
        );
    }
}
