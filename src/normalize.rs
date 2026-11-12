//! The engine: is there an instance that B accepts and A does not?
//!
//! `all[B, not A]` is taken apart into *branches*. A branch is a conjunction of what the
//! engine knows how to combine: the types an instance may still have, the booleans it may
//! still be, the leaves that must hold and those that must not, and the variables taken for
//! true or for false. A disjunction splits a branch in as many as it has alternatives.
//!
//! - A branch that contradicts itself is *refuted*. If every branch is, A subsumes B.
//! - A branch that is not refuted and has a type that no leaf is about gives an instance of
//!   that type: a counterexample.
//! - Any other branch that is not refuted depends on a leaf, and the answer is unknown.
//!
//! A leaf never refutes a branch, except together with its own negation.

#[cfg(test)]
mod exhaustive;

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde_json::Value;

use crate::context::{Context, Exhausted};
use crate::generate;
use crate::term::{InstanceType, LeafId, Term, TermId, Terms, TypeSet, VarId};

/// What the engine makes of two schemas.
#[derive(Debug, PartialEq)]
pub(crate) enum Outcome {
    Yes,
    /// With an instance that B accepts and A does not.
    No(Value),
    /// With a leaf that the answer depends on.
    Unknown(LeafId),
}

/// Decides whether the schema of `a` accepts every instance that the schema of `b` accepts.
///
/// # Errors
///
/// When the budget does not cover the work.
pub(crate) fn decide(context: &mut Context, a: VarId, b: VarId) -> Result<Outcome, Exhausted> {
    let (a, b) = (context.terms.reference(a), context.terms.reference(b));
    let mut engine = Engine {
        context,
        unfoldings: Vec::new(),
        depends_on: None,
    };
    // A branch that was split, with the alternatives of the split that are still to come.
    // The last split is the one at work: each of its alternatives is followed to its end
    // before the next is made, so an instance is found without the alternatives after it,
    // and a long `oneOf` is never written out. The check begins as a split in one.
    let whole = vec![Item::new(b, false), Item::new(a, true)];
    let whole: Box<dyn Iterator<Item = Alternative>> = Box::new(std::iter::once(whole));
    let mut splits = vec![(Branch::default(), whole)];
    while let Some((split, still_to_come)) = splits.last_mut() {
        let alternative = if engine.is_hopeless(split) {
            None
        } else {
            still_to_come.next()
        };
        let Some(alternative) = alternative else {
            splits.pop();
            continue;
        };
        engine.context.budget.charge(1 + split.weight() / 32)?;
        let mut branch = split.clone();
        branch.todo.extend(alternative);
        if !engine.settle(&mut branch)? || engine.is_hopeless(&branch) {
            continue;
        }
        let Some(choice) = branch.choices.pop_front() else {
            // Nothing is left to take in, and the branch stands.
            match branch.instance() {
                Some(instance) => return Ok(Outcome::No(instance)),
                None => {
                    let leaf = branch.leaf(&engine.context.terms);
                    engine.depends_on.get_or_insert(leaf);
                }
            }
            continue;
        };
        let alternatives = alternatives(&engine.context.terms, &choice);
        splits.push((branch, alternatives));
    }
    Ok(match engine.depends_on {
        Some(leaf) => Outcome::Unknown(leaf),
        None => Outcome::Yes,
    })
}

/// A term that a branch has yet to take in, as it is or negated.
#[derive(Debug, Clone, Copy)]
struct Item {
    term: TermId,
    negated: bool,
    /// The unfolding of a variable that the term came out of, if it came out of one.
    within: Option<usize>,
}

/// One of the alternatives of a disjunction: terms that hold together.
type Alternative = Vec<Item>;

impl Item {
    fn new(term: TermId, negated: bool) -> Self {
        Self {
            term,
            negated,
            within: None,
        }
    }
}

/// A variable whose term was put in the place of a reference to it.
#[derive(Debug, Clone, Copy)]
struct Unfolding {
    variable: VarId,
    negated: bool,
    /// The unfolding in which that reference stood, if it stood in one.
    within: Option<usize>,
}

#[derive(Debug, Clone)]
struct Branch {
    /// The types that an instance may still have.
    types: TypeSet,
    /// Whether an instance may still be `false`, and whether `true`.
    booleans: [bool; 2],
    /// The leaves that must hold, and the types that they are about.
    holds: BTreeSet<LeafId>,
    covered: TypeSet,
    /// The leaves that must not hold.
    fails: BTreeSet<LeafId>,
    /// The variables taken for true, with `false`, and those taken for false, with `true`.
    /// Each is unfolded once in a branch, and this is its unfolding.
    taken: BTreeMap<(VarId, bool), usize>,
    /// The references to a variable that was taken before: the unfolding of the variable,
    /// and the unfolding in which the reference stands.
    met: BTreeSet<(usize, usize)>,
    /// What is still to be taken in, in the order in which it came up. What a term unfolds
    /// to waits behind everything that was there before, so that a variable meets its own
    /// negation before either is opened.
    todo: VecDeque<Item>,
    /// The disjunctions that were met and not split yet.
    choices: VecDeque<Item>,
}

impl Default for Branch {
    fn default() -> Self {
        Self {
            types: TypeSet::ALL,
            booleans: [true; 2],
            holds: BTreeSet::new(),
            covered: TypeSet::NONE,
            fails: BTreeSet::new(),
            taken: BTreeMap::new(),
            met: BTreeSet::new(),
            todo: VecDeque::new(),
            choices: VecDeque::new(),
        }
    }
}

const BOOLEAN: TypeSet = TypeSet::of(InstanceType::Boolean);

impl Branch {
    /// How much there is to copy when the branch splits.
    fn weight(&self) -> u64 {
        let leaves = self.holds.len() + self.fails.len();
        let variables = self.taken.len() + self.met.len();
        (leaves + variables + self.choices.len()) as u64
    }

    /// Keeps only instances of these types. Returns whether any are left.
    fn restrict(&mut self, types: TypeSet) -> bool {
        self.types = self.types.intersection(types);
        !self.types.is_empty()
    }

    /// Rules out one boolean. Returns whether any instance is left.
    fn exclude(&mut self, value: bool) -> bool {
        self.booleans[usize::from(value)] = false;
        if self.booleans == [false; 2] {
            return self.restrict(BOOLEAN.complement());
        }
        true
    }

    /// The types that the branch says nothing about beyond the type: no leaf that must hold
    /// is about them. A leaf that must not hold is about every type that is left.
    fn free(&self) -> TypeSet {
        if self.fails.is_empty() {
            self.types.intersection(self.covered.complement())
        } else {
            TypeSet::NONE
        }
    }

    /// An instance that the branch accepts, if it is known to accept one.
    fn instance(&self) -> Option<Value> {
        let kind = self.free().iter().next()?;
        Some(generate::instance(kind, self.booleans[1]))
    }

    /// A leaf that stands between the branch and an instance.
    fn leaf(&self, terms: &Terms) -> LeafId {
        let about_what_is_left = |leaf: &&LeafId| {
            let about = terms.leaf(**leaf).domain;
            !about.intersection(self.types).is_empty()
        };
        let must_not_hold = self.fails.first();
        let leaf = must_not_hold.or_else(|| self.holds.iter().find(about_what_is_left));
        *leaf.expect("a branch without an instance depends on a leaf")
    }
}

struct Engine<'c> {
    context: &'c mut Context,
    unfoldings: Vec<Unfolding>,
    /// A leaf that some branch depends on, once there is such a branch. From then on the
    /// answer is not `Yes`.
    depends_on: Option<LeafId>,
}

impl Engine<'_> {
    /// Whether a branch can be left alone: the answer is not `Yes` any more, and the branch
    /// cannot give an instance. Leaves are never taken back and types never return, so what
    /// comes out of the branch cannot give one either.
    fn is_hopeless(&self, branch: &Branch) -> bool {
        self.depends_on.is_some() && branch.free().is_empty()
    }

    /// Takes in everything that needs no split. Returns whether the branch still stands.
    fn settle(&mut self, branch: &mut Branch) -> Result<bool, Exhausted> {
        while let Some(item) = branch.todo.pop_front() {
            self.context.budget.charge(1)?;
            if !self.take(branch, item)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Takes one term into a branch. Returns whether the branch still stands.
    fn take(&mut self, branch: &mut Branch, item: Item) -> Result<bool, Exhausted> {
        let Item {
            term,
            negated,
            within,
        } = item;
        if let Term::Ref(variable) = self.context.terms.term(term) {
            return self.unfold(branch, *variable, negated, within);
        }
        let stands = match (self.context.terms.term(term), negated) {
            (Term::True, false) | (Term::False, true) => true,
            (Term::False, false) | (Term::True, true) => false,
            (Term::TypeIs(types), false) => branch.restrict(*types),
            (Term::TypeIs(types), true) => branch.restrict(types.complement()),
            (Term::BoolConst(value), false) => branch.restrict(BOOLEAN) && branch.exclude(!*value),
            (Term::BoolConst(value), true) => branch.exclude(*value),
            (Term::Unknown(leaf), false) => {
                branch.holds.insert(*leaf);
                branch.covered = branch.covered.union(self.context.terms.leaf(*leaf).domain);
                !branch.fails.contains(leaf)
            }
            // A leaf fails only for an instance that it is about.
            (Term::Unknown(leaf), true) => {
                branch.fails.insert(*leaf);
                let about = self.context.terms.leaf(*leaf).domain;
                branch.restrict(about) && !branch.holds.contains(leaf)
            }
            (Term::AllOf(parts), false) | (Term::AnyOf(parts), true) => {
                let parts = parts.iter();
                branch.todo.extend(parts.map(|part| Item {
                    term: *part,
                    negated,
                    within,
                }));
                true
            }
            (Term::AnyOf(_), false) | (Term::AllOf(_), true) | (Term::OneOf(_), _) => {
                branch.choices.push_back(item);
                true
            }
            (Term::Not(inner), _) => {
                branch.todo.push_back(Item {
                    term: *inner,
                    negated: !negated,
                    within,
                });
                true
            }
            (Term::Ref(_), _) => unreachable!("a reference was unfolded above"),
        };
        Ok(stands)
    }

    /// Puts the term of a variable in the place of a reference to it, once in a branch.
    ///
    /// A schema that refers to itself with nothing in between accepts what it can be shown
    /// to accept in finitely many steps. So no variable is taken for true on the strength of
    /// itself: if what it asks for leads back to it by way of variables that are all taken
    /// for true, the branch accepts nothing. A way back that passes a variable taken for
    /// false is a schema that is negated inside itself, or the negation of one that refers
    /// to itself. Neither is modelled, and the branch depends on a leaf instead.
    fn unfold(
        &mut self,
        branch: &mut Branch,
        variable: VarId,
        negated: bool,
        within: Option<usize>,
    ) -> Result<bool, Exhausted> {
        if let Some(&open) = branch.taken.get(&(variable, !negated)) {
            // The variable and its negation in one branch: nothing is both. Unless the one
            // asks for the other, which is the schema that is negated inside itself.
            return match within {
                Some(from) if self.leads_to(branch, open, from, false)? => {
                    self.depend_on_recursion(branch, variable, from);
                    Ok(true)
                }
                _ => Ok(false),
            };
        }
        if let Some(&open) = branch.taken.get(&(variable, negated)) {
            // Taken before, so there is nothing to take in. A reference of A or B themselves
            // stands in no unfolding and closes no cycle.
            let Some(from) = within else {
                return Ok(true);
            };
            if !negated && self.leads_to(branch, open, from, true)? {
                return Ok(false);
            }
            if self.leads_to(branch, open, from, false)? {
                self.depend_on_recursion(branch, variable, from);
            } else {
                branch.met.insert((open, from));
            }
            return Ok(true);
        }
        let unfolding = self.unfoldings.len();
        self.unfoldings.push(Unfolding {
            variable,
            negated,
            within,
        });
        branch.taken.insert((variable, negated), unfolding);
        branch.todo.push_back(Item {
            term: self.context.terms.variable(variable).body,
            negated,
            within: Some(unfolding),
        });
        Ok(true)
    }

    /// Whether what the unfolding `open` asks for leads to the unfolding `from`: by the
    /// references that were unfolded, and by those that met a variable taken before. With
    /// `positive`, only by way of variables that are taken for true.
    fn leads_to(
        &mut self,
        branch: &Branch,
        open: usize,
        from: usize,
        positive: bool,
    ) -> Result<bool, Exhausted> {
        // The way is looked for from its end: from an unfolding to those that ask for it.
        let (mut seen, mut pending) = (BTreeSet::new(), vec![from]);
        while let Some(index) = pending.pop() {
            let unfolding = self.unfoldings[index];
            if (positive && unfolding.negated) || !seen.insert(index) {
                continue;
            }
            self.context.budget.charge(1)?;
            if index == open {
                return Ok(true);
            }
            pending.extend(unfolding.within);
            let references = branch.met.range((index, 0)..=(index, usize::MAX));
            pending.extend(references.map(|&(_, stands_in)| stands_in));
        }
        Ok(false)
    }

    /// Makes a branch depend on a leaf for a cycle that is not modelled. `from` is the
    /// unfolding in which the reference stands that closes the cycle.
    fn depend_on_recursion(&mut self, branch: &mut Branch, variable: VarId, from: usize) {
        let closes = self.unfoldings[from].variable;
        let closes = self.context.terms.variable(closes).node;
        let leaf = self.context.terms.recursion(variable, closes);
        branch.holds.insert(leaf);
        branch.covered = TypeSet::ALL;
    }
}

/// The alternatives of a disjunction, each made when it is asked for.
fn alternatives(terms: &Terms, choice: &Item) -> Box<dyn Iterator<Item = Alternative>> {
    let within = choice.within;
    let item = move |term: TermId, negated| Item {
        term,
        negated,
        within,
    };
    match (terms.term(choice.term), choice.negated) {
        // One of them holds, or one of them does not.
        (Term::AnyOf(parts), negated @ false) | (Term::AllOf(parts), negated @ true) => {
            let parts = parts.to_vec();
            let parts = parts.into_iter();
            Box::new(parts.map(move |part| vec![item(part, negated)]))
        }
        // One holds and no other does.
        (Term::OneOf(parts), false) => {
            let parts = parts.to_vec();
            Box::new((0..parts.len()).map(move |holds| {
                let all = parts.iter().enumerate();
                all.map(|(place, part)| item(*part, place != holds))
                    .collect()
            }))
        }
        // None holds, or two do.
        (Term::OneOf(parts), true) => {
            let parts = parts.to_vec();
            let none: Alternative = parts.iter().map(|part| item(*part, true)).collect();
            let count = parts.len();
            let pairs = (0..count)
                .flat_map(move |first| (first + 1..count).map(move |second| (first, second)));
            let two = pairs.map(move |(first, second)| {
                vec![item(parts[first], false), item(parts[second], false)]
            });
            Box::new(std::iter::once(none).chain(two))
        }
        (other, _) => unreachable!("{other:?} is no disjunction"),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, json};

    use super::*;
    use crate::{Checker, Reason, Side, Verdict};

    fn verdict(a: &Value, b: &Value) -> Verdict {
        Checker::new().subsumes(a, b).unwrap()
    }

    /// The counterexample of a check that must answer `No`.
    fn counterexample(a: &Value, b: &Value) -> Value {
        match verdict(a, b) {
            Verdict::No { counterexample } => counterexample,
            other => panic!("does {a} subsume {b}? {other:?}"),
        }
    }

    /// Where the leaf is that a check depends on, which must answer `Unknown`.
    fn depends_on(a: &Value, b: &Value) -> (Side, String) {
        match verdict(a, b) {
            Verdict::Unknown {
                reason: Reason::Unsupported { schema, location },
            } => (schema, location),
            other => panic!("does {a} subsume {b}? {other:?}"),
        }
    }

    fn yes(a: &Value, b: &Value) {
        assert_eq!(verdict(a, b), Verdict::Yes, "does {a} subsume {b}?");
    }

    #[test]
    fn types_are_compared_exactly() {
        let (string, null) = (json!({"type": "string"}), json!({"type": "null"}));
        let either = json!({"type": ["string", "null"]});
        yes(&string, &string);
        yes(&either, &string);
        yes(&json!({}), &either);
        yes(&json!(true), &json!(true));
        yes(&json!(false), &json!(false));
        yes(&string, &json!(false));
        assert_eq!(counterexample(&string, &either), json!(null));
        assert_eq!(counterexample(&null, &string), json!(""));
        // The first type that is left gives the instance.
        assert_eq!(counterexample(&json!(false), &json!(true)), json!(null));
        let instances = [
            ("null", json!(null)),
            ("boolean", json!(true)),
            ("number", json!(0)),
            ("string", json!("")),
            ("array", json!([])),
            ("object", json!({})),
        ];
        for (name, instance) in instances {
            assert_eq!(
                counterexample(&json!(false), &json!({"type": name})),
                instance
            );
        }
    }

    #[test]
    fn the_two_booleans_are_told_apart() {
        let boolean = json!({"type": "boolean"});
        let (is_true, is_false) = (json!({"const": true}), json!({"enum": [false]}));
        yes(&boolean, &is_true);
        yes(&boolean, &json!({"enum": [true, false]}));
        yes(&json!({"enum": [false, true]}), &boolean);
        yes(&json!({"enum": [true]}), &is_true);
        assert_eq!(counterexample(&is_true, &boolean), json!(false));
        assert_eq!(counterexample(&is_false, &boolean), json!(true));
        assert_eq!(counterexample(&is_false, &is_true), json!(true));
        // Without the two booleans, nothing of the type is left.
        let neither = json!({"type": "boolean", "not": {"enum": [true, false]}});
        yes(&json!(false), &neither);
        yes(&json!({"const": null}), &json!({"enum": [null]}));
        assert_eq!(
            counterexample(&json!({"const": null}), &is_true),
            json!(true)
        );
    }

    #[test]
    fn the_connectives_are_taken_apart() {
        let (string, nothing, number) = (
            json!({"type": "string"}),
            json!({"type": "null"}),
            json!({"type": "number"}),
        );
        let any = json!({"anyOf": [string, nothing]});
        yes(&any, &nothing);
        yes(&any, &json!({"type": ["null", "string"]}));
        yes(&json!({"type": ["null", "string"]}), &any);
        assert_eq!(counterexample(&any, &number), json!(0));

        let all = json!({"allOf": [{"type": ["string", "null"]}, {"type": ["null", "number"]}]});
        yes(&all, &nothing);
        yes(&nothing, &all);
        assert_eq!(counterexample(&all, &string), json!(""));

        let not = json!({"not": string});
        yes(&not, &number);
        yes(
            &json!({"type": ["null", "boolean", "number", "array", "object"]}),
            &not,
        );
        assert_eq!(counterexample(&not, &string), json!(""));
        yes(&string, &json!({"not": not}));
    }

    #[test]
    fn exactly_one_is_neither_none_nor_two() {
        // A string satisfies both, so only `null` satisfies exactly one.
        let one = json!({"oneOf": [{"type": "string"}, {"type": ["string", "null"]}]});
        let null = json!({"type": "null"});
        yes(&one, &null);
        yes(&null, &one);
        assert_eq!(counterexample(&one, &json!({"type": "string"})), json!(""));
        assert_eq!(counterexample(&one, &json!({"type": "number"})), json!(0));
        // Three that exclude each other are the same as any of them.
        let apart = json!({"oneOf": [{"type": "string"}, {"type": "null"}, {"type": "number"}]});
        let any = json!({"anyOf": [{"type": "string"}, {"type": "null"}, {"type": "number"}]});
        yes(&apart, &any);
        yes(&any, &apart);
    }

    #[test]
    fn a_condition_chooses_between_two_schemas() {
        let schema = json!({
            "if": {"type": "string"},
            "then": {"type": ["string", "null"]},
            "else": {"type": "null"},
        });
        let both = json!({"type": ["string", "null"]});
        yes(&schema, &both);
        yes(&both, &schema);
        assert_eq!(
            counterexample(&schema, &json!({"type": "number"})),
            json!(0)
        );
    }

    #[test]
    fn a_leaf_and_its_negation_refute_a_branch() {
        let long = json!({"minLength": 3});
        let long_string = json!({"type": "string", "minLength": 3});
        yes(&long, &long);
        yes(&long, &long_string);
        // The other way, an instance that is no string tells them apart.
        assert_eq!(counterexample(&long_string, &long), json!(null));
        // Subschemas of one class make one leaf.
        let person = json!({"type": "object", "properties": {"name": {"type": "string"}}});
        let named = json!({
            "type": "object",
            "properties": {"name": {"type": "string"}},
            "required": ["name"],
        });
        yes(&person, &named);
        assert_eq!(
            depends_on(&named, &person),
            (Side::A, "#/required".to_owned())
        );
    }

    #[test]
    fn a_leaf_is_about_one_type_only() {
        // No number is too short, and no string is too small.
        yes(&json!({"minLength": 3}), &json!({"type": "integer"}));
        yes(
            &json!({"minimum": 3}),
            &json!({"type": "string", "minLength": 1}),
        );
        let integer = json!({"type": "integer"});
        yes(&json!({"type": "number"}), &integer);
        assert_eq!(
            depends_on(&integer, &json!({"type": "number"})),
            (Side::A, "#/type".to_owned())
        );
        // A string satisfies the leaf for an integer, so a string is an instance.
        let either = json!({"type": ["integer", "string"]});
        assert_eq!(counterexample(&json!({"type": "null"}), &either), json!(""));
        assert_eq!(
            depends_on(
                &json!({"type": "string", "minLength": 3}),
                &json!({"type": "string"})
            ),
            (Side::A, "#/minLength".to_owned())
        );
        // A constant is of the type of its value.
        yes(&json!({"type": "string"}), &json!({"const": "a"}));
        yes(
            &json!({"enum": ["a", 1, null]}),
            &json!({"enum": [null, "a"]}),
        );
        assert_eq!(
            counterexample(&json!({"const": "a"}), &json!({"type": "number"})),
            json!(0)
        );
        assert_eq!(
            depends_on(&json!({"const": "a"}), &json!({"type": "string"})),
            (Side::A, "#/const".to_owned())
        );
    }

    #[test]
    fn dependencies_use_the_leaf_of_required() {
        yes(
            &json!({"required": ["a"]}),
            &json!({"required": ["b", "a"]}),
        );
        yes(
            &json!({"dependentRequired": {"a": ["b"]}}),
            &json!({"required": ["b"]}),
        );
        yes(
            &json!({"dependentSchemas": {"a": {"type": "object"}}}),
            &json!({"type": "object"}),
        );
        // What is no object satisfies a dependency.
        yes(
            &json!({"dependentRequired": {"a": ["b"]}}),
            &json!({"type": "string"}),
        );
        assert_eq!(
            depends_on(
                &json!({"required": ["b"]}),
                &json!({"dependentRequired": {"a": ["b"]}})
            ),
            (Side::A, "#/required".to_owned())
        );
    }

    #[test]
    fn a_schema_subsumes_itself_whatever_it_contains() {
        let schemas = [
            json!({"type": "integer", "minimum": 0, "multipleOf": 0.5}),
            json!({"pattern": "^a", "format": "date", "maxLength": 3}),
            json!({"properties": {"a": {"items": {"contains": {}}}}, "additionalProperties": false}),
            json!({"unevaluatedProperties": false, "allOf": [{"properties": {"a": {}}}]}),
            json!({"oneOf": [{"minimum": 1}, {"maximum": 0}], "not": {"uniqueItems": true}}),
            // A resource of its own, so that `#` is the schema wherever it stands.
            json!({"$id": "https://example.com/tree", "anyOf": [{"type": "null"}, {"items": {"$ref": "#"}}]}),
            json!({"$id": "https://example.com/endless", "$ref": "#"}),
        ];
        let other = json!({"type": "array", "maxItems": 2});
        for schema in &schemas {
            // Not by being the same value: the two are parsed apart.
            yes(schema, &schema.clone());
            yes(schema, &json!({"allOf": [schema, other]}));
            yes(&json!({"anyOf": [schema, other]}), schema);
            let (any, all) = (
                json!({"anyOf": [other, schema]}),
                json!({"allOf": [other, schema]}),
            );
            yes(&any, &all);
        }

        // A count that was too large to keep is like no other, so a schema with one is not
        // known to subsume even itself. A schema that leads to a `$dynamicRef` is not looked
        // at yet at all.
        let huge = json!({"type": "string", "maxLength": 1e30});
        assert_eq!(depends_on(&huge, &huge.clone()).1, "#/maxLength");
        let dynamic = json!({"$dynamicAnchor": "x", "items": {"$dynamicRef": "#x"}});
        assert_eq!(
            depends_on(&dynamic, &dynamic.clone()),
            (Side::A, "#/items/$dynamicRef".to_owned())
        );
    }

    #[test]
    fn a_schema_that_refers_to_itself_accepts_what_it_can_be_shown_to_accept() {
        // Nothing but `null` is ever accepted by a way that ends.
        let nulls = json!({"anyOf": [{"type": "null"}, {"$ref": "#"}]});
        let nothing = json!({"type": "null"});
        yes(&nothing, &nulls);
        yes(&nulls, &nothing);
        assert_eq!(
            counterexample(&json!({"type": "string"}), &nulls),
            json!(null)
        );
        // A schema that only refers to itself accepts nothing that way.
        let endless = json!({"$ref": "#"});
        yes(&json!(false), &endless);
        yes(
            &json!({"type": "string"}),
            &json!({"allOf": [{"$ref": "#"}, {"type": "null"}]}),
        );

        // What such a schema does not accept is not modelled. The leaf names the schema in
        // which the cycle closes.
        assert_eq!(depends_on(&endless, &nothing), (Side::A, "#".to_owned()));
        assert_eq!(
            depends_on(&nulls, &json!({"type": "string"})),
            (Side::A, "#/anyOf/1".to_owned())
        );
        let negated = json!({"not": {"$ref": "#"}});
        assert_eq!(
            depends_on(&nothing, &negated),
            (Side::B, "#/not".to_owned())
        );
        // Types still refute a branch with such a leaf in it.
        yes(
            &json!({"type": "string"}),
            &json!({"type": "string", "not": {"$ref": "#"}}),
        );
    }

    #[test]
    fn schemas_that_need_each_other_accept_nothing_however_they_are_met() {
        // `x` needs `y` and `y` needs `x`, so neither is ever shown to accept an instance.
        let defs = json!({
            "x": {"$ref": "#/$defs/y", "type": "null"},
            "y": {"$ref": "#/$defs/x"},
        });
        let (x, y) = (json!({"$ref": "#/$defs/x"}), json!({"$ref": "#/$defs/y"}));
        let with = |schema: Value| {
            let mut schema = schema;
            schema["$defs"] = defs.clone();
            schema
        };
        // From one end, the cycle closes inside the unfolding of the schema it began with.
        yes(&json!(false), &with(x.clone()));
        yes(&json!(false), &with(y.clone()));
        // Side by side, each is taken before the other refers to it.
        yes(&json!(false), &with(json!({"allOf": [x, y]})));
        yes(&json!(false), &with(json!({"allOf": [y, x]})));
        // The same without the definitions: the two parts are each other's reference.
        let beside =
            json!({"allOf": [{"$ref": "#/allOf/1", "type": "null"}, {"$ref": "#/allOf/0"}]});
        yes(&json!(false), &beside);
        // What accepts nothing is told apart from `true` by any instance but `null`, whose
        // branch asks for the negation of the cycle.
        assert_eq!(counterexample(&beside, &json!(true)), json!(true));
        // With a way out of the cycle, each accepts what the way out accepts and what the
        // other then accepts: a string by `y`, and so by `x`.
        let out = json!({
            "allOf": [{"$ref": "#/$defs/x"}, {"$ref": "#/$defs/y"}],
            "$defs": {
                "x": {"anyOf": [{"$ref": "#/$defs/y"}, {"type": "null"}]},
                "y": {"anyOf": [{"$ref": "#/$defs/x"}, {"type": "string"}]},
            },
        });
        let either = json!({"type": ["null", "string"]});
        yes(&out, &either);
        yes(&either, &out);
        assert_eq!(counterexample(&json!({"type": "null"}), &out), json!(""));
    }

    #[test]
    fn a_schema_that_is_used_twice_is_no_cycle() {
        // Both parts refer to `shared`, and the second meets it taken. Nothing leads back.
        let twice = json!({
            "allOf": [{"$ref": "#/$defs/x"}, {"$ref": "#/$defs/y"}],
            "$defs": {
                "x": {"$ref": "#/$defs/shared", "type": ["null", "string"]},
                "y": {"$ref": "#/$defs/shared", "type": ["null", "number"]},
                "shared": {"anyOf": [{"type": "null"}, {"type": "boolean"}]},
            },
        });
        let null = json!({"type": "null"});
        yes(&twice, &null);
        yes(&null, &twice);
        assert_eq!(counterexample(&json!(false), &twice), json!(null));
    }

    #[test]
    fn a_cycle_through_negation_is_not_modelled() {
        // `x` is what `z` is not, and `z` is what `x` is not. Each could be anything as long
        // as the other is the rest, so neither is known to accept nothing or everything. `z`
        // names every type, which keeps the two from being one class.
        let all = json!(["null", "boolean", "number", "string", "array", "object"]);
        let defs = json!({
            "x": {"not": {"$ref": "#/$defs/z"}},
            "z": {"not": {"$ref": "#/$defs/x"}, "type": all},
        });
        let x = json!({"allOf": [{"$ref": "#/$defs/x"}], "$defs": defs});
        let z = json!({"anyOf": [{"$ref": "#/$defs/z"}], "$defs": defs});
        for schema in [&x, &z] {
            assert_eq!(depends_on(&json!(false), schema).0, Side::B);
            assert_eq!(depends_on(schema, &json!(true)).0, Side::A);
        }
        // A schema that is its own negation: the leaf names the schema that leads back, also
        // when the reference is not a keyword of its own.
        let paradox = json!({"$ref": "#/$defs/x", "$defs": {"x": {"not": {"$ref": "#/$defs/x"}}}});
        assert_eq!(
            depends_on(&paradox, &json!(true)),
            (Side::A, "#/$defs/x".to_owned())
        );
    }

    #[test]
    fn a_long_one_of_is_never_written_out() {
        // Written out, exactly one of three thousand is nine million terms, and its negation
        // is four and a half million alternatives. They are made one at a time.
        let long = json!({"oneOf": vec![true; 3_000]});
        let (nothing, anything) = (json!(false), json!(true));
        // A budget that ends the check at the first alternative keeps the others unmade.
        let checker = Checker::new().budget(8);
        for (a, b) in [(&nothing, &long), (&long, &anything)] {
            let check = checker.check(a, b).unwrap();
            assert_eq!(
                check.verdict,
                Verdict::Unknown {
                    reason: Reason::Budget
                }
            );
        }
        // The first two that hold together give an instance, long before the last two.
        let check = Checker::new().check(&long, &anything).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::No {
                counterexample: json!(null)
            }
        );
        assert!(check.steps < 10_000, "{}", check.steps);
    }

    #[test]
    fn the_budget_ends_a_check() {
        let a = json!({"anyOf": [{"type": "null"}, {"type": "string"}]});
        let b = json!({"type": ["null", "string", "number"]});
        let steps = Checker::new().check(&a, &b).unwrap().steps;
        assert!(steps > 1, "{steps}");
        let check = Checker::new().budget(steps - 1).check(&a, &b).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Budget
            }
        );
        assert_eq!(check.steps, steps - 1);
        let check = Checker::new().budget(steps).check(&a, &b).unwrap();
        assert_eq!(
            check.verdict,
            Verdict::No {
                counterexample: json!(0)
            }
        );
        assert_eq!(check.steps, steps);
    }

    #[test]
    fn branches_that_cannot_give_an_instance_are_left_alone() {
        // Twenty choices between two leaves about strings: a million branches, none of which
        // is refuted and none of which gives an instance. The first one settles the answer.
        let choice = |n: u32| json!({"anyOf": [{"minLength": n}, {"maxLength": n + 100}]});
        let b = json!({"type": "string", "allOf": (0..20).map(choice).collect::<Vec<_>>()});
        let a = json!({"type": "string", "pattern": "^a"});
        let check = Checker::new().check(&a, &b).unwrap();
        assert!(matches!(
            check.verdict,
            Verdict::Unknown {
                reason: Reason::Unsupported { .. }
            }
        ));
        assert!(check.steps < 1_000, "{}", check.steps);
        // An instance is still found where there is one.
        let a = json!({"type": "null"});
        assert_eq!(
            counterexample(&a, &json!({"anyOf": [b, {"type": "number"}]})),
            json!(0)
        );
    }

    #[test]
    fn a_split_tries_every_alternative() {
        let terms = &mut Terms::default();
        let parts: Vec<TermId> = [true, false]
            .into_iter()
            .map(|value| terms.bool_const(value))
            .collect();
        let null = terms.type_is(TypeSet::of(InstanceType::Null));
        let parts = vec![parts[0], parts[1], null];
        let shown = |terms: &Terms, term: TermId, negated: bool| {
            let choice = Item::new(term, negated);
            let literal = |item: &Item| {
                let term = terms.show(item.term);
                if item.negated {
                    format!("not {term}")
                } else {
                    term
                }
            };
            alternatives(terms, &choice)
                .map(|all| all.iter().map(literal).collect::<Vec<_>>().join(" and "))
                .collect::<Vec<_>>()
        };
        let any = terms.any_of(parts.clone());
        assert_eq!(
            shown(terms, any, false),
            ["is(true)", "is(false)", "type(null)"]
        );
        let all = terms.all_of(parts.clone());
        assert_eq!(
            shown(terms, all, true),
            ["not is(true)", "not is(false)", "not type(null)"]
        );
        let one = terms.one_of(parts);
        assert_eq!(
            shown(terms, one, false),
            [
                "is(true) and not is(false) and not type(null)",
                "not is(true) and is(false) and not type(null)",
                "not is(true) and not is(false) and type(null)",
            ]
        );
        assert_eq!(
            shown(terms, one, true),
            [
                "not is(true) and not is(false) and not type(null)",
                "is(true) and is(false)",
                "is(true) and type(null)",
                "is(false) and type(null)",
            ]
        );
    }

    #[test]
    fn two_deep_schemas_that_say_the_same_are_not_opened() {
        let deep = || {
            let mut deep = json!({"minLength": 1});
            for _ in 0..100_000 {
                deep = Value::Object(Map::from_iter([("not".to_owned(), deep)]));
            }
            deep
        };
        let (a, b) = (deep(), deep());
        let check = Checker::new().check(&a, &b).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        assert!(check.steps < 10, "{}", check.steps);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget((a, b));
    }
}
