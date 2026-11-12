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

use std::collections::{BTreeSet, VecDeque};

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
    let mut first = Branch::default();
    first.todo.push_back(Item::new(b, false));
    first.todo.push_back(Item::new(a, true));
    let mut branches = vec![first];
    while let Some(mut branch) = branches.pop() {
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
        // Each alternative is taken in as far as it goes without another split. One that is
        // refuted by then is never split at all.
        let mut alive = Vec::new();
        for alternative in alternatives(&engine.context.terms, &choice) {
            engine.context.budget.charge(1 + branch.weight() / 32)?;
            let mut next = branch.clone();
            next.todo.extend(alternative);
            if engine.settle(&mut next)? {
                alive.push(next);
            }
        }
        branches.extend(alive.into_iter().rev());
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
    /// The unfolding that this one happened in.
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
    taken: BTreeSet<(VarId, bool)>,
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
            taken: BTreeSet::new(),
            todo: VecDeque::new(),
            choices: VecDeque::new(),
        }
    }
}

const BOOLEAN: TypeSet = TypeSet::of(InstanceType::Boolean);

impl Branch {
    /// How much there is to copy when the branch splits.
    fn weight(&self) -> u64 {
        let parts = self.holds.len() + self.fails.len() + self.taken.len() + self.choices.len();
        parts as u64
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

    /// Puts the term of a variable in the place of a reference to it.
    fn unfold(
        &mut self,
        branch: &mut Branch,
        variable: VarId,
        negated: bool,
        mut within: Option<usize>,
    ) -> Result<bool, Exhausted> {
        // A schema that refers to itself without anything in between accepts what it can be
        // shown to accept in finitely many steps. So a reference inside its own unfolding
        // adds nothing that would be accepted. The negation of that is not modelled, and
        // neither is a schema that is negated inside itself.
        let inner = within;
        while let Some(index) = within {
            self.context.budget.charge(1)?;
            let outer = self.unfoldings[index];
            if outer.variable == variable {
                if !negated && !outer.negated {
                    return Ok(false);
                }
                // The reference stands in the schema that was unfolded last.
                let last = inner.expect("the loop ran, so there is an unfolding");
                let closes = self
                    .context
                    .terms
                    .variable(self.unfoldings[last].variable)
                    .node;
                let leaf = self.context.terms.recursion(variable, closes);
                branch.holds.insert(leaf);
                branch.covered = TypeSet::ALL;
                return Ok(true);
            }
            within = outer.within;
        }
        // The variable and its negation in one branch: nothing is both.
        if branch.taken.contains(&(variable, !negated)) {
            return Ok(false);
        }
        if branch.taken.insert((variable, negated)) {
            self.unfoldings.push(Unfolding {
                variable,
                negated,
                within: inner,
            });
            branch.todo.push_back(Item {
                term: self.context.terms.variable(variable).body,
                negated,
                within: Some(self.unfoldings.len() - 1),
            });
        }
        Ok(true)
    }
}

/// The alternatives of a disjunction: each is a list of terms that hold together.
fn alternatives(terms: &Terms, choice: &Item) -> Vec<Vec<Item>> {
    let item = |term: &TermId, negated| Item {
        term: *term,
        negated,
        within: choice.within,
    };
    match (terms.term(choice.term), choice.negated) {
        // One of them holds, or one of them does not.
        (Term::AnyOf(parts), false) => parts.iter().map(|part| vec![item(part, false)]).collect(),
        (Term::AllOf(parts), true) => parts.iter().map(|part| vec![item(part, true)]).collect(),
        // One holds and no other does.
        (Term::OneOf(parts), false) => {
            let places = 0..parts.len();
            places
                .map(|holds| {
                    let all = parts.iter().enumerate();
                    all.map(|(place, part)| item(part, place != holds))
                        .collect()
                })
                .collect()
        }
        // None holds, or two do.
        (Term::OneOf(parts), true) => {
            let none = parts.iter().map(|part| item(part, true)).collect();
            let mut alternatives = vec![none];
            for (place, first) in parts.iter().enumerate() {
                for second in &parts[place + 1..] {
                    alternatives.push(vec![item(first, false), item(second, false)]);
                }
            }
            alternatives
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

        // Two things are like no other, so a schema with one of them is not known to subsume
        // even itself: a `$dynamicRef`, and a count that was too large to keep.
        let dynamic = json!({"$dynamicAnchor": "x", "items": {"$dynamicRef": "#x"}});
        assert_eq!(depends_on(&dynamic, &dynamic.clone()).1, "#/items");
        let huge = json!({"type": "string", "maxLength": 1e30});
        assert_eq!(depends_on(&huge, &huge.clone()).1, "#/maxLength");
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

        // What such a schema does not accept is not modelled. The leaf stands at the
        // reference that closes the cycle.
        assert_eq!(
            depends_on(&endless, &nothing),
            (Side::A, "#/$ref".to_owned())
        );
        assert_eq!(
            depends_on(&nulls, &json!({"type": "string"})),
            (Side::A, "#/anyOf/1/$ref".to_owned())
        );
        let negated = json!({"not": {"$ref": "#"}});
        assert_eq!(
            depends_on(&nothing, &negated),
            (Side::B, "#/not/$ref".to_owned())
        );
        // Types still refute a branch with such a leaf in it.
        yes(
            &json!({"type": "string"}),
            &json!({"type": "string", "not": {"$ref": "#"}}),
        );
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
            let alternatives = alternatives(terms, &choice);
            let literal = |item: &Item| {
                let term = terms.show(item.term);
                if item.negated {
                    format!("not {term}")
                } else {
                    term
                }
            };
            let alternatives = alternatives.iter();
            alternatives
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
