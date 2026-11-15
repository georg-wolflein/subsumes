//! The engine: is there an instance that B accepts and A does not?
//!
//! `all[B, not A]` is taken apart into *branches*. A branch is a conjunction of what the
//! engine knows how to combine: the types an instance may still have, the booleans, the
//! numbers and the strings it may still be, the leaves that must hold and those that must
//! not, and the variables taken for true or for false. A disjunction splits a branch in as
//! many as it has alternatives.
//!
//! - A branch that contradicts itself is *refuted*. If every branch is, A subsumes B.
//! - A branch that is not refuted and has a type that no leaf is about gives an instance of
//!   that type: a counterexample.
//! - Any other branch that is not refuted depends on a leaf, and the answer is unknown.
//!
//! A leaf never refutes a branch, except together with its own negation. What a branch says
//! about numbers and about strings is exact: when no number satisfies it, the branch has no
//! number among its instances, and when one does, that number is an instance. So it is with
//! strings.

#[cfg(test)]
mod exhaustive;

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde_json::Value;

use crate::canonical::number::Numbers;
use crate::canonical::string::Strings;
use crate::context::{Context, Exhausted};
use crate::generate;
use crate::term::{InstanceType, LeafId, Term, TermId, Terms, TypeSet, VarId};

/// What the engine makes of two schemas.
#[derive(Debug, PartialEq)]
pub(crate) enum Outcome {
    Yes,
    /// With an instance that B accepts and A does not.
    No(Value),
    /// With what the answer depends on.
    Unknown(Cause),
}

/// What stands between a branch and an instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Cause {
    /// A predicate that the engine does not model.
    Leaf(LeafId),
    /// The branch accepts numbers, and none that a JSON number stands for.
    Number,
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
            match engine.instance(&branch)? {
                Some(instance) => return Ok(Outcome::No(instance)),
                None => {
                    let cause = branch.cause(&engine.context.terms);
                    engine.depends_on.get_or_insert(cause);
                }
            }
            continue;
        };
        let alternatives = alternatives(&engine.context.terms, &choice);
        splits.push((branch, alternatives));
    }
    Ok(match engine.depends_on {
        Some(cause) => Outcome::Unknown(cause),
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
    /// The numbers that an instance may still be, and whether anything was asked of them
    /// since it was last seen that there are some.
    numbers: Numbers,
    numbers_asked: bool,
    /// The same for the strings.
    strings: Strings,
    strings_asked: bool,
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
            numbers: Numbers::default(),
            numbers_asked: false,
            strings: Strings::default(),
            strings_asked: false,
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
const NUMBER: TypeSet = TypeSet::of(InstanceType::Number);
const STRING: TypeSet = TypeSet::of(InstanceType::String);

impl Branch {
    /// How much there is to copy when the branch splits.
    fn weight(&self) -> u64 {
        let leaves = self.holds.len() + self.fails.len();
        let variables = self.taken.len() + self.met.len();
        let copied = (leaves + variables + self.choices.len()) as u64;
        copied + self.numbers.weight() + self.strings.weight()
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

    /// The types of which the branch is known to accept an instance if it stands: no leaf
    /// that must hold is about them. A leaf that must not hold is about every type that is
    /// left.
    fn free(&self) -> TypeSet {
        if self.fails.is_empty() {
            self.types.intersection(self.covered.complement())
        } else {
            TypeSet::NONE
        }
    }

    /// What stands between the branch and an instance: a leaf, if one is about a type that
    /// is left. Without one, every type that is left is free of leaves, and of those only
    /// numbers can fail to give an instance.
    fn cause(&self, terms: &Terms) -> Cause {
        let about_what_is_left = |leaf: &&LeafId| {
            let about = terms.leaf(**leaf).domain;
            !about.intersection(self.types).is_empty()
        };
        let must_not_hold = self.fails.first();
        let leaf = must_not_hold.or_else(|| self.holds.iter().find(about_what_is_left));
        leaf.map_or(Cause::Number, |leaf| Cause::Leaf(*leaf))
    }
}

struct Engine<'c> {
    context: &'c mut Context,
    unfoldings: Vec<Unfolding>,
    /// What some branch depends on, once there is such a branch. From then on the answer is
    /// not `Yes`.
    depends_on: Option<Cause>,
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
        // What was asked of numbers may have left none. Then the branch has no number among
        // its instances, and stands by what else it accepts. So it is with strings.
        if std::mem::take(&mut branch.numbers_asked)
            && branch.types.contains(InstanceType::Number)
            && branch.numbers.is_empty(&mut self.context.budget)?
            && !branch.restrict(NUMBER.complement())
        {
            return Ok(false);
        }
        let Context {
            languages, budget, ..
        } = &mut *self.context;
        if std::mem::take(&mut branch.strings_asked)
            && branch.types.contains(InstanceType::String)
            && branch.strings.is_empty(languages, budget)?
        {
            return Ok(branch.restrict(STRING.complement()));
        }
        Ok(true)
    }

    /// An instance that the branch accepts, if it is known to accept one that can be given:
    /// one of the first type that no leaf is about and that has one.
    fn instance(&mut self, branch: &Branch) -> Result<Option<Value>, Exhausted> {
        let Context {
            languages, budget, ..
        } = &mut *self.context;
        let of = generate::Left {
            may_be_true: branch.booleans[1],
            numbers: &branch.numbers,
            strings: &branch.strings,
        };
        for kind in branch.free().iter() {
            let instance = generate::instance(kind, &of, languages, budget)?;
            if instance.is_some() {
                return Ok(instance);
            }
        }
        Ok(None)
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
        let found = self.context.terms.term(term);
        let stands = match (found, negated) {
            (Term::True, false) | (Term::False, true) => true,
            (Term::False, false) | (Term::True, true) => false,
            (Term::TypeIs(types), false) => branch.restrict(*types),
            (Term::TypeIs(types), true) => branch.restrict(types.complement()),
            (Term::BoolConst(value), false) => branch.restrict(BOOLEAN) && branch.exclude(!*value),
            (Term::BoolConst(value), true) => branch.exclude(*value),
            // Only a number is a certain number. What is no number satisfies every other
            // term about numbers, so only a number fails one.
            (
                Term::NumConst(_)
                | Term::Min(_)
                | Term::ExMin(_)
                | Term::Max(_)
                | Term::ExMax(_)
                | Term::Mof(_),
                _,
            ) => {
                let of_numbers_only = negated != matches!(found, Term::NumConst(_));
                let stands = !of_numbers_only || branch.restrict(NUMBER);
                if stands && branch.types.contains(InstanceType::Number) {
                    branch.numbers.take(found, negated);
                    branch.numbers_asked = true;
                }
                stands
            }
            // The same for strings: only a string is a certain string, and only a string
            // fails another term about strings.
            (Term::StrConst(_) | Term::Patt(_) | Term::MinLen(_) | Term::MaxLen(_), _) => {
                let of_strings_only = negated != matches!(found, Term::StrConst(_));
                let stands = !of_strings_only || branch.restrict(STRING);
                if stands && branch.types.contains(InstanceType::String) {
                    let languages = &mut self.context.languages;
                    branch.strings.take(found, negated, languages);
                    branch.strings_asked = true;
                }
                stands
            }
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

    /// Why a check ended in `Unknown`, which it must.
    fn reason(a: &Value, b: &Value) -> Reason {
        match verdict(a, b) {
            Verdict::Unknown { reason } => reason,
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
        let long = json!({"minItems": 3});
        let long_list = json!({"type": "array", "minItems": 3});
        yes(&long, &long);
        yes(&long, &long_list);
        // The other way, an instance that is no array tells them apart.
        assert_eq!(counterexample(&long_list, &long), json!(null));
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
        // No number is too short a list, and no list is too small a number.
        yes(&json!({"minItems": 3}), &json!({"type": "integer"}));
        yes(
            &json!({"minimum": 3}),
            &json!({"type": "array", "minItems": 1}),
        );
        // An object satisfies the leaf about arrays, so an object is an instance.
        let either = json!({"type": ["array", "object"], "minItems": 3});
        assert_eq!(counterexample(&json!({"type": "null"}), &either), json!({}));
        assert_eq!(
            depends_on(
                &json!({"type": "array", "minItems": 3}),
                &json!({"type": "array"})
            ),
            (Side::A, "#/minItems".to_owned())
        );
        // A constant is of the type of its value.
        yes(&json!({"type": "array"}), &json!({"const": [1]}));
        yes(
            &json!({"enum": [[1], 1, null]}),
            &json!({"enum": [null, [1]]}),
        );
        assert_eq!(
            counterexample(&json!({"const": [1]}), &json!({"type": "number"})),
            json!(0)
        );
        assert_eq!(
            depends_on(&json!({"const": [1]}), &json!({"type": "array"})),
            (Side::A, "#/const".to_owned())
        );
    }

    #[test]
    fn lengths_are_compared_as_counts_of_characters() {
        yes(&json!({"minLength": 1}), &json!({"minLength": 2}));
        assert_eq!(
            counterexample(&json!({"minLength": 2}), &json!({"minLength": 1})),
            json!("a")
        );
        yes(&json!({"maxLength": 3}), &json!({"maxLength": 2}));
        assert_eq!(
            counterexample(&json!({"maxLength": 2}), &json!({"maxLength": 3})),
            json!("aaa")
        );
        yes(
            &json!({"minLength": 2, "maxLength": 4}),
            &json!({"type": "string", "minLength": 3, "maxLength": 3}),
        );
        // What is no string satisfies every bound.
        assert_eq!(
            counterexample(&json!({"type": "string"}), &json!({"minLength": 2})),
            json!(null)
        );
        yes(&json!({"minLength": 2}), &json!({"type": "number"}));
        // A schema that no string satisfies still accepts what is no string.
        let none = json!({"minLength": 3, "maxLength": 2});
        let no_string = json!({"not": {"type": "string"}});
        yes(&none, &no_string);
        yes(&no_string, &none);
        assert_eq!(counterexample(&json!(false), &none), json!(null));
        yes(
            &json!(false),
            &json!({"type": "string", "minLength": 3, "maxLength": 2}),
        );
        // A negated bound is a bound on strings only.
        let short = json!({"not": {"minLength": 2}});
        yes(&short, &json!({"type": "string", "maxLength": 1}));
        yes(&json!({"type": "string", "maxLength": 1}), &short);
        assert_eq!(
            counterexample(&short, &json!({"type": "string"})),
            json!("aa")
        );
        assert_eq!(
            counterexample(&short, &json!({"type": "null"})),
            json!(null)
        );
        // A character is counted once, however many bytes it takes.
        yes(&json!({"maxLength": 1}), &json!({"enum": ["é", "𝄞", ""]}));
        assert_eq!(
            counterexample(&json!({"maxLength": 1}), &json!({"const": "e\u{301}"})),
            json!("e\u{301}")
        );
    }

    #[test]
    fn a_pattern_is_compared_as_the_language_that_it_is() {
        let (lower, letters) = (
            json!({"pattern": "^[a-z]+$"}),
            json!({"pattern": "^[a-zA-Z]+$"}),
        );
        yes(&letters, &lower);
        assert_eq!(counterexample(&lower, &letters), json!("A"));
        // A pattern matches anywhere in the string.
        yes(&json!({"pattern": "a"}), &json!({"pattern": "^a"}));
        assert_eq!(
            counterexample(&json!({"pattern": "^a"}), &json!({"pattern": "a"})),
            json!("ba")
        );
        // Two patterns that are written differently and say the same.
        let (one, other) = (
            json!({"pattern": "^(a|b)c*$"}),
            json!({"pattern": "^[ab](?:c+)?$"}),
        );
        yes(&one, &other);
        yes(&other, &one);
        // To the `regex` crate a digit is any digit of Unicode.
        let (digits, ascii) = (json!({"pattern": r"^\d+$"}), json!({"pattern": "^[0-9]+$"}));
        yes(&digits, &ascii);
        assert_eq!(counterexample(&ascii, &digits), json!("٠"));
        // What is no string satisfies every pattern.
        assert_eq!(
            counterexample(&json!({"type": "string"}), &lower),
            json!(null)
        );
        yes(&lower, &json!({"type": "number"}));
        // A pattern and the bounds on the length that say the same.
        let counted = json!({"type": "string", "pattern": "^[a-z]{2,4}$"});
        let bounded =
            json!({"type": "string", "pattern": "^[a-z]*$", "minLength": 2, "maxLength": 4});
        yes(&counted, &bounded);
        yes(&bounded, &counted);
        assert_eq!(
            counterexample(&counted, &json!({"pattern": "^[a-z]*$", "maxLength": 4})),
            json!(null)
        );
        assert_eq!(
            counterexample(
                &counted,
                &json!({"type": "string", "pattern": "^[a-z]*$", "maxLength": 5})
            ),
            json!("")
        );
        // A negated pattern is a string that the pattern does not match.
        let other = json!({"not": {"pattern": "a"}});
        yes(&other, &json!({"type": "string", "pattern": "^[b-z]*$"}));
        assert_eq!(
            counterexample(&other, &json!({"type": "string"})),
            json!("a")
        );
        assert_eq!(
            counterexample(&other, &json!({"type": "null"})),
            json!(null)
        );
        // The connectives take patterns apart too.
        let either = json!({"anyOf": [{"pattern": "^a"}, {"pattern": "^b"}]});
        yes(&either, &json!({"pattern": "^[ab]"}));
        yes(&json!({"pattern": "^[ab]"}), &either);
        assert_eq!(
            counterexample(&either, &json!({"pattern": "^[a-c]"})),
            json!("c")
        );
    }

    #[test]
    fn a_constant_is_one_string() {
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
            counterexample(&json!({"const": "a"}), &json!({"enum": ["a", "b"]})),
            json!("b")
        );
        assert_eq!(
            counterexample(&json!({"const": "a"}), &json!({"type": "string"})),
            json!("")
        );
        assert_eq!(
            counterexample(&json!({"enum": ["", "a"]}), &json!({"type": "string"})),
            json!("b")
        );
        // A few strings, and the pattern that matches just these.
        let few = json!({"enum": ["a", "b"]});
        yes(&few, &json!({"type": "string", "pattern": "^[ab]$"}));
        yes(&json!({"pattern": "^[ab]$"}), &few);
        assert_eq!(
            counterexample(&few, &json!({"type": "string", "pattern": "^[a-c]$"})),
            json!("c")
        );
        assert_eq!(
            counterexample(
                &json!({"pattern": "^a"}),
                &json!({"enum": ["a", "ba", "ab"]})
            ),
            json!("ba")
        );
        yes(&json!({"minLength": 1}), &few);
        assert_eq!(
            counterexample(&json!({"minLength": 2}), &json!({"enum": ["ab", "é", 1]})),
            json!("é")
        );
        // Every string but one.
        let not_a = json!({"not": {"const": "a"}});
        assert_eq!(
            counterexample(&not_a, &json!({"type": "string"})),
            json!("a")
        );
        yes(&not_a, &json!({"type": "string", "minLength": 2}));
        yes(&not_a, &json!({"type": "number"}));
        yes(&not_a, &json!({"pattern": "^b"}));
        yes(
            &json!({"type": "string", "not": {"enum": ["a", "b"]}}),
            &json!({"type": "string", "not": {"pattern": "^[ab]$"}}),
        );
        // A string in a constant of another type is not looked at yet.
        assert_eq!(
            depends_on(&json!({"const": ["a"]}), &json!({"const": ["b"]})),
            (Side::A, "#/const".to_owned())
        );
    }

    #[test]
    fn a_format_is_the_language_of_its_pattern() {
        let (date, text) = (json!({"format": "date"}), json!({"type": "string"}));
        yes(&text, &json!({"type": "string", "format": "date"}));
        assert_eq!(counterexample(&date, &text), json!(""));
        assert_eq!(counterexample(&text, &date), json!(null));
        yes(&date, &json!({"const": "2024-02-29"}));
        assert_eq!(
            counterexample(&date, &json!({"const": "2023-02-29"})),
            json!("2023-02-29")
        );
        yes(&json!({"maxLength": 10, "minLength": 10}), &date);
        yes(&json!({"pattern": "^[0-9]{4}-[01]"}), &date);
        assert_eq!(
            counterexample(&json!({"pattern": "^[0-9]{4}-0"}), &date),
            json!("0000-10-01")
        );
        // A date-time begins with a date, and a URI is a reference.
        let begins_with_a_date = json!({"if": {"type": "string"}, "then": {"pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}[Tt]"}});
        yes(&begins_with_a_date, &json!({"format": "date-time"}));
        yes(
            &json!({"format": "uri-reference"}),
            &json!({"format": "uri"}),
        );
        assert_eq!(
            counterexample(
                &json!({"format": "uri"}),
                &json!({"format": "uri-reference"})
            ),
            json!("")
        );
        // Whether a time with the second 60 is one is left open, and nothing else is.
        let time = json!({"format": "time"});
        yes(&time, &time.clone());
        yes(
            &time,
            &json!({"enum": ["12:00:00Z", "23:59:59.5+01:00", 1]}),
        );
        assert_eq!(
            counterexample(&time, &json!({"enum": ["12:00:00Z", "23:59:61Z"]})),
            json!("23:59:61Z")
        );
        assert_eq!(
            depends_on(&time, &json!({"enum": ["12:00:00Z", "23:59:60Z"]})),
            (Side::A, "#/format".to_owned())
        );
        // What holds for every time, with whichever second, holds.
        yes(&json!({"pattern": "^[0-9]{2}:[0-9]{2}:"}), &time);
        yes(
            &json!({"type": "string", "minLength": 9}),
            &json!({"type": "string", "format": "time"}),
        );
        assert_eq!(
            counterexample(&json!({"maxLength": 9}), &time),
            json!("00:00:00.0z")
        );
        // Where the grammar of a format allows what validators do not take, that is left
        // open too: a number of an address with a zero before it, and a duration in small
        // letters.
        let address = json!({"format": "ipv4"});
        yes(&address, &json!({"enum": ["1.2.3.4", "0.0.0.0", 1]}));
        assert_eq!(
            counterexample(&address, &json!({"enum": ["1.2.3.4", "1.2.3.256"]})),
            json!("1.2.3.256")
        );
        assert_eq!(
            depends_on(&address, &json!({"const": "01.2.3.4"})),
            (Side::A, "#/format".to_owned())
        );
        assert_eq!(
            depends_on(
                &json!(false),
                &json!({"format": "ipv4", "const": "01.2.3.4"})
            ),
            (Side::B, "#/format".to_owned())
        );
        let duration = json!({"format": "duration"});
        yes(&duration, &json!({"enum": ["P1D", "PT0S"]}));
        assert_eq!(
            depends_on(&duration, &json!({"const": "p1d"})),
            (Side::A, "#/format".to_owned())
        );
        assert_eq!(
            counterexample(&duration, &json!({"const": "p1"})),
            json!("p1")
        );
        yes(&json!({"pattern": "^[Pp]"}), &duration);
        // A format that is not modelled is a leaf, and so is a pattern that is not.
        let host = json!({"format": "hostname"});
        yes(&host, &host.clone());
        yes(&text, &json!({"type": "string", "format": "hostname"}));
        assert_eq!(depends_on(&host, &text), (Side::A, "#/format".to_owned()));
        let word = json!({"pattern": r"\bword\b"});
        yes(&word, &word.clone());
        assert_eq!(depends_on(&word, &text), (Side::A, "#/pattern".to_owned()));
    }

    #[test]
    fn a_pattern_that_is_asked_for_and_against_costs_no_dfa() {
        // The pattern takes thousands of steps to become a DFA.
        let pattern = "^(?:[a-f]{50}[0-9]{50}){20}$";
        let (a, b) = (
            json!({"pattern": pattern}),
            json!({"pattern": pattern, "minLength": 1}),
        );
        let checker = Checker::new().budget(100);
        let check = checker.check(&a, &b).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        assert!(check.steps < 20, "{}", check.steps);
        // The other way the DFA has to say that the pattern does not match the
        // empty string.
        let unknown = Verdict::Unknown {
            reason: Reason::Budget,
        };
        assert_eq!(checker.check(&b, &a).unwrap().verdict, unknown);
        let check = Checker::new().check(&b, &a).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        assert!(check.steps > 4_000, "{}", check.steps);
        // With a type next to the pattern, the negation of A is a split. The branch asks
        // whether a string is left before it splits, and by then the pattern is an
        // DFA, although the split then cancels it.
        let typed = |schema: &Value| {
            let mut schema = schema.clone();
            schema["type"] = json!("string");
            schema
        };
        let check = Checker::new().check(&typed(&a), &typed(&b)).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        assert!(check.steps > 4_000, "{}", check.steps);
    }

    #[test]
    fn bounds_are_compared_as_the_numbers_they_are() {
        yes(&json!({"minimum": 3}), &json!({"minimum": 5}));
        yes(&json!({"minimum": 3}), &json!({"minimum": 3.0}));
        assert_eq!(
            counterexample(&json!({"minimum": 5}), &json!({"minimum": 3})),
            json!(3)
        );
        // An end that is itself outside.
        yes(&json!({"minimum": 0}), &json!({"exclusiveMinimum": 0}));
        assert_eq!(
            counterexample(&json!({"exclusiveMinimum": 0}), &json!({"minimum": 0})),
            json!(0)
        );
        yes(&json!({"exclusiveMaximum": 10}), &json!({"maximum": 9.5}));
        assert_eq!(
            counterexample(&json!({"exclusiveMaximum": 10}), &json!({"maximum": 10})),
            json!(10)
        );
        // Both ends, and a number that is beyond one of them by a little.
        let range = json!({"minimum": 1, "maximum": 5});
        yes(&range, &json!({"minimum": 2, "exclusiveMaximum": 5}));
        yes(
            &range,
            &json!({"type": "number", "minimum": 1.5, "maximum": 4.5}),
        );
        assert_eq!(
            counterexample(&range, &json!({"minimum": 2, "maximum": 5.5})),
            json!(5.1)
        );
        assert_eq!(
            counterexample(&range, &json!({"minimum": 0.5, "maximum": 2})),
            json!(0.5)
        );
        // What is no number satisfies every bound.
        assert_eq!(
            counterexample(&json!({"type": "number"}), &range),
            json!(null)
        );
        yes(&range, &json!({"type": "string"}));
        // A negated bound is a bound on numbers only.
        let below = json!({"not": {"minimum": 5}});
        yes(&below, &json!({"type": "number", "exclusiveMaximum": 5}));
        yes(&json!({"type": "number", "exclusiveMaximum": 5}), &below);
        assert_eq!(
            counterexample(&below, &json!({"type": "string"})),
            json!("")
        );
        assert_eq!(
            counterexample(&below, &json!({"type": "number", "maximum": 5})),
            json!(5)
        );
    }

    #[test]
    fn a_schema_that_no_number_satisfies_still_accepts_what_is_no_number() {
        let none = json!({"minimum": 5, "maximum": 3});
        let no_number = json!({"not": {"type": "number"}});
        yes(&none, &no_number);
        yes(&no_number, &none);
        assert_eq!(counterexample(&json!(false), &none), json!(null));
        // With the type, nothing is left.
        let never = [
            json!({"type": "number", "minimum": 5, "maximum": 3}),
            json!({"type": "number", "minimum": 5, "exclusiveMaximum": 5}),
            json!({"type": "integer", "exclusiveMinimum": 0, "exclusiveMaximum": 1}),
            json!({"type": "number", "multipleOf": 2, "not": {"multipleOf": 1}}),
            json!({"type": "integer", "const": 2.5}),
        ];
        for never in &never {
            yes(&json!(false), never);
        }
    }

    #[test]
    fn an_integer_is_a_number_that_is_a_multiple_of_one() {
        let (integer, number) = (json!({"type": "integer"}), json!({"type": "number"}));
        yes(&number, &integer);
        assert_eq!(counterexample(&integer, &number), json!(0.1));
        yes(&integer, &json!({"type": "number", "multipleOf": 2}));
        yes(&integer, &json!({"type": "number", "multipleOf": 1.0}));
        yes(&json!({"type": "number", "multipleOf": 1}), &integer);
        assert_eq!(
            counterexample(&json!({"multipleOf": 2}), &integer),
            json!(1)
        );
        // The integers above zero begin at one, and the numbers above zero do not.
        let from_one = json!({"minimum": 1});
        yes(
            &from_one,
            &json!({"type": "integer", "exclusiveMinimum": 0}),
        );
        assert_eq!(
            counterexample(&from_one, &json!({"exclusiveMinimum": 0})),
            json!(0.1)
        );
        // A string satisfies what is asked of an integer, and zero is the first number.
        let either = json!({"type": ["integer", "string"]});
        yes(&either, &json!({"type": "string"}));
        yes(&either, &json!({"type": "integer"}));
        assert_eq!(counterexample(&json!({"type": "null"}), &either), json!(0));
        assert_eq!(
            counterexample(&json!({"type": "string"}), &either),
            json!(0)
        );
        assert_eq!(counterexample(&either, &number), json!(0.1));
    }

    #[test]
    fn multiples_are_compared_as_the_numbers_they_are() {
        // As floats, 0.0075 is no multiple of 0.0001, and 0.07 none of 0.01.
        yes(
            &json!({"multipleOf": 0.0001}),
            &json!({"multipleOf": 0.0075}),
        );
        yes(&json!({"multipleOf": 0.01}), &json!({"multipleOf": 0.07}));
        yes(&json!({"multipleOf": 2}), &json!({"multipleOf": 6}));
        assert_eq!(
            counterexample(&json!({"multipleOf": 6}), &json!({"multipleOf": 2})),
            json!(2)
        );
        assert_eq!(
            counterexample(&json!({"multipleOf": 0.3}), &json!({"multipleOf": 0.1})),
            json!(1)
        );
        assert_eq!(
            counterexample(&json!({"multipleOf": 0.5}), &json!({"multipleOf": 0.25})),
            json!(0.25)
        );
        // A multiple of two numbers is one of the least that both divide.
        let both = json!({"allOf": [{"multipleOf": 4}, {"multipleOf": 6}]});
        yes(&both, &json!({"multipleOf": 12}));
        yes(&json!({"multipleOf": 12}), &both);
        assert_eq!(counterexample(&json!({"multipleOf": 24}), &both), json!(12));
        // What is no multiple of two is a number.
        let odd = json!({"type": "integer", "not": {"multipleOf": 2}});
        let uneven = json!({"not": {"multipleOf": 2}});
        yes(&uneven, &odd);
        assert_eq!(counterexample(&odd, &uneven), json!(0.1));
        assert_eq!(
            counterexample(&uneven, &json!({"type": "null"})),
            json!(null)
        );
        yes(&json!({"type": "integer"}), &odd);
        assert_eq!(counterexample(&odd, &json!({"type": "integer"})), json!(0));
        // Between two bounds there may be no multiple, or one that is excluded.
        yes(
            &json!(false),
            &json!({"type": "number", "multipleOf": 5, "minimum": 1, "maximum": 4}),
        );
        yes(
            &json!({"const": 9}),
            &json!({"type": "number", "multipleOf": 3, "minimum": 4, "maximum": 11, "not": {"multipleOf": 2}}),
        );
    }

    #[test]
    fn a_constant_is_one_number_however_it_is_written() {
        yes(&json!({"const": 1}), &json!({"const": 1.0}));
        yes(&json!({"enum": [1.0, 2]}), &json!({"enum": [2.0, 1]}));
        yes(&json!({"type": "integer"}), &json!({"const": 5.0}));
        assert_eq!(
            counterexample(&json!({"type": "integer"}), &json!({"const": 2.5})),
            json!(2.5)
        );
        yes(
            &json!({"minimum": 0.1, "maximum": 0.3}),
            &json!({"enum": [0.1, 0.2, 0.3]}),
        );
        assert_eq!(
            counterexample(&json!({"const": 1}), &json!({"enum": [1, 2]})),
            json!(2)
        );
        // A few numbers, and the integers of the same range.
        let few = json!({"enum": [1, 2, 3]});
        let range = json!({"type": "integer", "minimum": 1, "maximum": 3});
        yes(&few, &range);
        yes(&range, &few);
        assert_eq!(counterexample(&json!({"enum": [1, 3]}), &range), json!(2));
        assert_eq!(
            counterexample(&few, &json!({"minimum": 1, "maximum": 3})),
            json!(null)
        );
        // Every number but one is what lies below it and what lies above.
        let not_one = json!({"type": "number", "not": {"const": 1}});
        yes(&not_one, &json!({"type": "number", "exclusiveMinimum": 1}));
        assert_eq!(
            counterexample(&not_one, &json!({"type": "number"})),
            json!(1)
        );
        assert_eq!(counterexample(&json!({"const": 1}), &not_one), json!(0));
        // A number in a constant of another type is not looked at yet.
        assert_eq!(
            depends_on(&json!({"const": [1]}), &json!({"const": [1.0]})),
            (Side::A, "#/const".to_owned())
        );
    }

    #[test]
    fn the_connectives_take_numbers_apart_too() {
        // A number from 0 to 10 satisfies both, and so does what is no number.
        let outside = json!({"oneOf": [{"minimum": 0}, {"maximum": 10}]});
        yes(&outside, &json!({"type": "number", "exclusiveMinimum": 10}));
        yes(&json!({"type": "number"}), &outside);
        assert_eq!(
            counterexample(&outside, &json!({"type": "number"})),
            json!(0)
        );
        assert_eq!(
            counterexample(&outside, &json!({"type": "string"})),
            json!("")
        );
        // Two ranges that meet are one range.
        let either = json!({"anyOf": [{"maximum": 5}, {"minimum": 5}]});
        yes(&either, &json!(true));
        let apart = json!({"anyOf": [{"maximum": 4}, {"minimum": 5}]});
        assert_eq!(counterexample(&apart, &json!(true)), json!(4.1));
        yes(&apart, &json!({"type": "integer"}));
        // Large numbers are multiples of ten, and small ones may be anything.
        let rounded = json!({"if": {"minimum": 100}, "then": {"multipleOf": 10}});
        yes(&rounded, &json!({"maximum": 99.5}));
        yes(&rounded, &json!({"enum": [7, 100, 250]}));
        assert_eq!(
            counterexample(&rounded, &json!({"type": "integer"})),
            json!(101)
        );
    }

    #[test]
    fn a_number_that_no_json_value_holds_is_no_counterexample() {
        // Every number between two floats that are next to each other has more digits than
        // a float keeps.
        let between = json!({
            "type": "number",
            "exclusiveMinimum": 0.1,
            "exclusiveMaximum": 0.10000000000000002,
        });
        assert_eq!(reason(&json!(false), &between), Reason::Unrepresentable);
        // So has every number above the largest float.
        let beyond = json!({"type": "number", "exclusiveMinimum": f64::MAX});
        assert_eq!(reason(&json!(false), &beyond), Reason::Unrepresentable);
        assert_eq!(
            reason(&json!({"type": "integer"}), &beyond),
            Reason::Unrepresentable
        );
        // What holds for every number holds for these.
        yes(&json!({"minimum": 0}), &between);
        yes(&json!({"type": "number"}), &beyond);
        yes(&json!({"minimum": 1e308}), &beyond);
        // Another instance is given where there is one, and a leaf is named where there is one.
        let or_null = json!({"type": ["number", "null"], "exclusiveMinimum": f64::MAX});
        assert_eq!(counterexample(&json!(false), &or_null), json!(null));
        let or_list =
            json!({"type": ["number", "array"], "exclusiveMinimum": f64::MAX, "minItems": 1});
        assert_eq!(
            depends_on(&json!(false), &or_list),
            (Side::B, "#/minItems".to_owned())
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
        // Twenty choices between two leaves about arrays: a million branches, none of which
        // is refuted and none of which gives an instance. The first one settles the answer.
        let choice = |n: u32| json!({"anyOf": [{"minItems": n}, {"maxItems": n + 100}]});
        let b = json!({"type": "array", "allOf": (0..20).map(choice).collect::<Vec<_>>()});
        let a = json!({"type": "array", "uniqueItems": true});
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
