//! The engine: is there an instance that B accepts and A does not?
//!
//! `all[B, not A]` is taken apart into *branches*. A branch is a conjunction of what the
//! engine knows how to combine: the types an instance may still have, the booleans, the
//! numbers, the strings, the objects and the arrays it may still be, the leaves that must
//! hold and those that must not, and the variables taken for true or for false. A
//! disjunction splits a branch in as many as it has alternatives.
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
//!
//! # Values inside an instance
//!
//! What a branch says about objects is about the values of their properties, and what it
//! says about arrays is about their items. Such a value is an instance of its own. What a
//! value has to satisfy is a *c-reference*: a set of variables, each as it stands or
//! negated. Whether there is such a value is the question that the check began with, asked
//! of other schemas, and it is answered the same way: by a *task*, which takes the
//! c-reference apart into branches. The answer of a task is kept, so that each c-reference
//! is decided once.
//!
//! A branch that needs to know of a c-reference waits while a task decides it. The tasks
//! that wait are a stack, and none of this recurses, however deep the schemas go.
//!
//! A schema may hold itself in a property or in an item, and then a task comes to ask for
//! a c-reference that a task below it on the stack is still deciding. A value is finite, so
//! such a c-reference accepts what it can be shown to accept without itself: it is taken
//! to accept nothing. An answer that was found that way holds only as long as the task
//! below is at work, unless it is an instance, which nothing can take back. So it is kept
//! apart, and becomes an answer for good when the task below ends without an instance
//! either.

#[cfg(test)]
mod exhaustive;

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use serde_json::Value;

use crate::canonical::array::Arrays;
use crate::canonical::number::Numbers;
use crate::canonical::object::{Objects, Partitions};
use crate::canonical::string::Strings;
use crate::canonical::{Left, Solver};
use crate::context::{Budget, Context, Exhausted};
use crate::generate;
use crate::language::{LanguageId, Languages};
use crate::term::{CRefId, InstanceType, LeafId, Term, TermId, Terms, TypeSet, VarId};

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
    /// The branch accepts an object, and none that is nested no deeper than [`DEEPEST`].
    Depth,
}

/// How many objects and arrays an instance may hold inside one another. `serde_json` reads
/// no deeper text back, and copying or dropping a value recurses once for each level, so
/// this is also what keeps a deep counterexample from running out of stack.
pub(crate) const DEEPEST: u32 = 127;

/// What the engine knows of a c-reference: whether an instance satisfies it.
#[derive(Debug, Clone)]
pub(crate) enum Found {
    /// None does.
    Nothing,
    /// One may, and this stands between the engine and an instance.
    Unknown(Cause),
    Instance(Rc<Witness>),
}

/// An instance that the engine gives.
///
/// It is kept as what it is made of and not as a value: an array and an object share the
/// instances inside them with whatever else holds those, and an array holds an instance that
/// many positions in a row have once, with how many they are. So to put an instance together
/// costs nothing beyond finding the instances inside it, however large those are and however
/// many positions have one. Most instances are found for a c-reference that the
/// counterexample does not come to hold, or for a check that has none, and are never
/// written out. The one that is the answer of the check is written out once.
#[derive(Debug)]
pub(crate) struct Witness {
    made_of: MadeOf,
    /// How many values it is made of, itself among them. Those inside it are what it costs
    /// to write out.
    pub size: u64,
    /// How many objects and arrays it holds inside one another, itself among them.
    pub depth: u32,
}

/// What an instance is made of.
#[derive(Debug)]
enum MadeOf {
    /// A value that holds no other.
    Plain(Value),
    /// The items of an array in order: an instance, and how many positions in a row have it.
    Items(Vec<(Rc<Witness>, u64)>),
    /// The properties of an object.
    Properties(Vec<(String, Rc<Witness>)>),
}

impl Witness {
    /// A value that holds no other.
    pub(crate) fn plain(value: Value) -> Rc<Self> {
        let depth = u32::from(value.is_object() || value.is_array());
        Rc::new(Self {
            made_of: MadeOf::Plain(value),
            size: 1,
            depth,
        })
    }

    /// An array of these items: each instance at so many positions in a row.
    pub(crate) fn array(items: Vec<(Rc<Self>, u64)>) -> Rc<Self> {
        let sizes = items
            .iter()
            .map(|(item, count)| item.size.saturating_mul(*count));
        let size = sizes.fold(1_u64, u64::saturating_add);
        let deepest = items.iter().map(|(item, _)| item.depth).max();
        Rc::new(Self {
            made_of: MadeOf::Items(items),
            size,
            depth: deepest.unwrap_or(0) + 1,
        })
    }

    /// An object of these properties.
    pub(crate) fn object(properties: Vec<(String, Rc<Self>)>) -> Rc<Self> {
        let sizes = properties.iter().map(|(_, value)| value.size);
        let size = sizes.fold(1_u64, u64::saturating_add);
        let deepest = properties.iter().map(|(_, value)| value.depth).max();
        Rc::new(Self {
            made_of: MadeOf::Properties(properties),
            size,
            depth: deepest.unwrap_or(0) + 1,
        })
    }

    /// The instance as a value.
    ///
    /// # Errors
    ///
    /// When the budget does not cover writing it out, which is a step for every value
    /// inside it. What the instance holds once for many places is a value of its own at
    /// each of them.
    pub(crate) fn written(&self, budget: &mut Budget) -> Result<Value, Exhausted> {
        budget.charge(self.size - 1)?;
        Ok(self.value())
    }

    /// Writes the instance out. This recurses once for each level, and an instance has no
    /// more than [`DEEPEST`] of them.
    fn value(&self) -> Value {
        match &self.made_of {
            MadeOf::Plain(value) => value.clone(),
            MadeOf::Items(items) => {
                let mut values = Vec::new();
                for (item, count) in items {
                    let Some(others) = count.checked_sub(1) else {
                        continue;
                    };
                    let value = item.value();
                    for _ in 0..others {
                        values.push(value.clone());
                    }
                    values.push(value);
                }
                Value::Array(values)
            }
            MadeOf::Properties(properties) => {
                let written = |(name, value): &(String, Rc<Self>)| (name.clone(), value.value());
                Value::Object(properties.iter().map(written).collect())
            }
        }
    }
}

/// Decides whether the schema of `a` accepts every instance that the schema of `b` accepts.
///
/// # Errors
///
/// When the budget does not cover the work.
pub(crate) fn decide(context: &mut Context, a: VarId, b: VarId) -> Result<Outcome, Exhausted> {
    let terms = &mut context.terms;
    let (accepted, rejected) = (terms.literal(b, false), terms.literal(a, true));
    let both = terms.both(accepted, rejected);
    let mut engine = Engine {
        context,
        unfoldings: Vec::new(),
        tasks: Vec::new(),
        found: HashMap::new(),
        assumed: HashMap::new(),
        at_work: HashMap::new(),
        answers: 0,
        names: HashMap::new(),
        partitions: Partitions::default(),
        dead_ends: HashMap::new(),
    };
    Ok(match engine.decide(both)? {
        Found::Nothing => Outcome::Yes,
        // The counterexample is the one instance that is written out.
        Found::Instance(witness) => Outcome::No(witness.written(&mut engine.context.budget)?),
        Found::Unknown(cause) => Outcome::Unknown(cause),
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
    /// And for the objects. An object may be left only as far as the engine knows: then
    /// this stands between the branch and an object.
    objects: Objects,
    objects_asked: bool,
    objects_depend: Option<Cause>,
    /// And the same for the arrays.
    arrays: Arrays,
    arrays_asked: bool,
    arrays_depend: Option<Cause>,
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
            objects: Objects::default(),
            objects_asked: false,
            objects_depend: None,
            arrays: Arrays::default(),
            arrays_asked: false,
            arrays_depend: None,
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
const ARRAY: TypeSet = TypeSet::of(InstanceType::Array);
const OBJECT: TypeSet = TypeSet::of(InstanceType::Object);

impl Branch {
    /// How much there is to copy when the branch splits.
    fn weight(&self) -> u64 {
        let leaves = self.holds.len() + self.fails.len();
        let variables = self.taken.len() + self.met.len();
        let copied = (leaves + variables + self.choices.len()) as u64;
        let values = self.objects.weight() + self.arrays.weight();
        copied + self.numbers.weight() + self.strings.weight() + values
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

    /// Takes in a leaf that must hold, or with `negated` one that must not. Returns whether
    /// the branch still stands.
    fn take(&mut self, leaf: LeafId, negated: bool, terms: &Terms) -> bool {
        let about = terms.leaf(leaf).domain;
        if negated {
            // A leaf fails only for an instance that it is about.
            self.fails.insert(leaf);
            self.restrict(about) && !self.holds.contains(&leaf)
        } else {
            self.holds.insert(leaf);
            self.covered = self.covered.union(about);
            !self.fails.contains(&leaf)
        }
    }

    /// The types of which the branch is known to accept an instance if it stands: no leaf
    /// that must hold is about them, and the engine knows of nothing else in the way. A
    /// leaf that must not hold is about every type that is left.
    fn free(&self) -> TypeSet {
        if !self.fails.is_empty() {
            return TypeSet::NONE;
        }
        let mut free = self.types.intersection(self.covered.complement());
        if self.objects_depend.is_some() {
            free = free.intersection(OBJECT.complement());
        }
        if self.arrays_depend.is_some() {
            free = free.intersection(ARRAY.complement());
        }
        free
    }

    /// What stands between the branch and an instance: a leaf, if one is about a type that
    /// is left. Without one, every type that is left is free of leaves, and it is what
    /// stood in the way of an object, of an array or of a number.
    fn cause(&self, terms: &Terms, otherwise: Option<Cause>) -> Cause {
        let about_what_is_left = |leaf: &&LeafId| {
            let about = terms.leaf(**leaf).domain;
            !about.intersection(self.types).is_empty()
        };
        let must_not_hold = self.fails.first();
        let leaf = must_not_hold.or_else(|| self.holds.iter().find(about_what_is_left));
        let leaf = leaf.map(|leaf| Cause::Leaf(*leaf));
        leaf.or(self.objects_depend)
            .or(self.arrays_depend)
            .or(otherwise)
            .unwrap_or(Cause::Number)
    }
}

/// A c-reference that is being decided: the search for an instance that satisfies it.
struct Task {
    of: CRefId,
    /// A branch that was split, with the alternatives of the split that are still to come.
    /// The last split is the one at work: each of its alternatives is followed to its end
    /// before the next is made, so an instance is found without the alternatives after it,
    /// and a long `oneOf` is never written out. The task begins as a split in one.
    splits: Vec<Split>,
    /// A branch that waits for the engine to decide the c-references that it asked for.
    waiting: Option<Branch>,
    wanted: Vec<CRefId>,
    /// What some branch depends on, once there is such a branch. From then on the answer
    /// is not that nothing satisfies the c-reference.
    depends_on: Option<Cause>,
    /// The lowest task on the stack whose c-reference this one took to accept nothing
    /// because it was still at work, if it took any so.
    lowest: usize,
    /// How many answers had been found when the task began.
    began: u64,
}

/// A branch that was split on one of its disjunctions.
struct Split {
    branch: Branch,
    /// The alternatives of the disjunction that are still to come.
    still_to_come: Box<dyn Iterator<Item = Alternative>>,
    /// The disjunction, unless this is the split in one that a task begins as.
    choice: Option<Disjunction>,
    /// Whether the disjunction came with the alternative that the split below was at: it
    /// was not among those that the branch of that split had met.
    brought: bool,
    /// Whether an alternative stood by more than itself: it was not refuted when it had
    /// taken in what needs no split, and it did not end in a split on a disjunction that it
    /// brought and that left it with no alternative either.
    stood: bool,
}

/// A disjunction by what it says: a term, as it is or negated.
type Disjunction = (TermId, bool);

/// What a c-reference accepts as long as the tasks at work that it took to accept nothing
/// accept nothing.
struct Assumed {
    /// Nothing, or what stands between the engine and an instance.
    found: Found,
    /// The lowest of those tasks.
    lowest: usize,
    /// How many answers had been found when this one was.
    since: u64,
}

/// Whether a branch stands when it has taken in what needs no split.
enum Settled {
    Refuted,
    Stands,
    /// That depends on c-references of which the engine knows nothing yet.
    Needs(Vec<CRefId>),
}

/// What a branch that stands gives.
enum Given {
    Instance(Rc<Witness>),
    /// No instance, because of this.
    Depends(Cause),
    Needs(Vec<CRefId>),
}

struct Engine<'c> {
    context: &'c mut Context,
    unfoldings: Vec<Unfolding>,
    /// The c-references that are being decided. The last is at work, and each of the
    /// others waits for the one after it.
    tasks: Vec<Task>,
    /// What is known of a c-reference for good.
    found: HashMap<CRefId, Found>,
    /// What is known of one for as long as tasks that are at work accept nothing.
    assumed: HashMap<CRefId, Assumed>,
    /// Where on the stack the task of a c-reference is.
    at_work: HashMap<CRefId, usize>,
    /// How many answers were found so far.
    answers: u64,
    /// The language of the strings that the schema of a variable accepts, or `None` if no
    /// language says it.
    names: HashMap<VarId, Option<LanguageId>>,
    partitions: Partitions,
    /// How often each disjunction left a branch with no alternative: every one of them was
    /// refuted before it came to a split. A branch splits on the one that did so most often
    /// first, since it is likely to do so again whatever the other disjunctions are split to.
    dead_ends: HashMap<Disjunction, u32>,
}

impl Engine<'_> {
    /// Whether an instance satisfies a c-reference.
    fn decide(&mut self, of: CRefId) -> Result<Found, Exhausted> {
        if let Some(known) = self.known(of) {
            return Ok(known);
        }
        self.begin(of)?;
        loop {
            // What the task at work asked for comes first.
            let task = self.tasks.last_mut().expect("a task is at work");
            if let Some(wanted) = task.wanted.pop() {
                if self.known(wanted).is_none() {
                    self.begin(wanted)?;
                }
                continue;
            }
            let Some(found) = self.step()? else {
                continue;
            };
            self.end(&found);
            if self.tasks.is_empty() {
                return Ok(found);
            }
        }
    }

    /// What is known of a c-reference, if it was decided or is being decided.
    fn known(&self, of: CRefId) -> Option<Found> {
        match of {
            Terms::NOTHING => Some(Found::Nothing),
            Terms::ANYTHING => Some(Found::Instance(Witness::plain(Value::Null))),
            _ if self.at_work.contains_key(&of) => Some(Found::Nothing),
            _ => {
                let assumed = self.assumed.get(&of).map(|assumed| &assumed.found);
                self.found.get(&of).or(assumed).cloned()
            }
        }
    }

    /// Puts a task for a c-reference on the stack. It begins as one branch that takes in
    /// the variables: those that stand as they are first.
    fn begin(&mut self, of: CRefId) -> Result<(), Exhausted> {
        self.context.budget.charge(1)?;
        let terms = &mut self.context.terms;
        let literals = terms.literals(of).to_vec();
        let mut whole = Vec::with_capacity(literals.len());
        for negated in [false, true] {
            let of_a_kind = literals.iter().filter(|literal| literal.1 == negated);
            for (variable, _) in of_a_kind {
                whole.push(Item::new(terms.reference(*variable), negated));
            }
        }
        let whole: Box<dyn Iterator<Item = Alternative>> = Box::new(std::iter::once(whole));
        self.at_work.insert(of, self.tasks.len());
        self.tasks.push(Task {
            of,
            splits: vec![Split {
                branch: Branch::default(),
                still_to_come: whole,
                choice: None,
                brought: false,
                stood: true,
            }],
            waiting: None,
            wanted: Vec::new(),
            depends_on: None,
            lowest: usize::MAX,
            began: self.answers,
        });
        Ok(())
    }

    /// Takes the task at work off the stack and keeps what it found.
    fn end(&mut self, found: &Found) {
        let task = self.tasks.pop().expect("a task is at work");
        let at = self.tasks.len();
        self.at_work.remove(&task.of);
        self.answers += 1;
        let nothing = matches!(found, Found::Nothing);
        if !nothing {
            // What was found while this task was at work may have taken it to accept
            // nothing, which it does not.
            self.assumed
                .retain(|_, assumed| assumed.since <= task.began);
        }
        // An instance is one whatever else was taken to accept nothing. Anything else
        // holds for good only if no task that is still at work was taken so.
        let for_good = matches!(found, Found::Instance(_)) || task.lowest >= at;
        if for_good {
            if nothing {
                // And so does everything that only took this task so.
                let settled = |assumed: &Assumed| assumed.lowest >= at;
                let ids: Vec<CRefId> = self
                    .assumed
                    .iter()
                    .filter(|(_, assumed)| settled(assumed))
                    .map(|(of, _)| *of)
                    .collect();
                for of in ids {
                    let assumed = self.assumed.remove(&of).expect("it was just found");
                    self.found.insert(of, assumed.found);
                }
            }
            self.found.insert(task.of, found.clone());
            return;
        }
        if nothing {
            // What took this task to accept nothing was right as far as this task was.
            for assumed in self.assumed.values_mut() {
                if assumed.lowest >= at {
                    assumed.lowest = task.lowest;
                }
            }
        }
        let assumed = Assumed {
            found: found.clone(),
            lowest: task.lowest,
            since: self.answers,
        };
        self.assumed.insert(task.of, assumed);
    }

    /// Follows one alternative of the task at work as far as it goes without a split.
    /// Returns what the task found, if that ended it.
    fn step(&mut self) -> Result<Option<Found>, Exhausted> {
        let task = self.tasks.last_mut().expect("a task is at work");
        let mut branch = match task.waiting.take() {
            Some(branch) => branch,
            None => {
                let depends = task.depends_on;
                let Some(split) = task.splits.last_mut() else {
                    // Every alternative was followed to its end.
                    return Ok(Some(depends.map_or(Found::Nothing, Found::Unknown)));
                };
                if depends.is_some() && split.branch.free().is_empty() {
                    task.splits.pop();
                    self.stood();
                    return Ok(None);
                }
                let Some(alternative) = split.still_to_come.next() else {
                    let dead_end = !split.stood;
                    if let (Some(choice), true) = (split.choice, dead_end) {
                        *self.dead_ends.entry(choice).or_default() += 1;
                    }
                    // An alternative that brought the disjunction and was left with no
                    // alternative of it did not stand by more than itself.
                    let stood = !(split.brought && dead_end);
                    task.splits.pop();
                    if stood {
                        self.stood();
                    }
                    return Ok(None);
                };
                self.context.budget.charge(1 + split.branch.weight() / 32)?;
                let mut branch = split.branch.clone();
                branch.todo.extend(alternative);
                branch
            }
        };
        match self.settle(&mut branch)? {
            Settled::Refuted => return Ok(None),
            Settled::Needs(wanted) => {
                self.wait(branch, wanted);
                return Ok(None);
            }
            Settled::Stands => {}
        }
        if self.is_hopeless(&branch) {
            self.stood();
            return Ok(None);
        }
        if let Some((choice, brought)) = self.choose(&mut branch) {
            let still_to_come = alternatives(&self.context.terms, &choice);
            let task = self.tasks.last_mut().expect("a task is at work");
            task.splits.push(Split {
                branch,
                still_to_come,
                choice: Some((choice.term, choice.negated)),
                brought,
                stood: false,
            });
            return Ok(None);
        }
        self.stood();
        // Nothing is left to take in, and the branch stands.
        match self.instance(&branch)? {
            Given::Instance(witness) => return Ok(Some(Found::Instance(witness))),
            Given::Needs(wanted) => self.wait(branch, wanted),
            Given::Depends(cause) => {
                let task = self.tasks.last_mut().expect("a task is at work");
                task.depends_on.get_or_insert(cause);
            }
        }
        Ok(None)
    }

    /// Notes that an alternative of the split at work stood by more than itself.
    fn stood(&mut self) {
        let task = self.tasks.last_mut().expect("a task is at work");
        if let Some(split) = task.splits.last_mut() {
            split.stood = true;
        }
    }

    /// Takes the disjunction that the branch splits on next, and says whether the branch
    /// brought it: whether it was not yet met when the split at work was made. It is the
    /// disjunction that most often left a branch with no alternative, and of several the
    /// one that was met first.
    fn choose(&self, branch: &mut Branch) -> Option<(Item, bool)> {
        let task = self.tasks.last().expect("a task is at work");
        let split = task.splits.last().expect("a branch is of a split");
        let met = split.branch.choices.len();
        let mut most = (0, 0);
        if !self.dead_ends.is_empty() {
            let dead_ends = |choice: &Item| {
                let known = self.dead_ends.get(&(choice.term, choice.negated));
                known.copied().unwrap_or(0)
            };
            for (place, choice) in branch.choices.iter().enumerate() {
                let count = dead_ends(choice);
                if count > most.1 {
                    most = (place, count);
                }
            }
        }
        let choice = branch.choices.remove(most.0)?;
        Some((choice, most.0 >= met))
    }

    /// Lets a branch of the task at work wait for c-references to be decided.
    fn wait(&mut self, branch: Branch, wanted: Vec<CRefId>) {
        let task = self.tasks.last_mut().expect("a task is at work");
        (task.waiting, task.wanted) = (Some(branch), wanted);
    }

    /// Whether a branch of the task at work can be left alone: the task will not find that
    /// nothing satisfies its c-reference any more, and the branch cannot give an instance.
    /// Leaves are never taken back and types never return, so what comes out of the branch
    /// cannot give one either.
    fn is_hopeless(&self, branch: &Branch) -> bool {
        let task = self.tasks.last().expect("a task is at work");
        task.depends_on.is_some() && branch.free().is_empty()
    }

    /// Takes in everything that needs no split, and says whether the branch still stands.
    fn settle(&mut self, branch: &mut Branch) -> Result<Settled, Exhausted> {
        while let Some(item) = branch.todo.pop_front() {
            self.context.budget.charge(1)?;
            if !self.take(branch, item)? {
                return Ok(Settled::Refuted);
            }
        }
        // What was asked of numbers may have left none. Then the branch has no number among
        // its instances, and stands by what else it accepts. So it is with strings and with
        // objects.
        if std::mem::take(&mut branch.numbers_asked)
            && branch.types.contains(InstanceType::Number)
            && branch.numbers.is_empty(&mut self.context.budget)?
            && !branch.restrict(NUMBER.complement())
        {
            return Ok(Settled::Refuted);
        }
        let Context {
            languages, budget, ..
        } = &mut *self.context;
        if std::mem::take(&mut branch.strings_asked)
            && branch.types.contains(InstanceType::String)
            && branch.strings.is_empty(languages, budget)?
            && !branch.restrict(STRING.complement())
        {
            return Ok(Settled::Refuted);
        }
        // The objects come last: a branch that waits for the engine to decide what the
        // value of a property satisfies is asked again from here.
        if branch.objects_asked && branch.types.contains(InstanceType::Object) {
            match self.left(branch, InstanceType::Object, false)? {
                Left::Needs(wanted) => return Ok(Settled::Needs(wanted)),
                Left::Nothing => {
                    if !branch.restrict(OBJECT.complement()) {
                        return Ok(Settled::Refuted);
                    }
                }
                Left::Unknown(cause) => branch.objects_depend = Some(cause),
                Left::Value(_) => branch.objects_depend = None,
            }
        }
        branch.objects_asked = false;
        // And the arrays after them, which wait for the values of their items in the same
        // way. A branch that waits here has been asked about its objects.
        if branch.arrays_asked && branch.types.contains(InstanceType::Array) {
            match self.left(branch, InstanceType::Array, false)? {
                Left::Needs(wanted) => return Ok(Settled::Needs(wanted)),
                Left::Nothing => {
                    if !branch.restrict(ARRAY.complement()) {
                        return Ok(Settled::Refuted);
                    }
                }
                Left::Unknown(cause) => branch.arrays_depend = Some(cause),
                Left::Value(_) => branch.arrays_depend = None,
            }
        }
        branch.arrays_asked = false;
        Ok(Settled::Stands)
    }

    /// Whether the branch leaves an object, or with `of` an array, and with `give` such a
    /// value.
    fn left(&mut self, branch: &Branch, of: InstanceType, give: bool) -> Result<Left, Exhausted> {
        let Self {
            context,
            tasks,
            found,
            assumed,
            at_work,
            partitions,
            ..
        } = self;
        let Context {
            terms,
            languages,
            budget,
        } = &mut **context;
        // The task at work. The language of the names of an object is worked out with none.
        let mut lowest = tasks.last().map_or(usize::MAX, |task| task.lowest);
        // What the engine knows of a c-reference. One that a task is deciding, or that was
        // found to accept nothing only as long as tasks are at work, is taken to accept
        // nothing, and the task at work notes the lowest of those tasks.
        let mut ask = |of: CRefId| match of {
            Terms::NOTHING => Some(Found::Nothing),
            Terms::ANYTHING => Some(Found::Instance(Witness::plain(Value::Null))),
            _ => {
                if let Some(known) = found.get(&of) {
                    return Some(known.clone());
                }
                if let Some(at) = at_work.get(&of) {
                    lowest = lowest.min(*at);
                    return Some(Found::Nothing);
                }
                let assumed = assumed.get(&of)?;
                lowest = lowest.min(assumed.lowest);
                Some(assumed.found.clone())
            }
        };
        let mut solver = Solver {
            terms,
            languages,
            budget,
            partitions,
        };
        let left = if of == InstanceType::Array {
            branch.arrays.left(&mut solver, &mut ask, give)?
        } else {
            branch.objects.left(&mut solver, &mut ask, give)?
        };
        if let Some(task) = tasks.last_mut() {
            task.lowest = lowest;
        }
        Ok(left)
    }

    /// What the branch gives: an instance, if it is known to accept one that can be given.
    /// That is one of the first type that no leaf is about and that has one.
    fn instance(&mut self, branch: &Branch) -> Result<Given, Exhausted> {
        let mut in_the_way = None;
        for kind in branch.free().iter() {
            if matches!(kind, InstanceType::Object | InstanceType::Array) {
                match self.left(branch, kind, true)? {
                    Left::Value(Some(value)) => return Ok(Given::Instance(value)),
                    Left::Needs(wanted) => return Ok(Given::Needs(wanted)),
                    Left::Unknown(cause) => {
                        in_the_way.get_or_insert(cause);
                    }
                    Left::Nothing | Left::Value(None) => {}
                }
                continue;
            }
            let Context {
                languages, budget, ..
            } = &mut *self.context;
            let of = generate::Left {
                may_be_true: branch.booleans[1],
                numbers: &branch.numbers,
                strings: &branch.strings,
            };
            match generate::instance(kind, &of, languages, budget)? {
                Some(instance) => return Ok(Given::Instance(Witness::plain(instance))),
                None if kind == InstanceType::Number => {
                    in_the_way.get_or_insert(Cause::Number);
                }
                None => {}
            }
        }
        Ok(Given::Depends(
            branch.cause(&self.context.terms, in_the_way),
        ))
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
            // What is no object satisfies every term about objects, so only an object
            // fails one.
            (
                Term::PProp(..)
                | Term::PReq(_)
                | Term::PNames(_)
                | Term::MinProps(_)
                | Term::MaxProps(_),
                _,
            ) => {
                let stands = !negated || branch.restrict(OBJECT);
                if !stands || !branch.types.contains(InstanceType::Object) {
                    return Ok(stands);
                }
                let found = found.clone();
                return self.take_about_objects(branch, &found, negated);
            }
            // And what is no array satisfies every term about arrays.
            (
                Term::Item(..)
                | Term::AddIts(..)
                | Term::Contains(_)
                | Term::MinIts(_)
                | Term::MaxIts(_),
                _,
            ) => {
                let stands = !negated || branch.restrict(ARRAY);
                if stands && branch.types.contains(InstanceType::Array) {
                    let found = found.clone();
                    let Context { terms, budget, .. } = &mut *self.context;
                    // What is asked of every item from a position on is taken in at each
                    // position that the branch tells apart.
                    budget.charge(branch.arrays.weight() / 8)?;
                    branch.arrays.take(&found, negated, terms);
                    branch.arrays_asked = true;
                }
                stands
            }
            (Term::Unknown(leaf), _) => branch.take(*leaf, negated, &self.context.terms),
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

    /// Takes a term about objects into a branch that may still be an object. Returns
    /// whether the branch still stands.
    fn take_about_objects(
        &mut self,
        branch: &mut Branch,
        term: &Term,
        negated: bool,
    ) -> Result<bool, Exhausted> {
        let Term::PNames(variable) = term else {
            branch.objects.take(term, negated, &mut self.context.terms);
            branch.objects_asked = true;
            return Ok(true);
        };
        // Every name is of the language of the strings that the schema accepts: none is
        // outside it. Where no language says which strings those are, this is a leaf.
        let Some(names) = self.names(*variable)? else {
            let leaf = self.context.terms.names(*variable);
            return Ok(branch.take(leaf, negated, &self.context.terms));
        };
        let Context {
            terms, languages, ..
        } = &mut *self.context;
        let outside = languages.outside([names]);
        branch.objects.names(outside, negated, terms);
        branch.objects_asked = true;
        Ok(true)
    }

    /// The language of the strings that the schema of a variable accepts, or `None` if no
    /// language says it: the schema holds a leaf about strings, or a bound on the length
    /// that is more than a pattern says.
    ///
    /// The schema is taken apart as a c-reference is, only that every branch is followed
    /// to its end: each gives the strings that it leaves, and those of all are the
    /// language. A branch about strings waits for nothing, so this is done at once.
    fn names(&mut self, variable: VarId) -> Result<Option<LanguageId>, Exhausted> {
        if let Some(known) = self.names.get(&variable) {
            return Ok(*known);
        }
        let terms = &mut self.context.terms;
        let whole = vec![
            Item::new(terms.type_is(STRING), false),
            Item::new(terms.reference(variable), false),
        ];
        let whole: Box<dyn Iterator<Item = Alternative>> = Box::new(std::iter::once(whole));
        let mut splits: Vec<(Branch, Box<dyn Iterator<Item = Alternative>>)> =
            vec![(Branch::default(), whole)];
        let mut all = Some(Languages::NOTHING);
        while let Some((split, still_to_come)) = splits.last_mut() {
            let (Some(alternative), Some(so_far)) = (still_to_come.next(), all) else {
                splits.pop();
                continue;
            };
            self.context.budget.charge(1 + split.weight() / 32)?;
            let mut branch = split.clone();
            branch.todo.extend(alternative);
            if !matches!(self.settle(&mut branch)?, Settled::Stands) {
                continue;
            }
            if let Some(choice) = branch.choices.pop_front() {
                let alternatives = alternatives(&self.context.terms, &choice);
                splits.push((branch, alternatives));
                continue;
            }
            let Context {
                languages, budget, ..
            } = &mut *self.context;
            all = match branch.strings.language(languages, budget)? {
                Some(left) if branch.free().contains(InstanceType::String) => {
                    Some(languages.union(so_far, left, budget)?)
                }
                _ => None,
            };
        }
        self.names.insert(variable, all);
        Ok(all)
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
    use crate::{Checker, Reason, RegexDialect, Side, Verdict};

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
        let set = json!({"uniqueItems": true});
        let set_list = json!({"type": "array", "uniqueItems": true});
        yes(&set, &set);
        yes(&set, &set_list);
        // The other way, an instance that is no array tells them apart.
        assert_eq!(counterexample(&set_list, &set), json!(null));
        // Subschemas of one class make one leaf.
        let few = json!({"type": "array", "contains": {"type": "string"}, "maxContains": 2});
        let mut few_set = few.clone();
        few_set["uniqueItems"] = json!(true);
        yes(&few, &few_set);
        assert_eq!(
            depends_on(&few_set, &few),
            (Side::A, "#/uniqueItems".to_owned())
        );
        // A leaf with another schema, or with another count, is another leaf.
        let fewer = json!({"type": "array", "contains": {"type": "string"}, "maxContains": 1});
        assert_eq!(
            depends_on(&few, &fewer),
            (Side::A, "#/maxContains".to_owned())
        );
        let twice = json!({"type": "array", "contains": {"type": "null"}, "minContains": 2});
        assert_eq!(
            depends_on(&twice, &few),
            (Side::A, "#/minContains".to_owned())
        );
        // With a least of none, a most still says something.
        let none_or_one = json!({"contains": {}, "minContains": 0, "maxContains": 1});
        assert_eq!(
            depends_on(&none_or_one, &json!({"type": "array"})),
            (Side::A, "#/maxContains".to_owned())
        );
    }

    #[test]
    fn a_leaf_is_about_one_type_only() {
        // No number has the same item twice, and no list is too small a number.
        yes(&json!({"uniqueItems": true}), &json!({"type": "integer"}));
        yes(
            &json!({"minimum": 3}),
            &json!({"type": "array", "uniqueItems": true}),
        );
        // An object satisfies the leaf about arrays, so an object is an instance.
        let either = json!({"type": ["array", "object"], "uniqueItems": true});
        assert_eq!(counterexample(&json!({"type": "null"}), &either), json!({}));
        assert_eq!(
            depends_on(
                &json!({"type": "array", "uniqueItems": true}),
                &json!({"type": "array"})
            ),
            (Side::A, "#/uniqueItems".to_owned())
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
        // To ECMA-262 a digit is one of the ten of ASCII, and to the `regex` crate any digit
        // of Unicode.
        let (digits, ascii) = (json!({"pattern": r"^\d+$"}), json!({"pattern": "^[0-9]+$"}));
        yes(&digits, &ascii);
        yes(&ascii, &digits);
        let rust = Checker::new().regex_dialect(RegexDialect::Rust);
        assert_eq!(rust.subsumes(&digits, &ascii), Ok(Verdict::Yes));
        let no = Verdict::No {
            counterexample: json!("٠"),
        };
        assert_eq!(rust.subsumes(&ascii, &digits), Ok(no));
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
        // A string in a constant that is an array is that string too.
        assert_eq!(
            counterexample(&json!({"const": ["a"]}), &json!({"const": ["b"]})),
            json!(["b"])
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
        // A number of an address has no zero before it, as the corpus and validators have
        // it, although the grammar that the draft names would let it.
        let address = json!({"format": "ipv4"});
        yes(&address, &json!({"enum": ["1.2.3.4", "0.0.0.0", 1]}));
        assert_eq!(
            counterexample(&address, &json!({"enum": ["1.2.3.4", "1.2.3.256"]})),
            json!("1.2.3.256")
        );
        assert_eq!(
            counterexample(&address, &json!({"const": "087.10.0.1"})),
            json!("087.10.0.1")
        );
        yes(
            &json!(false),
            &json!({"format": "ipv4", "const": "01.2.3.4"}),
        );
        // A duration in small letters is left open: the grammar allows it by the letter,
        // validators do not take it, and the corpus has no such duration.
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
        let small = Checker::new().budget(100);
        assert_eq!(small.subsumes(&a, &b).unwrap(), Verdict::Yes);
        // The other way the DFA has to say that the pattern does not match the
        // empty string.
        let unknown = Verdict::Unknown {
            reason: Reason::Budget,
        };
        assert_eq!(small.subsumes(&b, &a).unwrap(), unknown);
        yes(&b, &a);
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
        // A number in a constant that is an array is that number too.
        yes(&json!({"const": [1]}), &json!({"const": [1.0]}));
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
        let or_list = json!({
            "type": ["number", "array"],
            "exclusiveMinimum": f64::MAX,
            "uniqueItems": true,
        });
        assert_eq!(
            depends_on(&json!(false), &or_list),
            (Side::B, "#/uniqueItems".to_owned())
        );
    }

    #[test]
    fn a_large_float_is_compared_as_the_whole_number_that_it_holds() {
        // The bounds of a 64-bit integer, written as integers and as the floats nearest to
        // them. The float for the least is that number, -2^63, and the float for the most
        // is one more than it, 2^63.
        let as_integers = json!({
            "type": "integer",
            "minimum": i64::MIN,
            "maximum": i64::MAX,
        });
        let as_floats = json!({
            "type": "integer",
            "minimum": -9.223_372_036_854_776e18,
            "maximum": 9.223_372_036_854_776e18,
        });
        yes(&as_floats, &as_integers);
        assert_eq!(
            counterexample(&as_integers, &as_floats),
            json!(9_223_372_036_854_775_808_u64)
        );
        // A whole number between a float and what the float is printed as: 2^60 + 256 is
        // printed as a number that ends in 200.
        let (float, below) = (
            json!({"minimum": 1.152_921_504_606_847_2e18}),
            json!({"minimum": 1_152_921_504_606_847_210_u64}),
        );
        yes(&below, &float);
        assert_eq!(
            counterexample(&float, &below),
            json!(1_152_921_504_606_847_210_u64)
        );
        // A float is given where no integer holds the number.
        let beyond = json!({"type": "integer", "exclusiveMinimum": u64::MAX});
        assert_eq!(
            counterexample(&json!(false), &beyond),
            json!(18_446_744_073_709_551_616.0)
        );
    }

    #[test]
    fn a_property_that_there_has_to_be_is_there() {
        let (a, both) = (json!({"required": ["a"]}), json!({"required": ["b", "a"]}));
        yes(&a, &both);
        assert_eq!(counterexample(&both, &a), json!({"a": null}));
        // What is no object has to have no property.
        assert_eq!(counterexample(&json!({"type": "object"}), &a), json!(null));
        yes(&a, &json!({"type": "string"}));
        let object = json!({"type": "object"});
        assert_eq!(
            counterexample(&json!({"type": "object", "required": ["a"]}), &object),
            json!({})
        );
        // An object without the property is all that the negation accepts.
        let without = json!({"not": {"required": ["a"]}});
        yes(&object, &without);
        yes(
            &without,
            &json!({"type": "object", "properties": {"a": false}}),
        );
        yes(
            &json!({"properties": {"a": false}}),
            &json!({"type": "object", "not": {"required": ["a"]}}),
        );
        assert_eq!(counterexample(&without, &object), json!({"a": null}));
        yes(&json!(false), &json!({"allOf": [without, a]}));
    }

    #[test]
    fn dependencies_are_about_the_properties_that_there_are() {
        let needs = json!({"dependentRequired": {"a": ["b"]}});
        yes(&needs, &json!({"required": ["b"]}));
        yes(&needs, &json!({"properties": {"a": false}}));
        yes(&needs, &json!({"type": "string"}));
        assert_eq!(
            counterexample(&json!({"required": ["b"]}), &needs),
            json!({})
        );
        assert_eq!(
            counterexample(&needs, &json!({"required": ["a"]})),
            json!({"a": null})
        );
        // The same as a condition says.
        let condition = json!({"if": {"required": ["a"]}, "then": {"required": ["b"]}});
        yes(&needs, &condition);
        yes(&condition, &needs);
        let schemas = json!({"dependentSchemas": {"a": {"required": ["b"]}}});
        yes(&needs, &schemas);
        yes(&schemas, &needs);
        // A schema that depends on a property is asked of the whole instance.
        let typed = json!({"dependentSchemas": {"a": {"properties": {"b": {"type": "null"}}}}});
        yes(&typed, &json!({"properties": {"b": {"type": "null"}}}));
        assert_eq!(
            counterexample(&typed, &json!({"type": "object"})),
            json!({"a": null, "b": true})
        );
        yes(
            &json!({"dependentSchemas": {"a": {"type": "object"}}}),
            &json!({"type": "object"}),
        );
    }

    #[test]
    fn a_property_is_compared_by_the_schema_of_its_value() {
        let named = |schema: Value| json!({"properties": {"name": schema}});
        let (text, optional) = (
            named(json!({"type": "string"})),
            named(json!({"type": ["string", "null"]})),
        );
        yes(&optional, &text);
        assert_eq!(counterexample(&text, &optional), json!({"name": null}));
        // The property need not be there, and what is no object has none.
        yes(&text, &json!({"type": "string"}));
        yes(&text, &json!({"properties": {"name": false}}));
        assert_eq!(
            counterexample(&text, &json!({"properties": {"other": {"type": "null"}}})),
            json!({"name": null})
        );
        assert_eq!(
            counterexample(&text, &json!({"required": ["name"]})),
            json!({"name": null})
        );
        yes(
            &text,
            &json!({"required": ["name"], "properties": {"name": {"minLength": 2, "type": "string"}}}),
        );
        // A value is an instance of its own, with numbers, strings and objects in it.
        yes(
            &named(json!({"minimum": 0})),
            &named(json!({"type": "integer", "minimum": 1})),
        );
        assert_eq!(
            counterexample(
                &named(json!({"type": "integer", "minimum": 1})),
                &named(json!({"type": "number", "minimum": 0.5}))
            ),
            json!({"name": 0.5})
        );
        let deep = |schema: Value| named(named(named(schema)));
        yes(
            &deep(json!({"pattern": "^[a-z]"})),
            &deep(json!({"pattern": "^[a-f]"})),
        );
        assert_eq!(
            counterexample(
                &deep(json!({"pattern": "^[a-f]"})),
                &deep(json!({"pattern": "^[a-z]"}))
            ),
            json!({"name": {"name": {"name": "g"}}})
        );
        // Two schemas for one property are asked of one value.
        let both = json!({"allOf": [named(json!({"minimum": 0})), named(json!({"maximum": 9}))]});
        let range = named(json!({"minimum": 0, "maximum": 9}));
        yes(&both, &range);
        yes(&range, &both);
        // A property that cannot have a value cannot be there.
        let never = json!({"properties": {"name": false}});
        yes(&never, &json!({"not": {"required": ["name"]}}));
        yes(
            &json!(false),
            &json!({"type": "object", "required": ["name"], "properties": {"name": false}}),
        );
        yes(
            &json!(false),
            &json!({
                "type": "object",
                "required": ["name"],
                "properties": {"name": {"type": "string", "maxLength": 1, "pattern": "^ab"}},
            }),
        );
    }

    #[test]
    fn names_are_told_apart_by_the_patterns_that_match_them() {
        let (narrow, wide) = (
            json!({"patternProperties": {"^x-": {"type": "string"}}}),
            json!({"patternProperties": {"^x": {"type": "string"}}}),
        );
        yes(&narrow, &wide);
        assert_eq!(counterexample(&wide, &narrow), json!({"x": null}));
        // A name that a pattern matches satisfies what the pattern asks and what the name
        // itself is asked.
        let both = json!({
            "properties": {"x-a": {"minLength": 1}},
            "patternProperties": {"^x-": {"type": "string"}},
        });
        yes(&narrow, &both);
        yes(
            &json!({"properties": {"x-a": {"type": "string", "minLength": 1}}}),
            &both,
        );
        assert_eq!(counterexample(&both, &narrow), json!({"x-a": ""}));
        // Two patterns that are written differently and match the same names.
        let again = json!({"patternProperties": {"^x-[^]*$": {"type": "string"}}});
        yes(&again, &narrow);
        yes(&narrow, &again);
        // The dot stops at the end of a line, which a separator of lines is too.
        let lines = json!({"patternProperties": {"^x-.*$": {"type": "string"}}});
        assert_eq!(counterexample(&narrow, &lines), json!({"x-\u{2028}": null}));
        // A name that two patterns match satisfies both.
        let two = json!({"patternProperties": {"^a": {"minimum": 0}, "b$": {"maximum": 9}}});
        yes(
            &json!({"properties": {"ab": {"minimum": 0, "maximum": 9}}}),
            &two,
        );
        assert_eq!(
            counterexample(&json!({"properties": {"ab": {"minimum": 1}}}), &two),
            json!({"ab": 0})
        );
        // A pattern of a few words asks of those names what `properties` would, and so
        // does a pattern of one word.
        let words = json!({"patternProperties": {"^(a|b)$": {"type": "null"}}});
        let named = json!({"properties": {"a": {"type": "null"}, "b": {"type": "null"}}});
        yes(&words, &named);
        yes(&named, &words);
        let word = json!({"patternProperties": {"^a$": {"type": "null"}}});
        let name = json!({"properties": {"a": {"type": "null"}}});
        yes(&word, &name);
        yes(&name, &word);
        yes(&word, &named);
        assert_eq!(counterexample(&named, &word), json!({"b": true}));
    }

    #[test]
    fn what_no_name_and_no_pattern_is_about_is_additional() {
        let closed = |names: &[&str]| {
            let properties: Map<String, Value> = names
                .iter()
                .map(|name| ((*name).to_owned(), json!({})))
                .collect();
            json!({"properties": properties, "additionalProperties": false})
        };
        yes(&closed(&["a", "b"]), &closed(&["a"]));
        assert_eq!(
            counterexample(&closed(&["a"]), &closed(&["a", "b"])),
            json!({"b": null})
        );
        assert_eq!(
            counterexample(&closed(&[]), &json!({"type": "object"})),
            json!({"a": null})
        );
        yes(&closed(&[]), &json!({"maxProperties": 0}));
        yes(&json!({"maxProperties": 0}), &closed(&[]));
        // A schema for the other properties.
        let texts = json!({"properties": {"a": {}}, "additionalProperties": {"type": "string"}});
        yes(&texts, &closed(&["a"]));
        yes(
            &texts,
            &json!({"additionalProperties": {"type": "string", "minLength": 1}}),
        );
        assert_eq!(
            counterexample(&json!({"additionalProperties": {"type": "string"}}), &texts),
            json!({"a": null})
        );
        assert_eq!(
            counterexample(&texts, &json!({"properties": {"a": {}}})),
            json!({"b": null})
        );
        // What a pattern matches is not additional.
        let extended = json!({
            "properties": {"a": {}},
            "patternProperties": {"^x-": {}},
            "additionalProperties": false,
        });
        yes(&extended, &closed(&["a"]));
        assert_eq!(
            counterexample(&closed(&["a"]), &extended),
            json!({"x-": null})
        );
        yes(
            &json!({"propertyNames": {"pattern": "^(a$|x-)"}}),
            &extended,
        );
        // The keyword is about the names of its own schema, and of no schema next to it.
        let apart = json!({"allOf": [{"properties": {"a": {}}}, {"additionalProperties": false}]});
        yes(&apart, &closed(&[]));
        yes(&closed(&[]), &apart);
    }

    #[test]
    fn the_names_of_an_object_are_strings_that_a_schema_accepts() {
        let names = |schema: Value| json!({"propertyNames": schema});
        let (lower, few) = (
            names(json!({"pattern": "^[a-z]+$"})),
            names(json!({"pattern": "^[a-c]+$"})),
        );
        yes(&lower, &few);
        assert_eq!(counterexample(&few, &lower), json!({"d": null}));
        yes(&lower, &names(json!({"enum": ["a", "bc"]})));
        assert_eq!(
            counterexample(
                &names(json!({"maxLength": 3})),
                &names(json!({"enum": ["a", "abcd"]}))
            ),
            json!({"abcd": null})
        );
        // The names that the properties may have, said in two ways.
        let closed = json!({"properties": {"a": {}, "b": {}}, "additionalProperties": false});
        yes(&names(json!({"enum": ["a", "b", "c"]})), &closed);
        yes(&closed, &names(json!({"enum": ["a", "b"]})));
        assert_eq!(
            counterexample(&closed, &names(json!({"enum": ["a", "b", "c"]}))),
            json!({"c": null})
        );
        // The schema is taken apart like any other, and a name is no number.
        let either = names(json!({"anyOf": [{"maxLength": 1}, {"pattern": "^x"}]}));
        yes(&either, &names(json!({"enum": ["a", "xyz"]})));
        assert_eq!(
            counterexample(&either, &json!({"type": "object"})),
            json!({"aa": null})
        );
        yes(
            &names(json!({"type": "string"})),
            &json!({"type": "object"}),
        );
        yes(
            &names(json!({"type": "number"})),
            &json!({"maxProperties": 0}),
        );
        yes(&json!({"maxProperties": 0}), &names(json!(false)));
        // A schema that says of strings what the engine does not model is a leaf.
        let hosts = names(json!({"format": "hostname"}));
        yes(&hosts, &hosts.clone());
        assert_eq!(
            depends_on(&hosts, &json!({"type": "object"})),
            (Side::A, "#/propertyNames".to_owned())
        );
    }

    #[test]
    fn properties_are_counted() {
        let (two, three) = (json!({"minProperties": 2}), json!({"minProperties": 3}));
        yes(&two, &three);
        assert_eq!(counterexample(&three, &two), json!({"a": null, "b": null}));
        yes(&json!({"maxProperties": 3}), &json!({"maxProperties": 2}));
        assert_eq!(
            counterexample(&json!({"maxProperties": 1}), &json!({"maxProperties": 2})),
            json!({"a": null, "b": null})
        );
        // The properties that there have to be are counted, each once.
        let both = json!({"required": ["a", "b"]});
        yes(&two, &both);
        assert_eq!(counterexample(&three, &both), json!({"a": null, "b": null}));
        assert_eq!(
            counterexample(&json!({"maxProperties": 1}), &both),
            json!({"a": null, "b": null})
        );
        yes(
            &json!(false),
            &json!({"type": "object", "required": ["a", "b"], "maxProperties": 1}),
        );
        yes(
            &json!({"required": ["a"]}),
            &json!({"required": ["a"], "maxProperties": 1, "minProperties": 1}),
        );
        // Only so many names are there to be had.
        let closed = json!({
            "type": "object",
            "properties": {"a": {}, "b": {}, "c": false},
            "additionalProperties": false,
        });
        yes(&json!({"maxProperties": 2}), &closed);
        yes(&json!(false), &json!({"allOf": [closed, three]}));
        assert_eq!(
            counterexample(&json!(false), &json!({"allOf": [closed, two]})),
            json!({"a": null, "b": null})
        );
        let few = json!({
            "type": "object",
            "patternProperties": {"^[ab]$": {}, "^c": false},
            "additionalProperties": false,
        });
        yes(&json!(false), &json!({"allOf": [few, three]}));
        // With room for one property, the two that there have to be are one.
        let one = json!({
            "type": "object",
            "maxProperties": 1,
            "allOf": [
                {"not": {"additionalProperties": {"type": "string"}}},
                {"not": {"additionalProperties": {"minimum": 5}}},
            ],
        });
        assert_eq!(counterexample(&json!(false), &one), json!({"a": 0}));
        // What is no object has no count.
        yes(&three, &json!({"type": "array"}));
        assert_eq!(
            counterexample(
                &json!({"not": {"minProperties": 1}}),
                &json!({"type": "object"})
            ),
            json!({"a": null})
        );
        yes(
            &json!({"not": {"minProperties": 1}}),
            &json!({"type": "object", "maxProperties": 0}),
        );
    }

    #[test]
    fn a_schema_that_holds_itself_in_a_property_accepts_what_is_built_in_finitely_many_steps() {
        let list = |value: Value| {
            json!({
                "type": "object",
                "properties": {"value": value, "next": {"$ref": "#"}},
                "required": ["value"],
            })
        };
        let (whole, any) = (
            list(json!({"type": "integer"})),
            list(json!({"type": "number"})),
        );
        yes(&any, &whole);
        assert_eq!(counterexample(&whole, &any), json!({"value": 0.1}));
        // A list that has to go on has no end, and so there is none.
        let endless =
            json!({"type": "object", "required": ["next"], "properties": {"next": {"$ref": "#"}}});
        yes(&json!(false), &endless);
        yes(&json!({"type": "string"}), &endless);
        // With a way to end it, there is one, and the shortest is given.
        let ends = json!({
            "type": ["object", "null"],
            "required": ["next"],
            "properties": {"next": {"$ref": "#"}},
        });
        assert_eq!(counterexample(&json!(false), &ends), json!(null));
        assert_eq!(
            counterexample(&json!({"type": "null"}), &ends),
            json!({"next": null})
        );
        // Two schemas that hold each other.
        let pair = json!({
            "$ref": "#/$defs/even",
            "$defs": {
                "even": {"type": "object", "properties": {"next": {"$ref": "#/$defs/odd"}}, "additionalProperties": false},
                "odd": {"type": "object", "properties": {"next": {"$ref": "#/$defs/even"}}, "required": ["next"], "additionalProperties": false},
            },
        });
        let chain = json!({"type": "object", "properties": {"next": {"$ref": "#"}}, "additionalProperties": false});
        yes(&chain, &pair);
        assert_eq!(counterexample(&pair, &chain), json!({"next": {}}));
    }

    #[test]
    fn what_is_found_while_a_schema_is_being_decided_holds_only_as_long_as_that() {
        let never = |least: u32| json!({"type": "string", "minLength": least, "maxLength": 1});
        let with = |name: &str, schema: Value| json!({"type": "object", "required": [name], "properties": {name: schema}});
        let reference = |name: &str| json!({"$ref": format!("#/$defs/{name}")});
        // `x` is `null` or holds a `y`, and `y` holds an `x`. While `x` is being decided,
        // `y` is found to accept nothing, since `x` accepts nothing yet. That must not be
        // kept: `x` turns out to accept `null`, and so `y` accepts an object. B asks for
        // `x` first, in an alternative that then comes to nothing, and for `y` after it.
        let b = json!({
            "anyOf": [
                {
                    "type": "object",
                    "required": ["p", "r"],
                    "properties": {"p": reference("x"), "r": never(2)},
                },
                with("q", reference("y")),
            ],
            "$defs": {
                "x": {"anyOf": [with("a", reference("y")), {"type": "null"}]},
                "y": with("b", reference("x")),
            },
        });
        assert_eq!(counterexample(&json!(false), &b), json!({"q": {"b": null}}));

        // The same one level further in. `e` holds an `x2`, which holds an `e` or an `x`.
        // While `x` and `x2` are being decided, `e` is found to accept nothing, and then
        // so is `x2`. When `x2` is done, what was found of `e` holds as long as `x` is
        // being decided, and no longer: the next schema that is found to accept nothing in
        // the place of `x2`, which is `m`, must not make it hold for good.
        let b = json!({
            "anyOf": [
                {
                    "type": "object",
                    "required": ["p", "r"],
                    "properties": {"p": reference("x"), "r": never(2)},
                },
                with("q", reference("e")),
            ],
            "$defs": {
                "x": {
                    "anyOf": [
                        {
                            "type": "object",
                            "required": ["m", "n"],
                            "properties": {"m": never(3), "n": reference("x2")},
                        },
                        {"type": "null"},
                    ],
                },
                "x2": {"anyOf": [with("b", reference("e")), with("c", reference("x"))]},
                "e": with("d", reference("x2")),
            },
        });
        assert_eq!(
            counterexample(&json!(false), &b),
            json!({"q": {"d": {"c": null}}})
        );
    }

    #[test]
    fn a_schema_that_is_nested_deep_in_properties_is_decided_without_recursion() {
        let nested = |depth: usize, innermost: Value| {
            let mut schema = innermost;
            for _ in 0..depth {
                let properties = Map::from_iter([("a".to_owned(), schema)]);
                schema = Value::Object(Map::from_iter([
                    ("type".to_owned(), json!("object")),
                    ("properties".to_owned(), Value::Object(properties)),
                ]));
            }
            schema
        };
        // Each level is a value of the level above, and a task of its own.
        let (whole, any) = (
            nested(20_000, json!({"type": "integer"})),
            nested(20_000, json!({"type": "number"})),
        );
        let check = Checker::new()
            .budget(10_000_000)
            .check(&any, &whole)
            .unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        // A task costs steps, so a budget that is smaller than the schema is deep ends it.
        let small = Checker::new().budget(1_000);
        let verdict = small.subsumes(&any, &whole).unwrap();
        assert_eq!(reason_of(&verdict), Some(Reason::Budget));
        // The other way an instance holds an object for each level, and one that deep
        // cannot be given: there is no counterexample, and no stack is used up for one.
        let check = Checker::new()
            .budget(10_000_000)
            .check(&whole, &any)
            .unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Unrepresentable));
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget((whole, any));
    }

    /// Why a verdict is `Unknown`, if it is.
    fn reason_of(verdict: &Verdict) -> Option<Reason> {
        match verdict {
            Verdict::Unknown { reason } => Some(reason.clone()),
            _ => None,
        }
    }

    #[test]
    fn a_counterexample_is_no_deeper_than_it_can_be_read_back() {
        let nested = |depth: usize, innermost: Value| {
            let mut schema = innermost;
            for _ in 0..depth {
                schema = json!({"type": "object", "properties": {"a": schema}});
            }
            schema
        };
        let (integer, number) = (json!({"type": "integer"}), json!({"type": "number"}));
        // An instance of 127 objects inside one another is given, and `serde_json` reads
        // it back from its text.
        let instance = counterexample(&nested(127, integer.clone()), &nested(127, number.clone()));
        let read: Value = serde_json::from_str(&instance.to_string()).unwrap();
        assert_eq!(read, instance);
        let mut innermost = &instance;
        for _ in 0..127 {
            innermost = &innermost["a"];
        }
        assert_eq!(innermost, &json!(0.1));
        // One level more is not, and neither is the text of it read.
        assert_eq!(
            reason(&nested(128, integer.clone()), &nested(128, number.clone())),
            Reason::Unrepresentable
        );
        let mut too_deep = json!(0.1);
        for _ in 0..128 {
            too_deep = json!({"a": too_deep});
        }
        assert!(serde_json::from_str::<Value>(&too_deep.to_string()).is_err());
        // Where another instance tells the two apart, that one is given.
        let either = json!({"anyOf": [nested(128, number.clone()), {"type": "null"}]});
        assert_eq!(
            counterexample(&nested(128, integer.clone()), &either),
            json!(null)
        );
        // A yes holds for instances of any depth.
        yes(&nested(128, number.clone()), &nested(128, integer.clone()));

        // A chain of schemas that each hold the next in a property, with the steps for a
        // counterexample of that depth: copying a value recurses once for each level,
        // which ran out of stack before there was a limit.
        let mut definitions = Map::new();
        for at in 0..1_500 {
            let next = json!({"$ref": format!("#/$defs/d{}", at + 1)});
            let link = json!({"type": "object", "required": ["a"], "properties": {"a": next}});
            definitions.insert(format!("d{at}"), link);
        }
        definitions.insert("d1500".to_owned(), json!({"type": "null"}));
        let chain = json!({"$ref": "#/$defs/d0", "$defs": definitions});
        let check = Checker::new()
            .budget(2_000_000)
            .check(&json!(false), &chain)
            .unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Unrepresentable));
    }

    #[test]
    fn more_names_than_can_be_counted_are_never_too_few() {
        // The pattern matches 2^64 names, and one of them may not be there. As many
        // properties as the largest count are still to be had, so B accepts an object. It
        // is larger than a budget covers, and the answer is not that there is none. A small
        // budget says so as well as the default, in less time.
        let name = "a".repeat(64);
        let many = |least: u64| {
            json!({
                "type": "object",
                "propertyNames": {"pattern": "^[ab]{64}$"},
                "properties": {name.as_str(): false},
                "minProperties": least,
            })
        };
        let small = Checker::new().budget(100_000);
        let check = small.check(&json!(false), &many(u64::MAX)).unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Budget));
        // With one property to have, it is the plainest name that is left.
        let other = format!("{}b", "a".repeat(63));
        assert_eq!(
            counterexample(&json!(false), &many(1)),
            json!({other: null})
        );
        // Names that can be counted are counted exactly.
        let few = |least: u64| {
            json!({
                "type": "object",
                "propertyNames": {"pattern": "^[ab]{2}$"},
                "properties": {"aa": false},
                "minProperties": least,
            })
        };
        yes(&json!(false), &few(4));
        assert_eq!(
            counterexample(&json!(false), &few(3)),
            json!({"ab": null, "ba": null, "bb": null})
        );
    }

    #[test]
    fn what_stands_in_the_way_of_a_value_stands_in_the_way_of_the_object() {
        let listed = |schema: Value| json!({"type": "object", "properties": {"a": schema}});
        assert_eq!(
            depends_on(
                &listed(json!({"uniqueItems": true})),
                &listed(json!({"type": "array"}))
            ),
            (Side::A, "#/properties/a/uniqueItems".to_owned())
        );
        // What cancels inside the value cancels.
        yes(
            &listed(json!({"uniqueItems": true})),
            &listed(json!({"type": "array", "uniqueItems": true})),
        );
        // A value of another type is an instance.
        assert_eq!(
            counterexample(
                &listed(json!({"type": "array", "uniqueItems": true})),
                &listed(json!({}))
            ),
            json!({"a": null})
        );
        // Another object is given where there is one, and types refute as ever.
        let filled = json!({
            "type": "object",
            "properties": {"a": {"uniqueItems": true}},
            "required": ["b"],
        });
        assert_eq!(
            counterexample(&filled, &listed(json!({"type": "array"}))),
            json!({})
        );
        yes(
            &json!({"type": "object"}),
            &listed(json!({"uniqueItems": true})),
        );
    }

    #[test]
    fn an_item_is_compared_by_the_schema_of_its_position() {
        let (strings, words) = (
            json!({"items": {"type": "string"}}),
            json!({"items": {"type": "string", "minLength": 1}}),
        );
        yes(&strings, &words);
        assert_eq!(counterexample(&words, &strings), json!([""]));
        // What is no array has no items.
        assert_eq!(
            counterexample(&json!({"type": "array"}), &words),
            json!(null)
        );
        yes(&words, &json!({"type": "number"}));
        // Every array has every item of the empty one as it should be.
        yes(&words, &json!({"maxItems": 0}));
        yes(&json!({"items": false}), &json!({"maxItems": 0}));
        yes(&json!({"maxItems": 0}), &json!({"items": false}));

        // `prefixItems` is about the first positions, each by itself, and about no item
        // that is not there.
        let pair = json!({"prefixItems": [{"type": "string"}, {"type": "number"}]});
        let first = json!({"prefixItems": [{"type": "string"}]});
        yes(&first, &pair);
        assert_eq!(counterexample(&pair, &first), json!(["", null]));
        assert_eq!(
            counterexample(&pair, &json!({"type": "array"})),
            json!([null])
        );
        let swapped = json!({"prefixItems": [{"type": "number"}, {"type": "string"}]});
        assert_eq!(counterexample(&pair, &swapped), json!([0]));
        // `items` is about what comes after them.
        let then = json!({"prefixItems": [{"type": "string"}], "items": {"type": "number"}});
        yes(&pair, &then);
        assert_eq!(counterexample(&then, &pair), json!(["", 0, null]));
        yes(&then, &json!({"const": ["a", 1, 2.5]}));
        assert_eq!(
            counterexample(&then, &json!({"items": {"type": "number"}})),
            json!([0])
        );
        // With no item allowed after the first, the array has one at most.
        let one = json!({"prefixItems": [{}], "items": false});
        yes(&one, &json!({"maxItems": 1}));
        yes(&json!({"maxItems": 1}), &one);

        // An item of an item.
        let (table, rows) = (
            json!({"items": {"items": {"type": "integer"}}}),
            json!({"items": {"items": {"type": "number"}}}),
        );
        yes(&rows, &table);
        assert_eq!(counterexample(&table, &rows), json!([[0.1]]));
        // And an item that is an object, or an object with a property that is an array.
        let named = |schema: Value| json!({"items": {"properties": {"a": schema}}});
        yes(
            &named(json!({"type": "number"})),
            &named(json!({"const": 1})),
        );
        assert_eq!(
            counterexample(
                &named(json!({"const": 1})),
                &named(json!({"type": "number"}))
            ),
            json!([{"a": 0}])
        );
        let listed = |schema: Value| json!({"properties": {"a": {"items": schema}}});
        assert_eq!(
            counterexample(&listed(json!(false)), &listed(json!({"type": "null"}))),
            json!({"a": [null]})
        );
    }

    #[test]
    fn an_array_contains_an_item_or_it_does_not() {
        let (with_null, with_string) = (
            json!({"contains": {"type": "null"}}),
            json!({"contains": {"type": "string"}}),
        );
        assert_eq!(
            counterexample(&with_null, &json!({"type": "array"})),
            json!([])
        );
        assert_eq!(counterexample(&with_null, &with_string), json!([""]));
        yes(&with_null, &json!({"const": [1, null]}));
        yes(
            &with_null,
            &json!({"prefixItems": [{"type": "null"}], "minItems": 1}),
        );
        // Without such an item, every item is another.
        let none = json!({"not": {"contains": {"type": "null"}}});
        yes(
            &none,
            &json!({"type": "array", "items": {"type": "string"}}),
        );
        yes(&json!({"items": {"not": {"type": "null"}}}), &none);
        assert_eq!(
            counterexample(&none, &json!({"type": "array"})),
            json!([null])
        );
        // Two schemas want an item each, and share one where the array has no more.
        let both = json!({
            "type": "array",
            "allOf": [with_null, {"contains": {"type": ["null", "string"]}}],
        });
        assert_eq!(counterexample(&json!(false), &both), json!([null, null]));
        let apart = json!({"type": "array", "allOf": [with_null, with_string]});
        assert_eq!(counterexample(&json!(false), &apart), json!(["", null]));
        let one = |schema: &Value| json!({"allOf": [schema, {"maxItems": 1}]});
        assert_eq!(
            counterexample(&json!({"not": both}), &one(&both)),
            json!([null])
        );
        yes(&json!({"not": {"type": "array"}}), &one(&apart));
        // An item that the array contains is one of those that `items` is about.
        let strings = json!({"type": "array", "items": {"type": "string"}});
        yes(
            &json!({"not": {"type": "array"}}),
            &json!({"allOf": [strings, with_null]}),
        );
        yes(&with_string, &json!({"allOf": [strings, {"minItems": 1}]}));
        assert_eq!(counterexample(&with_string, &strings), json!([]),);
        // `minContains` of one is what `contains` asks by itself, and of none it asks
        // nothing.
        let (once, never) = (
            json!({"contains": {"type": "null"}, "minContains": 1}),
            json!({"contains": {"type": "null"}, "minContains": 0}),
        );
        yes(&once, &with_null);
        yes(&with_null, &once);
        yes(&never, &json!(true));
    }

    #[test]
    fn items_are_counted() {
        yes(&json!({"minItems": 1}), &json!({"minItems": 2}));
        assert_eq!(
            counterexample(&json!({"minItems": 2}), &json!({"minItems": 1})),
            json!([null])
        );
        yes(&json!({"maxItems": 2}), &json!({"maxItems": 1}));
        assert_eq!(
            counterexample(&json!({"maxItems": 1}), &json!({"maxItems": 2})),
            json!([null, null])
        );
        // No array has at least two items and at most one.
        let neither = json!({"minItems": 2, "maxItems": 1});
        yes(&json!({"not": {"type": "array"}}), &neither);
        yes(
            &json!({"minItems": 1, "maxItems": 1}),
            &json!({"const": [null]}),
        );
        // An item that there has to be counts, and so does a position that has to be there.
        yes(&json!({"minItems": 1}), &json!({"contains": {}}));
        yes(&json!({"contains": {}}), &json!({"minItems": 1}));
        let second = json!({"not": {"prefixItems": [{}, {"type": "null"}]}});
        yes(&json!({"minItems": 2}), &second);
        assert_eq!(counterexample(&json!(false), &second), json!([null, true]));
        // The items that are added to have enough satisfy what their positions ask.
        let filled = json!({"type": "array", "items": {"const": "a"}, "minItems": 3});
        assert_eq!(
            counterexample(&json!(false), &filled),
            json!(["a", "a", "a"])
        );
        // A count that no array of the budget has is not reached. A small budget says so as
        // well as the default, in less time.
        let endless = json!({"type": "array", "minItems": u64::MAX});
        let small = Checker::new().budget(100_000);
        let check = small.check(&json!(false), &endless).unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Budget));
        yes(&json!({"minItems": 3}), &endless);
    }

    #[test]
    fn an_instance_is_written_out_once_and_only_as_the_counterexample() {
        let within = |schema: Value| json!({"type": "object", "required": ["x"], "properties": {"x": schema}});
        // An array of a billion numbers in a property. A check that ends in `Yes` finds
        // that there is such an array and never writes it out, so a small budget covers it.
        let many =
            json!({"type": "array", "minItems": 1_000_000_000, "items": {"type": "integer"}});
        let small = Checker::new().budget(10_000);
        let any = within(json!({"type": "array"}));
        let check = small.check(&any, &within(many.clone())).unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        // As the counterexample it is written out, at a step for each of its items.
        let none = within(json!({"type": "string"}));
        let check = small.check(&none, &within(many)).unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Budget));
        // Ten thousand numbers in thirty objects inside one another are written out once
        // and not once for each object around them: the budget is far smaller than thirty
        // times the numbers.
        let numbers = |least: i64| {
            let item = json!({"type": "number", "minimum": least});
            json!({"type": "array", "minItems": 10_000, "items": item})
        };
        let nested = |inner: Value| (0..30).fold(inner, |inner, _| within(inner));
        let enough = Checker::new().budget(100_000);
        let check = enough.check(&nested(numbers(0)), &nested(numbers(-1)));
        let Verdict::No { counterexample } = check.unwrap().verdict else {
            panic!("the numbers below zero tell the two apart");
        };
        let mut innermost = &counterexample;
        for _ in 0..30 {
            innermost = &innermost["x"];
        }
        // One item is below zero, and each of the others is a value of its own.
        let items = innermost.as_array().unwrap();
        let below = items.iter().filter(|item| **item == json!(-1));
        assert_eq!((items.len(), below.count()), (10_000, 1));
    }

    #[test]
    fn a_constant_that_is_an_array_or_an_object_is_that_value() {
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
        // Every other array is another value: shorter, longer, or with another item.
        let one = json!({"const": [1]});
        assert_eq!(
            counterexample(&one, &json!({"type": "array"})),
            json!([null])
        );
        assert_eq!(counterexample(&one, &json!({"maxItems": 0})), json!(null));
        let empty = json!({"type": "array", "maxItems": 0});
        assert_eq!(counterexample(&one, &empty), json!([]));
        let filled = json!({"type": "array", "minItems": 1});
        assert_eq!(counterexample(&one, &filled), json!([null]));
        let ones = json!({"type": "array", "minItems": 1, "items": {"const": 1}});
        assert_eq!(counterexample(&one, &ones), json!([1, 1]));
        yes(&one, &json!({"allOf": [ones, {"maxItems": 1}]}));
        assert_eq!(
            counterexample(&one, &json!({"const": [1, 2]})),
            json!([1, 2])
        );
        assert_eq!(counterexample(&json!({"const": [1, 2]}), &one), json!([1]));
        // What a schema asks of the items, the constant answers.
        let schema = json!({
            "prefixItems": [{"type": "integer"}],
            "items": {"type": "string"},
            "contains": {"type": "string", "minLength": 2},
        });
        yes(&schema, &json!({"const": [1, "a", "bc"]}));
        assert_eq!(
            counterexample(&schema, &json!({"enum": [[1, "ab"], [1, "a"]]})),
            json!([1, "a"])
        );

        // An object is its properties and no other.
        let record = json!({"const": {"a": 1, "b": [null]}});
        yes(&json!({"type": "object", "required": ["a", "b"]}), &record);
        yes(
            &json!({"properties": {"b": {"items": {"type": "null"}}}}),
            &record,
        );
        yes(
            &json!({"additionalProperties": {"not": {"type": "string"}}}),
            &record,
        );
        assert_eq!(
            counterexample(&record, &json!({"type": "object"})),
            json!({"a": null})
        );
        let same = json!({
            "type": "object",
            "properties": {"a": {"const": 1.0}, "b": {"const": [null]}},
            "required": ["a", "b"],
            "additionalProperties": false,
        });
        yes(&record, &same);
        yes(&same, &record);
        let open = json!({
            "type": "object",
            "properties": {"a": {"const": 1}, "b": {"const": [null]}},
            "required": ["a", "b"],
        });
        assert_eq!(
            counterexample(&record, &open),
            json!({"a": 1, "b": [null], "c": null})
        );
        // A value inside a value, and one that is met twice.
        let deep = json!({"const": [[1], {"a": [1]}, [1]]});
        yes(&deep, &deep.clone());
        yes(&json!({"items": {"not": {"type": "number"}}}), &deep);
        assert_eq!(
            counterexample(&json!({"const": [[1], {"a": [2]}, [1]]}), &deep),
            json!([[1], {"a": [1]}, [1]])
        );
        // A value of an `enum` is that value, among the others.
        let either = json!({"enum": [{"a": 1}, [], "a"]});
        assert_eq!(
            counterexample(&json!({"enum": [[], "a"]}), &either),
            json!({"a": 1})
        );
        yes(&either, &json!({"const": []}));
    }

    #[test]
    fn a_schema_that_holds_itself_in_an_item_accepts_what_is_built_in_finitely_many_steps() {
        // Nulls in arrays, however deep.
        let tree = json!({
            "$id": "https://example.com/tree",
            "anyOf": [{"type": "null"}, {"type": "array", "items": {"$ref": "#"}}],
        });
        yes(&tree, &json!({"const": [[null, []], null]}));
        assert_eq!(counterexample(&tree, &json!(true)), json!(true));
        assert_eq!(
            counterexample(&tree, &json!({"type": "array"})),
            json!([true])
        );
        assert_eq!(
            counterexample(&tree, &json!({"const": [[null, [1]]]})),
            json!([[null, [1]]])
        );
        // An array that must hold an array like itself has no end, so there is none.
        let endless = json!({
            "$id": "https://example.com/endless",
            "type": "array",
            "minItems": 1,
            "items": {"$ref": "#"},
        });
        yes(&json!(false), &endless);
        // With an end allowed, the shortest is given.
        let chain = json!({
            "$id": "https://example.com/chain",
            "type": "array",
            "items": {"$ref": "#"},
        });
        assert_eq!(counterexample(&json!(false), &chain), json!([]));
        assert_eq!(counterexample(&json!({"maxItems": 0}), &chain), json!([[]]));
    }

    #[test]
    fn what_stands_in_the_way_of_an_item_stands_in_the_way_of_the_array() {
        let listed = |schema: Value| json!({"type": "array", "items": schema});
        assert_eq!(
            depends_on(
                &listed(json!({"uniqueItems": true})),
                &listed(json!({"type": "array"}))
            ),
            (Side::A, "#/items/uniqueItems".to_owned())
        );
        // What cancels inside the item cancels.
        yes(
            &listed(json!({"uniqueItems": true})),
            &listed(json!({"type": "array", "uniqueItems": true})),
        );
        // An item of another type is an instance, and so is an array without the item.
        assert_eq!(
            counterexample(
                &listed(json!({"type": "array", "uniqueItems": true})),
                &listed(json!({}))
            ),
            json!([null])
        );
        let filled = json!({"type": "array", "items": {"uniqueItems": true}, "minItems": 1});
        assert_eq!(
            counterexample(&filled, &listed(json!({"type": "array"}))),
            json!([])
        );
        // An array is given where the leaf is about the arrays of another place.
        let either = json!({"type": "array", "prefixItems": [{}, {"uniqueItems": true}]});
        assert_eq!(counterexample(&json!(false), &either), json!([]));
        assert_eq!(
            counterexample(&json!({"maxItems": 0}), &either),
            json!([null])
        );
        assert_eq!(
            depends_on(
                &json!({"maxItems": 1}),
                &json!({"allOf": [either, {"items": {"type": "array"}}]})
            ),
            (Side::B, "#/allOf/0/prefixItems/1/uniqueItems".to_owned())
        );
    }

    #[test]
    fn a_schema_that_is_nested_deep_in_items_is_decided_without_recursion() {
        let nested = |depth: usize, innermost: Value| {
            let mut schema = innermost;
            for _ in 0..depth {
                schema = Value::Object(Map::from_iter([
                    ("type".to_owned(), json!("array")),
                    ("items".to_owned(), schema),
                ]));
            }
            schema
        };
        // Each level is an item of the level above, and a task of its own.
        let (whole, any) = (
            nested(20_000, json!({"type": "integer"})),
            nested(20_000, json!({"type": "number"})),
        );
        let check = Checker::new()
            .budget(10_000_000)
            .check(&any, &whole)
            .unwrap();
        assert_eq!(check.verdict, Verdict::Yes);
        // A task costs steps, so a budget that is smaller than the schema is deep ends it.
        let small = Checker::new().budget(1_000);
        let verdict = small.subsumes(&any, &whole).unwrap();
        assert_eq!(reason_of(&verdict), Some(Reason::Budget));
        // The other way an instance holds an array for each level, and one that deep
        // cannot be given: there is no counterexample, and no stack is used up for one.
        let check = Checker::new()
            .budget(10_000_000)
            .check(&whole, &any)
            .unwrap();
        assert_eq!(reason_of(&check.verdict), Some(Reason::Unrepresentable));
        // An instance of 127 arrays inside one another is given, and no deeper one.
        let (integer, number) = (json!({"type": "integer"}), json!({"type": "number"}));
        let instance = counterexample(&nested(127, integer.clone()), &nested(127, number.clone()));
        let read: Value = serde_json::from_str(&instance.to_string()).unwrap();
        assert_eq!(read, instance);
        assert_eq!(
            reason(&nested(128, integer), &nested(128, number)),
            Reason::Unrepresentable
        );
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget((whole, any));
    }

    #[test]
    fn a_schema_subsumes_itself_whatever_it_contains() {
        let schemas = [
            json!({"type": "integer", "minimum": 0, "multipleOf": 0.5}),
            json!({"pattern": "^a", "format": "date", "maxLength": 3}),
            json!({"properties": {"a": {"items": {"contains": {}}}}, "additionalProperties": false}),
            json!({"unevaluatedProperties": false, "allOf": [{"properties": {"a": {}}}]}),
            json!({"oneOf": [{"minimum": 1}, {"maximum": 0}], "not": {"uniqueItems": true}}),
            json!({"prefixItems": [{"type": "null"}], "items": {"minItems": 2}, "maxItems": 3}),
            json!({"contains": {"contains": {}, "maxContains": 2}, "const": [[1, {"a": []}]]}),
            // A resource of its own, so that `#` is the schema wherever it stands.
            json!({"$id": "https://example.com/tree", "anyOf": [{"type": "null"}, {"items": {"$ref": "#"}}]}),
            json!({"$id": "https://example.com/endless", "$ref": "#"}),
            json!({"$dynamicAnchor": "x", "items": {"$dynamicRef": "#x"}, "minItems": 1}),
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
        // known to subsume even itself.
        let huge = json!({"type": "string", "maxLength": 1e30});
        assert_eq!(depends_on(&huge, &huge.clone()).1, "#/maxLength");
    }

    #[test]
    fn a_dynamic_reference_leads_to_one_schema_by_one_way_and_to_another_by_the_next() {
        // Through `a` the dynamic reference leads to a schema that accepts everything, and
        // through `d` alone to one that accepts nothing. So the schema accepts everything.
        // With one meaning for the reference it would be a schema and its own negation.
        let both_ways = json!({
            "$id": "https://example.com/root",
            "$ref": "a",
            "not": {"$ref": "d"},
            "$defs": {
                "d": {
                    "$id": "d",
                    "$dynamicRef": "#x",
                    "$defs": {"x": {"$dynamicAnchor": "x", "not": {}}},
                },
                "a": {
                    "$id": "a",
                    "$ref": "d",
                    "$defs": {"x": {"$dynamicAnchor": "x"}},
                },
            },
        });
        yes(&both_ways, &json!(true));
        assert_eq!(counterexample(&json!(false), &both_ways), json!(null));

        // A list whose items are what the schema that led to it says they are.
        let list = |of: Value| {
            json!({
                "$id": "https://example.com/of",
                "$ref": "list",
                "$defs": {
                    "item": of,
                    "list": {
                        "$id": "list",
                        "type": "array",
                        "items": {"$dynamicRef": "#item"},
                        "$defs": {"item": {"$dynamicAnchor": "item"}},
                    },
                },
            })
        };
        let integers = list(json!({"$dynamicAnchor": "item", "type": "integer"}));
        let numbers = list(json!({"$dynamicAnchor": "item", "type": "number"}));
        yes(&numbers, &integers);
        assert_eq!(counterexample(&integers, &numbers), json!([0.1]));
        // Without an anchor of that name on the way, the anchor of the list itself is
        // meant, which takes any item. So does a `$ref`, whatever is on the way.
        let any = list(json!({"type": "integer"}));
        yes(&any, &json!({"type": "array"}));
        let mut fixed = integers.clone();
        fixed["$defs"]["list"]["items"] = json!({"$ref": "#item"});
        yes(&fixed, &json!({"type": "array"}));
        assert_eq!(counterexample(&integers, &fixed), json!([null]));

        // A reference that leads into the middle of a resource enters the resource: its
        // anchor is further out than that of the list.
        let by_the_middle = json!({
            "$id": "https://example.com/root",
            "$ref": "integers#/$defs/inner",
            "$defs": {
                "integers": {
                    "$id": "integers",
                    "$defs": {
                        "inner": {"$ref": "list"},
                        "item": {"$dynamicAnchor": "item", "type": "integer"},
                    },
                },
                "list": integers["$defs"]["list"],
            },
        });
        yes(&by_the_middle, &integers);
        yes(&integers, &by_the_middle);
    }

    #[test]
    fn an_anchor_where_the_draft_puts_no_schema_is_bound_to_nothing() {
        // The draft puts no schema under `x-shared`, so it looks for no anchor there, and a
        // reference that leads there by a pointer does not change that. The items of the
        // list are what its own anchor says.
        let list = |shared: &str| {
            let mut document = json!({
                "$id": "https://example.com/root",
                "allOf": [{"$ref": format!("#/{shared}/item")}, {"$ref": "list"}],
                "$defs": {
                    "list": {
                        "$id": "list",
                        "items": {"$dynamicRef": "#item"},
                        "$defs": {"item": {"$dynamicAnchor": "item", "type": "string"}},
                    },
                },
            });
            document[shared]["item"] = json!({"$dynamicAnchor": "item", "type": ["null", "array"]});
            document
        };
        let of = |items: Value| json!({"type": ["null", "array"], "items": items});
        let (strings, lists) = (
            of(json!({"type": "string"})),
            of(json!({"type": ["null", "array"]})),
        );
        yes(&list("x-shared"), &strings);
        yes(&strings, &list("x-shared"));
        // Where the draft puts a schema, the anchor is one, and it is further out.
        yes(&list("$defs"), &lists);
        yes(&lists, &list("$defs"));
    }

    #[test]
    fn a_leaf_that_holds_a_schema_is_a_leaf_for_each_thing_that_the_schema_says() {
        // A `contains` that counts is a leaf that holds a schema. By way of `strings` that
        // schema takes what `item` says, and by itself it takes anything. The document asks
        // for the first and not for the second.
        let lists = |count: Value, item: Value| {
            json!({
                "$id": "https://example.com/root",
                "$ref": "strings",
                "not": {"$ref": "list"},
                "$defs": {
                    "strings": {"$id": "strings", "$ref": "list", "$defs": {"item": item}},
                    "list": {
                        "$id": "list",
                        "contains": {"$dynamicRef": "#item"},
                        "minContains": count,
                        "$defs": {"item": {"$dynamicAnchor": "item"}},
                    },
                },
            })
        };
        // A count that is kept, and one that is too large to keep.
        for (count, keyword) in [(json!(2), "minContains"), (json!(1e30), "contains")] {
            // Where the two say the same, they are one leaf, and a leaf with its negation is
            // nothing.
            let same = lists(count.clone(), json!({"$dynamicAnchor": "item"}));
            yes(&json!(false), &same);
            // Where they differ, they are two, and nothing follows from one about the other.
            let strings = json!({"$dynamicAnchor": "item", "type": "string"});
            assert_eq!(
                depends_on(&json!(false), &lists(count, strings)),
                (Side::B, format!("#/$defs/list/{keyword}"))
            );
        }
    }

    #[test]
    fn unevaluated_properties_are_those_that_no_schema_in_place_evaluates() {
        let same = |one: &Value, other: &Value| {
            yes(one, other);
            yes(other, one);
        };
        let closed = |mut schema: Value| {
            schema["unevaluatedProperties"] = json!(false);
            schema
        };
        let only =
            |properties: Value| json!({"properties": properties, "additionalProperties": false});
        let text = json!({"type": "string"});

        // Next to nothing in place it is `additionalProperties`.
        same(
            &closed(json!({"properties": {"a": text}})),
            &only(json!({"a": text})),
        );
        // It sees into the schemas in place, which `additionalProperties` does not.
        let parts = json!({"allOf": [{"properties": {"a": text}}, {"properties": {"b": {}}}]});
        same(&closed(parts.clone()), &only(json!({"a": text, "b": {}})));
        let mut blind = parts;
        blind["additionalProperties"] = json!(false);
        same(&blind, &json!({"maxProperties": 0}));
        // And not into a schema beside it.
        let beside =
            json!({"allOf": [{"properties": {"a": {}}}, {"unevaluatedProperties": false}]});
        same(&beside, &json!({"maxProperties": 0}));

        // A branch of `anyOf` evaluates its properties where the instance satisfies it. So
        // a property that makes its branch fail is evaluated by nothing.
        let number = json!({"type": "number"});
        let either = closed(json!({
            "anyOf": [{"properties": {"a": text}}, {"properties": {"b": number}}],
        }));
        same(&either, &only(json!({"a": text, "b": number})));
        // A branch that the instance does not satisfy evaluates nothing, also not the
        // properties that are as it asks.
        let needed = closed(json!({
            "anyOf": [
                {"properties": {"a": text, "c": {}}, "required": ["c"]},
                {"properties": {"b": number}},
            ],
        }));
        assert_eq!(
            counterexample(&needed, &only(json!({"a": text, "b": number}))),
            json!({"a": "", "b": 0})
        );

        // What the condition names is evaluated only where the condition is met.
        let kind = json!({"properties": {"kind": {"const": "a"}}, "required": ["kind"]});
        let conditional = closed(json!({
            "if": kind,
            "then": {"properties": {"x": {}}},
            "else": {"properties": {"y": {}}},
        }));
        let mut met = only(json!({"kind": {"const": "a"}, "x": {}}));
        met["required"] = json!(["kind"]);
        same(
            &conditional,
            &json!({"anyOf": [met, only(json!({"y": {}}))]}),
        );
        assert_eq!(
            counterexample(&conditional, &only(json!({"kind": {}, "x": {}, "y": {}}))),
            json!({"kind": null, "x": null, "y": null})
        );

        // A schema of `dependentSchemas` evaluates where the object has the property.
        let dependent = closed(json!({
            "properties": {"a": {}},
            "dependentSchemas": {"a": {"properties": {"b": text}}},
        }));
        let mut with_a = only(json!({"a": {}, "b": text}));
        with_a["required"] = json!(["a"]);
        same(
            &dependent,
            &json!({"anyOf": [with_a, {"maxProperties": 0}]}),
        );

        // A schema in place with an `unevaluatedProperties` of its own evaluates every
        // property, so the one around it has nothing left.
        let inner = closed(json!({
            "allOf": [{"properties": {"a": text}, "unevaluatedProperties": {"type": "null"}}],
        }));
        let mut open = only(json!({"a": text}));
        open["additionalProperties"] = json!({"type": "null"});
        same(&inner, &open);

        // What a `$dynamicRef` leads to evaluates as well, and that is another schema by
        // another way: with the anchor of the root on the way it is `b`, and without it
        // nothing.
        let extended = |anchor: &str| {
            json!({
                "$id": "https://example.com/root",
                "$ref": "base",
                "$defs": {
                    "more": {anchor: "more", "properties": {"b": {}}},
                    "base": {
                        "$id": "base",
                        "properties": {"a": {}},
                        "allOf": [{"$dynamicRef": "#more"}],
                        "unevaluatedProperties": false,
                        "$defs": {"more": {"$dynamicAnchor": "more"}},
                    },
                },
            })
        };
        same(
            &extended("$dynamicAnchor"),
            &only(json!({"a": {}, "b": {}})),
        );
        same(&extended("$anchor"), &only(json!({"a": {}})));
    }

    #[test]
    fn unevaluated_items_are_those_that_no_schema_in_place_evaluates() {
        let same = |one: &Value, other: &Value| {
            yes(one, other);
            yes(other, one);
        };
        let closed = |mut schema: Value| {
            schema["unevaluatedItems"] = json!(false);
            schema
        };
        let (text, number) = (json!({"type": "string"}), json!({"type": "number"}));
        let first = |items: Value| json!({"prefixItems": items, "items": false});

        // Next to nothing in place it is `items`.
        same(
            &closed(json!({"prefixItems": [text]})),
            &first(json!([text])),
        );
        // The first items that a schema of `allOf` names are evaluated too.
        let longer = json!({"allOf": [{"prefixItems": [{}, number]}], "prefixItems": [text]});
        same(&closed(longer), &first(json!([text, number])));
        // An item that the schema of `contains` accepts is evaluated, so every item is one.
        let nulls = json!({"items": {"type": "null"}, "minItems": 1});
        same(&closed(json!({"contains": {"type": "null"}})), &nulls);

        // A branch of `anyOf` evaluates where the instance satisfies it: a second item
        // that is no number makes its branch fail, and nothing evaluates it then.
        let either = closed(json!({
            "anyOf": [{"prefixItems": [text]}, {"prefixItems": [{}, number]}],
        }));
        yes(&json!({"maxItems": 2}), &either);
        assert_eq!(
            counterexample(&either, &json!({"prefixItems": [text], "maxItems": 2})),
            json!(["", null])
        );
        same(
            &either,
            &json!({"anyOf": [first(json!([{}, number])), {"maxItems": 1, "prefixItems": [text]}]}),
        );

        // Where the condition is met, it evaluates with `then`.
        let conditional = closed(json!({
            "if": {"prefixItems": [{"const": 1}], "minItems": 1},
            "then": {"prefixItems": [{}, text]},
            "else": {"prefixItems": [number]},
        }));
        let mut met = first(json!([{"const": 1}, text]));
        met["minItems"] = json!(1);
        let unmet =
            json!({"prefixItems": [{"type": "number", "not": {"const": 1}}], "maxItems": 1});
        same(&conditional, &json!({"anyOf": [met, unmet]}));

        // A schema of `dependentSchemas` is asked of no array, so it evaluates no item.
        let dependent = closed(json!({"dependentSchemas": {"a": {"items": {}}}}));
        same(&dependent, &json!({"maxItems": 0}));
        // A schema in place with an `unevaluatedItems` of its own evaluates every item.
        let inner = closed(json!({
            "allOf": [{"prefixItems": [text], "unevaluatedItems": {"type": "null"}}],
        }));
        same(
            &inner,
            &json!({"prefixItems": [text], "items": {"type": "null"}}),
        );

        // The schema of a `contains` is what it is by the way that led to it: with the
        // anchor of the root on the way its items are strings, and without it nulls.
        let contained = |anchor: &str| {
            json!({
                "$id": "https://example.com/root",
                "$ref": "list",
                "$defs": {
                    "item": {anchor: "item", "type": "string"},
                    "list": {
                        "$id": "list",
                        "contains": {"$dynamicRef": "#item"},
                        "unevaluatedItems": false,
                        "$defs": {"item": {"$dynamicAnchor": "item", "type": "null"}},
                    },
                },
            })
        };
        let of = |kind: &str| json!({"items": {"type": kind}, "minItems": 1});
        same(&contained("$dynamicAnchor"), &of("string"));
        same(&contained("$anchor"), &of("null"));
    }

    #[test]
    fn a_tree_that_is_extended_is_extended_at_every_node() {
        // The children of a node are whatever the outermost schema with the anchor says a
        // node is. So a tree that asks for a name asks for it at every node.
        let tree = |children: Value| {
            json!({
                "$id": "tree",
                "$dynamicAnchor": "node",
                "type": "object",
                "properties": {"children": {"type": "array", "items": children}},
            })
        };
        let named = |tree: Value| {
            json!({
                "$id": "https://example.com/named",
                "$dynamicAnchor": "node",
                "$ref": "tree",
                "required": ["name"],
                "$defs": {"tree": tree},
            })
        };
        let plain = |tree: Value| json!({"$id": "https://example.com/plain", "$ref": "tree", "$defs": {"tree": tree}});
        let dynamic = || tree(json!({"$dynamicRef": "#node"}));
        let everywhere = named(dynamic());
        // With a `$ref` the children are nodes of the tree as it was, without a name.
        let at_the_root = named(tree(json!({"$ref": "#"})));
        yes(&at_the_root, &everywhere);
        assert_eq!(
            counterexample(&everywhere, &at_the_root),
            json!({"children": [{}], "name": null})
        );
        yes(&plain(dynamic()), &everywhere);
        assert_eq!(counterexample(&everywhere, &plain(dynamic())), json!({}));
        // By itself the tree is the same with either reference.
        yes(&plain(dynamic()), &plain(tree(json!({"$ref": "#"}))));
        yes(&plain(tree(json!({"$ref": "#"}))), &plain(dynamic()));
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
        // A budget that ends the check at the first alternatives keeps the others unmade.
        let small = Checker::new().budget(100);
        for (a, b) in [(&nothing, &long), (&long, &anything)] {
            let verdict = small.subsumes(a, b).unwrap();
            assert_eq!(reason_of(&verdict), Some(Reason::Budget));
        }
        // The first two that hold together give an instance, long before the last two: with
        // far fewer steps than there are alternatives.
        let enough = Checker::new().budget(100_000);
        let counterexample = json!(null);
        assert_eq!(
            enough.subsumes(&long, &anything).unwrap(),
            Verdict::No { counterexample }
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
        // Twenty choices between two leaves about arrays: a million branches, none of which
        // is refuted and none of which gives an instance. The first one settles the answer.
        let choice = |n: u32| {
            json!({"anyOf": [
                {"contains": {}, "minContains": n + 2},
                {"contains": {}, "maxContains": n + 100},
            ]})
        };
        let b = json!({"type": "array", "allOf": (0..20).map(choice).collect::<Vec<_>>()});
        let a = json!({"type": "array", "uniqueItems": true});
        // So the budget may be far smaller than the branches are many.
        let small = Checker::new().budget(10_000);
        assert!(matches!(
            small.subsumes(&a, &b).unwrap(),
            Verdict::Unknown {
                reason: Reason::Unsupported { .. }
            }
        ));
        // An instance is still found where there is one.
        let a = json!({"type": "null"});
        assert_eq!(
            counterexample(&a, &json!({"anyOf": [b, {"type": "number"}]})),
            json!(0)
        );
    }

    #[test]
    fn branches_whose_array_depends_on_a_leaf_are_left_alone_too() {
        // Every item is an array of which a leaf is asked, so whether there is an array
        // with an item is what the engine does not know. Twenty choices that such an array
        // satisfies either way: a million branches, none of which is refuted and none of
        // which gives an instance. The first one settles the answer here too.
        let choice = |n: u32| json!({"anyOf": [{"maxItems": n + 1}, {"contains": {"minimum": n}}]});
        let b = json!({
            "type": "array",
            "minItems": 1,
            "items": {"type": "array", "uniqueItems": true},
            "allOf": (0..20).map(choice).collect::<Vec<_>>(),
        });
        // So the budget may be far smaller than the branches are many.
        let small = Checker::new().budget(10_000);
        assert_eq!(
            small.subsumes(&json!({"type": "null"}), &b).unwrap(),
            Verdict::Unknown {
                reason: Reason::Unsupported {
                    schema: Side::B,
                    location: "#/items/uniqueItems".to_owned(),
                },
            }
        );
        // So it is with an object whose property depends on a leaf.
        let choice = |n: u32| json!({"anyOf": [{"maxProperties": n + 1}, {"required": ["a"]}]});
        let b = json!({
            "type": "object",
            "required": ["a"],
            "properties": {"a": {"type": "array", "uniqueItems": true}},
            "allOf": (0..20).map(choice).collect::<Vec<_>>(),
        });
        assert!(matches!(
            small.subsumes(&json!({"type": "null"}), &b).unwrap(),
            Verdict::Unknown {
                reason: Reason::Unsupported { .. }
            }
        ));
    }

    #[test]
    fn a_disjunction_that_leaves_no_alternative_is_split_before_the_others() {
        // Eight kinds of object, each with a property of its own that it requires, written
        // in two ways: A closes each kind with a second schema beside the first, and B in
        // the schema itself. Each alternative of the `oneOf` of B stands with the negation of
        // every other alternative and of every alternative of A, which are fifteen
        // disjunctions, and only the negation of its own kind in A leaves no alternative.
        // Split in the order in which they are met, the others come first, and the steps
        // grow fivefold or more with each kind: with seven kinds they are past ten million.
        let names = ["a", "b", "c", "d", "e", "f", "g", "h"];
        let open = |name: &str| {
            json!({
                "type": "object",
                "properties": {name: {"type": "string"}, "extra": {"type": "boolean"}},
                "required": [name],
            })
        };
        let plain = |name: &&str| {
            let mut kind = open(name);
            kind["additionalProperties"] = json!(false);
            kind
        };
        let wordy = |name: &&str| {
            let named = json!({format!("^{name}$"): true, "^extra$": true});
            json!({"allOf": [
                open(name),
                {"patternProperties": named, "additionalProperties": false},
            ]})
        };
        let a = json!({"oneOf": names.iter().map(wordy).collect::<Vec<_>>()});
        let b = json!({"oneOf": names.iter().map(plain).collect::<Vec<_>>()});
        let enough = Checker::new().budget(100_000);
        assert_eq!(enough.subsumes(&a, &b).unwrap(), Verdict::Yes);
        assert_eq!(enough.subsumes(&b, &a).unwrap(), Verdict::Yes);
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
        // A budget that is far smaller than the schemas are deep says so.
        let (a, b) = (deep(), deep());
        let small = Checker::new().budget(100);
        assert_eq!(small.subsumes(&a, &b).unwrap(), Verdict::Yes);
        // Dropping a value this deep would recurse, which is no concern of this test.
        std::mem::forget((a, b));
    }
}
