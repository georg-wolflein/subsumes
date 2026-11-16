//! What a branch says about objects.
//!
//! A term about objects asks one of a few things of an object: that every property with a
//! name of some language has a value that a schema accepts, that there is a property with a
//! name of some language, or that there are at least or at most so many properties. Negated,
//! the first asks for a property that there has to be, with a value that the schema does not
//! accept. So what a branch takes in comes down to three things:
//!
//! - what *every* property with a name of a language satisfies,
//! - *some* property that there has to be, with a name of a language and a value that
//!   satisfies something,
//! - and two bounds on the number of properties.
//!
//! What a value satisfies is a [c-reference](CRefId): schemas by name, never written out.
//!
//! # Is an object left?
//!
//! The languages cut the names into *fragments*: sets of names that are in the same
//! languages, so that every name of a fragment is asked the same. A name that a language
//! lists is a fragment by itself, and what no language lists is cut by the patterns. A
//! fragment says how many names it has, which may be without end.
//!
//! An object is left when each property that there has to be finds a name: one of a
//! fragment in its language, whose value satisfies what every property of the fragment does
//! and what this one is asked besides. Two of them may share a name, and then the value
//! satisfies both. They have to share where a fragment has fewer names than they are, or
//! where the object may not have as many properties as they are. And there have to be
//! names enough for the least number of properties, in fragments whose properties can have
//! a value at all.
//!
//! Whether a value can satisfy a c-reference is not decided here. The engine is asked, and
//! what it does not know yet it is told to find out first.

use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use serde_json::{Map, Value};

use super::search::{self, Place, Placed, Places, Slot};
use super::{Left, Solver, State, state};
use crate::context::{Budget, Exhausted};
use crate::language::{LanguageId, Languages, Lengths, Shape};
use crate::normalize::{Cause, DEEPEST, Found, Witness};
use crate::term::{CRefId, Term, Terms};

/// The objects that a branch still accepts.
#[derive(Debug, Clone, Default)]
pub(crate) struct Objects {
    /// What the value of every property with a name of a language satisfies.
    every: BTreeSet<(LanguageId, CRefId)>,
    /// The properties that there have to be: each with a name of a language and a value
    /// that satisfies something.
    some: BTreeSet<(LanguageId, CRefId)>,
    /// The least number of properties, and the most if there is a most.
    min: u64,
    max: Option<u64>,
    /// Whether what was asked leaves no object on the face of it.
    none: bool,
}

impl Objects {
    /// Takes in what a term about objects asks of an object, as it stands or negated.
    /// `PNames` is not among them: the engine works out the language of the names first.
    pub fn take(&mut self, term: &Term, negated: bool, terms: &mut Terms) {
        match (term, negated) {
            (Term::PProp(names, variable), false) => {
                let of = terms.literal(*variable, false);
                self.every(*names, of, terms);
            }
            // Some property with such a name has a value that the schema does not accept.
            (Term::PProp(names, variable), true) => {
                let of = terms.literal(*variable, true);
                self.some(*names, of, terms);
            }
            (Term::PReq(names), false) => self.some(*names, Terms::ANYTHING, terms),
            // No property has such a name: the value of one that has satisfies nothing.
            (Term::PReq(names), true) => self.every(*names, Terms::NOTHING, terms),
            (Term::MinProps(least), false) => self.min = self.min.max(*least),
            // Fewer than the least.
            (Term::MinProps(least), true) => match least.checked_sub(1) {
                Some(most) => self.at_most(most),
                None => self.none = true,
            },
            (Term::MaxProps(most), false) => self.at_most(*most),
            // More than the most. Beyond the largest count this asks for one property less
            // than it should, which lets objects in and none out.
            (Term::MaxProps(most), true) => self.min = self.min.max(most.saturating_add(1)),
            (other, _) => unreachable!("{other:?} is not about objects"),
        }
    }

    /// Takes in that every property has a name outside a language, or with `negated` that
    /// some property has one.
    pub fn names(&mut self, outside: LanguageId, negated: bool, terms: &mut Terms) {
        if negated {
            self.some(outside, Terms::ANYTHING, terms);
        } else {
            self.every(outside, Terms::NOTHING, terms);
        }
    }

    fn every(&mut self, names: LanguageId, of: CRefId, terms: &mut Terms) {
        if of == Terms::ANYTHING || names == Languages::NOTHING {
            return;
        }
        // A property that there has to be with just these names satisfies this too.
        let mut there = self
            .some
            .range((names, CRefId::FIRST)..=(names, CRefId::LAST));
        if there.any(|(_, other)| terms.both(of, *other) == Terms::NOTHING) {
            self.none = true;
        }
        self.every.insert((names, of));
    }

    fn some(&mut self, names: LanguageId, of: CRefId, terms: &mut Terms) {
        let mut all = self
            .every
            .range((names, CRefId::FIRST)..=(names, CRefId::LAST));
        if of == Terms::NOTHING
            || names == Languages::NOTHING
            || all.any(|(_, other)| terms.both(of, *other) == Terms::NOTHING)
        {
            self.none = true;
        }
        self.some.insert((names, of));
    }

    fn at_most(&mut self, most: u64) {
        self.max = Some(self.max.map_or(most, |max| max.min(most)));
    }

    /// How much there is to copy when the branch splits.
    pub fn weight(&self) -> u64 {
        (self.every.len() + self.some.len()) as u64
    }

    /// Whether an object is left, and with `give` such an object.
    ///
    /// `ask` says what the engine knows of a c-reference: whether a value can satisfy it.
    /// `None` is one that the engine has yet to decide. Those are handed back, and the
    /// question is put again when they are decided.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search.
    pub fn left(
        &self,
        with: &mut Solver,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
        give: bool,
    ) -> Result<Left, Exhausted> {
        if self.none || self.max.is_some_and(|max| max < self.min) {
            return Ok(Left::Nothing);
        }
        let languages = self.every.iter().chain(&self.some).map(|asked| asked.0);
        let languages: BTreeSet<LanguageId> = languages.collect();
        let languages: Vec<LanguageId> = languages.into_iter().collect();
        let partition = with
            .partitions
            .of(&languages, with.languages, with.budget)?;

        // What every property of a fragment satisfies.
        let mut every = vec![Terms::ANYTHING; partition.fragments.len()];
        for (names, of) in &self.every {
            let held = &partition.within[names];
            with.budget.charge(1 + (held.len() / 8) as u64)?;
            for fragment in held.iter() {
                let all = &mut every[*fragment as usize];
                *all = with.terms.both(*all, *of);
            }
        }
        // The properties that there have to be, those first that have the fewest fragments
        // to be in.
        let mut some: Vec<(&[u32], CRefId)> = Vec::with_capacity(self.some.len());
        for (names, of) in &self.some {
            some.push((&partition.within[names], *of));
        }
        some.sort_by_key(|(fragments, _)| fragments.len());

        let search = Search {
            objects: self,
            partition: &partition,
            every: &every,
            some: &some,
            used: vec![Vec::new(); partition.fragments.len()],
        };
        search::run(search, with, ask, give)
    }
}

/// The names of all properties, cut into fragments by a list of languages.
#[derive(Debug)]
pub(crate) struct Partition {
    /// The fragments: first those of one name each, in the order of the names, then the
    /// others.
    fragments: Vec<Fragment>,
    /// How many of them are of one name each.
    named: usize,
    /// The fragments that each language of the list holds, in order.
    within: HashMap<LanguageId, Box<[u32]>>,
}

#[derive(Debug)]
struct Fragment {
    names: Names,
    /// How many names it has, or `None` if there is no end of them.
    size: Option<u64>,
}

#[derive(Debug)]
enum Names {
    /// One name.
    One(Box<str>),
    /// The names of a language, but for a few of them that are fragments of their own.
    Of {
        language: LanguageId,
        but: Vec<Box<str>>,
    },
}

/// The names that no language lists, cut by a list of patterns: one part for each way of
/// being in some of them and outside the others, unless no name is that way.
#[derive(Debug)]
struct Rest {
    names: LanguageId,
    /// Whether the names are in each pattern of the list.
    within: Box<[bool]>,
}

/// The partitions of a check, each made once.
#[derive(Debug, Default)]
pub(crate) struct Partitions {
    of: HashMap<Box<[LanguageId]>, Rc<Partition>>,
    rests: HashMap<Box<[LanguageId]>, Rc<[Rest]>>,
}

impl Partitions {
    /// The partition by a list of languages, which is in order and names none twice.
    fn of(
        &mut self,
        asked: &[LanguageId],
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<Rc<Partition>, Exhausted> {
        if let Some(known) = self.of.get(asked) {
            return Ok(Rc::clone(known));
        }
        // A language that is kept as what is outside a few others is cut as they are.
        let mut made_of: BTreeSet<LanguageId> = BTreeSet::new();
        for language in asked {
            match languages.shape(*language) {
                Shape::Outside(of) => made_of.extend(of.iter().copied()),
                _ => {
                    made_of.insert(*language);
                }
            }
        }
        // Every word that a set of words lists is a name of its own. Every other language
        // is a pattern here.
        let mut names: BTreeSet<Box<str>> = BTreeSet::new();
        let mut patterns: Vec<LanguageId> = Vec::new();
        for language in &made_of {
            match languages.shape(*language) {
                Shape::Words { words, .. } => names.extend(words.iter().cloned()),
                Shape::Outside(_) | Shape::Other => patterns.push(*language),
            }
        }
        let names: Vec<Box<str>> = names.into_iter().collect();
        let mut matched: Vec<Box<[bool]>> = Vec::with_capacity(names.len());
        for name in &names {
            let mut by = Vec::with_capacity(patterns.len());
            for pattern in &patterns {
                by.push(languages.contains(*pattern, name, budget)?);
            }
            matched.push(by.into());
        }

        let mut fragments: Vec<Fragment> = Vec::with_capacity(names.len() + 1);
        for name in &names {
            fragments.push(Fragment {
                names: Names::One(name.clone()),
                size: Some(1),
            });
        }
        let rests = self.rests(&patterns, languages, budget)?;
        let mut kept: Vec<&Rest> = Vec::with_capacity(rests.len());
        for rest in rests.iter() {
            // The names that are fragments of their own are not of this one.
            let listed = names.iter().zip(&matched);
            let but: Vec<Box<str>> = listed
                .filter(|(_, by)| **by == rest.within)
                .map(|(name, _)| name.clone())
                .collect();
            let size = languages.size(rest.names, budget)?;
            let size = size.map(|size| size.saturating_sub(but.len() as u64));
            if size != Some(0) {
                kept.push(rest);
                fragments.push(Fragment {
                    names: Names::Of {
                        language: rest.names,
                        but,
                    },
                    size,
                });
            }
        }

        // Whether one of the languages that the list is made of holds a fragment.
        let place: HashMap<LanguageId, usize> = patterns.iter().copied().zip(0..).collect();
        let named = names.len();
        let holds = |languages: &Languages, language: LanguageId, fragment: usize| match (
            languages.shape(language),
            fragment.checked_sub(named),
        ) {
            (Shape::Words { words, others }, None) => words.contains(&names[fragment]) != others,
            (Shape::Words { others, .. }, Some(_)) => others,
            (_, None) => matched[fragment][place[&language]],
            (_, Some(rest)) => kept[rest].within[place[&language]],
        };
        let index: HashMap<&str, u32> = names.iter().map(AsRef::as_ref).zip(0..).collect();
        let mut within = HashMap::with_capacity(asked.len());
        for language in asked {
            let all = 0..fragments.len();
            let held: Vec<u32> = match languages.shape(*language) {
                // A few words are found by their names.
                Shape::Words {
                    words,
                    others: false,
                } => words.iter().map(|word| index[word.as_ref()]).collect(),
                Shape::Outside(of) => {
                    budget.charge(1 + (fragments.len() / 8) as u64)?;
                    let outside =
                        |fragment: &usize| !of.iter().any(|one| holds(languages, *one, *fragment));
                    all.filter(outside).map(number).collect()
                }
                _ => {
                    budget.charge(1 + (fragments.len() / 8) as u64)?;
                    all.filter(|fragment| holds(languages, *language, *fragment))
                        .map(number)
                        .collect()
                }
            };
            within.insert(*language, held.into());
        }
        let partition = Rc::new(Partition {
            fragments,
            named,
            within,
        });
        self.of.insert(asked.into(), Rc::clone(&partition));
        Ok(partition)
    }

    /// Every string, cut by a list of patterns.
    fn rests(
        &mut self,
        patterns: &[LanguageId],
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<Rc<[Rest]>, Exhausted> {
        if let Some(known) = self.rests.get(patterns) {
            return Ok(Rc::clone(known));
        }
        let mut rests: Vec<(LanguageId, Vec<bool>)> = vec![(Languages::EVERYTHING, Vec::new())];
        for pattern in patterns {
            let other = languages.complement(*pattern, budget)?;
            let mut cut = Vec::with_capacity(rests.len() + 1);
            for (names, within) in rests {
                budget.charge(1)?;
                for (side, inside) in [(*pattern, true), (other, false)] {
                    let both = languages.intersection(names, side, budget)?;
                    if !languages.is_empty(both, Lengths::ANY, budget)? {
                        let mut within = within.clone();
                        within.push(inside);
                        cut.push((both, within));
                    }
                }
            }
            rests = cut;
        }
        let rests = rests.into_iter().map(|(names, within)| Rest {
            names,
            within: within.into(),
        });
        let rests: Rc<[Rest]> = rests.collect();
        self.rests.insert(patterns.into(), Rc::clone(&rests));
        Ok(rests)
    }
}

fn number(fragment: usize) -> u32 {
    u32::try_from(fragment).expect("fewer than 2^32 fragments")
}

/// The search for an object: a place for every property that there has to be. A place is a
/// fragment, of which the property has a name that is not chosen yet.
struct Search<'s> {
    objects: &'s Objects,
    partition: &'s Partition,
    /// What every property of each fragment satisfies.
    every: &'s [CRefId],
    /// The properties that there have to be: the fragments that each may be in, and what
    /// its value satisfies.
    some: &'s [(&'s [u32], CRefId)],
    /// The slots of each fragment.
    used: Vec<Vec<usize>>,
}

impl Places for Search<'_> {
    type At = u32;

    fn asked(&self, which: usize) -> Option<CRefId> {
        self.some.get(which).map(|(_, of)| *of)
    }

    fn at(&self, fragment: u32) -> CRefId {
        self.every[fragment as usize]
    }

    fn open(&mut self, fragment: u32, slot: usize) {
        self.used[fragment as usize].push(slot);
    }

    fn close(&mut self, fragment: u32) {
        self.used[fragment as usize].pop();
    }

    /// Where one of the properties that there have to be may go.
    fn places(&self, placed: &Placed<u32>, which: usize) -> Vec<Place<u32>> {
        let (fragments, _) = self.some[which];
        let most = self.objects.max;
        let room = most.is_none_or(|most| (placed.slots.len() as u64) < most);
        let (mut join, mut open) = (Vec::new(), Vec::new());
        // The fragments that are not of one name come last and are tried first: what their
        // properties satisfy is the least.
        for fragment in fragments.iter().rev() {
            let size = self.partition.fragments[*fragment as usize].size;
            let used = &self.used[*fragment as usize];
            // A new property is asked no more than one that is shared. So sharing is tried
            // only where a fragment may run out of names or the object out of properties.
            if most.is_some() || size.is_some() {
                join.extend(used.iter().map(|slot| Place::Join(*slot)));
            }
            if room && size.is_none_or(|size| (used.len() as u64) < size) {
                open.push(Place::Open(*fragment));
            }
        }
        // With a most, the fewest properties first.
        if most.is_some() {
            join.extend(open);
            join
        } else {
            open.extend(join);
            open
        }
    }

    /// With a place for every property that there has to be: whether the object has
    /// properties enough, with more of them from the fragments that have names to spare.
    ///
    /// `None` if the object stands only as far as the engine knows, which is noted.
    fn fill(
        &mut self,
        placed: &mut Placed<u32>,
        with: &mut Solver,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
        give: bool,
    ) -> Result<Option<Left>, Exhausted> {
        let need = self.objects.min.saturating_sub(placed.slots.len() as u64);
        let in_the_way = |slot: &Slot<u32>| slot.value.as_ref().err().copied().flatten();
        let mut cause = placed.slots.iter().find_map(in_the_way);
        // The properties that are known to have a value, and those that may have one.
        let (mut sure, mut possible) = (0_u64, 0_u64);
        let mut more: Vec<(usize, u64, Rc<Witness>)> = Vec::new();
        // The fragments of one name each come last: of those, each is asked something else.
        let named = self.partition.named;
        for fragment in (named..self.partition.fragments.len()).chain(0..named) {
            if sure >= need {
                break;
            }
            let size = self.partition.fragments[fragment].size;
            let used = self.used[fragment].len() as u64;
            let spare = size.map_or(u64::MAX, |size| size.saturating_sub(used));
            if spare == 0 {
                continue;
            }
            with.budget.charge(1)?;
            let taken = spare.min(need - sure);
            match state(self.every[fragment], ask, &mut placed.wanted) {
                State::Nothing => {}
                State::Possible(why) => {
                    possible = possible.saturating_add(spare);
                    cause.get_or_insert(why);
                }
                State::Sure(witness) => {
                    sure += taken;
                    more.push((fragment, taken, witness));
                }
                State::Wanted => sure += taken,
            }
        }
        if !placed.wanted.is_empty() {
            return Ok(Some(Left::Needs(std::mem::take(&mut placed.wanted))));
        }
        // However the properties that there have to be are placed, the names of the same
        // fragments are there to be had. So without names enough here, there are none.
        if sure.saturating_add(possible) < need {
            return Ok(Some(Left::Nothing));
        }
        if let Some(cause) =
            cause.filter(|_| sure < need || placed.slots.iter().any(|slot| slot.value.is_err()))
        {
            placed.depends.get_or_insert(cause);
            return Ok(None);
        }
        // An object is one level deeper than the deepest of its values. One that would be
        // too deep to give is passed over for another.
        let values = placed
            .slots
            .iter()
            .filter_map(|slot| slot.value.as_ref().ok());
        let values = values.chain(more.iter().map(|(_, _, value)| value));
        let deepest = values.map(|value| value.depth).max().unwrap_or(0);
        if deepest >= DEEPEST {
            placed.depends.get_or_insert(Cause::Depth);
            return Ok(None);
        }
        if !give {
            return Ok(Some(Left::Value(None)));
        }
        let object = self.given(&placed.slots, with, &more, deepest + 1)?;
        Ok(Some(Left::Value(Some(object))))
    }
}

impl Search<'_> {
    /// The object: a name and a value for each slot, and for each property that was added
    /// to have enough. `depth` is how deep it is.
    fn given(
        &self,
        slots: &[Slot<u32>],
        with: &mut Solver,
        more: &[(usize, u64, Rc<Witness>)],
        depth: u32,
    ) -> Result<Rc<Witness>, Exhausted> {
        let filled = slots.iter().map(|slot| {
            let value = slot.value.as_ref().expect("every slot has a value");
            (slot.at as usize, 1, value)
        });
        let added = more
            .iter()
            .map(|(fragment, count, value)| (*fragment, *count, value));
        let mut members = Map::new();
        let mut size = 1_u64;
        // The names that were made up for each fragment of more than one name.
        let mut made_up: HashMap<usize, Vec<String>> = HashMap::new();
        for (fragment, count, value) in filled.chain(added) {
            for _ in 0..count {
                // A step for everything that is copied.
                with.budget.charge(value.size)?;
                let name = match &self.partition.fragments[fragment].names {
                    Names::One(name) => name.to_string(),
                    Names::Of { language, but } => {
                        let before = made_up.entry(fragment).or_default();
                        let name = new_name(*language, but, before, with)?;
                        before.push(name.clone());
                        name
                    }
                };
                size = size.saturating_add(value.size);
                members.insert(name, value.value.clone());
            }
        }
        Ok(Rc::new(Witness {
            value: Value::Object(members),
            size,
            depth,
        }))
    }
}

/// A name of a language that is none of those left out and none of those made up before:
/// the shortest that is not empty, and of several one of plain characters.
fn new_name(
    language: LanguageId,
    but: &[Box<str>],
    before: &[String],
    with: &mut Solver,
) -> Result<String, Exhausted> {
    with.budget.charge(1 + before.len() as u64)?;
    let left_out = but.iter().map(AsRef::as_ref);
    let left_out = left_out.chain(before.iter().map(String::as_str));
    let left_out = with.languages.words(left_out);
    let others = with.languages.outside([left_out]);
    let left = with.languages.intersection(language, others, with.budget)?;
    let not_empty = Lengths { min: 1, max: None };
    for lengths in [not_empty, Lengths::ANY] {
        if let Some(name) = with.languages.shortest(left, lengths, with.budget)? {
            return Ok(name);
        }
    }
    unreachable!("a fragment has as many names as its size says")
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::schema::NodeId;
    use crate::term::{InstanceType, TypeSet, VarId};

    /// What is asked of the objects of a branch, with an engine that is made up.
    ///
    /// A variable is named by a number, and `-2` is the second one negated. To the engine
    /// here, no value satisfies variable 0, and none satisfies 3 and 4 together. Whether
    /// one satisfies variable 1 it does not know. Any other value is the names of what it
    /// satisfies.
    struct Asked {
        terms: Terms,
        languages: Languages,
        partitions: Partitions,
        variables: Vec<VarId>,
        objects: Objects,
        found: HashMap<CRefId, Found>,
        /// How many times the engine was told to find something out first.
        waited: usize,
    }

    impl Asked {
        fn new() -> Self {
            let mut terms = Terms::default();
            let string = TypeSet::of(InstanceType::String);
            let variables = (0..6).map(|index| {
                let variable = terms.new_variable(NodeId::new(0));
                let body = terms.unknown(string, format!("{index}"), NodeId::new(0), "x");
                terms.variable_mut(variable).body = body;
                variable
            });
            Self {
                variables: variables.collect(),
                terms,
                languages: Languages::default(),
                partitions: Partitions::default(),
                objects: Objects::default(),
                found: HashMap::new(),
                waited: 0,
            }
        }

        /// The language of a pattern, or with `=` in front of a few words, or with `!`
        /// of every string but a few words.
        fn names(&mut self, names: &str) -> LanguageId {
            if let Some(words) = names.strip_prefix('=') {
                return self.languages.words(words.split(','));
            }
            if let Some(words) = names.strip_prefix('!') {
                let words = self.languages.words(words.split(','));
                return self.languages.outside([words]);
            }
            self.languages.pattern(names).unwrap()
        }

        fn of(&mut self, variables: &[i32]) -> CRefId {
            let mut all = Terms::ANYTHING;
            for variable in variables {
                let named = self.variables[variable.unsigned_abs() as usize];
                let one = self.terms.literal(named, *variable < 0);
                all = self.terms.both(all, one);
            }
            all
        }

        /// Every property with such a name satisfies these.
        fn every(mut self, names: &str, variables: &[i32]) -> Self {
            let (names, of) = (self.names(names), self.of(variables));
            self.objects.every(names, of, &mut self.terms);
            self
        }

        /// No property has such a name.
        fn none(mut self, names: &str) -> Self {
            let names = self.names(names);
            self.objects.every(names, Terms::NOTHING, &mut self.terms);
            self
        }

        /// Some property with such a name satisfies these.
        fn some(mut self, names: &str, variables: &[i32]) -> Self {
            let (names, of) = (self.names(names), self.of(variables));
            self.objects.some(names, of, &mut self.terms);
            self
        }

        fn count(mut self, min: u64, max: Option<u64>) -> Self {
            (self.objects.min, self.objects.max) = (min, max);
            self
        }

        /// What the engine that is made up finds of a c-reference.
        fn decide(&self, of: CRefId) -> Found {
            let literals = self.terms.literals(of);
            let holds = |index: usize| literals.contains(&(self.variables[index], false));
            if holds(0) || (holds(3) && holds(4)) {
                return Found::Nothing;
            }
            if holds(1) {
                return Found::Unknown(Cause::Number);
            }
            let named = literals.iter().map(|(variable, negated)| {
                let sign = if *negated { "-" } else { "" };
                format!("{sign}{}", variable.index())
            });
            let value = json!(named.collect::<Vec<_>>().join(" "));
            Found::Instance(Witness::plain(value))
        }

        /// What is left, with the engine deciding what it is asked for until nothing is
        /// asked any more.
        fn left(&mut self, budget: &mut Budget) -> Result<Left, Exhausted> {
            loop {
                let found = &self.found;
                let mut ask = |of: CRefId| match of {
                    Terms::NOTHING => Some(Found::Nothing),
                    Terms::ANYTHING => Some(Found::Instance(Witness::plain(Value::Null))),
                    _ => found.get(&of).cloned(),
                };
                let mut solver = Solver {
                    terms: &mut self.terms,
                    languages: &mut self.languages,
                    budget,
                    partitions: &mut self.partitions,
                };
                let left = self.objects.left(&mut solver, &mut ask, true)?;
                let Left::Needs(wanted) = left else {
                    return Ok(left);
                };
                assert!(!wanted.is_empty());
                self.waited += 1;
                for of in wanted {
                    assert!(!self.found.contains_key(&of));
                    self.found.insert(of, self.decide(of));
                }
            }
        }

        /// The object that is given, or why none is.
        fn given(mut self) -> Result<Value, String> {
            match self.left(&mut Budget::new(u64::MAX)).unwrap() {
                Left::Value(Some(object)) => Ok(object.value.clone()),
                Left::Nothing => Err("nothing".to_owned()),
                Left::Unknown(cause) => Err(format!("{cause:?}")),
                other => panic!("{other:?} is no answer"),
            }
        }
    }

    fn none() -> Result<Value, String> {
        Err("nothing".to_owned())
    }

    #[test]
    fn without_anything_asked_the_empty_object_is_left() {
        assert_eq!(Asked::new().given(), Ok(json!({})));
        // As many properties as there have to be, with names that are made up.
        let three = Asked::new().count(3, None);
        assert_eq!(three.given(), Ok(json!({"a": null, "b": null, "c": null})));
        assert_eq!(
            Asked::new().count(1, Some(1)).given(),
            Ok(json!({"a": null}))
        );
        assert_eq!(Asked::new().count(2, Some(1)).given(), none());
    }

    #[test]
    fn a_property_that_there_has_to_be_satisfies_what_every_one_of_its_name_does() {
        let asked = Asked::new().every("=a", &[2]).some("=a", &[]);
        assert_eq!(asked.given(), Ok(json!({"a": "2"})));
        let asked = Asked::new()
            .every("=a", &[2])
            .every("=a,b", &[-3])
            .some("=a", &[4]);
        assert_eq!(asked.given(), Ok(json!({"a": "2 -3 4"})));
        // Without one that has to be there, the object has no property.
        assert_eq!(Asked::new().every("=a", &[2]).given(), Ok(json!({})));
        assert_eq!(Asked::new().every("=a", &[0]).given(), Ok(json!({})));
        // What no value satisfies, as the engine says or on the face of it.
        assert_eq!(
            Asked::new().every("=a", &[0]).some("=a", &[]).given(),
            none()
        );
        assert_eq!(
            Asked::new().every("=a", &[3]).some("=a", &[4]).given(),
            none()
        );
        let on_the_face_of_it = Asked::new().every("=a", &[2]).some("=a", &[-2]);
        assert!(on_the_face_of_it.objects.none);
        assert_eq!(on_the_face_of_it.given(), none());
        assert_eq!(Asked::new().none("=a").some("=a", &[]).given(), none());
        // What the engine does not know stands in the way.
        let unknown = Asked::new().every("=a", &[1]).some("=a", &[]);
        assert_eq!(unknown.given(), Err("Number".to_owned()));
    }

    #[test]
    fn a_property_goes_where_its_value_can_be() {
        // One of two names: the first is closed.
        let asked = Asked::new().none("=a").some("=a,b", &[2]);
        assert_eq!(asked.given(), Ok(json!({"b": "2"})));
        // A name that is made up, where no listed one will do.
        let asked = Asked::new()
            .every("=a", &[0])
            .every("=b", &[0])
            .some("!c", &[2]);
        assert_eq!(asked.given(), Ok(json!({"d": "2"})));
        // The names that are made up are told apart by the patterns.
        let asked = Asked::new()
            .every("^x", &[2])
            .every("y$", &[0])
            .some("^x", &[4]);
        assert_eq!(asked.given(), Ok(json!({"x": "2 4"})));
        let asked = Asked::new().every("^x", &[2]).every("^x.", &[0]);
        assert_eq!(asked.some("^x", &[4]).given(), Ok(json!({"x": "2 4"})));
        let asked = Asked::new().every("^x", &[2]).every("^x$", &[0]);
        assert_eq!(asked.some("^x", &[4]).given(), Ok(json!({"xa": "2 4"})));
        // A listed name that a pattern matches is asked what the pattern asks.
        let asked = Asked::new()
            .every("^x", &[2])
            .some("=xy", &[])
            .some("=y", &[]);
        assert_eq!(asked.given(), Ok(json!({"xy": "2", "y": null})));
        // No name is left.
        let asked = Asked::new().every("^x", &[0]).some("^xy", &[]);
        assert_eq!(asked.given(), none());
    }

    #[test]
    fn two_properties_share_a_name_only_where_they_have_to() {
        // Each has a name of its own.
        let apart = Asked::new().some("^x", &[3]).some("^x", &[4]);
        assert_eq!(apart.given(), Ok(json!({"x": "3", "xa": "4"})));
        // With room for one property, they are one, if a value can be both.
        let apart = Asked::new().some("^x", &[3]).some("^x", &[4]);
        assert_eq!(apart.count(0, Some(1)).given(), none());
        let together = Asked::new().some("^x", &[2]).some("^x", &[4]);
        assert_eq!(together.count(0, Some(1)).given(), Ok(json!({"x": "2 4"})));
        // Three for two names: the two that can be one are.
        let asked = Asked::new().some("^[xy]$", &[2]).some("^[xy]$", &[3]);
        let asked = asked.some("^[xy]$", &[4]);
        let given = asked.given().unwrap();
        let given = given.as_object().unwrap();
        assert_eq!(given.len(), 2);
        let mut values: Vec<&str> = given
            .values()
            .map(|value| value.as_str().unwrap())
            .collect();
        values.sort_unstable();
        assert!(
            values == ["2 3", "4"] || values == ["2 4", "3"],
            "{values:?}"
        );
        // Three that cannot share, for two names.
        let asked = Asked::new().some("^[xy]$", &[3]).some("^[xy]$", &[4]);
        assert_eq!(asked.some("^[xy]$", &[3, 4]).given(), none());
    }

    #[test]
    fn there_have_to_be_names_enough_for_the_least_number_of_properties() {
        // Every name but two is closed, and one of the two.
        let closed = || Asked::new().none("!a,b").every("=b", &[0]);
        assert_eq!(closed().count(1, None).given(), Ok(json!({"a": null})));
        assert_eq!(closed().count(2, None).given(), none());
        // The properties that have to be there count.
        let asked = Asked::new().none("!a,b").some("=a", &[2]).every("=b", &[4]);
        assert_eq!(
            asked.count(2, None).given(),
            Ok(json!({"a": "2", "b": "4"}))
        );
        // A pattern of a few words has that many names.
        let few = || Asked::new().every("^[xy]$", &[2]).none("(?s)^[^xy]|^..|^$");
        assert_eq!(
            few().count(2, None).given(),
            Ok(json!({"x": "2", "y": "2"}))
        );
        assert_eq!(few().count(3, None).given(), none());
        // Whether a name can be had may be what the engine does not know.
        let unknown = Asked::new().none("!a").every("=a", &[1]).count(1, None);
        assert_eq!(unknown.given(), Err("Number".to_owned()));
        // The empty name is made up only where no other is left.
        let empty = Asked::new().none("(?s)^.").count(1, None);
        assert_eq!(empty.given(), Ok(json!({"": null})));
    }

    #[test]
    fn the_engine_is_asked_once_for_everything_that_it_does_not_know() {
        let four = || {
            let mut asked = Asked::new();
            for name in ["=a", "=b", "=c", "=d"] {
                asked = asked.every(name, &[2]).some(name, &[4]);
            }
            asked
        };
        let mut asked = four();
        let mut budget = Budget::new(u64::MAX);
        assert!(matches!(asked.left(&mut budget), Ok(Left::Value(Some(_)))));
        // One c-reference for the four, asked for in one go.
        assert_eq!((asked.waited, asked.found.len()), (1, 1));
        // The search costs steps, and the partition is made once.
        let spent = budget.spent();
        assert!(spent > 8, "{spent}");
        assert!(matches!(asked.left(&mut budget), Ok(Left::Value(Some(_)))));
        assert_eq!(asked.partitions.of.len(), 1);
        assert_eq!(four().left(&mut Budget::new(spent)).map(|_| ()), Ok(()));
        assert_eq!(
            four().left(&mut Budget::new(spent - 1)).map(|_| ()),
            Err(Exhausted)
        );
    }
}
