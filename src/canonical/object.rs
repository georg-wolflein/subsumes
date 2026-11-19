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

use std::collections::BTreeSet;
use std::ops::Range;
use std::rc::Rc;

use super::search::{self, Place, Placed, Places, Slot};
use super::{Left, Solver, State, add, state};
use crate::context::{Budget, Exhausted};
use crate::hash::Map;
use crate::language::{LanguageId, Languages, Lengths, Shape};
use crate::normalize::{Cause, DEEPEST, Found, Witness};
use crate::term::{CRefId, Term, Terms};

/// The objects that a branch still accepts.
///
/// A copy shares the two sets with what it was copied from, and each is copied when one of
/// the two first adds to it. An alternative of a split adds to one of them at most before it
/// is refuted, more often than not.
#[derive(Debug, Clone, Default)]
pub(crate) struct Objects {
    /// What the value of every property with a name of a language satisfies.
    every: Rc<BTreeSet<(LanguageId, CRefId)>>,
    /// The properties that there have to be: each with a name of a language and a value
    /// that satisfies something.
    some: Rc<BTreeSet<(LanguageId, CRefId)>>,
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
        add(&mut self.every, (names, of));
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
        add(&mut self.some, (names, of));
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
        // The lists of the search are those of the search before, which keeps their memory.
        let mut work = std::mem::take(&mut with.partitions.work);
        let (every, some) = (self.every.iter(), self.some.iter());
        merge(
            every.map(|of| of.0),
            some.map(|of| of.0),
            &mut work.languages,
        );
        let partition = with
            .partitions
            .of(&work.languages, with.languages, with.budget)?;

        // What every property of a fragment satisfies.
        let every = &mut work.every;
        every.clear();
        every.resize(partition.fragments.len(), Terms::ANYTHING);
        let mut from = 0;
        for (names, of) in &*self.every {
            let held = partition.within(*names, &mut from);
            with.budget.charge(1 + (held.len() / 8) as u64)?;
            for fragment in held {
                let all = &mut every[*fragment as usize];
                *all = with.terms.both(*all, *of);
            }
        }
        // The properties that there have to be, each with the fragments that it may be in:
        // those of its language whose properties can have a value at all. An object that
        // takes no property but those that it names leaves few of them, and a property
        // that is left with none leaves no object.
        let (open, some) = (&mut work.open, &mut work.some);
        open.clear();
        some.clear();
        let mut from = 0;
        for (names, of) in &*self.some {
            let held = partition.within(*names, &mut from);
            with.budget.charge((held.len() / 8) as u64)?;
            let before = open.len();
            let takes_a_value = |fragment: &&u32| every[**fragment as usize] != Terms::NOTHING;
            open.extend(held.iter().filter(takes_a_value));
            if open.len() == before {
                with.partitions.work = work;
                return Ok(Left::Nothing);
            }
            some.push((held.len(), before..open.len(), *of));
        }
        // Those first whose language holds the fewest fragments.
        some.sort_by_key(|(held, _, _)| *held);
        let used = &mut work.used;
        used.truncate(partition.fragments.len());
        used.iter_mut().for_each(Vec::clear);
        used.resize_with(partition.fragments.len(), Vec::new);

        let search = Search {
            objects: self,
            partition: &partition,
            every: &work.every,
            open: &work.open,
            some: &work.some,
            used: &mut work.used,
        };
        let left = search::run(search, with, ask, give, &mut work.search);
        with.partitions.work = work;
        left
    }
}

/// The names of all properties, cut into fragments by a list of languages.
#[derive(Debug)]
pub(crate) struct Partition {
    /// The names that a language lists, in order. Each is a fragment of its own.
    names: Vec<Box<str>>,
    /// The fragments: first those of one name each, in the order of the names, then the
    /// others.
    fragments: Vec<Fragment>,
    /// How many of them are of one name each.
    named: usize,
    /// The languages of the list, each with where the fragments that it holds are in
    /// `held`, in order.
    within: Vec<(LanguageId, Range<usize>)>,
    held: Vec<u32>,
}

impl Partition {
    /// The fragments that a language of the list holds, in order. The languages are asked
    /// in order, from where the one before was found, so the list is gone through once.
    fn within(&self, language: LanguageId, from: &mut usize) -> &[u32] {
        while self.within[*from].0 < language {
            *from += 1;
        }
        let (of, held) = &self.within[*from];
        debug_assert_eq!(*of, language, "the language is one of the list");
        &self.held[held.clone()]
    }
}

#[derive(Debug)]
struct Fragment {
    names: Names,
    /// How many names it has, or `None` if there is no end of them.
    size: Option<u64>,
}

#[derive(Debug)]
enum Names {
    /// The name of the same number.
    One,
    /// The names of a language, but for a few of them that are fragments of their own,
    /// each by its number.
    Of { language: LanguageId, but: Vec<u32> },
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
    of: Map<Box<[LanguageId]>, Rc<Partition>>,
    rests: Map<Box<[LanguageId]>, Rc<[Rest]>>,
    /// The lists that the search for an object is put together in. A search leaves them
    /// to the next, which clears them and keeps their memory.
    work: Work,
}

/// The lists of a search for an object.
#[derive(Debug, Default)]
struct Work {
    /// The languages that the object is asked about, in order.
    languages: Vec<LanguageId>,
    /// What every property of each fragment satisfies.
    every: Vec<CRefId>,
    /// The fragments that the properties that there have to be may be in, one after the
    /// other.
    open: Vec<u32>,
    /// The properties that there have to be: how many fragments their language holds,
    /// where their fragments are in `open`, and what their value satisfies.
    some: Vec<(usize, Range<usize>, CRefId)>,
    /// The slots of each fragment.
    used: Vec<Vec<usize>>,
    /// The lists of the search itself.
    search: search::Work<u32>,
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
        let mut made_of: Vec<LanguageId> = Vec::with_capacity(asked.len());
        for language in asked {
            match languages.shape(*language) {
                Shape::Outside(of) => made_of.extend_from_slice(of),
                _ => made_of.push(*language),
            }
        }
        made_of.sort_unstable();
        made_of.dedup();
        // Every word that a set of words lists is a name of its own. Every other language
        // is a pattern here. A name that several sets list is copied once.
        let mut patterns: Vec<LanguageId> = Vec::new();
        let mut listed: Vec<&str> = Vec::new();
        for language in &made_of {
            match languages.shape(*language) {
                Shape::Words { words, .. } => listed.extend(words.iter().map(AsRef::as_ref)),
                Shape::Outside(_) | Shape::Other => patterns.push(*language),
            }
        }
        listed.sort_unstable();
        listed.dedup();
        let names: Vec<Box<str>> = listed.into_iter().map(Box::from).collect();
        // Whether each name is in each pattern: a row of the patterns for each name.
        let mut matched: Vec<bool> = Vec::with_capacity(names.len() * patterns.len());
        for name in &names {
            for pattern in &patterns {
                matched.push(languages.contains(*pattern, name, budget)?);
            }
        }
        let row = |name: usize| &matched[name * patterns.len()..(name + 1) * patterns.len()];

        let named = names.len();
        let mut fragments: Vec<Fragment> = Vec::with_capacity(named + 1);
        fragments.extend((0..named).map(|_| Fragment {
            names: Names::One,
            size: Some(1),
        }));
        let rests = self.rests(&patterns, languages, budget)?;
        let mut kept: Vec<&Rest> = Vec::with_capacity(rests.len());
        for rest in rests.iter() {
            // The names that are fragments of their own are not of this one.
            let but: Vec<u32> = (0..named)
                .filter(|name| row(*name) == &*rest.within)
                .map(number)
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

        // The fragments that one of the languages that the list is made of holds are marked.
        // The names are in order, and the patterns too.
        let index = |word: &str| {
            let found = names.binary_search_by(|name| (**name).cmp(word));
            found.expect("every word that is listed is a name")
        };
        let place = |pattern: LanguageId| {
            let found = patterns.binary_search(&pattern);
            found.expect("every language that lists no words is a pattern")
        };
        let mark = |languages: &Languages, language: LanguageId, marks: &mut [bool]| {
            let (of_names, of_rests) = marks.split_at_mut(named);
            match languages.shape(language) {
                Shape::Words {
                    words,
                    others: false,
                } => {
                    for word in words {
                        of_names[index(word)] = true;
                    }
                }
                Shape::Words {
                    words,
                    others: true,
                } => {
                    for (name, marked) in names.iter().zip(of_names) {
                        *marked |= !words.contains(name);
                    }
                    of_rests.fill(true);
                }
                Shape::Outside(_) | Shape::Other => {
                    let at = place(language);
                    for (name, marked) in of_names.iter_mut().enumerate() {
                        *marked |= row(name)[at];
                    }
                    for (rest, marked) in kept.iter().zip(of_rests) {
                        *marked |= rest.within[at];
                    }
                }
            }
        };
        let mut marks = vec![false; fragments.len()];
        let mut within = Vec::with_capacity(asked.len());
        let mut held: Vec<u32> = Vec::new();
        for language in asked {
            let from = held.len();
            match languages.shape(*language) {
                // A few words are found by their names.
                Shape::Words {
                    words,
                    others: false,
                } => held.extend(words.iter().map(|word| number(index(word)))),
                Shape::Outside(of) => {
                    budget.charge(1 + (fragments.len() / 8) as u64)?;
                    marks.fill(false);
                    for one in of {
                        mark(languages, *one, &mut marks);
                    }
                    let outside = marks.iter().enumerate().filter(|(_, marked)| !**marked);
                    held.extend(outside.map(|(fragment, _)| number(fragment)));
                }
                _ => {
                    budget.charge(1 + (fragments.len() / 8) as u64)?;
                    marks.fill(false);
                    mark(languages, *language, &mut marks);
                    let inside = marks.iter().enumerate().filter(|(_, marked)| **marked);
                    held.extend(inside.map(|(fragment, _)| number(fragment)));
                }
            }
            within.push((*language, from..held.len()));
        }
        let partition = Rc::new(Partition {
            names,
            fragments,
            named,
            within,
            held,
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
        let rests = languages.cut(patterns, budget)?;
        let rests = rests
            .into_iter()
            .map(|(names, within)| Rest { names, within });
        let rests: Rc<[Rest]> = rests.collect();
        self.rests.insert(patterns.into(), Rc::clone(&rests));
        Ok(rests)
    }
}

/// Puts what two lists in order hold into a third, in order and each once.
fn merge<T: Ord + Copy>(
    one: impl Iterator<Item = T>,
    other: impl Iterator<Item = T>,
    all: &mut Vec<T>,
) {
    all.clear();
    let (mut one, mut other) = (one.peekable(), other.peekable());
    loop {
        let next = match (one.peek(), other.peek()) {
            (Some(first), Some(second)) if second < first => other.next(),
            (Some(_), _) => one.next(),
            (None, _) => other.next(),
        };
        let Some(next) = next else {
            return;
        };
        if all.last() != Some(&next) {
            all.push(next);
        }
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
    /// The properties that there have to be: where the fragments that each may be in are
    /// in `open`, and what its value satisfies.
    open: &'s [u32],
    some: &'s [(usize, Range<usize>, CRefId)],
    /// The slots of each fragment.
    used: &'s mut [Vec<usize>],
}

impl Places for Search<'_> {
    type At = u32;

    fn asked(&self, which: usize) -> Option<CRefId> {
        self.some.get(which).map(|(_, _, of)| *of)
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
    fn places(&self, placed: &Placed<u32>, which: usize, places: &mut Vec<Place<u32>>) {
        let fragments = &self.open[self.some[which].1.clone()];
        let most = self.objects.max;
        let room = most.is_none_or(|most| (placed.slots.len() as u64) < most);
        // The fragments that are not of one name come last and are tried first: what their
        // properties satisfy is the least.
        let fragments = fragments.iter().map(|fragment| {
            let size = self.partition.fragments[*fragment as usize].size;
            (*fragment, size, &self.used[*fragment as usize])
        });
        let fragments = fragments.rev();
        // A new property is asked no more than one that is shared. So sharing is tried only
        // where a fragment may run out of names or the object out of properties.
        let join = |places: &mut Vec<Place<u32>>| {
            let shared = fragments
                .clone()
                .filter(|(_, size, _)| most.is_some() || size.is_some());
            for (_, _, used) in shared {
                places.extend(used.iter().map(|slot| Place::Join(*slot)));
            }
        };
        let open = |places: &mut Vec<Place<u32>>| {
            let more = |(_, size, used): &(u32, Option<u64>, &Vec<usize>)| {
                room && size.is_none_or(|size| (used.len() as u64) < size)
            };
            places.extend(
                fragments
                    .clone()
                    .filter(more)
                    .map(|(at, ..)| Place::Open(at)),
            );
        };
        // With a most, the fewest properties first.
        if most.is_some() {
            join(places);
            open(places);
        } else {
            open(places);
            join(places);
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
            *with.too_deep = true;
            placed.depends.get_or_insert(Cause::Depth);
            return Ok(None);
        }
        if !give {
            return Ok(Some(Left::Value(None)));
        }
        let object = self.given(&placed.slots, with, &more)?;
        Ok(Some(Left::Value(Some(object))))
    }
}

impl Search<'_> {
    /// The object: a name and a value for each slot, and for each property that was added
    /// to have enough.
    ///
    /// A value costs no step here: it is shared and not copied. A fragment of one name
    /// gives one property at most, which cost a step when it was placed or when the
    /// fragment was looked at, and every other name costs steps to make up. So the budget
    /// covers each property that is added.
    fn given(
        &self,
        slots: &[Slot<u32>],
        with: &mut Solver,
        more: &[(usize, u64, Rc<Witness>)],
    ) -> Result<Rc<Witness>, Exhausted> {
        let filled = slots.iter().map(|slot| {
            let value = slot.value.as_ref().expect("every slot has a value");
            (slot.at as usize, 1, value)
        });
        let added = more
            .iter()
            .map(|(fragment, count, value)| (*fragment, *count, value));
        let mut properties = Vec::new();
        // The names that were made up for each fragment of more than one name.
        let mut made_up: Map<usize, Vec<String>> = Map::default();
        for (fragment, count, value) in filled.chain(added) {
            for _ in 0..count {
                let name = match &self.partition.fragments[fragment].names {
                    Names::One => self.partition.names[fragment].to_string(),
                    Names::Of { language, but } => {
                        let before = made_up.entry(fragment).or_default();
                        let but = but
                            .iter()
                            .map(|name| &*self.partition.names[*name as usize]);
                        let name = new_name(*language, but, before, with)?;
                        before.push(name.clone());
                        name
                    }
                };
                properties.push((name, Rc::clone(value)));
            }
        }
        Ok(Witness::object(properties))
    }
}

/// A name of a language that is none of those left out and none of those made up before:
/// the shortest that is not empty, and of several one of plain characters.
fn new_name<'n>(
    language: LanguageId,
    but: impl Iterator<Item = &'n str>,
    before: &'n [String],
    with: &mut Solver,
) -> Result<String, Exhausted> {
    with.budget.charge(1 + before.len() as u64)?;
    let left_out = but.chain(before.iter().map(String::as_str));
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
    use serde_json::{Value, json};

    use super::*;
    use crate::canonical::made_up::{Engine, given, none};

    /// What is asked of the objects of a branch, with an engine that is made up.
    struct Asked {
        engine: Engine,
        objects: Objects,
    }

    impl Asked {
        fn new() -> Self {
            Self {
                engine: Engine::new(),
                objects: Objects::default(),
            }
        }

        /// The language of a pattern, or with `=` in front of a few words, or with `!`
        /// of every string but a few words.
        fn names(&mut self, names: &str) -> LanguageId {
            let languages = &mut self.engine.languages;
            if let Some(words) = names.strip_prefix('=') {
                return languages.words(words.split(','));
            }
            if let Some(words) = names.strip_prefix('!') {
                let words = languages.words(words.split(','));
                return languages.outside([words]);
            }
            languages.pattern(names).unwrap()
        }

        /// Every property with such a name satisfies these.
        fn every(mut self, names: &str, variables: &[i32]) -> Self {
            let (names, of) = (self.names(names), self.engine.of(variables));
            self.objects.every(names, of, &mut self.engine.terms);
            self
        }

        /// No property has such a name.
        fn none(mut self, names: &str) -> Self {
            let names = self.names(names);
            let terms = &mut self.engine.terms;
            self.objects.every(names, Terms::NOTHING, terms);
            self
        }

        /// Some property with such a name satisfies these.
        fn some(mut self, names: &str, variables: &[i32]) -> Self {
            let (names, of) = (self.names(names), self.engine.of(variables));
            self.objects.some(names, of, &mut self.engine.terms);
            self
        }

        fn count(mut self, min: u64, max: Option<u64>) -> Self {
            (self.objects.min, self.objects.max) = (min, max);
            self
        }

        /// What is left, with the engine deciding what it is asked for.
        fn left(&mut self, budget: &mut Budget) -> Result<Left, Exhausted> {
            let objects = &self.objects;
            self.engine
                .left(budget, |with, ask| objects.left(with, ask, true))
        }

        /// The object that is given, or why none is.
        fn given(mut self) -> Result<Value, String> {
            given(self.left(&mut Budget::new(u64::MAX)).unwrap())
        }
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
        assert_eq!((asked.engine.waited, asked.engine.found.len()), (1, 1));
        // The partition is made once.
        assert!(matches!(asked.left(&mut budget), Ok(Left::Value(Some(_)))));
        assert_eq!(asked.engine.partitions.of.len(), 1);
        // The search costs steps.
        let left = four().left(&mut Budget::new(0));
        assert_eq!(left.map(|_| ()), Err(Exhausted));
    }

    #[test]
    fn a_search_leaves_nothing_to_the_next() {
        // The searches of a check are made with the lists of the one before. Each finds
        // what it finds with lists of its own: the largest comes first, then one that
        // ends before the search, one in which properties share a name, and one of no
        // property at all.
        let asks: [fn(Asked) -> Asked; 5] = [
            |asked| {
                let asked = asked.every("=a,b", &[2]).every("!a,b", &[5]);
                asked.some("=a", &[3]).some("=b", &[-3]).some("[0-9]", &[4])
            },
            |asked| asked.none("!a").some("=b", &[2]),
            |asked| asked.count(2, Some(2)).some("=a", &[2]).some("=a,b", &[-3]),
            |asked| asked.some("=a", &[3]).some("=a", &[4]),
            |asked| asked,
        ];
        let mut asked = Asked::new();
        for ask in asks {
            let alone = ask(Asked::new()).given();
            asked.objects = Objects::default();
            asked = ask(asked);
            let left = asked.left(&mut Budget::new(u64::MAX)).unwrap();
            assert_eq!(given(left), alone);
        }
    }

    #[test]
    fn two_lists_in_order_are_merged_in_order() {
        let mut all = vec![9];
        merge([1, 3, 3, 5].into_iter(), [2, 3, 6].into_iter(), &mut all);
        assert_eq!(all, [1, 2, 3, 5, 6]);
        merge([].into_iter(), [4, 4].into_iter(), &mut all);
        assert_eq!(all, [4]);
        merge([7].into_iter(), [].into_iter(), &mut all);
        assert_eq!(all, [7]);
    }
}
