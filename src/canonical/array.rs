//! What a branch says about arrays.
//!
//! A term about arrays asks one of a few things of an array: that the item at a position, if
//! there is one, is a value that a schema accepts, that every item from a position on is
//! such a value, that some item is, or that there are at least or at most so many items.
//! Negated, the first asks for an item at that position that the schema does not accept, the
//! second for such an item from that position on, and the third that the schema accepts no
//! item at all. So what a branch takes in comes down to three things:
//!
//! - what the item at each position satisfies: one c-reference for each of the first
//!   positions, the *head*, and one for every position after them, the *tail*,
//! - *some* item that there has to be, at a position or after it, with a value that
//!   satisfies something,
//! - and two bounds on the number of items.
//!
//! What a value satisfies is a [c-reference](CRefId): schemas by name, never written out.
//!
//! # Is an array left?
//!
//! An array has no gaps: with an item at a position, it has one at every position before.
//! So it ends before the first position whose item can have no value at all.
//!
//! An array is left when each item that there has to be finds a position: one at or after
//! its own and before that end, whose value satisfies what the position asks and what this
//! item is asked besides. Two of them may share a position, and then the value satisfies
//! both. Within the head they share wherever both are put at one position. After the head
//! every position asks the same, so there each gets a position of its own, where it is
//! asked the least, and they share only if the array may not have that many items. And there
//! have to be items enough for the least number, each with a value.
//!
//! Whether a value can satisfy a c-reference is not decided here. The engine is asked, and
//! what it does not know yet it is told to find out first.

use std::borrow::Cow;
use std::collections::BTreeSet;
use std::rc::Rc;

use serde_json::Value;

use super::search::{self, Place, Placed, Places, Slot};
use super::{Left, Solver, State, state};
use crate::context::{Budget, Exhausted};
use crate::normalize::{Cause, DEEPEST, Found, Witness};
use crate::term::{CRefId, Term, Terms};

/// The arrays that a branch still accepts.
#[derive(Debug, Clone)]
pub(crate) struct Arrays {
    /// What the item at each of the first positions satisfies.
    head: Vec<CRefId>,
    /// What the item at every position after those satisfies.
    tail: CRefId,
    /// The items that there have to be: each at this position or after it, with a value
    /// that satisfies something.
    some: BTreeSet<(u64, CRefId)>,
    /// The least number of items, and the most if there is a most.
    min: u64,
    max: Option<u64>,
    /// Whether what was asked leaves no array on the face of it.
    none: bool,
}

impl Default for Arrays {
    fn default() -> Self {
        Self {
            head: Vec::new(),
            tail: Terms::ANYTHING,
            some: BTreeSet::new(),
            min: 0,
            max: None,
            none: false,
        }
    }
}

/// A position of the head, which is one that a schema names.
fn index(position: u64) -> usize {
    usize::try_from(position).expect("a schema names fewer positions than memory holds")
}

impl Arrays {
    /// Takes in what a term about arrays asks of an array, as it stands or negated.
    pub fn take(&mut self, term: &Term, negated: bool, terms: &mut Terms) {
        match (term, negated) {
            (Term::Item(position, variable), false) => {
                let of = terms.literal(*variable, false);
                self.at(*position, of, terms);
            }
            // There is an item at the position, and the schema does not accept it.
            (Term::Item(position, variable), true) => {
                let of = terms.literal(*variable, true);
                self.at(*position, of, terms);
                self.min = self.min.max(position.saturating_add(1));
            }
            (Term::AddIts(from, variable), false) => {
                let of = terms.literal(*variable, false);
                self.from(*from, of, terms);
            }
            // Some item from the position on is one that the schema does not accept.
            (Term::AddIts(from, variable), true) => {
                let of = terms.literal(*variable, true);
                self.some(*from, of);
            }
            (Term::Contains(variable), false) => {
                let of = terms.literal(*variable, false);
                self.some(0, of);
            }
            // No item is one that the schema accepts.
            (Term::Contains(variable), true) => {
                let of = terms.literal(*variable, true);
                self.from(0, of, terms);
            }
            (Term::MinIts(least), false) => self.min = self.min.max(*least),
            // Fewer than the least.
            (Term::MinIts(least), true) => match least.checked_sub(1) {
                Some(most) => self.at_most(most),
                None => self.none = true,
            },
            (Term::MaxIts(most), false) => self.at_most(*most),
            // More than the most. Beyond the largest count this asks for one item less than
            // it should, which lets arrays in and none out.
            (Term::MaxIts(most), true) => self.min = self.min.max(most.saturating_add(1)),
            (other, _) => unreachable!("{other:?} is not about arrays"),
        }
    }

    /// The item at a position satisfies this, if there is one.
    fn at(&mut self, position: u64, of: CRefId, terms: &mut Terms) {
        let position = index(position);
        if self.head.len() <= position {
            self.head.resize(position + 1, self.tail);
        }
        self.head[position] = terms.both(self.head[position], of);
    }

    /// Every item from a position on satisfies this.
    fn from(&mut self, from: u64, of: CRefId, terms: &mut Terms) {
        let from = index(from);
        if self.head.len() < from {
            self.head.resize(from, self.tail);
        }
        for item in &mut self.head[from..] {
            *item = terms.both(*item, of);
        }
        self.tail = terms.both(self.tail, of);
    }

    /// Some item at a position or after it satisfies this.
    fn some(&mut self, from: u64, of: CRefId) {
        match of {
            Terms::NOTHING => self.none = true,
            // Any value will do, so there only has to be an item.
            Terms::ANYTHING => self.min = self.min.max(from.saturating_add(1)),
            _ => {
                self.some.insert((from, of));
            }
        }
    }

    fn at_most(&mut self, most: u64) {
        self.max = Some(self.max.map_or(most, |max| max.min(most)));
    }

    /// How much there is to copy when the branch splits, and to look at when a term about
    /// every item from a position on is taken in.
    pub fn weight(&self) -> u64 {
        (self.head.len() + self.some.len()) as u64
    }

    /// Whether an array is left, and with `give` such an array.
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
        // The head, as far as the last position that an item has to be at or after. So
        // every position after the head will do for every such item.
        let last = self.some.last().map_or(0, |(from, _)| index(*from));
        with.budget
            .charge(1 + (self.head.len().max(last) / 8) as u64)?;
        let mut head = Cow::Borrowed(self.head.as_slice());
        if head.len() < last {
            head.to_mut().resize(last, self.tail);
        }
        // The items that there have to be, those first that have the fewest positions to
        // be at.
        let some = self.some.iter().rev();
        let some: Vec<(usize, CRefId)> = some.map(|(from, of)| (index(*from), *of)).collect();
        let search = Search {
            arrays: self,
            head: &head,
            some: &some,
            at_head: vec![None; head.len()],
            after: Vec::new(),
            looked: 0,
            end: None,
        };
        search::run(search, with, ask, give)
    }
}

/// The search for an array: a position for every item that there has to be. A slot is an
/// item of which more is asked than its position asks.
struct Search<'s> {
    arrays: &'s Arrays,
    /// What the item at each position of the head satisfies.
    head: &'s [CRefId],
    /// The items that there have to be: the first position that each may be at, and what
    /// its value satisfies.
    some: &'s [(usize, CRefId)],
    /// The slot of each position of the head that has one.
    at_head: Vec<Option<usize>>,
    /// The slots after the head. They are at the positions right after it, in this order.
    after: Vec<usize>,
    /// How many of the first positions were looked at and found to ask nothing that no
    /// value satisfies. The positions after the head count as one.
    looked: u64,
    /// The first position whose item can have no value, once it is found: an array ends
    /// before it.
    end: Option<u64>,
}

impl Places for Search<'_> {
    type At = u64;

    fn asked(&self, which: usize) -> Option<CRefId> {
        self.some.get(which).map(|(_, of)| *of)
    }

    /// What the item at a position satisfies by its position alone.
    fn at(&self, position: u64) -> CRefId {
        let of_the_head = usize::try_from(position).ok();
        let of_the_head = of_the_head.and_then(|position| self.head.get(position));
        of_the_head.copied().unwrap_or(self.arrays.tail)
    }

    /// The array has to get as far as the position, and not end at it.
    fn reaches(
        &mut self,
        position: u64,
        placed: &mut Placed<u64>,
        with: &mut Solver,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    ) -> Result<bool, Exhausted> {
        self.look(position, &mut placed.wanted, with.budget, ask)?;
        Ok(self.end.is_none_or(|end| position < end))
    }

    fn open(&mut self, position: u64, slot: usize) {
        match self.at_head.get_mut(index(position)) {
            Some(at) => *at = Some(slot),
            None => self.after.push(slot),
        }
    }

    fn close(&mut self, position: u64) {
        match self.at_head.get_mut(index(position)) {
            Some(at) => *at = None,
            None => {
                self.after.pop();
            }
        }
    }

    /// Where one of the items that there have to be may go.
    fn places(&self, _: &Placed<u64>, which: usize) -> Vec<Place<u64>> {
        let (from, _) = self.some[which];
        let head = self.head.len();
        // No position at which the array has ended, and none that it may not get to.
        let most = self.arrays.max.unwrap_or(u64::MAX);
        let before = self.end.map_or(most, |end| end.min(most));
        let mut places = Vec::new();
        // The first positions first, which makes the shortest array.
        for position in from..head {
            if position as u64 >= before {
                break;
            }
            places.push(match self.at_head[position] {
                Some(slot) => Place::Join(slot),
                None => Place::Open(position as u64),
            });
        }
        // After the head, an item with a position of its own is asked no more than one that
        // shares. So sharing is tried only where the array may run out of positions.
        let next = (head + self.after.len()) as u64;
        if next < before {
            places.push(Place::Open(next));
        }
        if self.arrays.max.is_some() {
            places.extend(self.after.iter().map(|slot| Place::Join(*slot)));
        }
        places
    }

    /// With a place for every item that there has to be: whether the array has items
    /// enough, and a value for each item at a position before the last of them.
    ///
    /// `None` if this array is none, or one only as far as the engine knows, which is
    /// noted.
    fn fill(
        &mut self,
        placed: &mut Placed<u64>,
        with: &mut Solver,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
        give: bool,
    ) -> Result<Option<Left>, Exhausted> {
        let budget = &mut *with.budget;
        let min = self.arrays.min;
        let last = placed.slots.iter().map(|slot| slot.at + 1).max();
        let length = min.max(last.unwrap_or(0));
        self.look(length, &mut placed.wanted, budget, ask)?;
        if let Some(end) = self.end.filter(|end| *end < length) {
            // However the items that there have to be are placed, the array ends where it
            // ends. So without items enough here, there is no array.
            return Ok((end < min).then_some(Left::Nothing));
        }
        let in_the_way = |slot: &Slot<u64>| slot.value.as_ref().err().copied().flatten();
        let mut cause = placed.slots.iter().find_map(in_the_way);
        // The items of which no more is asked than their positions ask: those of the head,
        // in order, and one value for all that come after it.
        let head = self.head.len() as u64;
        let mut plain: Vec<Rc<Witness>> = Vec::new();
        for position in 0..index(length.min(head)) {
            if self.at_head[position].is_some() {
                continue;
            }
            budget.charge(1)?;
            match state(self.head[position], ask, &mut placed.wanted) {
                State::Nothing => unreachable!("the array ends before such a position"),
                State::Possible(why) => {
                    cause.get_or_insert(why);
                }
                State::Sure(witness) => plain.push(witness),
                State::Wanted => {}
            }
        }
        let mut rest = None;
        if length > head + self.after.len() as u64 {
            match state(self.arrays.tail, ask, &mut placed.wanted) {
                State::Nothing => unreachable!("the array ends before such a position"),
                State::Possible(why) => {
                    cause.get_or_insert(why);
                }
                State::Sure(witness) => rest = Some(witness),
                State::Wanted => {}
            }
        }
        if !placed.wanted.is_empty() {
            return Ok(Some(Left::Needs(std::mem::take(&mut placed.wanted))));
        }
        if let Some(cause) = cause {
            placed.depends.get_or_insert(cause);
            return Ok(None);
        }
        // An array is one level deeper than the deepest of its items. One that would be too
        // deep to give is passed over for another.
        let of_slots = placed
            .slots
            .iter()
            .filter_map(|slot| slot.value.as_ref().ok());
        let values = of_slots.chain(&plain).chain(&rest);
        let deepest = values.map(|value| value.depth).max().unwrap_or(0);
        if deepest >= DEEPEST {
            placed.depends.get_or_insert(Cause::Depth);
            return Ok(None);
        }
        if !give {
            return Ok(Some(Left::Value(None)));
        }
        let rest = rest.as_ref();
        let array = self.given(&placed.slots, budget, length, &plain, rest, deepest + 1)?;
        Ok(Some(Left::Value(Some(array))))
    }
}

impl Search<'_> {
    /// Looks at what the first so many positions ask, as far as the first of them that
    /// asks what no value satisfies: the array ends before that one.
    fn look(
        &mut self,
        length: u64,
        wanted: &mut Vec<CRefId>,
        budget: &mut Budget,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    ) -> Result<(), Exhausted> {
        // Every position after the head asks the same, so the first of them stands for all.
        let apart = self.head.len() as u64 + 1;
        while self.end.is_none() && self.looked < length.min(apart) {
            budget.charge(1)?;
            let of = self.at(self.looked);
            if matches!(state(of, ask, wanted), State::Nothing) {
                self.end = Some(self.looked);
            } else {
                self.looked += 1;
            }
        }
        Ok(())
    }

    /// The array: the value of the slot at each position that has one, and at every other
    /// position a value that satisfies what the position asks. `depth` is how deep it is.
    fn given(
        &self,
        slots: &[Slot<u64>],
        budget: &mut Budget,
        length: u64,
        plain: &[Rc<Witness>],
        rest: Option<&Rc<Witness>>,
        depth: u32,
    ) -> Result<Rc<Witness>, Exhausted> {
        let of_slot = |slot: &usize| {
            let value = slots[*slot].value.as_ref();
            value.expect("every slot has a value")
        };
        let head = self.head.len() as u64;
        let mut plain = plain.iter();
        let mut items = Vec::new();
        let mut size = 1_u64;
        for position in 0..length {
            let value = if position < head {
                let slot = self.at_head[index(position)].as_ref();
                slot.map(of_slot).or_else(|| plain.next())
            } else {
                let slot = self.after.get(index(position - head));
                slot.map(of_slot).or(rest)
            };
            let value = value.expect("every item of the array has a value");
            // A step for everything that is copied.
            budget.charge(value.size)?;
            size = size.saturating_add(value.size);
            items.push(value.value.clone());
        }
        Ok(Rc::new(Witness {
            value: Value::Array(items),
            size,
            depth,
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use serde_json::json;

    use super::*;
    use crate::canonical::object::Partitions;
    use crate::language::Languages;
    use crate::schema::NodeId;
    use crate::term::{InstanceType, TypeSet, VarId};

    /// What is asked of the arrays of a branch, with an engine that is made up.
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
        arrays: Arrays,
        found: HashMap<CRefId, Found>,
        /// The c-references that the engine was told to find out about.
        decided: Vec<CRefId>,
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
                arrays: Arrays::default(),
                found: HashMap::new(),
                decided: Vec::new(),
            }
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

        /// The item at a position satisfies these.
        fn at(mut self, position: u64, variables: &[i32]) -> Self {
            let of = self.of(variables);
            self.arrays.at(position, of, &mut self.terms);
            self
        }

        /// Every item from a position on satisfies these.
        fn from(mut self, from: u64, variables: &[i32]) -> Self {
            let of = self.of(variables);
            self.arrays.from(from, of, &mut self.terms);
            self
        }

        /// Some item at a position or after it satisfies these.
        fn some(mut self, from: u64, variables: &[i32]) -> Self {
            let of = self.of(variables);
            self.arrays.some(from, of);
            self
        }

        fn count(mut self, min: u64, max: Option<u64>) -> Self {
            (self.arrays.min, self.arrays.max) = (min, max);
            self
        }

        /// A term as it stands, or with a variable below zero the term negated. The
        /// variable of a term that has none is 2 or -2.
        fn term(mut self, variable: i32, term: impl Fn(VarId) -> Term) -> Self {
            let term = term(self.variables[variable.unsigned_abs() as usize]);
            self.arrays.take(&term, variable < 0, &mut self.terms);
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
                let left = self.arrays.left(&mut solver, &mut ask, true)?;
                let Left::Needs(wanted) = left else {
                    return Ok(left);
                };
                assert!(!wanted.is_empty());
                for of in wanted {
                    assert!(!self.found.contains_key(&of));
                    self.found.insert(of, self.decide(of));
                    self.decided.push(of);
                }
            }
        }

        /// The array that is given, or why none is.
        fn given(mut self) -> Result<Value, String> {
            match self.left(&mut Budget::new(u64::MAX)).unwrap() {
                Left::Value(Some(array)) => Ok(array.value.clone()),
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
    fn without_anything_asked_the_empty_array_is_left() {
        assert_eq!(Asked::new().given(), Ok(json!([])));
        // As many items as there have to be.
        let three = Asked::new().count(3, None);
        assert_eq!(three.given(), Ok(json!([null, null, null])));
        assert_eq!(Asked::new().count(1, Some(1)).given(), Ok(json!([null])));
        assert_eq!(Asked::new().count(2, Some(1)).given(), none());
    }

    #[test]
    fn an_item_satisfies_what_its_position_asks() {
        // Without an item at the position, nothing is asked.
        assert_eq!(Asked::new().at(0, &[2]).given(), Ok(json!([])));
        let first = Asked::new().at(0, &[2]).at(0, &[5]).count(2, None);
        assert_eq!(first.given(), Ok(json!(["2 5", null])));
        let second = Asked::new().at(1, &[2]).count(3, None);
        assert_eq!(second.given(), Ok(json!([null, "2", null])));
        // Every item from a position on, also those that the head has got to before and
        // those that it gets to after.
        let all = Asked::new().at(1, &[2]).from(0, &[5]).at(2, &[4]);
        assert_eq!(
            all.count(4, None).given(),
            Ok(json!(["5", "2 5", "4 5", "5"]))
        );
        let later = Asked::new().from(2, &[5]).from(1, &[2]).count(4, None);
        assert_eq!(later.given(), Ok(json!([null, "2", "2 5", "2 5"])));
    }

    #[test]
    fn an_array_ends_before_an_item_that_can_have_no_value() {
        // No value satisfies variable 0, so the array has one item at most.
        let short = || Asked::new().at(1, &[0]);
        assert_eq!(short().given(), Ok(json!([])));
        assert_eq!(short().count(1, None).given(), Ok(json!([null])));
        assert_eq!(short().count(2, None).given(), none());
        // After the head too.
        let closed = || Asked::new().at(0, &[2]).from(1, &[0]);
        assert_eq!(closed().count(1, None).given(), Ok(json!(["2"])));
        assert_eq!(closed().count(2, None).given(), none());
        // And of two that are asked for at once, what is asked of both.
        let neither = Asked::new().from(0, &[3]).from(0, &[4]);
        assert_eq!(neither.count(1, None).given(), none());
        // An item that there has to be is at no position after the end.
        assert_eq!(short().some(0, &[2]).given(), Ok(json!(["2"])));
        assert_eq!(short().some(1, &[2]).given(), none());
        // Two of them share the one position that there is, if a value satisfies both.
        let both = short().some(0, &[2]).some(0, &[5]);
        assert_eq!(both.given(), Ok(json!(["2 5"])));
        assert_eq!(short().some(0, &[3]).some(0, &[4]).given(), none());
    }

    #[test]
    fn an_item_that_there_has_to_be_finds_a_position() {
        assert_eq!(Asked::new().some(0, &[2]).given(), Ok(json!(["2"])));
        // It satisfies what its position asks too, and takes the first position that it
        // can.
        let asked = Asked::new().at(0, &[3]).at(1, &[5]);
        assert_eq!(asked.some(0, &[4]).given(), Ok(json!(["3", "4 5"])));
        let asked = Asked::new().from(0, &[5]).some(0, &[2]);
        assert_eq!(asked.given(), Ok(json!(["2 5"])));
        // From a position on: the positions before it are there too.
        assert_eq!(
            Asked::new().some(2, &[2]).given(),
            Ok(json!([null, null, "2"]))
        );
        let asked = Asked::new().at(0, &[5]).some(1, &[2]).some(0, &[4]);
        assert_eq!(asked.given(), Ok(json!(["4 5", "2"])));
        // Where no position will do, there is no array.
        assert_eq!(Asked::new().from(0, &[3]).some(0, &[4]).given(), none());
        assert_eq!(Asked::new().some(0, &[0]).given(), none());
        // Nothing asked of the value: there only has to be an item.
        assert_eq!(Asked::new().some(1, &[]).given(), Ok(json!([null, null])));
    }

    #[test]
    fn two_items_share_a_position_only_where_they_have_to() {
        let two = || Asked::new().some(0, &[2]).some(0, &[5]);
        // After the head each has a position of its own.
        assert_eq!(two().given(), Ok(json!(["5", "2"])));
        // An array that may have one item only has one that satisfies both.
        assert_eq!(two().count(0, Some(1)).given(), Ok(json!(["2 5"])));
        assert_eq!(two().count(0, Some(0)).given(), none());
        // Unless no value satisfies both.
        let apart = || Asked::new().some(0, &[3]).some(0, &[4]);
        assert_eq!(apart().count(0, Some(1)).given(), none());
        assert_eq!(apart().count(0, Some(2)).given(), Ok(json!(["4", "3"])));
        // Within the head, the first position that will do is tried first, also when
        // another item is there already.
        let first = Asked::new().at(0, &[2]).at(1, &[2]);
        assert_eq!(
            first.some(0, &[4]).some(0, &[5]).given(),
            Ok(json!(["2 4 5"]))
        );
        let first = Asked::new().at(0, &[2]).at(1, &[2]);
        assert_eq!(
            first.some(0, &[3]).some(0, &[4]).given(),
            Ok(json!(["2 4", "2 3"]))
        );
    }

    #[test]
    fn there_have_to_be_items_enough_for_the_least_number() {
        let asked = Asked::new().some(0, &[2]).count(3, None);
        assert_eq!(asked.given(), Ok(json!(["2", null, null])));
        let asked = Asked::new().from(1, &[5]).some(1, &[2]).count(4, Some(4));
        assert_eq!(asked.given(), Ok(json!([null, "2 5", "5", "5"])));
        // Whether an item can have a value may be what the engine does not know.
        let unknown = || Asked::new().from(0, &[1]);
        assert_eq!(unknown().given(), Ok(json!([])));
        assert_eq!(unknown().count(1, None).given(), Err("Number".to_owned()));
        assert_eq!(unknown().some(0, &[2]).given(), Err("Number".to_owned()));
        // An array that is known is given before one that is not.
        let either = Asked::new().at(0, &[1]).some(0, &[2]);
        assert_eq!(either.given(), Err("Number".to_owned()));
        let either = Asked::new().at(0, &[2]).at(0, &[1]).at(1, &[5]);
        assert_eq!(either.some(0, &[4]).given(), Err("Number".to_owned()));
        let either = Asked::new().from(1, &[1]).some(0, &[2]);
        assert_eq!(either.given(), Ok(json!(["2"])));
    }

    #[test]
    fn a_negated_term_asks_for_an_item_or_of_every_item() {
        let item = |position| move |variable| Term::Item(position, variable);
        // An item at the position that the schema does not accept.
        let asked = Asked::new().term(-2, item(1));
        assert_eq!(asked.given(), Ok(json!([null, "-2"])));
        assert_eq!(
            Asked::new().term(2, item(1)).term(-2, item(1)).given(),
            none()
        );
        // An item from the position on that it does not accept.
        let from = |from| move |variable| Term::AddIts(from, variable);
        let asked = Asked::new().term(-2, from(1));
        assert_eq!(asked.given(), Ok(json!([null, "-2"])));
        let asked = Asked::new().term(2, from(0)).term(-2, from(1));
        assert_eq!(asked.given(), none());
        let asked = Asked::new().term(2, from(1)).term(-2, from(0));
        assert_eq!(asked.given(), Ok(json!(["-2"])));
        // No item that the schema accepts.
        let asked = Asked::new().term(-2, Term::Contains).count(2, None);
        assert_eq!(asked.given(), Ok(json!(["-2", "-2"])));
        let asked = Asked::new()
            .term(-2, Term::Contains)
            .term(2, Term::Contains);
        assert_eq!(asked.given(), none());
        let asked = Asked::new().term(2, Term::Contains).term(5, Term::Contains);
        assert_eq!(asked.given(), Ok(json!(["5", "2"])));
        // Fewer than the least, and more than the most.
        let least = |least| move |_| Term::MinIts(least);
        let most = |most| move |_| Term::MaxIts(most);
        let asked = Asked::new().term(-2, least(2)).term(2, least(1));
        assert_eq!(asked.given(), Ok(json!([null])));
        assert_eq!(
            Asked::new().term(-2, least(1)).term(2, least(1)).given(),
            none()
        );
        let asked = Asked::new().term(-2, most(1));
        assert_eq!(asked.given(), Ok(json!([null, null])));
        assert_eq!(
            Asked::new().term(-2, most(1)).term(2, most(1)).given(),
            none()
        );
        let asked = Asked::new().term(-2, most(u64::MAX)).term(2, most(3));
        assert_eq!(asked.given(), none());
    }

    #[test]
    fn the_engine_is_asked_only_about_the_items_that_the_array_has() {
        // The empty array is given without a question.
        let mut asked = Asked::new().at(0, &[2]).at(1, &[4]).from(2, &[5]);
        let left = asked.left(&mut Budget::new(u64::MAX));
        assert!(matches!(left, Ok(Left::Value(Some(_)))));
        assert_eq!(asked.decided, []);
        // One item: about the first position, and about no other.
        let mut asked = Asked::new().at(0, &[2]).at(1, &[4]).from(2, &[5]);
        asked = asked.count(1, None);
        let left = asked.left(&mut Budget::new(u64::MAX)).unwrap();
        let Left::Value(Some(array)) = left else {
            panic!("{left:?} is no array");
        };
        assert_eq!(array.value, json!(["2"]));
        assert_eq!((array.size, array.depth), (2, 1));
        let first = asked.of(&[2]);
        assert_eq!(asked.decided, [first]);
        // Nor is it asked about an item at a position after the end of the array.
        let mut asked = Asked::new().at(1, &[0]).some(1, &[2]);
        let left = asked.left(&mut Budget::new(u64::MAX));
        assert!(matches!(left, Ok(Left::Nothing)));
        let (end, at_the_end) = (asked.of(&[0]), asked.of(&[0, 2]));
        assert_eq!(asked.decided, [at_the_end, end]);
        // A thousand items after the head are one question, and a step for each to copy.
        let mut asked = Asked::new().from(0, &[5]).count(1000, None);
        let mut budget = Budget::new(u64::MAX);
        let left = asked.left(&mut budget).unwrap();
        let Left::Value(Some(array)) = left else {
            panic!("{left:?} is no array");
        };
        assert_eq!(array.value.as_array().unwrap().len(), 1000);
        assert_eq!((array.size, asked.decided.len()), (1001, 1));
        assert!(budget.spent() >= 1000, "{}", budget.spent());
        // Without steps enough to copy them, there is no answer.
        let mut asked = Asked::new().count(1000, None);
        assert!(asked.left(&mut Budget::new(500)).is_err());
    }

    #[test]
    fn an_array_is_no_deeper_than_it_can_be_given() {
        let deep = |depth| {
            Rc::new(Witness {
                value: json!(null),
                size: 1,
                depth,
            })
        };
        for (depth, given) in [(DEEPEST - 1, true), (DEEPEST, false)] {
            let mut asked = Asked::new().from(0, &[2]).count(1, None);
            let of = asked.of(&[2]);
            asked.found.insert(of, Found::Instance(deep(depth)));
            match asked.left(&mut Budget::new(u64::MAX)).unwrap() {
                Left::Value(Some(array)) => assert!(given && array.depth == depth + 1),
                Left::Unknown(Cause::Depth) => assert!(!given),
                other => panic!("{other:?} is no answer"),
            }
        }
    }
}
