//! The search that objects and arrays share: a place for every value that there has to be.
//!
//! An object has properties that there have to be, and an array has items. Each of them
//! needs a place: a name of a fragment, or a position. Two of them may share a place, and
//! then the value there satisfies what both are asked. The search tries the places of
//! each, one after the other, and goes back where none is left to try.
//!
//! What a place is, where a value may go, and whether what has been placed makes an object
//! or an array, is for the two to say: each has its [`Places`].
//!
//! # Where the search goes back to
//!
//! Not to the value before, but to the last value that had a part in what failed: this is
//! conflict-directed backjumping. When no value satisfies what a place asks together with
//! what the value is asked, that is so wherever the other values are, and no other value
//! has a part in it. When no value satisfies what a slot asks together with it, the values
//! in the slot have a part in it and no other. So each value keeps the values before it that
//! it *owes* a failed place to. When it has no place left, another place for a value that it
//! owes nothing to would leave it without one again, so the search goes back to the last
//! value that it owes one to, which is then owed the rest. A value that owes nothing to any
//! other has no place whatever the others do, and the search ends.
//!
//! Without this, a property that has no name to go by, after ten others that have six names
//! each, is found to have none once for each of the 60 million ways of placing those.

use std::collections::BTreeSet;
use std::rc::Rc;

use super::{Left, Solver, State, state};
use crate::context::Exhausted;
use crate::normalize::{Cause, Found, Witness};
use crate::term::CRefId;

/// A value of what is being put together of which more is asked than its place asks: where
/// it is, and what it satisfies.
#[derive(Debug)]
pub(super) struct Slot<At> {
    pub at: At,
    pub of: CRefId,
    /// A value. Without one: what stands in the way, or nothing if the engine has yet to
    /// decide whether there is one.
    pub value: Result<Rc<Witness>, Option<Cause>>,
}

/// Where a value that there has to be may go: to a slot that is there already, or to a new
/// one at a place.
#[derive(Debug, Clone, Copy)]
pub(super) enum Place<At> {
    Join(usize),
    Open(At),
}

/// What was done for one value that there has to be, and what else can be tried.
struct Level<At> {
    places: Vec<Place<At>>,
    next: usize,
    /// What the place that was tried last did, if it stands.
    done: Option<Done<At>>,
    /// The values before this one that it owes a place to which failed, by their numbers:
    /// were one of them placed otherwise, that place might stand.
    owes: BTreeSet<usize>,
}

/// What putting a value in a place did, to take it back.
enum Done<At> {
    /// The value joined this slot, which was this before.
    Joined(usize, Slot<At>),
    /// The value opened this slot, which is the last.
    Opened(usize),
}

impl<At> Done<At> {
    /// The slot that the value is in.
    fn slot(&self) -> usize {
        match self {
            Self::Joined(slot, _) | Self::Opened(slot) => *slot,
        }
    }

    /// Takes the value out of its place again. It is the value that was placed last.
    fn take_back<P: Places<At = At>>(self, placed: &mut Placed<At>, places: &mut P) {
        match self {
            Self::Joined(slot, was) => placed.slots[slot] = was,
            Self::Opened(_) => {
                let slot = placed.slots.pop();
                places.close(slot.expect("the slot that was opened is there").at);
            }
        }
    }
}

/// What the search has put together.
pub(super) struct Placed<At> {
    pub slots: Vec<Slot<At>>,
    /// The c-references that the engine has yet to decide.
    pub wanted: Vec<CRefId>,
    /// What stood in the way of an object or an array that was put together without a value
    /// in every slot. Once there is such a one, only one with every value is looked for.
    pub depends: Option<Cause>,
}

/// The places of an object or of an array, and what it takes for the values that are placed
/// to make one.
pub(super) trait Places {
    /// A place: the fragment of a name, or a position.
    type At: Copy;

    /// What the value that there has to be of this number is asked besides what its place
    /// asks, or `None` where there are fewer of them.
    fn asked(&self, which: usize) -> Option<CRefId>;

    /// Where the value of this number may go, in the order in which the places are tried.
    ///
    /// The search has to know which values a place is owed to that is left out because of
    /// what is placed. So a new slot is left out only where every slot that takes its room
    /// is among the places, or where [`Places::crowded`] says so.
    fn places(&self, placed: &Placed<Self::At>, which: usize) -> Vec<Place<Self::At>>;

    /// Whether the slots that there are leave no room for a new one anywhere, also where
    /// they are not among the places of a value. Then a value owes the places that it is
    /// not given to every value before it.
    fn crowded(&self, _placed: &Placed<Self::At>) -> bool {
        false
    }

    /// What a value satisfies by its place alone.
    fn at(&self, at: Self::At) -> CRefId;

    /// Whether there can be a value at a place at all. There can, unless what is being put
    /// together ends before the place, which no value that is placed has a part in.
    ///
    /// # Errors
    ///
    /// When the budget does not cover finding that out.
    fn reaches(
        &mut self,
        _at: Self::At,
        _placed: &mut Placed<Self::At>,
        _with: &mut Solver,
        _ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    ) -> Result<bool, Exhausted> {
        Ok(true)
    }

    /// Notes the slot that is opened at a place.
    fn open(&mut self, at: Self::At, slot: usize);

    /// Takes back the slot that was opened last, which was at this place.
    fn close(&mut self, at: Self::At);

    /// With a place for every value that there has to be: whether they make an object or
    /// an array, which takes values enough besides them.
    ///
    /// `None` if they make none, or one only as far as the engine knows, which is noted.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the work.
    fn fill(
        &mut self,
        placed: &mut Placed<Self::At>,
        with: &mut Solver,
        ask: &mut dyn FnMut(CRefId) -> Option<Found>,
        give: bool,
    ) -> Result<Option<Left>, Exhausted>;
}

/// Tries the places of each value that there has to be, one after the other. Where none is
/// left to try for a value, it goes back to the last value that this one owes a failed
/// place to, and ends where there is none.
///
/// # Errors
///
/// When the budget does not cover the search. Each place that is tried costs a step.
pub(super) fn run<P: Places>(
    mut places: P,
    with: &mut Solver,
    ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    give: bool,
) -> Result<Left, Exhausted> {
    let mut placed = Placed {
        slots: Vec::new(),
        wanted: Vec::new(),
        depends: None,
    };
    let mut levels: Vec<Level<P::At>> = Vec::new();
    let mut onward = true;
    loop {
        if onward && places.asked(levels.len()).is_none() {
            // Every one of them has a place.
            if let Some(left) = places.fill(&mut placed, with, ask, give)? {
                return Ok(left);
            }
            // As they are placed, the values make nothing, which the last of them owes to
            // every one before it.
            if let Some((last, before)) = levels.split_last_mut() {
                last.owes.extend(0..before.len());
            }
        } else if onward {
            let tried = places.places(&placed, levels.len());
            let crowded = places.crowded(&placed);
            levels.push(Level {
                places: tried,
                next: 0,
                done: None,
                owes: (0..levels.len()).filter(|_| crowded).collect(),
            });
        }
        let Some((level, before)) = levels.split_last_mut() else {
            break;
        };
        if let Some(done) = level.done.take() {
            done.take_back(&mut placed, &mut places);
        }
        let Some(place) = level.places.get(level.next).copied() else {
            // No place is left for this value. Another place for a value that it owes
            // nothing to would leave it without one again.
            let mut spent = levels.pop().expect("a level is at work");
            let Some(back) = spent.owes.pop_last() else {
                // It owes nothing to any: it has no place however the others are placed.
                break;
            };
            // The values after the one that the search goes back to are taken out of their
            // places, the last first. That one is owed what this one was.
            with.budget.charge((spent.owes.len() / 8) as u64)?;
            for skipped in levels.drain(back + 1..).rev() {
                let done = skipped
                    .done
                    .expect("a value before the one at work is placed");
                done.take_back(&mut placed, &mut places);
            }
            let level = levels.last_mut().expect("the value that is owed is there");
            level.owes.append(&mut spent.owes);
            onward = false;
            continue;
        };
        level.next += 1;
        with.budget.charge(1)?;
        let asked = places.asked(before.len());
        let asked = asked.expect("a level is of a value that there has to be");
        let (at, of) = match place {
            Place::Join(slot) => (placed.slots[slot].at, placed.slots[slot].of),
            Place::Open(at) => (at, places.at(at)),
        };
        onward = places.reaches(at, &mut placed, with, ask)?;
        if !onward {
            continue;
        }
        if matches!(place, Place::Join(_)) {
            // A value that cannot be at the place by itself cannot share it either, and it
            // owes that to no value in the slot. The engine is not told to find this out:
            // what it does not know of the place, it is asked of the slot.
            let alone = with.terms.both(places.at(at), asked);
            if matches!(ask(alone), Some(Found::Nothing)) {
                onward = false;
                continue;
            }
        }
        let of = with.terms.both(of, asked);
        let known = state(of, ask, &mut placed.wanted);
        let nothing = matches!(known, State::Nothing);
        let value = match known {
            State::Nothing => None,
            State::Possible(_) if placed.depends.is_some() => None,
            State::Possible(cause) => Some(Err(Some(cause))),
            State::Sure(witness) => Some(Ok(witness)),
            State::Wanted => Some(Err(None)),
        };
        onward = value.is_some();
        let Some(value) = value else {
            match place {
                // No value satisfies what the place asks together with what this value is
                // asked, wherever the others are.
                Place::Open(_) if nothing => {}
                // None satisfies what the values in the slot are asked together with it.
                // So it is with more values in the slot, and those that are in it have a
                // part in that.
                Place::Join(joined) if nothing => {
                    let shares = |level: &Level<P::At>| {
                        let slot = level.done.as_ref().map(Done::slot);
                        slot == Some(joined)
                    };
                    let sharing = before.iter().enumerate().filter(|(_, level)| shares(level));
                    level.owes.extend(sharing.map(|(number, _)| number));
                }
                // A value may satisfy it, and the place fails for the engine not knowing
                // one. Of what the engine knows of a value with more asked of it, that
                // says nothing, so every value before has a part in it.
                Place::Open(_) | Place::Join(_) => level.owes.extend(0..before.len()),
            }
            continue;
        };
        let slot = Slot { at, of, value };
        let done = match place {
            Place::Join(joined) => {
                Done::Joined(joined, std::mem::replace(&mut placed.slots[joined], slot))
            }
            Place::Open(at) => {
                let opened = placed.slots.len();
                places.open(at, opened);
                placed.slots.push(slot);
                Done::Opened(opened)
            }
        };
        level.done = Some(done);
    }
    Ok(match placed.depends {
        _ if !placed.wanted.is_empty() => Left::Needs(placed.wanted),
        Some(cause) => Left::Unknown(cause),
        None => Left::Nothing,
    })
}
