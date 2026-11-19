//! The search that objects and arrays share: a place for every value that there has to be.
//!
//! An object has properties that there have to be, and an array has items. Each of them
//! needs a place: a name of a fragment, or a position. Two of them may share a place, and
//! then the value there satisfies what both are asked. The search tries the places of
//! each, one after the other, and goes back to the one before where none is left to try.
//!
//! What a place is, where a value may go, and whether what has been placed makes an object
//! or an array, is for the two to say: each has its [`Places`].

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
    /// Where its places are in the places of all levels, and the next to try.
    from: usize,
    to: usize,
    next: usize,
    /// What the place that was tried last did, if it stands.
    done: Option<Done<At>>,
}

/// The lists that a search is put together in. A search leaves them to the next, which
/// clears them and keeps their memory.
pub(super) struct Work<At> {
    levels: Vec<Level<At>>,
    /// The places of each level, one level after the other.
    places: Vec<Place<At>>,
    slots: Vec<Slot<At>>,
}

impl<At> Default for Work<At> {
    fn default() -> Self {
        Self {
            levels: Vec::new(),
            places: Vec::new(),
            slots: Vec::new(),
        }
    }
}

impl<At> std::fmt::Debug for Work<At> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("Work")
    }
}

/// What putting a value in a place did, to take it back.
enum Done<At> {
    /// The value joined this slot, which was this before.
    Joined(usize, Slot<At>),
    /// The value opened the last slot.
    Opened,
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

    /// Where the value of this number may go, in the order in which the places are tried,
    /// put after the places that are there.
    fn places(&self, placed: &Placed<Self::At>, which: usize, places: &mut Vec<Place<Self::At>>);

    /// What a value satisfies by its place alone.
    fn at(&self, at: Self::At) -> CRefId;

    /// Whether there can be a value at a place at all. There can, unless what is being put
    /// together ends before the place.
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

/// Tries the places of each value that there has to be, one after the other, and goes back
/// to the one before where none is left to try.
///
/// # Errors
///
/// When the budget does not cover the search. Each place that is tried costs a step.
pub(super) fn run<P: Places>(
    places: P,
    with: &mut Solver,
    ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    give: bool,
    work: &mut Work<P::At>,
) -> Result<Left, Exhausted> {
    let mut placed = Placed {
        slots: std::mem::take(&mut work.slots),
        wanted: Vec::new(),
        depends: None,
    };
    work.levels.clear();
    work.places.clear();
    let left = search(places, &mut placed, with, ask, give, work);
    // What the search holds is let go, and the memory of its lists is kept.
    work.levels.clear();
    work.places.clear();
    placed.slots.clear();
    work.slots = placed.slots;
    left
}

/// The search of [`run`], in the lists of `work` and with what it has put together in
/// `placed`.
fn search<P: Places>(
    mut places: P,
    placed: &mut Placed<P::At>,
    with: &mut Solver,
    ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    give: bool,
    work: &mut Work<P::At>,
) -> Result<Left, Exhausted> {
    let Work {
        levels,
        places: tried,
        ..
    } = work;
    let mut onward = true;
    loop {
        if onward && places.asked(levels.len()).is_none() {
            // Every one of them has a place.
            if let Some(left) = places.fill(placed, with, ask, give)? {
                return Ok(left);
            }
        } else if onward {
            let from = tried.len();
            places.places(placed, levels.len(), tried);
            levels.push(Level {
                from,
                to: tried.len(),
                next: from,
                done: None,
            });
        }
        let Some(level) = levels.last_mut() else {
            break;
        };
        match level.done.take() {
            Some(Done::Joined(slot, was)) => placed.slots[slot] = was,
            Some(Done::Opened) => {
                let slot = placed.slots.pop();
                places.close(slot.expect("the slot that was opened is there").at);
            }
            None => {}
        }
        if level.next == level.to {
            tried.truncate(level.from);
            levels.pop();
            onward = false;
            continue;
        }
        let place = tried[level.next];
        level.next += 1;
        with.budget.charge(1)?;
        let asked = places.asked(levels.len() - 1);
        let asked = asked.expect("a level is of a value that there has to be");
        let (at, of) = match place {
            Place::Join(slot) => (placed.slots[slot].at, placed.slots[slot].of),
            Place::Open(at) => (at, places.at(at)),
        };
        onward = places.reaches(at, placed, with, ask)?;
        if !onward {
            continue;
        }
        let of = with.terms.both(of, asked);
        let value = match state(of, ask, &mut placed.wanted) {
            State::Nothing => None,
            State::Possible(_) if placed.depends.is_some() => None,
            State::Possible(cause) => Some(Err(Some(cause))),
            State::Sure(witness) => Some(Ok(witness)),
            State::Wanted => Some(Err(None)),
        };
        onward = value.is_some();
        let Some(value) = value else {
            continue;
        };
        let slot = Slot { at, of, value };
        let done = match place {
            Place::Join(joined) => {
                Done::Joined(joined, std::mem::replace(&mut placed.slots[joined], slot))
            }
            Place::Open(at) => {
                places.open(at, placed.slots.len());
                placed.slots.push(slot);
                Done::Opened
            }
        };
        levels.last_mut().expect("a level is at work").done = Some(done);
    }
    Ok(match placed.depends {
        _ if !placed.wanted.is_empty() => Left::Needs(std::mem::take(&mut placed.wanted)),
        Some(cause) => Left::Unknown(cause),
        None => Left::Nothing,
    })
}
