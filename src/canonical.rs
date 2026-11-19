//! The canonical conjunctions: what a branch says about the instances of one type, in the
//! one shape that everything said about that type comes down to.
//!
//! An object and an array hold values, and a value is an instance of its own. What it has to
//! satisfy is a c-reference, and whether a value can satisfy one is not decided here: the
//! engine is asked, and what it does not know yet it is told to find out first. Whether an
//! object or an array is left is one search for both, in `search`.

pub(crate) mod array;
#[cfg(test)]
mod made_up;
pub(crate) mod number;
pub(crate) mod object;
mod search;
pub(crate) mod string;

use std::collections::BTreeSet;
use std::rc::Rc;

use self::object::Partitions;
use crate::context::Budget;
use crate::language::Languages;
use crate::normalize::{Cause, Found, Witness};
use crate::term::{CRefId, Terms};

/// What the search for an object or an array works with: the terms, for the c-references,
/// the languages and the budget of the check, and the partitions of the names of objects
/// that were made before.
pub(crate) struct Solver<'s> {
    pub terms: &'s mut Terms,
    pub languages: &'s mut Languages,
    pub budget: &'s mut Budget,
    pub partitions: &'s mut Partitions,
    /// Whether an object or an array was passed over because it would be too deep to give.
    pub too_deep: &'s mut bool,
}

/// Adds to a set that a branch may share with the branch that it was copied from. A set
/// that is shared is copied first, unless it holds the element already (copy on write).
pub(crate) fn add<T: Ord + Clone>(set: &mut Rc<BTreeSet<T>>, element: T) {
    if let Some(own) = Rc::get_mut(set) {
        own.insert(element);
    } else if !set.contains(&element) {
        Rc::make_mut(set).insert(element);
    }
}

/// What is left of the objects of a branch, or of its arrays.
#[derive(Debug)]
pub(crate) enum Left {
    /// No object, or no array.
    Nothing,
    /// One as far as the engine knows: this stands between it and a value that it holds.
    Unknown(Cause),
    /// One, which is given if one was asked for.
    Value(Option<Rc<Witness>>),
    /// That depends on these c-references, of which the engine knows nothing yet.
    Needs(Vec<CRefId>),
}

/// What the engine makes of a c-reference, as the search for an object or an array sees it.
pub(crate) enum State {
    Nothing,
    Possible(Cause),
    Sure(Rc<Witness>),
    /// The engine has yet to decide. The search goes on as if there were a value.
    Wanted,
}

/// Asks the engine whether a value can satisfy a c-reference. One that it has yet to decide
/// is put with those that are wanted.
pub(crate) fn state(
    of: CRefId,
    ask: &mut dyn FnMut(CRefId) -> Option<Found>,
    wanted: &mut Vec<CRefId>,
) -> State {
    match ask(of) {
        Some(Found::Nothing) => State::Nothing,
        Some(Found::Unknown(cause)) => State::Possible(cause),
        Some(Found::Instance(witness)) => State::Sure(witness),
        None => {
            if !wanted.contains(&of) {
                wanted.push(of);
            }
            State::Wanted
        }
    }
}
