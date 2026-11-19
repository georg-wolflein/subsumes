//! An engine that is made up, for the tests of the objects and of the arrays.
//!
//! A variable is named by a number, and `-2` is the second one negated. To the engine here,
//! no value satisfies variable 0, and none satisfies 3 and 4 together. Whether one satisfies
//! variable 1 it does not know. Any other value is the names of what it satisfies.

use std::collections::HashMap;

use serde_json::{Value, json};

use super::object::Partitions;
use super::{Left, Solver};
use crate::context::{Budget, Exhausted};
use crate::language::{Languages, RegexDialect};
use crate::normalize::{Cause, Found, Witness};
use crate::schema::NodeId;
use crate::term::{CRefId, InstanceType, Terms, TypeSet, VarId};

/// The engine, with what a search works with.
pub(super) struct Engine {
    pub terms: Terms,
    pub languages: Languages,
    pub partitions: Partitions,
    variables: Vec<VarId>,
    pub found: HashMap<CRefId, Found>,
    /// The c-references that the engine was told to find out about, in that order.
    pub decided: Vec<CRefId>,
    /// How many times the engine was told to find something out first.
    pub waited: usize,
}

impl Engine {
    pub fn new() -> Self {
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
            // The patterns of the tests are those of the `regex` crate.
            languages: Languages::new(RegexDialect::Rust),
            partitions: Partitions::default(),
            found: HashMap::new(),
            decided: Vec::new(),
            waited: 0,
        }
    }

    /// The variable of a number, which may be below zero.
    pub fn variable(&self, number: i32) -> VarId {
        self.variables[number.unsigned_abs() as usize]
    }

    /// What a value satisfies that satisfies these.
    pub fn of(&mut self, variables: &[i32]) -> CRefId {
        let mut all = Terms::ANYTHING;
        for variable in variables {
            let one = self.terms.literal(self.variable(*variable), *variable < 0);
            all = self.terms.both(all, one);
        }
        all
    }

    /// What the engine finds of a c-reference.
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

    /// What a search leaves, with the engine deciding what it is asked for until nothing
    /// is asked any more.
    pub fn left(
        &mut self,
        budget: &mut Budget,
        search: impl Fn(&mut Solver, &mut dyn FnMut(CRefId) -> Option<Found>) -> Result<Left, Exhausted>,
    ) -> Result<Left, Exhausted> {
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
                too_deep: &mut false,
            };
            let left = search(&mut solver, &mut ask)?;
            let Left::Needs(wanted) = left else {
                return Ok(left);
            };
            assert!(!wanted.is_empty());
            self.waited += 1;
            for of in wanted {
                assert!(!self.found.contains_key(&of));
                self.found.insert(of, self.decide(of));
                self.decided.push(of);
            }
        }
    }
}

/// The object or the array that a search gives, or why it gives none.
pub(super) fn given(left: Left) -> Result<Value, String> {
    match left {
        Left::Value(Some(given)) => Ok(given.written(&mut Budget::new(u64::MAX)).unwrap()),
        Left::Nothing => Err("nothing".to_owned()),
        Left::Unknown(cause) => Err(format!("{cause:?}")),
        other => panic!("{other:?} is no answer"),
    }
}

pub(super) fn none() -> Result<Value, String> {
    Err("nothing".to_owned())
}
