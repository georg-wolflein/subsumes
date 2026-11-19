//! The state of a load of two schemas: of a check, and of its converse if that is asked for.
//! Nothing in it outlives the two or is shared with another pair.

use crate::language::{Languages, RegexDialect};
use crate::normalize::Facts;
use crate::term::Terms;

/// Everything that a check builds on its way: the terms, the languages of strings, what the
/// engine has found out for good, and the work it may still do.
///
/// All but the budget is about the two schemas and not about which of them is to accept the
/// instances of the other. So the converse goes on with the same context, and with a budget
/// of its own.
#[derive(Debug)]
pub(crate) struct Context {
    pub budget: Budget,
    pub terms: Terms,
    pub languages: Languages,
    pub facts: Facts,
}

impl Context {
    /// The state of a check with a work budget, which reads its patterns in a dialect.
    pub fn new(budget: u64, dialect: RegexDialect) -> Self {
        Self {
            budget: Budget::new(budget),
            terms: Terms::default(),
            languages: Languages::new(dialect),
            facts: Facts::default(),
        }
    }
}

/// The work that a check may do, in steps. A step is one unit of whatever can grow beyond the
/// size of the two schemas, so the count depends on the schemas alone and not on the machine.
#[derive(Debug)]
pub(crate) struct Budget {
    limit: u64,
    spent: u64,
    /// How many steps may be spent before the work at hand has to end: all of the budget,
    /// or fewer while a piece of work has an allowance of its own.
    allowed: u64,
}

/// The budget does not cover the work. The check ends in `Unknown`, unless the work had an
/// allowance of its own: then that piece of work is given up, and the check goes on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Exhausted;

impl Budget {
    pub fn new(limit: u64) -> Self {
        Self {
            limit,
            spent: 0,
            allowed: limit,
        }
    }

    /// Takes the steps for work that is about to be done.
    ///
    /// # Errors
    ///
    /// When the budget does not cover them, or the allowance of the work at hand.
    pub fn charge(&mut self, steps: u64) -> Result<(), Exhausted> {
        self.spent = self.spent.saturating_add(steps);
        if self.spent > self.allowed {
            Err(Exhausted)
        } else {
            Ok(())
        }
    }

    /// The steps taken so far. A budget that ran out counts as spent in full.
    pub fn spent(&self) -> u64 {
        self.spent.min(self.limit)
    }

    /// Gives the work that follows an allowance: it may take so many steps and no more,
    /// and never more than it might have taken without one. Returns what was allowed
    /// before, which [`restore`](Self::restore) takes when that work has ended.
    pub fn allow(&mut self, steps: u64) -> u64 {
        let before = self.allowed;
        self.allowed = before.min(self.spent.saturating_add(steps));
        before
    }

    /// Ends an allowance. Work that the allowance did not cover was not done, so its steps
    /// are not counted: an allowance that ran out is spent in full and no further.
    pub fn restore(&mut self, before: u64) {
        self.spent = self.spent.min(self.allowed);
        self.allowed = before;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_budget_covers_its_limit_and_no_more() {
        let mut budget = Budget::new(3);
        assert_eq!(budget.charge(2), Ok(()));
        assert_eq!(budget.charge(1), Ok(()));
        assert_eq!(budget.spent(), 3);
        assert_eq!(budget.charge(1), Err(Exhausted));
        assert_eq!(budget.charge(u64::MAX), Err(Exhausted));
        assert_eq!(budget.spent(), 3);
    }

    #[test]
    fn an_allowance_ends_the_work_that_it_is_for_and_no_other() {
        let mut budget = Budget::new(10);
        assert_eq!(budget.charge(2), Ok(()));
        let before = budget.allow(3);
        assert_eq!(budget.charge(3), Ok(()));
        // An allowance inside another is no more than what is left of that one.
        let outer = budget.allow(5);
        assert_eq!(budget.charge(1), Err(Exhausted));
        budget.restore(outer);
        assert_eq!(budget.charge(4), Err(Exhausted));
        // The work that was not covered is not counted, and the budget covers what it did.
        budget.restore(before);
        assert_eq!(budget.spent(), 5);
        assert_eq!(budget.charge(5), Ok(()));
        // An allowance is never more than the budget has left.
        let before = budget.allow(7);
        assert_eq!(budget.charge(1), Err(Exhausted));
        budget.restore(before);
        assert_eq!(budget.spent(), 10);
        assert_eq!(budget.charge(1), Err(Exhausted));
    }
}
