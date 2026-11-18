//! The state of one check. Nothing in it outlives the check or is shared with another.

use crate::language::{Languages, RegexDialect};
use crate::term::Terms;

/// Everything that a check builds on its way: the terms, the languages of strings, and the
/// work it may still do.
#[derive(Debug)]
pub(crate) struct Context {
    pub budget: Budget,
    pub terms: Terms,
    pub languages: Languages,
}

impl Context {
    /// The state of a check with a work budget, which reads its patterns in a dialect.
    pub fn new(budget: u64, dialect: RegexDialect) -> Self {
        Self {
            budget: Budget::new(budget),
            terms: Terms::default(),
            languages: Languages::new(dialect),
        }
    }
}

/// The work that a check may do, in steps. A step is one unit of whatever can grow beyond the
/// size of the two schemas, so the count depends on the schemas alone and not on the machine.
#[derive(Debug)]
pub(crate) struct Budget {
    limit: u64,
    spent: u64,
}

/// The budget does not cover the work. The check ends in `Unknown`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Exhausted;

impl Budget {
    pub fn new(limit: u64) -> Self {
        Self { limit, spent: 0 }
    }

    /// Takes the steps for work that is about to be done.
    ///
    /// # Errors
    ///
    /// When the budget does not cover them.
    pub fn charge(&mut self, steps: u64) -> Result<(), Exhausted> {
        self.spent = self.spent.saturating_add(steps);
        if self.spent > self.limit {
            Err(Exhausted)
        } else {
            Ok(())
        }
    }

    /// The steps taken so far. A budget that ran out counts as spent in full.
    pub fn spent(&self) -> u64 {
        self.spent.min(self.limit)
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
}
