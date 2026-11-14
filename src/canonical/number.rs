//! What a branch says about numbers.
//!
//! A term about numbers asks one of a few things of a number: to be at least some number or
//! at most some number, to be a multiple of one or no multiple of one, to be one number or
//! not to be it. However many terms a branch takes in, what they leave is of one shape: the
//! numbers of an interval that are multiples of one number and of none of a few others,
//! without a few numbers that are taken out one by one.
//!
//! Whether any number is left is decided exactly. Without a number to be a multiple of, an
//! interval that is more than one point always holds a number, because the excluded ones lie
//! apart. With one, the multiples in the interval are looked at one by one from zero
//! outwards, and the first that is in the set ends the search.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::context::{Budget, Exhausted};
use crate::rational::{Rational, common_multiple, is_multiple};
use crate::term::Term;

/// The numbers that a branch still accepts.
#[derive(Debug, Clone, Default)]
pub(crate) struct Numbers {
    /// The two ends of the interval. Without one, the interval has no end on that side.
    lower: Option<End>,
    upper: Option<End>,
    /// What every number is a multiple of: the least common multiple of all that were asked.
    multiple: Option<Rational>,
    /// What no number is a multiple of.
    excluded: BTreeSet<Rational>,
    /// The numbers that are not in the set, whatever else lets them be: "not this number"
    /// takes one number out and leaves the rest as it is.
    removed: BTreeSet<Rational>,
}

/// One end of an interval.
#[derive(Debug, Clone)]
struct End {
    at: Rational,
    /// Whether the end itself is outside the interval.
    open: bool,
}

impl Numbers {
    /// Takes in what a term about numbers asks of a number, as it stands or negated. The
    /// negation of "at least" is "less than", and so on.
    pub fn take(&mut self, term: &Term, negated: bool) {
        match (term, negated) {
            (Term::Min(at), false) | (Term::ExMax(at), true) => self.at_least(at, false),
            (Term::ExMin(at), false) | (Term::Max(at), true) => self.at_least(at, true),
            (Term::Max(at), false) | (Term::ExMin(at), true) => self.at_most(at, false),
            (Term::ExMax(at), false) | (Term::Min(at), true) => self.at_most(at, true),
            (Term::Mof(step), false) => {
                self.multiple = Some(match &self.multiple {
                    Some(multiple) => common_multiple(multiple, step),
                    None => step.clone(),
                });
            }
            (Term::Mof(step), true) => {
                self.excluded.insert(step.clone());
            }
            (Term::NumConst(number), false) => {
                self.at_least(number, false);
                self.at_most(number, false);
            }
            (Term::NumConst(number), true) => {
                self.removed.insert(number.clone());
            }
            (other, _) => unreachable!("{other:?} is not about numbers"),
        }
    }

    /// Keeps the numbers from `at` on, without `at` itself if `open`.
    fn at_least(&mut self, at: &Rational, open: bool) {
        let asks_more = self
            .lower
            .as_ref()
            .is_none_or(|lower| match at.cmp(&lower.at) {
                std::cmp::Ordering::Equal => open && !lower.open,
                order => order.is_gt(),
            });
        if asks_more {
            let at = at.clone();
            self.lower = Some(End { at, open });
        }
    }

    /// Keeps the numbers up to `at`, without `at` itself if `open`.
    fn at_most(&mut self, at: &Rational, open: bool) {
        let asks_more = self
            .upper
            .as_ref()
            .is_none_or(|upper| match at.cmp(&upper.at) {
                std::cmp::Ordering::Equal => open && !upper.open,
                order => order.is_lt(),
            });
        if asks_more {
            let at = at.clone();
            self.upper = Some(End { at, open });
        }
    }

    /// How much there is to copy when the branch splits.
    pub fn weight(&self) -> u64 {
        (self.excluded.len() + self.removed.len()) as u64
    }

    /// What every number of the set is a multiple of, if anything was asked.
    pub fn multiple(&self) -> Option<&Rational> {
        self.multiple.as_ref()
    }

    /// The one number of the interval, if the interval is one point.
    pub fn point(&self) -> Option<&Rational> {
        match (&self.lower, &self.upper) {
            (Some(lower), Some(upper)) if lower.at == upper.at && !lower.open && !upper.open => {
                Some(&lower.at)
            }
            _ => None,
        }
    }

    /// Whether the interval holds no number at all, whatever else is asked.
    fn interval_is_empty(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Some(lower), Some(upper)) => match lower.at.cmp(&upper.at) {
                std::cmp::Ordering::Equal => lower.open || upper.open,
                order => order.is_gt(),
            },
            _ => false,
        }
    }

    /// Whether a number is in the set.
    pub fn contains(&self, number: &Rational) -> bool {
        let lower = self.lower.as_ref();
        let upper = self.upper.as_ref();
        lower.is_none_or(|lower| *number > lower.at || (*number == lower.at && !lower.open))
            && upper.is_none_or(|upper| *number < upper.at || (*number == upper.at && !upper.open))
            && (self.multiple.iter()).all(|multiple| is_multiple(number, multiple))
            && !(self.excluded.iter()).any(|excluded| is_multiple(number, excluded))
            && !self.removed.contains(number)
    }

    /// Whether no number is in the set.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search among the multiples.
    pub fn is_empty(&self, budget: &mut Budget) -> Result<bool, Exhausted> {
        if self.interval_is_empty() {
            return Ok(true);
        }
        match (&self.multiple, self.point()) {
            (Some(multiple), _) => Ok(self.nearest_zero(multiple, budget)?.is_none()),
            (None, Some(only)) => Ok(!self.contains(only)),
            // The multiples of the excluded numbers lie apart, and the numbers that were
            // removed are few. Between any two of them the interval has a number.
            (None, None) => Ok(false),
        }
    }

    /// The number of the set that is a multiple of `step` and nearest to zero, if the set
    /// has a multiple of `step`. Of two that are equally near, it is the one above zero.
    ///
    /// Every candidate costs a step. The search ends at the first that is in the set, or at
    /// the ends of the interval. Among the multiples of a number, those of an excluded one
    /// come at an even pace, so unless they are all excluded, one that is not is never far.
    /// The numbers that were removed are passed over one by one.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the candidates.
    pub fn nearest_zero(
        &self,
        step: &Rational,
        budget: &mut Budget,
    ) -> Result<Option<Rational>, Exhausted> {
        let step = match &self.multiple {
            Some(multiple) => common_multiple(multiple, step),
            None => step.clone(),
        };
        // The multiples of the step in the interval: from `low` times the step to `high`
        // times. An open end that is a multiple itself is one further out.
        let low = self.lower.as_ref().map(|lower| {
            let times = &lower.at / &step;
            let whole = times.ceil().to_integer();
            if lower.open && times.is_integer() {
                whole + 1
            } else {
                whole
            }
        });
        let high = self.upper.as_ref().map(|upper| {
            let times = &upper.at / &step;
            let whole = times.floor().to_integer();
            if upper.open && times.is_integer() {
                whole - 1
            } else {
                whole
            }
        });
        let within = |times: &BigInt| {
            low.as_ref().is_none_or(|low| times >= low)
                && high.as_ref().is_none_or(|high| times <= high)
        };
        // Of the multiples of the step, every so many is a multiple of an excluded number.
        let every: Vec<BigInt> = (self.excluded.iter())
            .map(|excluded| (common_multiple(&step, excluded) / &step).to_integer())
            .collect();
        if every.iter().any(One::is_one) {
            return Ok(None);
        }

        let nearest = match (&low, &high) {
            (Some(low), _) if low.is_positive() => low.clone(),
            (_, Some(high)) if high.is_negative() => high.clone(),
            _ => BigInt::zero(),
        };
        let mut distance = BigInt::zero();
        loop {
            let both = [&nearest + &distance, &nearest - &distance];
            // At no distance the two are one.
            let candidates = if distance.is_zero() {
                &both[..1]
            } else {
                &both[..]
            };
            let mut any = false;
            for times in candidates.iter().filter(|times| within(times)) {
                any = true;
                // A candidate is held against every excluded number, so a set with many of
                // them costs more for each.
                budget.charge(1 + every.len() as u64)?;
                if every.iter().all(|every| !times.is_multiple_of(every)) {
                    let found = Rational::from_integer(times.clone()) * &step;
                    if !self.removed.contains(&found) {
                        return Ok(Some(found));
                    }
                }
            }
            // The interval lies on one side of where the search began, or around it, so
            // once nothing is within, nothing further out is.
            if !any {
                return Ok(None);
            }
            distance += 1;
        }
    }
}

#[cfg(test)]
pub(crate) mod testing {
    use super::*;
    use crate::rational::testing::number;
    use crate::term::Terms;
    use crate::testing::Random;

    /// A set of numbers together with what was asked of it, in plain arithmetic: a number is
    /// counted in quarters, and each thing asked is kept as it was said.
    pub(crate) struct Asked {
        pub numbers: Numbers,
        /// The ends that were asked, in quarters, each with whether it is open.
        at_least: Vec<(i64, bool)>,
        at_most: Vec<(i64, bool)>,
        multiples: Vec<i64>,
        excluded: Vec<i64>,
        removed: Vec<i64>,
    }

    /// The halves that an end may be at, and the numbers to be a multiple of or not. All are
    /// multiples of a half, so the quarters between them are multiples of none.
    const ENDS: [&str; 7] = ["-3", "-1.5", "-0.5", "0", "1", "2.5", "3"];
    const STEPS: [&str; 5] = ["0.5", "1", "1.5", "2", "3"];

    /// The quarters from -10 to 10. Beyond the ends at -3 and 3 there is one of every kind
    /// of number that the steps can tell apart, because they repeat every 6.
    pub(crate) const QUARTERS: std::ops::RangeInclusive<i64> = -40..=40;

    /// The set that is left when these terms are taken in: `>= 1`, `< 2.5`, `mof 0.5`,
    /// `not mof 2` for no multiple, `= 3` for one number and `!= 3` for any other.
    pub(crate) fn numbers(asked: &[&str]) -> Numbers {
        let mut terms = Terms::default();
        let mut numbers = Numbers::default();
        for asked in asked {
            let (what, at) = asked.rsplit_once(' ').unwrap();
            let at = number(at);
            let (term, negated) = match what {
                ">=" => (terms.min(at), false),
                ">" => (terms.ex_min(at), false),
                "<=" => (terms.max(at), false),
                "<" => (terms.ex_max(at), false),
                "mof" => (terms.mof(at), false),
                "not mof" => (terms.mof(at), true),
                "=" => (terms.num_const(at), false),
                "!=" => (terms.num_const(at), true),
                other => panic!("{other} is nothing to ask"),
            };
            numbers.take(terms.term(term), negated);
        }
        numbers
    }

    fn quarters(decimal: &str) -> i64 {
        let quarters = decimal.parse::<f64>().unwrap() * 4.0;
        assert!(quarters.fract() == 0.0);
        quarters as i64
    }

    impl Asked {
        /// Whether a number satisfies everything that was asked. The number is exact where
        /// it is a multiple of an eighth, and no other number is near an end or a multiple.
        pub fn holds(&self, number: f64) -> bool {
            let quarters = number * 4.0;
            let at_least = self
                .at_least
                .iter()
                .all(|&(at, open)| quarters > at as f64 || (quarters == at as f64 && !open));
            let at_most = self
                .at_most
                .iter()
                .all(|&(at, open)| quarters < at as f64 || (quarters == at as f64 && !open));
            let is_multiple = |of: &i64| (quarters / *of as f64).fract() == 0.0;
            at_least
                && at_most
                && self.multiples.iter().all(is_multiple)
                && !self.excluded.iter().any(is_multiple)
                && !self.removed.iter().any(|at| quarters == *at as f64)
        }

        /// A set that a few random things were asked of.
        pub fn random(random: &mut Random) -> Self {
            let mut terms = Terms::default();
            let mut asked = Self {
                numbers: Numbers::default(),
                at_least: Vec::new(),
                at_most: Vec::new(),
                multiples: Vec::new(),
                excluded: Vec::new(),
                removed: Vec::new(),
            };
            for _ in 0..random.below(7) {
                let (end, step) = (random.pick(&ENDS), random.pick(&STEPS));
                let negated = random.chance(50);
                // Each term both ways, so that every negation is among them. One number is
                // asked for less often than not asked for, because it leaves little.
                let (term, at) = match random.below(8) {
                    0 => (terms.min(number(end)), end),
                    1 => (terms.ex_min(number(end)), end),
                    2 => (terms.max(number(end)), end),
                    3 => (terms.ex_max(number(end)), end),
                    4 | 5 => (terms.mof(number(step)), step),
                    _ => (terms.num_const(number(end)), end),
                };
                let negated =
                    negated || matches!(terms.term(term), Term::NumConst(_)) && random.chance(60);
                let term = terms.term(term);
                asked.numbers.take(term, negated);
                let at = quarters(at);
                match (term, negated) {
                    (Term::Min(_), false) | (Term::ExMax(_), true) => {
                        asked.at_least.push((at, false));
                    }
                    (Term::ExMin(_), false) | (Term::Max(_), true) => {
                        asked.at_least.push((at, true));
                    }
                    (Term::Max(_), false) | (Term::ExMin(_), true) => {
                        asked.at_most.push((at, false));
                    }
                    (Term::ExMax(_), false) | (Term::Min(_), true) => {
                        asked.at_most.push((at, true));
                    }
                    (Term::NumConst(_), false) => {
                        asked.at_least.push((at, false));
                        asked.at_most.push((at, false));
                    }
                    (Term::NumConst(_), true) => asked.removed.push(at),
                    (_, false) => asked.multiples.push(at),
                    (_, true) => asked.excluded.push(at),
                }
            }
            asked
        }
    }
}

#[cfg(test)]
mod tests {
    use super::testing::{Asked, QUARTERS, numbers};
    use super::*;
    use crate::rational::testing::number;
    use crate::term::Terms;
    use crate::testing::Random;

    fn is_empty(asked: &[&str]) -> bool {
        numbers(asked).is_empty(&mut Budget::new(u64::MAX)).unwrap()
    }

    /// The multiple of `step` in the set that is nearest zero, as text.
    fn nearest(asked: &[&str], step: &str) -> Option<String> {
        let found = numbers(asked).nearest_zero(&number(step), &mut Budget::new(u64::MAX));
        found.unwrap().map(|found| found.to_string())
    }

    fn some(text: &str) -> Option<String> {
        Some(text.to_owned())
    }

    #[test]
    fn an_interval_is_empty_when_its_ends_cross() {
        assert!(!is_empty(&[]));
        assert!(!is_empty(&[">= 1"]));
        assert!(!is_empty(&[">= 1", "<= 2"]));
        assert!(!is_empty(&[">= 1", "<= 1"]));
        assert!(is_empty(&[">= 1", "< 1"]));
        assert!(is_empty(&["> 1", "<= 1"]));
        assert!(is_empty(&[">= 2", "<= 1"]));
        // The end that asks most is the one that counts, whenever it comes.
        assert!(is_empty(&[">= 0", ">= 3", "<= 5", "<= 2", "<= 4"]));
        assert!(is_empty(&["> 1", ">= 1", "<= 1"]));
        assert!(is_empty(&[">= 1", "> 1", "<= 1"]));
        assert!(!is_empty(&["> 1", "< 1.0000001"]));
    }

    #[test]
    fn a_negation_asks_the_opposite() {
        let mut terms = Terms::default();
        let cases = [
            (terms.min(number("1")), "1", false, false),
            (terms.ex_min(number("1")), "1", true, false),
            (terms.max(number("1")), "1", false, true),
            (terms.ex_max(number("1")), "1", true, true),
        ];
        // What the negation of each term makes of the number at its end and of one on
        // either side.
        for (term, at, keeps_end, keeps_above) in cases {
            let mut numbers = Numbers::default();
            numbers.take(terms.term(term), true);
            assert_eq!(numbers.contains(&number(at)), keeps_end);
            assert_eq!(numbers.contains(&number("2")), keeps_above);
            assert_eq!(numbers.contains(&number("0")), !keeps_above);
        }
    }

    #[test]
    fn multiples_are_looked_for_in_the_interval() {
        assert!(!is_empty(&["mof 2"]));
        assert!(!is_empty(&["mof 2", ">= 3", "<= 4"]));
        assert!(is_empty(&["mof 2", "> 2", "< 4"]));
        assert!(is_empty(&["mof 1", "> 0", "< 1"]));
        assert!(!is_empty(&["mof 0.5", "> 0", "< 1"]));
        // Two numbers to be a multiple of are their least common multiple.
        assert!(is_empty(&["mof 4", "mof 6", "> 0", "< 12"]));
        assert!(!is_empty(&["mof 4", "mof 6", "> 0", "<= 12"]));
        assert!(is_empty(&["mof 0.01", "mof 0.0075", "> 0", "< 0.03"]));
        // Zero is a multiple of everything.
        assert!(!is_empty(&["mof 7", ">= -1", "<= 1"]));

        assert_eq!(nearest(&[">= 3", "<= 10"], "2"), some("4"));
        assert_eq!(nearest(&["> 4", "<= 10"], "2"), some("6"));
        assert_eq!(nearest(&["<= -3"], "2"), some("-4"));
        assert_eq!(nearest(&["< -4"], "2"), some("-6"));
        assert_eq!(nearest(&[">= -5", "<= 5"], "2"), some("0"));
        assert_eq!(nearest(&[], "2"), some("0"));
        assert_eq!(nearest(&["> 0", "< 1"], "0.1"), some("1/10"));
        assert_eq!(nearest(&["> 0", "< 1"], "1"), None);
        // The step is taken together with what the set is a multiple of already.
        assert_eq!(nearest(&["mof 3", "> 0"], "2"), some("6"));
    }

    #[test]
    fn excluded_multiples_are_passed_over() {
        // Every multiple of two is one of one.
        assert!(is_empty(&["mof 2", "not mof 1"]));
        assert!(is_empty(&["mof 1.5", "not mof 0.5"]));
        assert!(!is_empty(&["mof 1", "not mof 2"]));
        assert!(!is_empty(&["mof 0.5", "not mof 1", "not mof 1.5"]));
        // Zero is excluded with anything, and so is the only even number here.
        assert_eq!(nearest(&["not mof 2"], "1"), some("1"));
        assert_eq!(nearest(&["not mof 2", "<= -1"], "1"), some("-1"));
        assert_eq!(nearest(&["not mof 2", "not mof 3", ">= 2"], "1"), some("5"));
        assert!(is_empty(&["mof 1", "not mof 2", ">= 2", "<= 2"]));
        assert!(is_empty(&[
            "mof 1",
            "not mof 2",
            "not mof 3",
            ">= 2",
            "<= 4"
        ]));
        assert!(!is_empty(&[
            "mof 1",
            "not mof 2",
            "not mof 3",
            ">= 2",
            "<= 5"
        ]));
        // Below and above zero by turns, the one above first.
        assert_eq!(nearest(&["not mof 1", ">= -1", "<= 1"], "0.5"), some("1/2"));
        assert_eq!(
            nearest(&["not mof 1", ">= -1", "< 0.5"], "0.5"),
            some("-1/2")
        );

        // Without a number to be a multiple of, only a single point can be excluded.
        assert!(!is_empty(&["not mof 1"]));
        assert!(!is_empty(&["not mof 1", "> 0", "< 1"]));
        assert!(!is_empty(&["not mof 0.5", "not mof 0.3", ">= 0", "<= 0.5"]));
        assert!(is_empty(&["not mof 1", ">= 2", "<= 2"]));
        assert!(!is_empty(&["not mof 1", ">= 2.5", "<= 2.5"]));
    }

    #[test]
    fn one_number_is_asked_for_or_taken_out() {
        assert!(!is_empty(&["= 2.5"]));
        assert!(!is_empty(&[
            "= 2.5",
            ">= 2.5",
            "<= 2.5",
            "mof 0.5",
            "not mof 2"
        ]));
        assert!(is_empty(&["= 2.5", "= 3"]));
        assert!(is_empty(&["= 2.5", "> 2.5"]));
        assert!(is_empty(&["= 2.5", "mof 1"]));
        assert!(is_empty(&["= 2.5", "not mof 0.5"]));
        assert!(is_empty(&["= 2.5", "!= 2.5"]));
        assert!(!is_empty(&["= 2.5", "!= 2"]));
        // Taking a number out of an interval leaves the rest of it.
        assert!(!is_empty(&["!= 0"]));
        assert!(!is_empty(&[">= 0", "<= 1", "!= 0", "!= 1", "!= 0.5"]));
        assert!(is_empty(&[">= 0", "<= 0", "!= 0"]));
        // Among multiples, each number that is taken out is one candidate less.
        assert!(!is_empty(&["mof 1", ">= 1", "<= 3", "!= 1", "!= 3"]));
        assert!(is_empty(&["mof 1", ">= 1", "<= 3", "!= 1", "!= 2", "!= 3"]));
        assert_eq!(nearest(&["!= 0", "!= 1", "!= -1"], "1"), some("2"));
        assert_eq!(nearest(&["!= 0", "not mof 2", "!= 1"], "1"), some("-1"));
        assert_eq!(
            nearest(&[">= 1", "<= 3", "!= 1", "!= 2"], "0.5"),
            some("3/2")
        );
    }

    #[test]
    fn the_search_costs_a_step_for_each_candidate_and_for_each_excluded_number() {
        let search = |asked: &[&str], budget: u64| {
            let mut budget = Budget::new(budget);
            let found = numbers(asked).is_empty(&mut budget);
            (found, budget.spent())
        };
        // An interval alone is compared and not searched.
        assert_eq!(search(&[">= 1", "<= 2", "not mof 1"], 0), (Ok(false), 0));
        assert_eq!(search(&["mof 1", ">= 5"], 1), (Ok(false), 1));
        // 24 to 28 are excluded, and 29 is not: six candidates, each held against three
        // excluded numbers.
        let asked = ["mof 1", "not mof 2", "not mof 3", "not mof 5", ">= 24"];
        assert_eq!(search(&asked, 24), (Ok(false), 24));
        assert_eq!(search(&asked, 23), (Err(Exhausted), 23));
        // A number that was taken out is a candidate like any other.
        let asked = ["mof 1", ">= 1", "!= 1", "!= 2", "!= 3"];
        assert_eq!(search(&asked, 4), (Ok(false), 4));
        // Where every multiple is excluded, none is looked at.
        assert_eq!(search(&["mof 4", "not mof 2"], 0), (Ok(true), 0));
        // Very large numbers and very small ones are numbers like any other.
        let far = ["mof 1e-300", ">= 1e300", "not mof 1e300"];
        assert_eq!(search(&far, 4), (Ok(false), 4));
    }

    #[test]
    fn the_set_is_what_was_asked_of_it() {
        let random = &mut Random(3);
        let (mut empty, mut searched) = (0, 0);
        for _ in 0..20_000 {
            let asked = Asked::random(random);
            let numbers = &asked.numbers;
            let members: Vec<i64> = QUARTERS
                .filter(|quarters| asked.holds(*quarters as f64 / 4.0))
                .collect();
            for quarters in QUARTERS {
                let exact = Rational::new(quarters.into(), 4.into());
                assert_eq!(
                    numbers.contains(&exact),
                    members.contains(&quarters),
                    "{quarters} quarters in {numbers:?}"
                );
            }
            let is_empty = numbers.is_empty(&mut Budget::new(1000)).unwrap();
            assert_eq!(is_empty, members.is_empty(), "{numbers:?}");
            empty += usize::from(is_empty);

            // Among the multiples of what the set is a multiple of, the search finds the one
            // nearest zero.
            if let Some(multiple) = numbers.multiple() {
                let found = numbers.nearest_zero(multiple, &mut Budget::new(1000));
                let nearest = members
                    .iter()
                    .min_by_key(|quarters| (quarters.abs(), **quarters < 0));
                let nearest = nearest.map(|quarters| Rational::new((*quarters).into(), 4.into()));
                assert_eq!(found.unwrap(), nearest, "{numbers:?}");
                searched += 1;
            }
        }
        assert!(empty > 2_000 && searched > 5_000, "{empty} {searched}");
    }
}
