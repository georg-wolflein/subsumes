//! What a branch says about a number: an interval, a number that it is a multiple of, and
//! numbers that it is no multiple of.
//!
//! Several multiples are one, the least number that is a multiple of each. The numbers that
//! an instance must be no multiple of stay a list, and whether a number is left with them is
//! found by a search.

use crate::context::{Budget, Exhausted};
use crate::rational::{Rational, RationalId, Rationals, whole};

/// The numbers that satisfy every term about numbers of a branch.
#[derive(Debug, Clone, Default)]
pub(crate) struct Numbers {
    lower: Option<Bound>,
    upper: Option<Bound>,
    multiple: Option<RationalId>,
    excluded: Vec<RationalId>,
}

/// One end of an interval. An open end is not part of it.
#[derive(Debug, Clone, Copy)]
struct Bound {
    at: RationalId,
    open: bool,
}

/// One thing that is said about a number. What a number is a multiple of, or not, is greater
/// than zero.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Says {
    AtLeast(RationalId),
    Above(RationalId),
    AtMost(RationalId),
    Below(RationalId),
    MultipleOf(RationalId),
    NoMultipleOf(RationalId),
}

/// How many numbers an interval holds.
enum Extent<'r> {
    None,
    One(&'r Rational),
    Many,
}

impl Numbers {
    /// How much there is to copy.
    pub fn weight(&self) -> u64 {
        self.excluded.len() as u64
    }

    /// Keeps the numbers of which this holds too.
    pub fn take(&mut self, rationals: &mut Rationals, says: Says) {
        match says {
            Says::AtLeast(at) => self.at_least(rationals, at, false),
            Says::Above(at) => self.at_least(rationals, at, true),
            Says::AtMost(at) => self.at_most(rationals, at, false),
            Says::Below(at) => self.at_most(rationals, at, true),
            Says::MultipleOf(of) => self.multiple_of(rationals, of),
            Says::NoMultipleOf(of) => {
                if !self.excluded.contains(&of) {
                    self.excluded.push(of);
                }
            }
        }
    }

    /// Keeps the numbers from `at` on, without `at` itself if the end is open.
    fn at_least(&mut self, rationals: &Rationals, at: RationalId, open: bool) {
        let tighter = self.lower.is_none_or(|bound| {
            let (new, old) = (rationals.get(at), rationals.get(bound.at));
            new > old || (new == old && open)
        });
        if tighter {
            self.lower = Some(Bound { at, open });
        }
    }

    /// Keeps the numbers up to `at`, without `at` itself if the end is open.
    fn at_most(&mut self, rationals: &Rationals, at: RationalId, open: bool) {
        let tighter = self.upper.is_none_or(|bound| {
            let (new, old) = (rationals.get(at), rationals.get(bound.at));
            new < old || (new == old && open)
        });
        if tighter {
            self.upper = Some(Bound { at, open });
        }
    }

    /// Keeps the multiples of `of`.
    fn multiple_of(&mut self, rationals: &mut Rationals, of: RationalId) {
        let Some(multiple) = self.multiple else {
            self.multiple = Some(of);
            return;
        };
        // The least number that is a multiple of both. A multiple `k * a` of `a` is one of
        // `b` when the denominator of `a / b` divides `k`.
        let (a, b) = (rationals.get(multiple), rationals.get(of));
        let both = a * Rational::from_integer((a / b).denom().clone());
        self.multiple = Some(rationals.intern(both));
    }

    /// Whether no number is left.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search.
    pub fn is_empty(&self, rationals: &Rationals, budget: &mut Budget) -> Result<bool, Exhausted> {
        if let Some(multiple) = self.multiple {
            let on_grid = self.on_grid(rationals, rationals.get(multiple), budget)?;
            return Ok(on_grid.is_none());
        }
        Ok(match self.extent(rationals) {
            Extent::None => true,
            Extent::One(only) => self.excludes(rationals, only),
            Extent::Many => false,
        })
    }

    /// A number that is left, if there is one: one with few digits, and of those one that is
    /// close to zero.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search.
    pub fn member(
        &self,
        rationals: &Rationals,
        budget: &mut Budget,
    ) -> Result<Option<Rational>, Exhausted> {
        // The multiples of a grid are looked through, on a coarse grid first: its multiples
        // have the fewest digits. Each next grid is a tenth of the one before.
        let ten = whole(10);
        if let Some(multiple) = self.multiple {
            // No grid is finer than the multiple itself, which holds every number left.
            let multiple = rationals.get(multiple);
            for exponent in (0..=self.coarsest(rationals, multiple).max(0)).rev() {
                budget.charge(1)?;
                let grid = multiple * ten.pow(exponent);
                if let Some(member) = self.on_grid(rationals, &grid, budget)? {
                    return Ok(Some(member));
                }
            }
            return Ok(None);
        }
        match self.extent(rationals) {
            Extent::None => return Ok(None),
            Extent::One(only) => {
                return Ok((!self.excludes(rationals, only)).then(|| only.clone()));
            }
            Extent::Many => {}
        }
        // An interval of more than one number holds a decimal that is no multiple of the
        // excluded numbers: their multiples lie apart, and the decimals do not. So some grid
        // is fine enough.
        let mut exponent = self.coarsest(rationals, &whole(1));
        loop {
            budget.charge(1)?;
            if let Some(member) = self.on_grid(rationals, &ten.pow(exponent), budget)? {
                return Ok(Some(member));
            }
            exponent -= 1;
        }
    }

    /// How many numbers the interval holds, whatever they are multiples of.
    fn extent<'r>(&self, rationals: &'r Rationals) -> Extent<'r> {
        let (Some(lower), Some(upper)) = (self.lower, self.upper) else {
            return Extent::Many;
        };
        let (least, greatest) = (rationals.get(lower.at), rationals.get(upper.at));
        if least < greatest {
            Extent::Many
        } else if least == greatest && !lower.open && !upper.open {
            Extent::One(least)
        } else {
            Extent::None
        }
    }

    /// Whether the number is a multiple of one that it must be no multiple of.
    fn excludes(&self, rationals: &Rationals, number: &Rational) -> bool {
        let mut excluded = self.excluded.iter();
        excluded.any(|of| (number / rationals.get(*of)).is_integer())
    }

    /// The power of ten of the coarsest grid that is worth a look, for grids that are `unit`
    /// times a power of ten: the largest that is no further from zero than both ends of the
    /// interval are.
    fn coarsest(&self, rationals: &Rationals, unit: &Rational) -> i32 {
        let (zero, ten) = (whole(0), whole(10));
        // The power of ten that the first digit of an end stands for, counted in units.
        let magnitude = |bound: Option<Bound>| {
            let units = rationals.get(bound?.at) / unit;
            let units = if units < zero { -units } else { units };
            if units == zero {
                return None;
            }
            let length = |digits: String| digits.len() as i32;
            let estimate = length(units.numer().to_string()) - length(units.denom().to_string());
            Some(if units >= ten.pow(estimate) {
                estimate
            } else {
                estimate - 1
            })
        };
        let coarsest = magnitude(self.lower).max(magnitude(self.upper));
        coarsest.unwrap_or(0)
    }

    /// A multiple of `grid` in the interval that is no multiple of the excluded numbers: of
    /// those the one that is closest to zero, and the one above zero of two that are as close.
    fn on_grid(
        &self,
        rationals: &Rationals,
        grid: &Rational,
        budget: &mut Budget,
    ) -> Result<Option<Rational>, Exhausted> {
        // `k * grid` is a multiple of an excluded number when the denominator of the grid
        // over that number divides `k`. A denominator of one divides every `k`.
        let (zero, one) = (whole(0), whole(1));
        let divisors = self.excluded.iter().map(|of| {
            let units = grid / rationals.get(*of);
            Rational::from_integer(units.denom().clone())
        });
        let divisors: Vec<Rational> = divisors.collect();
        if divisors.contains(&one) {
            return Ok(None);
        }

        // The whole numbers `k` for which `k * grid` is in the interval.
        let least = self.lower.map(|bound| {
            let units = rationals.get(bound.at) / grid;
            let whole = units.ceil();
            if bound.open && whole == units {
                whole + &one
            } else {
                whole
            }
        });
        let greatest = self.upper.map(|bound| {
            let units = rationals.get(bound.at) / grid;
            let whole = units.floor();
            if bound.open && whole == units {
                whole - &one
            } else {
                whole
            }
        });

        // They are tried from zero outwards: one counter goes up and one goes down. Without
        // an end to stop at, a counter soon finds a number that none of the divisors divides,
        // since none of them divides the number after a multiple of them all.
        let mut up = least.clone().map_or(zero.clone(), |least| least.max(zero));
        let mut down = greatest
            .clone()
            .map_or(-&one, |greatest| greatest.min(-&one));
        loop {
            let may_go_up = greatest.as_ref().is_none_or(|greatest| up <= *greatest);
            let may_go_down = least.as_ref().is_none_or(|least| down >= *least);
            let goes_up = match (may_go_up, may_go_down) {
                (false, false) => return Ok(None),
                (true, true) => up <= -&down,
                (goes_up, _) => goes_up,
            };
            budget.charge(1)?;
            let tried = if goes_up {
                let next = &up + &one;
                std::mem::replace(&mut up, next)
            } else {
                let next = &down - &one;
                std::mem::replace(&mut down, next)
            };
            if divisors
                .iter()
                .all(|divisor| !(&tried / divisor).is_integer())
            {
                return Ok(Some(tried * grid));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{Value, json};

    use super::*;
    use crate::rational::{read, shown};
    use crate::testing::Random;

    /// What a test says about a number, with the value as a keyword would hold it.
    #[derive(Debug, Clone, Copy)]
    enum Said {
        AtLeast(f64),
        Above(f64),
        AtMost(f64),
        Below(f64),
        MultipleOf(f64),
        NoMultipleOf(f64),
    }
    use Said::{Above, AtLeast, AtMost, Below, MultipleOf, NoMultipleOf};

    fn rational(value: f64) -> Rational {
        read(json!(value).as_number().unwrap()).unwrap()
    }

    fn left(rationals: &mut Rationals, said: &[Said]) -> Numbers {
        let mut numbers = Numbers::default();
        for said in said {
            let mut id = |value: f64| rationals.intern(rational(value));
            let says = match *said {
                AtLeast(at) => Says::AtLeast(id(at)),
                Above(at) => Says::Above(id(at)),
                AtMost(at) => Says::AtMost(id(at)),
                Below(at) => Says::Below(id(at)),
                MultipleOf(of) => Says::MultipleOf(id(of)),
                NoMultipleOf(of) => Says::NoMultipleOf(id(of)),
            };
            numbers.take(rationals, says);
        }
        numbers
    }

    /// The member of the numbers that are left, as text, and `None` if none is left.
    fn member(said: &[Said]) -> Option<String> {
        let rationals = &mut Rationals::default();
        let numbers = left(rationals, said);
        let budget = &mut Budget::new(100_000);
        let member = numbers.member(rationals, budget).unwrap();
        assert_eq!(
            numbers.is_empty(rationals, budget).unwrap(),
            member.is_none(),
            "{said:?}"
        );
        member.as_ref().map(shown)
    }

    fn is(text: &str) -> Option<String> {
        Some(text.to_owned())
    }

    /// Whether a number satisfies everything that was said.
    fn satisfies(number: &Rational, said: &[Said]) -> bool {
        let multiple = |of: f64| (number / rational(of)).is_integer();
        said.iter().all(|said| match *said {
            AtLeast(at) => *number >= rational(at),
            Above(at) => *number > rational(at),
            AtMost(at) => *number <= rational(at),
            Below(at) => *number < rational(at),
            MultipleOf(of) => multiple(of),
            NoMultipleOf(of) => !multiple(of),
        })
    }

    /// The same for a number of eighths, with every value in eighths too.
    fn eighths_satisfy(number: i64, said: &[Said]) -> bool {
        let eighths = |value: f64| (value * 8.0) as i64;
        said.iter().all(|said| match *said {
            AtLeast(at) => number >= eighths(at),
            Above(at) => number > eighths(at),
            AtMost(at) => number <= eighths(at),
            Below(at) => number < eighths(at),
            MultipleOf(of) => number % eighths(of) == 0,
            NoMultipleOf(of) => number % eighths(of) != 0,
        })
    }

    #[test]
    fn an_interval_gives_the_number_with_the_fewest_digits() {
        assert_eq!(member(&[]), is("0"));
        assert_eq!(member(&[AtLeast(-3.0), AtMost(8.0)]), is("0"));
        assert_eq!(member(&[AtLeast(5.0)]), is("5"));
        assert_eq!(member(&[Above(5.0)]), is("6"));
        assert_eq!(member(&[AtMost(-5.0)]), is("-5"));
        assert_eq!(member(&[Below(0.0)]), is("-1"));
        assert_eq!(member(&[Above(0.0), Below(1.0)]), is("0.1"));
        assert_eq!(member(&[AtLeast(17.0), AtMost(123.0)]), is("100"));
        assert_eq!(member(&[AtLeast(17.0), Below(100.0)]), is("20"));
        assert_eq!(member(&[AtLeast(4.56789), AtMost(4.5679)]), is("4.5679"));
        assert_eq!(member(&[Above(0.001), Below(0.002)]), is("0.0011"));
        assert_eq!(member(&[Above(1e30)]), is(&format!("2{}", "0".repeat(30))));
        assert_eq!(member(&[AtLeast(2.5), AtMost(2.5)]), is("2.5"));
        // The later of two ends counts, and an open end over a closed one at the same place.
        assert_eq!(member(&[AtLeast(5.0), AtLeast(7.0), AtLeast(6.0)]), is("7"));
        assert_eq!(member(&[AtLeast(7.0), Above(7.0), AtLeast(7.0)]), is("8"));
        assert_eq!(member(&[AtMost(-7.0), Below(-7.0)]), is("-8"));
    }

    #[test]
    fn an_interval_without_a_number_is_empty() {
        assert_eq!(member(&[AtLeast(5.0), AtMost(3.0)]), None);
        assert_eq!(member(&[Above(5.0), AtMost(5.0)]), None);
        assert_eq!(member(&[AtLeast(5.0), Below(5.0)]), None);
        assert_eq!(member(&[Above(5.0), Below(5.0)]), None);
    }

    #[test]
    fn a_multiple_is_looked_for_in_the_interval() {
        assert_eq!(member(&[MultipleOf(1.0)]), is("0"));
        assert_eq!(member(&[MultipleOf(7.0), AtLeast(10.0)]), is("14"));
        assert_eq!(
            member(&[MultipleOf(7.0), Above(10.0), Below(70.0)]),
            is("14")
        );
        assert_eq!(member(&[MultipleOf(7.0), AtMost(-10.0)]), is("-14"));
        assert_eq!(
            member(&[MultipleOf(0.5), Above(0.0), Below(1.0)]),
            is("0.5")
        );
        assert_eq!(member(&[MultipleOf(1.0), Above(0.0), Below(1.0)]), None);
        assert_eq!(member(&[MultipleOf(7.0), AtLeast(1.0), AtMost(6.0)]), None);
        assert_eq!(
            member(&[MultipleOf(7.0), AtLeast(7.0), AtMost(7.0)]),
            is("7")
        );
        assert_eq!(member(&[MultipleOf(7.0), Above(7.0), Below(14.0)]), None);
        // A coarse grid gives a number that a JSON value holds, where the least multiple in
        // the interval has thirty digits.
        let large = format!("14{}", "0".repeat(29));
        assert_eq!(member(&[MultipleOf(7.0), AtLeast(1e30)]), is(&large));
    }

    #[test]
    fn several_multiples_are_the_least_that_is_a_multiple_of_each() {
        assert_eq!(
            member(&[MultipleOf(4.0), MultipleOf(6.0), Above(0.0)]),
            is("12")
        );
        assert_eq!(
            member(&[MultipleOf(0.5), MultipleOf(0.75), Above(0.0)]),
            is("1.5")
        );
        assert_eq!(
            member(&[MultipleOf(0.3), MultipleOf(0.7), Above(0.0)]),
            is("2.1")
        );
        // One that is a multiple of the other adds nothing.
        let said = [MultipleOf(0.0001), MultipleOf(0.0075), Above(0.0)];
        assert_eq!(member(&said), is("0.0075"));
        let said = [MultipleOf(6.0), MultipleOf(4.0), Above(0.0), Below(12.0)];
        assert_eq!(member(&said), None);
    }

    #[test]
    fn a_number_that_is_no_multiple_is_looked_for() {
        assert_eq!(member(&[NoMultipleOf(1.0)]), is("0.1"));
        assert_eq!(member(&[NoMultipleOf(0.1)]), is("0.01"));
        assert_eq!(member(&[NoMultipleOf(2.0)]), is("1"));
        assert_eq!(member(&[NoMultipleOf(2.0), AtMost(0.0)]), is("-1"));
        assert_eq!(
            member(&[NoMultipleOf(0.5), AtLeast(0.0), AtMost(0.0)]),
            None
        );
        assert_eq!(
            member(&[NoMultipleOf(2.0), AtLeast(3.0), AtMost(3.0)]),
            is("3")
        );
        assert_eq!(
            member(&[NoMultipleOf(2.0), AtLeast(4.0), AtMost(4.0)]),
            None
        );
        // Zero is a multiple of everything.
        assert_eq!(member(&[MultipleOf(3.0), NoMultipleOf(7.0)]), is("3"));
        assert_eq!(
            member(&[MultipleOf(1.0), NoMultipleOf(2.0), NoMultipleOf(3.0)]),
            is("1")
        );
        let said = [
            MultipleOf(1.0),
            NoMultipleOf(2.0),
            NoMultipleOf(3.0),
            Above(1.0),
        ];
        assert_eq!(member(&said), is("5"));
        let said = [
            MultipleOf(1.0),
            NoMultipleOf(2.0),
            NoMultipleOf(3.0),
            Above(1.0),
            Below(5.0),
        ];
        assert_eq!(member(&said), None);
        // Every multiple of the one is a multiple of the other.
        assert_eq!(member(&[MultipleOf(0.1), NoMultipleOf(0.01)]), None);
        assert_eq!(
            member(&[MultipleOf(6.0), NoMultipleOf(2.0), NoMultipleOf(5.0)]),
            None
        );
        assert_eq!(
            member(&[MultipleOf(0.01), NoMultipleOf(0.1), Above(0.0)]),
            is("0.01")
        );
    }

    #[test]
    fn the_search_is_as_long_as_the_interval_at_most() {
        // Every whole number from 2 to 30 is a multiple of one of the ten: the search ends
        // where the interval does, and with no end it goes on to 31.
        let primes = [2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0, 19.0, 23.0, 29.0];
        let mut said = vec![MultipleOf(1.0), Above(1.0)];
        said.extend(primes.map(NoMultipleOf));
        assert_eq!(member(&said), is("31"));
        said.push(AtMost(30.0));
        assert_eq!(member(&said), None);

        let rationals = &mut Rationals::default();
        let numbers = left(rationals, &said);
        for (budget, enough) in [(28, false), (29, true)] {
            let budget = &mut Budget::new(budget);
            assert_eq!(numbers.is_empty(rationals, budget).is_ok(), enough);
        }
        // A search with no end is not long either, however many numbers are left.
        let said = [MultipleOf(1e-300), NoMultipleOf(2e-300), Above(1e300)];
        let numbers = left(rationals, &said);
        let budget = &mut Budget::new(u64::MAX);
        assert!(!numbers.is_empty(rationals, budget).unwrap());
        assert!(budget.spent() < 10, "{}", budget.spent());
    }

    #[test]
    fn a_member_satisfies_what_was_said_and_none_means_that_nothing_does() {
        let random = &mut Random(3);
        // Every value is a multiple of a quarter, and so is every member that a search on
        // quarters would find.
        let values = [-2.5, -1.0, 0.0, 0.25, 0.5, 1.0, 1.5, 3.0, 4.0];
        let multiples = [0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 3.0];
        let (mut found, mut empty) = (0, 0);
        for _ in 0..5_000 {
            let said: Vec<Said> = (0..random.below(6))
                .map(|_| {
                    let (value, multiple) = (random.pick(&values), random.pick(&multiples));
                    match random.below(6) {
                        0 => AtLeast(value),
                        1 => Above(value),
                        2 => AtMost(value),
                        3 => Below(value),
                        4 => MultipleOf(multiple),
                        _ => NoMultipleOf(multiple),
                    }
                })
                .collect();
            let rationals = &mut Rationals::default();
            let numbers = left(rationals, &said);
            let budget = &mut Budget::new(100_000);
            let member = numbers.member(rationals, budget).unwrap();
            assert_eq!(
                numbers.is_empty(rationals, budget).unwrap(),
                member.is_none(),
                "{said:?}"
            );
            match member {
                Some(member) => {
                    assert!(satisfies(&member, &said), "{member} for {said:?}");
                    found += 1;
                }
                // Whatever is left is between -30 and 30, or there are others like it there:
                // the multiples repeat every 6. An eighth is a multiple of nothing.
                None => {
                    let mut eighths = -240..=240;
                    let left = eighths.find(|number| eighths_satisfy(*number, &said));
                    assert_eq!(left, None, "in eighths, for {said:?}");
                    empty += 1;
                }
            }
        }
        assert!(found > 1_000 && empty > 1_000, "{found} {empty}");
    }

    #[test]
    fn a_member_is_a_number_that_json_holds_where_there_is_one() {
        let written = |said: &[Said]| -> Option<Value> {
            let rationals = &mut Rationals::default();
            let numbers = left(rationals, said);
            let member = numbers
                .member(rationals, &mut Budget::new(100_000))
                .unwrap();
            crate::rational::written(&member?).map(Value::Number)
        };
        assert_eq!(written(&[Above(1e30)]), Some(json!(2e30)));
        assert_eq!(
            written(&[Below(-1e300), MultipleOf(0.5)]),
            Some(json!(-1.5e300))
        );
        assert_eq!(written(&[AtLeast(0.1), AtMost(0.3)]), Some(json!(0.1)));
        // Between two floats that are next to each other, every number has more digits than
        // a float holds.
        let narrow = [Above(1e30), Below(1.000_000_000_000_000_2e30)];
        assert_eq!(written(&narrow), None);
    }
}
