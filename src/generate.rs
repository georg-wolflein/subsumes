//! Counterexamples: an instance for a branch that the engine could not refute.

use num_bigint::BigInt;
use num_traits::One;
use serde_json::{Number, Value, json};

use crate::canonical::number::Numbers;
use crate::canonical::string::Strings;
use crate::context::{Budget, Exhausted};
use crate::language::Languages;
use crate::rational::{Rational, written};
use crate::term::InstanceType;

/// What a branch leaves of the types that it says more about than that an instance is of
/// them.
pub(crate) struct Left<'b> {
    /// Whether an instance may be `true`. If not, it may be `false`.
    pub may_be_true: bool,
    pub numbers: &'b Numbers,
    pub strings: &'b Strings,
}

/// An instance of a type about which a branch says nothing else, except which booleans,
/// which numbers and which strings it may be.
///
/// `None` for a number when the branch leaves only numbers that no JSON number stands for.
///
/// # Errors
///
/// When the budget does not cover the search for a number or for a string.
pub(crate) fn instance(
    kind: InstanceType,
    left: &Left,
    languages: &mut Languages,
    budget: &mut Budget,
) -> Result<Option<Value>, Exhausted> {
    Ok(Some(match kind {
        InstanceType::Null => Value::Null,
        InstanceType::Boolean => Value::Bool(left.may_be_true),
        InstanceType::Number => return Ok(number(left.numbers, budget)?.map(Value::Number)),
        // The shortest string that is left, and of several one of plain characters.
        InstanceType::String => {
            let shortest = left.strings.shortest(languages, budget)?;
            return Ok(shortest.map(Value::String));
        }
        InstanceType::Array => json!([]),
        InstanceType::Object => json!({}),
    }))
}

/// A number of the set, the plainest that the search comes by: the whole number nearest
/// zero. A set without a whole number gives its multiple nearest zero, or if it is a
/// multiple of nothing, its decimal with the fewest places.
///
/// `None` if the set is empty, or if no JSON number stands for the number that was found
/// and for none of the rounder ones that are tried in its place. The search is not all
/// there could be: a set may hold a number that could be written and that is not found.
fn number(numbers: &Numbers, budget: &mut Budget) -> Result<Option<Number>, Exhausted> {
    let Some(whole) = numbers.nearest_zero(&Rational::one(), budget)? else {
        let found = match (numbers.multiple(), numbers.point()) {
            (Some(multiple), _) => numbers.nearest_zero(multiple, budget)?,
            (None, Some(only)) => numbers.contains(only).then(|| only.clone()),
            (None, None) => shortest(numbers, budget)?,
        };
        // A number with more places has more digits, not fewer, so no other is tried.
        return Ok(found.as_ref().and_then(written));
    };
    match written(&whole) {
        Some(written) => Ok(Some(written)),
        None => rounder(numbers, &whole, budget),
    }
}

/// A whole number of the set that a float holds: the multiple of a power of two that is
/// nearest zero, for the least power that gives one which a JSON number stands for.
///
/// This is for a set whose whole number nearest zero is none that an integer or a float
/// holds, as the one after 2^64 is. A float this large holds 53 digits in base two and zeros
/// after them, so the search begins with as many zeros as such a number has.
fn rounder(
    numbers: &Numbers,
    whole: &Rational,
    budget: &mut Budget,
) -> Result<Option<Number>, Exhausted> {
    let spare = whole
        .numer()
        .bits()
        .saturating_sub(u64::from(f64::MANTISSA_DIGITS));
    let Ok(spare) = u32::try_from(spare) else {
        return Ok(None);
    };
    let two = Rational::from_integer(2.into());
    let mut step = Rational::from_integer(BigInt::from(2).pow(spare));
    // No float is as large as the power of two after these.
    for _ in spare..=f64::MAX_EXP.unsigned_abs() {
        budget.charge(1)?;
        // The multiples of a power of two are among those of the power before, so where
        // one has none in the set, neither has the next.
        let Some(found) = numbers.nearest_zero(&step, budget)? else {
            break;
        };
        if let Some(written) = written(&found) {
            return Ok(Some(written));
        }
        step *= &two;
    }
    Ok(None)
}

/// The decimal with the fewest places in a set that is a multiple of nothing and whose
/// interval is more than a point, and of those the one nearest zero.
fn shortest(numbers: &Numbers, budget: &mut Budget) -> Result<Option<Rational>, Exhausted> {
    if numbers.is_empty(budget)? {
        return Ok(None);
    }
    let tenth = Rational::new(1.into(), 10.into());
    let mut step = Rational::one();
    // With enough places a decimal is in the interval. The excluded numbers lie apart, so
    // with a place more there is one that is not excluded.
    loop {
        budget.charge(1)?;
        step *= &tenth;
        if let Some(found) = numbers.nearest_zero(&step, budget)? {
            return Ok(Some(found));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::canonical::number::testing::{Asked, numbers};
    use crate::testing::Random;

    /// The number that is given for a set, as text.
    fn given(asked: &[&str]) -> Option<String> {
        let found = number(&numbers(asked), &mut Budget::new(u64::MAX)).unwrap();
        found.map(|found| found.to_string())
    }

    fn some(text: &str) -> Option<String> {
        Some(text.to_owned())
    }

    #[test]
    fn a_type_without_anything_else_gives_its_plainest_instance() {
        let (budget, languages) = (&mut Budget::new(0), &mut Languages::default());
        let (numbers, strings) = (&Numbers::default(), &Strings::default());
        let mut of = |kind, may_be_true| {
            let left = Left {
                may_be_true,
                numbers,
                strings,
            };
            instance(kind, &left, languages, budget).unwrap()
        };
        assert_eq!(of(InstanceType::Null, true), Some(json!(null)));
        assert_eq!(of(InstanceType::Boolean, true), Some(json!(true)));
        assert_eq!(of(InstanceType::Boolean, false), Some(json!(false)));
        assert_eq!(of(InstanceType::String, true), Some(json!("")));
        assert_eq!(of(InstanceType::Array, true), Some(json!([])));
        assert_eq!(of(InstanceType::Object, true), Some(json!({})));
    }

    #[test]
    fn a_number_is_whole_and_near_zero_where_it_may_be() {
        assert_eq!(given(&[]), some("0"));
        assert_eq!(given(&[">= -5", "<= 5"]), some("0"));
        assert_eq!(given(&[">= 3"]), some("3"));
        assert_eq!(given(&["> 3"]), some("4"));
        assert_eq!(given(&["<= -2.5"]), some("-3"));
        assert_eq!(given(&[">= 2.5", "< 4"]), some("3"));
        assert_eq!(given(&["mof 1.5", ">= 1"]), some("3"));
        assert_eq!(given(&["mof 7", "not mof 2", ">= 1"]), some("7"));
        assert_eq!(given(&["not mof 2"]), some("1"));
        // A number of thirty digits is a float, and one of twenty an integer.
        assert_eq!(given(&[">= 1e30"]), some("1e+30"));
        assert_eq!(
            given(&["> 18446744073709551614"]),
            some("18446744073709551615")
        );
        assert_eq!(
            given(&["< -9223372036854775807"]),
            some("-9223372036854775808")
        );
    }

    #[test]
    fn without_a_whole_number_it_is_the_multiple_or_the_shortest_decimal() {
        assert_eq!(given(&["mof 0.25", "> 0", "< 1"]), some("0.25"));
        assert_eq!(given(&["mof 0.25", "not mof 0.5", "< 0"]), some("-0.25"));
        assert_eq!(given(&["mof 0.01", "> 2", "< 3"]), some("2.01"));
        assert_eq!(given(&["> 0", "< 1"]), some("0.1"));
        assert_eq!(given(&["> -1", "< 0"]), some("-0.1"));
        assert_eq!(given(&["> 0.25", "< 0.35"]), some("0.3"));
        assert_eq!(given(&["> 0.5", "< 0.6"]), some("0.51"));
        assert_eq!(given(&["> 0.001", "< 0.002"]), some("0.0011"));
        assert_eq!(given(&["not mof 1"]), some("0.1"));
        assert_eq!(given(&["not mof 0.1", "> 0", "< 1"]), some("0.01"));
        assert_eq!(
            given(&["not mof 1", "not mof 0.1", "not mof 0.03"]),
            some("0.01")
        );
        // One point is that point, also where it is far from whole.
        assert_eq!(given(&[">= 2.5", "<= 2.5"]), some("2.5"));
        assert_eq!(given(&[">= 0.0075", "<= 0.0075"]), some("0.0075"));
    }

    #[test]
    fn a_set_without_a_number_gives_none() {
        assert_eq!(given(&[">= 1", "< 1"]), None);
        assert_eq!(given(&["mof 1", "> 0", "< 1"]), None);
        assert_eq!(given(&["mof 2", "not mof 1"]), None);
        assert_eq!(given(&["not mof 1", ">= 2", "<= 2"]), None);
    }

    #[test]
    fn a_number_that_no_json_number_stands_for_is_not_given() {
        // Between two floats that are next to each other.
        assert_eq!(given(&["> 0.1", "< 0.10000000000000002"]), None);
        // Above the largest float, and between two floats of thirty-one digits that are
        // next to each other.
        assert_eq!(given(&["> 1.7976931348623157e308"]), None);
        assert_eq!(given(&["> 1e30", "< 1.0000000000000002e30"]), None);
    }

    #[test]
    fn a_whole_number_that_no_float_holds_gives_way_to_one_that_a_float_holds() {
        // The whole number after 2^64 - 1 is 2^64, which a float holds.
        assert_eq!(
            given(&["> 18446744073709551615"]),
            some("1.8446744073709552e+19")
        );
        // The one after that is between two floats, and the next float is 4096 further.
        assert_eq!(
            given(&["> 18446744073709551616"]),
            some("1.8446744073709556e+19")
        );
        // After a float of thirty-one digits, the first number that is written is the next
        // float, which is 2^47 further.
        assert_eq!(given(&["> 1e30"]), some("1.0000000000000002e+30"));
        assert_eq!(given(&["< -1e30"]), some("-1.0000000000000002e+30"));
        // What else is asked holds for that number too.
        assert_eq!(given(&["> 1e30", "mof 7"]), some("1.0000000000000006e+30"));
        assert_eq!(
            given(&[">= 1e30", "not mof 1e30", "not mof 3"]),
            some("1.0000000000000003e+30")
        );
        // Every float of this size is a multiple of 2^47.
        assert_eq!(given(&["> 1e30", "not mof 140737488355328"]), None);
        assert_eq!(given(&["mof 0.01", "> 1e16", "< 10000000000000001"]), None);
    }

    #[test]
    fn the_search_for_a_decimal_costs_a_step_for_each_place() {
        let search = |asked: &[&str], budget: u64| {
            let found = number(&numbers(asked), &mut Budget::new(budget));
            found.map(|found| found.map(|found| found.to_string()))
        };
        // Two places without a decimal in the interval, and the third has one.
        assert_eq!(search(&["> 0.001", "< 0.01"], 100), Ok(some("0.002")));
        // The first decimal of this interval has three hundred places.
        assert_eq!(search(&["> 1e-300", "< 2e-300"], 10), Err(Exhausted));
    }

    #[test]
    fn a_set_gives_a_number_of_its_own_whenever_it_has_one() {
        let random = &mut Random(5);
        let mut given = 0;
        for _ in 0..20_000 {
            let asked = Asked::random(random);
            let budget = &mut Budget::new(1000);
            let is_empty = asked.numbers.is_empty(budget).unwrap();
            let found = number(&asked.numbers, budget).unwrap();
            assert_eq!(found.is_none(), is_empty, "{:?}", asked.numbers);
            if let Some(found) = found {
                let found = found.as_f64().unwrap();
                assert!(asked.holds(found), "{found} in {:?}", asked.numbers);
                given += 1;
            }
        }
        assert!(given > 10_000, "{given}");
    }
}
