//! Counterexamples: an instance for a branch that the engine could not refute.

use serde_json::{Number, Value, json};

use crate::canonical::number::Numbers;
use crate::context::{Budget, Exhausted};
use crate::decimal::{Decimal, written};
use crate::term::InstanceType;

/// An instance of a type about which a branch says nothing else, except which booleans and
/// which numbers it may be.
///
/// `None` for a number when the branch leaves only numbers that the library cannot give.
///
/// # Errors
///
/// When the budget does not cover the search for a number.
pub(crate) fn instance(
    kind: InstanceType,
    may_be_true: bool,
    numbers: &Numbers,
    budget: &mut Budget,
) -> Result<Option<Value>, Exhausted> {
    Ok(Some(match kind {
        InstanceType::Null => Value::Null,
        InstanceType::Boolean => Value::Bool(may_be_true),
        InstanceType::Number => return Ok(number(numbers, budget)?.map(Value::Number)),
        InstanceType::String => json!(""),
        InstanceType::Array => json!([]),
        InstanceType::Object => json!({}),
    }))
}

/// A number of the set, the plainest there is: the whole number nearest zero. A set without
/// a whole number gives its multiple nearest zero, or if it is a multiple of nothing, its
/// decimal with the fewest places.
///
/// `None` if the set is empty, and for a number that the library cannot give: one beyond the
/// range that the engine models, or one that no JSON number stands for.
fn number(numbers: &Numbers, budget: &mut Budget) -> Result<Option<Number>, Exhausted> {
    if numbers.is_beyond() {
        // Of a set that holds more than was asked for, zero is known to be asked for: it is
        // a multiple of whatever was too large to keep.
        let zero = numbers.contains(Decimal::ZERO).then_some(Decimal::ZERO);
        return Ok(zero.and_then(written));
    }
    let found = match numbers.nearest_zero(Decimal::ONE, budget)? {
        Some(whole) => Some(whole),
        None => match (numbers.multiple(), numbers.point()) {
            (Some(multiple), _) => numbers.nearest_zero(multiple, budget)?,
            (None, Some(only)) => numbers.contains(only).then_some(only),
            (None, None) => shortest(numbers, budget)?,
        },
    };
    Ok(found.and_then(written))
}

/// The decimal with the fewest places in a set that is a multiple of nothing and whose
/// interval is more than a point, and of those the one nearest zero.
fn shortest(numbers: &Numbers, budget: &mut Budget) -> Result<Option<Decimal>, Exhausted> {
    if numbers.is_empty(budget)? {
        return Ok(None);
    }
    // A unit has a place more than any number that was asked. So among the numbers with
    // that many places, the interval holds one that is no multiple of an excluded number
    // and that was not removed.
    for place in 1..=Decimal::PLACES {
        budget.charge(1)?;
        let found = numbers.nearest_zero(Decimal::place(place), budget)?;
        if found.is_some() {
            return Ok(found);
        }
    }
    // The last place has one, so this is not reached.
    Ok(None)
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
        let budget = &mut Budget::new(0);
        let all = Numbers::default();
        let mut of = |kind, may_be_true| instance(kind, may_be_true, &all, budget).unwrap();
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
        // The largest whole numbers of the range are integers of 64 bits.
        assert_eq!(given(&[">= 1e19"]), some("10000000000000000000"));
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
        // Between two numbers with as many places as a schema may give them lies one with
        // a place more.
        assert_eq!(given(&["> 0", "< 1e-16"]), some("1e-17"));
        assert_eq!(given(&["not mof 1e-16", "> 0", "< 1e-15"]), some("1e-17"));
    }

    #[test]
    fn a_set_without_a_number_gives_none() {
        assert_eq!(given(&[">= 1", "< 1"]), None);
        assert_eq!(given(&["mof 1", "> 0", "< 1"]), None);
        assert_eq!(given(&["mof 2", "not mof 1"]), None);
        assert_eq!(given(&["not mof 1", ">= 2", "<= 2"]), None);
    }

    #[test]
    fn a_number_that_the_library_cannot_give_is_not_given() {
        // Beyond the range: every number above the largest that it holds.
        assert_eq!(given(&["> 18446744073709551615"]), None);
        assert_eq!(
            given(&["mof 18446744073709551557", "> 18446744073709551557"]),
            None
        );
        // Between two floats that are next to each other. The floats of this size are whole.
        assert_eq!(given(&["> 9007199254740991", "< 9007199254740992"]), None);
        assert_eq!(
            given(&["mof 0.5", "not mof 1", ">= 9007199254740991"]),
            None
        );
        // A whole number below the least `i64` is given if a float holds it. The search
        // does not go on to one where the nearest is none.
        assert_eq!(given(&["<= -1e19"]), some("-1e+19"));
        assert_eq!(given(&["< -9223372036854775808"]), None);
    }

    #[test]
    fn of_a_set_that_is_wider_than_was_asked_only_zero_is_given() {
        let asked = ["mof 18446744073709551557", "mof 3"];
        assert_eq!(given(&asked), some("0"));
        assert_eq!(given(&[asked[0], asked[1], ">= -5"]), some("0"));
        assert_eq!(given(&[asked[0], asked[1], "> 0"]), None);
        assert_eq!(given(&[asked[0], asked[1], "!= 0"]), None);
        assert_eq!(given(&[asked[0], asked[1], "not mof 7"]), None);
    }

    #[test]
    fn the_search_for_a_decimal_costs_a_step_for_each_place_and_candidate() {
        let search = |asked: &[&str], budget: u64| {
            let mut budget = Budget::new(budget);
            let found = number(&numbers(asked), &mut budget);
            (
                found.map(|found| found.map(|found| found.to_string())),
                budget.spent(),
            )
        };
        // Zero is the first whole number that is looked at.
        assert_eq!(search(&[], 1), (Ok(some("0")), 1));
        // No whole number is in the interval, and the first tenth is.
        assert_eq!(search(&["> 0", "< 1"], 2), (Ok(some("0.1")), 2));
        // Two places without a decimal in the interval, and the third has one.
        assert_eq!(search(&["> 0.001", "< 0.01"], 4), (Ok(some("0.002")), 4));
        assert_eq!(search(&["> 0.001", "< 0.01"], 3), (Err(Exhausted), 3));
        // No number has more places than a unit, so the search is never long.
        let (found, spent) = search(&["> 0", "< 1e-16"], u64::MAX);
        assert_eq!(found, Ok(some("1e-17")));
        assert!(spent <= 2 * u64::from(Decimal::PLACES), "{spent}");
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
