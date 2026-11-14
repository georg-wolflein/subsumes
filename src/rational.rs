//! Exact numbers.
//!
//! A number of a schema is read as the decimal that it is printed as. For a float that is the
//! shortest decimal that gives the same float back, so `0.1` is a tenth and `0.0075` is a
//! multiple of `0.0001`, which the two floats themselves are not. Every such decimal is a
//! ratio of two integers, and the integers are of any size: nothing is rounded and nothing
//! overflows.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive};
use serde_json::Number;

/// A number, as the ratio of two integers.
pub(crate) type Rational = BigRational;

/// The number that a JSON number stands for.
///
/// A `Number` holds a `u64`, an `i64` or a finite float, and prints each as a decimal with
/// an exponent at most.
pub(crate) fn exact(number: &Number) -> Rational {
    let text = number.to_string();
    let (digits, exponent) = match text.split_once(['e', 'E']) {
        Some((digits, exponent)) => (digits, exponent.parse().expect("an exponent is whole")),
        None => (text.as_str(), 0_i64),
    };
    let (whole, fraction) = digits.split_once('.').unwrap_or((digits, ""));
    let unscaled: BigInt = [whole, fraction].concat().parse().expect("digits");
    // Each digit behind the point is one power of ten less.
    let exponent = exponent - i64::try_from(fraction.len()).expect("a number is short");
    let scale = power_of_ten(exponent.unsigned_abs());
    if exponent < 0 {
        Rational::new(unscaled, scale)
    } else {
        Rational::from_integer(unscaled * scale)
    }
}

/// The JSON number that stands for exactly this number, if there is one: an integer that an
/// `i64` or a `u64` holds, or else a float that is printed as this number.
///
/// There is none for a number with more digits than a float keeps, such as a whole number of
/// thirty digits that does not end in zeros, or one that lies between two floats next to
/// each other.
pub(crate) fn written(number: &Rational) -> Option<Number> {
    if number.is_integer() {
        let whole = number.numer();
        if let Some(whole) = whole.to_i64() {
            return Some(whole.into());
        }
        if let Some(whole) = whole.to_u64() {
            return Some(whole.into());
        }
    }
    // The float nearest to the number is the only one that could be printed as it.
    let nearest: f64 = decimal(number)?.parse().ok()?;
    let nearest = Number::from_f64(nearest)?;
    (exact(&nearest) == *number).then_some(nearest)
}

/// The number as text for a term: as the JSON number, or as a ratio where there is none.
pub(crate) fn shown(number: &Rational) -> String {
    written(number).map_or_else(|| number.to_string(), |written| written.to_string())
}

/// The number in digits with an exponent, such as `-75e-4`. `None` for a number whose
/// decimal does not end, such as a third.
fn decimal(number: &Rational) -> Option<String> {
    // A decimal ends when the denominator has no prime factor but two and five.
    let (mut rest, mut places) = (number.denom().clone(), [0_u64; 2]);
    for (factor, count) in [2, 5].map(BigInt::from).iter().zip(&mut places) {
        while rest.is_multiple_of(factor) {
            rest /= factor;
            *count += 1;
        }
    }
    if !rest.is_one() {
        return None;
    }
    let places = places[0].max(places[1]);
    let digits = number.numer() * power_of_ten(places) / number.denom();
    Some(format!("{digits}e-{places}"))
}

fn power_of_ten(exponent: u64) -> BigInt {
    let exponent = u32::try_from(exponent).expect("a number is short");
    BigInt::from(10).pow(exponent)
}

/// The least number that both are multiples of. Both are more than zero.
pub(crate) fn common_multiple(a: &Rational, b: &Rational) -> Rational {
    // Both are in lowest terms, so this is too.
    Rational::new(a.numer().lcm(b.numer()), a.denom().gcd(b.denom()))
}

/// Whether a number is a multiple of another, which is more than zero.
pub(crate) fn is_multiple(number: &Rational, of: &Rational) -> bool {
    (number / of).is_integer()
}

#[cfg(test)]
pub(crate) mod testing {
    use super::*;

    /// The number that a decimal names, such as `"0.25"`.
    pub(crate) fn number(decimal: &str) -> Rational {
        exact(&decimal.parse().expect("a JSON number"))
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::testing::number;
    use super::*;
    use crate::testing::Random;

    fn ratio(numerator: i64, denominator: i64) -> Rational {
        Rational::new(numerator.into(), denominator.into())
    }

    fn of(value: &serde_json::Value) -> Rational {
        exact(value.as_number().expect("a number"))
    }

    #[test]
    fn a_number_is_the_decimal_that_it_is_printed_as() {
        assert_eq!(of(&json!(0)), ratio(0, 1));
        assert_eq!(of(&json!(-3)), ratio(-3, 1));
        assert_eq!(of(&json!(1.0)), ratio(1, 1));
        assert_eq!(of(&json!(-0.0)), ratio(0, 1));
        // A tenth, although the float is a little more.
        assert_eq!(of(&json!(0.1)), ratio(1, 10));
        assert_eq!(of(&json!(0.0075)), ratio(3, 400));
        assert_eq!(of(&json!(-2.5)), ratio(-5, 2));
        assert_eq!(of(&json!(1.5e-7)), ratio(3, 20_000_000));
        assert_eq!(of(&json!(123_456.789)), ratio(123_456_789, 1000));
        // What an integer type holds is the number that was written.
        assert_eq!(of(&json!(u64::MAX)).to_string(), "18446744073709551615");
        assert_eq!(of(&json!(i64::MIN)).to_string(), "-9223372036854775808");
        // The largest float, the smallest, and a power of ten.
        let largest = of(&json!(f64::MAX)).to_string();
        assert!(largest.starts_with("17976931348623157") && largest.len() == 309);
        let smallest = of(&json!(5e-324));
        assert!(smallest.numer() == &BigInt::from(1) && smallest.denom().to_string().len() == 324);
        assert_eq!(of(&json!(1e300)).to_string().len(), 301);
    }

    #[test]
    fn a_number_is_written_as_an_integer_or_as_the_float_that_names_it() {
        let text = |number: &Rational| written(number).map(|written| written.to_string());
        let some = |text: &str| Some(text.to_owned());
        assert_eq!(text(&ratio(0, 1)), some("0"));
        assert_eq!(text(&ratio(-7, 1)), some("-7"));
        assert_eq!(text(&of(&json!(u64::MAX))), some("18446744073709551615"));
        assert_eq!(text(&of(&json!(i64::MIN))), some("-9223372036854775808"));
        assert_eq!(text(&ratio(1, 10)), some("0.1"));
        assert_eq!(text(&ratio(3, 400)), some("0.0075"));
        assert_eq!(text(&ratio(-5, 2)), some("-2.5"));
        assert_eq!(text(&number("1e30")), some("1e+30"));
        assert_eq!(text(&of(&json!(f64::MAX))), some("1.7976931348623157e+308"));
        assert_eq!(text(&of(&json!(5e-324))), some("5e-324"));

        // A third has no decimal that ends.
        assert_eq!(text(&ratio(1, 3)), None);
        // One more than the largest `u64`: the float nearest to it is printed with zeros
        // where it has other digits.
        let beyond = of(&json!(u64::MAX)) + ratio(1, 1);
        assert_eq!(text(&beyond), None);
        assert_eq!(
            text(&number("18446744073709552000")),
            some("1.8446744073709552e+19")
        );
        // Between a tenth and the next float, and above the largest float.
        assert_eq!(text(&(ratio(1, 10) + number("1e-17"))), None);
        assert_eq!(
            text(&(ratio(1, 10) + number("2e-17"))),
            some("0.10000000000000002")
        );
        assert_eq!(text(&(of(&json!(f64::MAX)) + ratio(1, 1))), None);
        assert_eq!(text(&(number("1e300") * number("1e100"))), None);
    }

    #[test]
    fn a_term_shows_a_number_as_json_does_where_it_can() {
        assert_eq!(shown(&ratio(1, 100)), "0.01");
        assert_eq!(shown(&ratio(5, 1)), "5");
        assert_eq!(shown(&ratio(1, 3)), "1/3");
    }

    #[test]
    fn every_number_of_a_value_comes_back_as_it_was() {
        let random = &mut Random(7);
        for _ in 0..20_000 {
            let value = match random.below(4) {
                0 => json!(random.next()),
                1 => json!(random.next() as i64),
                // Any float at all, by its bits.
                2 => json!(f64::from_bits(random.next())),
                _ => json!((random.next() % 2_000_001) as f64 / 1000.0 - 1000.0),
            };
            // A float that is not finite is no JSON number.
            let Some(before) = value.as_number() else {
                continue;
            };
            let after = written(&exact(before)).expect("the number was written before");
            assert_eq!(exact(&after), exact(before), "{before}");
            // A whole float comes back as an integer where one holds it, and as itself else.
            if !(before.is_f64() && exact(before).is_integer()) {
                assert_eq!(after.to_string(), before.to_string());
            }
        }
    }

    #[test]
    fn the_least_common_multiple_of_two_ratios() {
        let common = |a: &str, b: &str| common_multiple(&number(a), &number(b));
        assert_eq!(common("2", "3"), number("6"));
        assert_eq!(common("4", "6"), number("12"));
        assert_eq!(common("0.01", "0.0075"), number("0.03"));
        assert_eq!(common("1.5", "1"), number("3"));
        assert_eq!(common("0.5", "0.25"), number("0.5"));
        assert_eq!(common_multiple(&ratio(1, 2), &ratio(1, 3)), ratio(1, 1));

        assert!(is_multiple(&number("0.0075"), &number("0.0001")));
        assert!(is_multiple(&number("-6"), &number("1.5")));
        assert!(is_multiple(&number("0"), &number("7")));
        assert!(!is_multiple(&number("0.1"), &number("0.03")));
        assert!(!is_multiple(&number("1"), &number("2")));
    }
}
