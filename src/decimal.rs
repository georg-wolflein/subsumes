//! Exact numbers, within a range.
//!
//! A number of a schema is read as the decimal that it is printed as. For a float that is the
//! shortest decimal that gives the same float back, so `0.1` is a tenth and `0.0075` is a
//! multiple of `0.0001`, which the two floats themselves are not.
//!
//! The engine models the numbers of a range: those whose size is below 2^64 and that have at
//! most sixteen decimal places. That is every integer that a JSON value holds as an integer,
//! and the decimals that a schema is likely to hold. Such a number is a whole count of units
//! of 10^-17, and the count fits 128 bits with room to spare. So nothing is rounded, and the
//! arithmetic is that of integers. A keyword with a number outside the range is one that the
//! engine does not model.
//!
//! A unit is one place finer than a number of a schema. Between any two such numbers lies one
//! with a place more, and a counterexample may have to be that one.

use std::fmt;

use serde_json::Number;

/// A number of the range, as a whole count of units of 10^-17.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Decimal(i128);

/// The units in one.
const ONE: i128 = 10_i128.pow(Decimal::PLACES);
/// The units in 2^64. The size of a number is below it.
const LIMIT: i128 = (1 << 64) * ONE;

impl Decimal {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(ONE);
    /// The decimal places of a unit: one more than a number of a schema has at most.
    pub const PLACES: u32 = 17;

    /// The number that is a one at this decimal place and zeros elsewhere: a tenth for the
    /// first place. No place is finer than a unit.
    pub fn place(place: u32) -> Self {
        Self(ONE / 10_i128.pow(place))
    }

    pub fn units(self) -> i128 {
        self.0
    }

    /// The number of this many units, if it is within the range.
    pub fn of_units(units: i128) -> Option<Self> {
        (-LIMIT < units && units < LIMIT).then_some(Self(units))
    }

    /// This many times the number, if that is within the range.
    pub fn times(self, times: i128) -> Option<Self> {
        Self::of_units(self.0.checked_mul(times)?)
    }

    pub fn is_multiple_of(self, of: Self) -> bool {
        self.0 % of.0 == 0
    }

    /// The greatest number that both are multiples of. Both are more than zero.
    pub fn common_divisor(self, other: Self) -> Self {
        let (mut a, mut b) = (self.0, other.0);
        while b != 0 {
            (a, b) = (b, a % b);
        }
        Self(a)
    }

    /// The least number that is a multiple of both, if it is within the range. Both are more
    /// than zero.
    pub fn common_multiple(self, other: Self) -> Option<Self> {
        let common = (self.0 / self.common_divisor(other).0).checked_mul(other.0)?;
        Self::of_units(common)
    }
}

/// The number as a decimal, such as `-0.0075`.
impl fmt::Display for Decimal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let sign = if self.0 < 0 { "-" } else { "" };
        let (whole, fraction) = (self.0.abs() / ONE, self.0.abs() % ONE);
        if fraction == 0 {
            return write!(f, "{sign}{whole}");
        }
        let fraction = format!("{fraction:0places$}", places = Self::PLACES as usize);
        write!(f, "{sign}{whole}.{}", fraction.trim_end_matches('0'))
    }
}

/// The number that a JSON number stands for, if it is a number of a schema within the range:
/// one with a place less than a unit has.
///
/// A `Number` holds a `u64`, an `i64` or a finite float, and prints each as a decimal with
/// an exponent at most. With the feature of `serde_json` for numbers of any precision, which
/// another crate of a build may turn on, it may hold any decimal, and one that is too long
/// to read is outside the range like any other.
pub(crate) fn exact(number: &Number) -> Option<Decimal> {
    read(number).filter(|number| number.0 % 10 == 0)
}

/// The number that a JSON number stands for, if it is a whole count of units within the
/// range.
fn read(number: &Number) -> Option<Decimal> {
    named(&number.to_string())
}

/// The number that the text of a JSON number names, if it is a whole count of units within
/// the range.
fn named(text: &str) -> Option<Decimal> {
    let (digits, exponent) = match text.split_once(['e', 'E']) {
        Some((digits, exponent)) => (digits, exponent.parse::<i64>().ok()?),
        None => (text, 0),
    };
    let (whole, fraction) = digits.split_once('.').unwrap_or((digits, ""));
    let unscaled: i128 = [whole, fraction].concat().parse().ok()?;
    // Each digit behind the point is one power of ten less, and a unit is a few more.
    let places = i64::try_from(fraction.len()).ok()?;
    let power = exponent.checked_sub(places)? + i64::from(Decimal::PLACES);
    let scale = 10_i128.checked_pow(u32::try_from(power.unsigned_abs()).ok()?)?;
    let units = if power >= 0 {
        unscaled.checked_mul(scale)?
    } else if unscaled % scale == 0 {
        unscaled / scale
    } else {
        // The number has more places than a unit.
        return None;
    };
    Decimal::of_units(units)
}

/// The JSON number that stands for exactly this number, if there is one: an integer that an
/// `i64` or a `u64` holds, or else a float that is printed as this number.
///
/// There is none for a number with more digits than a float keeps, unless it is such an
/// integer: a number between two floats that are next to each other has none.
pub(crate) fn written(number: Decimal) -> Option<Number> {
    if number.0 % ONE == 0 {
        let whole = number.0 / ONE;
        if let Ok(whole) = i64::try_from(whole) {
            return Some(whole.into());
        }
        if let Ok(whole) = u64::try_from(whole) {
            return Some(whole.into());
        }
    }
    // The float nearest to the number is the only one that could be printed as it.
    let nearest: f64 = number.to_string().parse().ok()?;
    let nearest = Number::from_f64(nearest)?;
    (read(&nearest) == Some(number)).then_some(nearest)
}

#[cfg(test)]
pub(crate) mod testing {
    use super::*;

    /// The number of a schema that a decimal names, such as `"0.25"`.
    pub(crate) fn number(decimal: &str) -> Decimal {
        let number = decimal.parse().expect("a JSON number");
        exact(&number).expect("a number of a schema within the range")
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::testing::number;
    use super::*;
    use crate::testing::Random;

    fn of(value: &serde_json::Value) -> Option<Decimal> {
        exact(value.as_number().expect("a number"))
    }

    fn shown(value: &serde_json::Value) -> Option<String> {
        of(value).map(|number| number.to_string())
    }

    fn some(text: &str) -> Option<String> {
        Some(text.to_owned())
    }

    #[test]
    fn a_number_is_the_decimal_that_it_is_printed_as() {
        assert_eq!(of(&json!(0)), Some(Decimal::ZERO));
        assert_eq!(of(&json!(1)), Some(Decimal::ONE));
        assert_eq!(of(&json!(1.0)), Some(Decimal::ONE));
        assert_eq!(of(&json!(-0.0)), Some(Decimal::ZERO));
        assert_eq!(shown(&json!(-3)), some("-3"));
        // A tenth, although the float is a little more.
        assert_eq!(of(&json!(0.1)), Some(Decimal::place(1)));
        assert_eq!(of(&json!(0.1)).unwrap().units() * 10, Decimal::ONE.units());
        assert_eq!(shown(&json!(0.0075)), some("0.0075"));
        assert_eq!(shown(&json!(-2.5)), some("-2.5"));
        assert_eq!(shown(&json!(1.5e-7)), some("0.00000015"));
        assert_eq!(shown(&json!(123_456.789)), some("123456.789"));
        assert_eq!(shown(&json!(1e16)), some("10000000000000000"));
        assert_eq!(shown(&json!(1e-16)), some("0.0000000000000001"));
        // What an integer type holds is the number that was written.
        assert_eq!(shown(&json!(u64::MAX)), some("18446744073709551615"));
        assert_eq!(shown(&json!(i64::MIN)), some("-9223372036854775808"));
    }

    #[test]
    fn a_number_outside_the_range_is_not_read() {
        // The size is below 2^64, whichever way the number is held.
        assert_eq!(shown(&json!(1e19)), some("10000000000000000000"));
        assert_eq!(shown(&json!(-1e19)), some("-10000000000000000000"));
        // The float 2^64 is printed as a number a little above it.
        for beyond in [
            18_446_744_073_709_551_616.0,
            -1e20,
            1e30,
            f64::MAX,
            f64::MIN,
        ] {
            assert_eq!(of(&json!(beyond)), None, "{beyond}");
        }
        // A number of a schema has sixteen places at most.
        assert_eq!(
            shown(&json!(0.123_456_789_012_345_6)),
            some("0.1234567890123456")
        );
        for finer in [1e-17, 0.100_000_000_000_000_02, 5e-324, 1.5e-300] {
            assert_eq!(of(&json!(finer)), None, "{finer}");
        }
    }

    #[test]
    fn a_number_is_read_from_any_text_that_json_allows() {
        // With its feature for numbers of any precision, `serde_json` hands over the text
        // that was written, and the text may be long.
        let shown = |text: &str| named(text).map(|number| number.to_string());
        assert_eq!(shown("1E3"), some("1000"));
        assert_eq!(shown("1.50"), some("1.5"));
        assert_eq!(shown("-0e5"), some("0"));
        assert_eq!(shown("0.25e+1"), some("2.5"));
        assert_eq!(shown("12300e-2"), some("123"));
        assert_eq!(
            shown("18446744073709551615.99999999999999999"),
            some("18446744073709551615.99999999999999999")
        );
        assert_eq!(shown("0.00000000000000001000"), some("0.00000000000000001"));
        assert_eq!(shown("18446744073709551616"), None);
        assert_eq!(shown("0.000000000000000001"), None);
        assert_eq!(shown("1e1000000000"), None);
        assert_eq!(shown("1e-1000000000"), None);
        assert_eq!(shown("1e99999999999999999999"), None);
        assert_eq!(shown(&format!("1{}", "0".repeat(1000))), None);
        assert_eq!(shown(&format!("0.{}1", "0".repeat(1000))), None);
        // Zeros behind the last place of a unit are no more places, while the text is not
        // too long to read.
        assert_eq!(shown(&format!("0.5{}", "0".repeat(30))), some("0.5"));
        assert_eq!(shown(&format!("0.5{}", "0".repeat(1000))), None);
    }

    #[test]
    fn a_number_is_written_as_an_integer_or_as_the_float_that_names_it() {
        let text = |number: Decimal| written(number).map(|written| written.to_string());
        assert_eq!(text(Decimal::ZERO), some("0"));
        assert_eq!(text(number("-7")), some("-7"));
        assert_eq!(text(number("1.0")), some("1"));
        assert_eq!(
            text(number("18446744073709551615")),
            some("18446744073709551615")
        );
        assert_eq!(
            text(number("-9223372036854775808")),
            some("-9223372036854775808")
        );
        assert_eq!(text(number("0.1")), some("0.1"));
        assert_eq!(text(number("0.0075")), some("0.0075"));
        assert_eq!(text(number("-2.5")), some("-2.5"));
        // A number with as many places as a unit, which no schema holds.
        assert_eq!(text(Decimal::place(17)), some("1e-17"));
        assert_eq!(text(Decimal::of_units(11).unwrap()), some("1.1e-16"));

        // A whole number below the least `i64` is a float or nothing.
        assert_eq!(text(number("-1e19")), some("-1e+19"));
        let below = Decimal::of_units(number("-9223372036854775808").units() - ONE);
        assert_eq!(text(below.unwrap()), None);
        // Between two floats that are next to each other: the floats of this size are whole.
        let between = Decimal::of_units(number("9007199254740991").units() + ONE / 2);
        assert_eq!(between.unwrap().to_string(), "9007199254740991.5");
        assert_eq!(text(between.unwrap()), None);
        let between = Decimal::of_units(number("18446744073709551615").units() + 1);
        assert_eq!(text(between.unwrap()), None);
    }

    #[test]
    fn a_number_is_shown_as_a_decimal() {
        assert_eq!(number("0.01").to_string(), "0.01");
        assert_eq!(number("5").to_string(), "5");
        assert_eq!(number("-0.5").to_string(), "-0.5");
        assert_eq!(number("1e3").to_string(), "1000");
        assert_eq!(Decimal::place(17).to_string(), "0.00000000000000001");
        assert_eq!(
            Decimal::of_units(-ONE - 1).unwrap().to_string(),
            "-1.00000000000000001"
        );
    }

    #[test]
    fn every_number_of_a_schema_comes_back_as_it_was() {
        let random = &mut Random(7);
        let mut read = 0;
        for _ in 0..20_000 {
            let value = match random.below(5) {
                0 => json!(random.next()),
                1 => json!(random.next() as i64),
                // Any float at all, by its bits. Few of them are within the range.
                2 => json!(f64::from_bits(random.next())),
                3 => json!((random.next() % 2_000_001) as f64 / 1000.0 - 1000.0),
                _ => {
                    json!((random.next() % 1_000_000) as f64 / 10f64.powi(random.below(17) as i32))
                }
            };
            // A float that is not finite is no JSON number.
            let Some(before) = value.as_number() else {
                continue;
            };
            let Some(number) = exact(before) else {
                continue;
            };
            read += 1;
            let after = written(number).expect("the number was written before");
            assert_eq!(exact(&after), Some(number), "{before}");
            // A whole float comes back as an integer where one holds it, and as itself else.
            if !(before.is_f64() && number.is_multiple_of(Decimal::ONE)) {
                assert_eq!(after.to_string(), before.to_string());
            }
        }
        assert!(read > 15_000, "{read}");
    }

    #[test]
    fn the_least_common_multiple_of_two_numbers() {
        let common = |a: &str, b: &str| number(a).common_multiple(number(b));
        assert_eq!(common("2", "3"), Some(number("6")));
        assert_eq!(common("4", "6"), Some(number("12")));
        assert_eq!(common("0.01", "0.0075"), Some(number("0.03")));
        assert_eq!(common("1.5", "1"), Some(number("3")));
        assert_eq!(common("0.5", "0.25"), Some(number("0.5")));
        assert_eq!(common("0.3", "0.7"), Some(number("2.1")));
        assert_eq!(number("4").common_divisor(number("6")), number("2"));
        assert_eq!(number("0.5").common_divisor(number("0.75")), number("0.25"));
        // The largest prime below 2^64 is within the range, and twice it is not.
        let prime = "18446744073709551557";
        assert_eq!(common(prime, "1"), Some(number(prime)));
        assert_eq!(common(prime, prime), Some(number(prime)));
        assert_eq!(common(prime, "2"), None);
        assert_eq!(common(prime, "0.1234567890123457"), None);

        assert!(number("0.0075").is_multiple_of(number("0.0001")));
        assert!(number("-6").is_multiple_of(number("1.5")));
        assert!(number("0").is_multiple_of(number("7")));
        assert!(!number("0.1").is_multiple_of(number("0.03")));
        assert!(!number("1").is_multiple_of(number("2")));
    }
}
