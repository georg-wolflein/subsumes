//! Exact numbers.
//!
//! Every number of a schema is a rational: the one that the shortest decimal of the number
//! names. `0.1` is a tenth, and not the float next to it, so `0.0075` is a multiple of
//! `0.0001`. Rationals are kept once each, so equal ids mean equal numbers.

use std::collections::HashMap;

use num_rational::BigRational;
use serde_json::Number;

pub(crate) type Rational = BigRational;

/// The id of a rational.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct RationalId(u32);

/// Every rational of a check.
#[derive(Debug, Default)]
pub(crate) struct Rationals {
    values: Vec<Rational>,
    ids: HashMap<Rational, RationalId>,
}

impl Rationals {
    pub fn get(&self, id: RationalId) -> &Rational {
        &self.values[id.0 as usize]
    }

    pub fn intern(&mut self, value: Rational) -> RationalId {
        if let Some(&id) = self.ids.get(&value) {
            return id;
        }
        let id = u32::try_from(self.values.len()).expect("a check has fewer than 2^32 numbers");
        let id = RationalId(id);
        self.values.push(value.clone());
        self.ids.insert(value, id);
        id
    }

    /// The number that a JSON number names, if it names one.
    pub fn read(&mut self, number: &Number) -> Option<RationalId> {
        read(number).map(|value| self.intern(value))
    }

    pub fn whole(&mut self, value: i64) -> RationalId {
        self.intern(whole(value))
    }
}

pub(crate) fn whole(value: i64) -> Rational {
    Rational::from_integer(value.into())
}

/// The number that a JSON number names: the integer, or the shortest decimal that is read
/// back as the same float.
///
/// A number of `serde_json` is always one or the other. With its feature for numbers of any
/// precision, which another crate of a build may turn on, a number may also be too large for
/// a float, and then it names nothing here.
pub(crate) fn read(number: &Number) -> Option<Rational> {
    if let Some(integer) = number.as_u64() {
        return Some(Rational::from_integer(integer.into()));
    }
    if let Some(integer) = number.as_i64() {
        return Some(whole(integer));
    }
    let float = number.as_f64().filter(|float| float.is_finite())?;
    // The shortest digits that name the float, as in `-7.5e-3`.
    let text = format!("{float:e}");
    let (mantissa, exponent) = text.split_once('e')?;
    let (integer, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits: Rational = format!("{integer}{fraction}").parse().ok()?;
    let exponent = exponent.parse::<i32>().ok()? - i32::try_from(fraction.len()).ok()?;
    Some(digits * whole(10).pow(exponent))
}

/// The most decimal places that a number is written with. A float has at most 340: the
/// smallest is `5e-324`, and none has more than 17 digits.
const PLACES: i32 = 400;

/// The number as a decimal, if it is one with at most [`PLACES`] places.
fn decimal(value: &Rational) -> Option<String> {
    let negative = *value < whole(0);
    let value = if negative { -value } else { value.clone() };
    // The fewest places with which the number is written: with more it is written too.
    let scaled = |places: i32| &value * whole(10).pow(places);
    if !scaled(PLACES).is_integer() {
        return None;
    }
    let (mut enough, mut too_few) = (PLACES, -1);
    while enough - too_few > 1 {
        let places = (enough + too_few) / 2;
        if scaled(places).is_integer() {
            enough = places;
        } else {
            too_few = places;
        }
    }
    let digits = scaled(enough).to_integer().to_string();
    let places = usize::try_from(enough).expect("a number has no fewer than zero places");
    // At least one digit stands before the point.
    let digits = format!("{digits:0>width$}", width = places + 1);
    let (integer, fraction) = digits.split_at(digits.len() - places);
    let sign = if negative { "-" } else { "" };
    let point = if places > 0 { "." } else { "" };
    Some(format!("{sign}{integer}{point}{fraction}"))
}

/// The number as text: a decimal, or a fraction where it is none.
pub(crate) fn shown(value: &Rational) -> String {
    decimal(value).unwrap_or_else(|| value.to_string())
}

/// The JSON number that names this number, if there is one: an integer of at most 64 bits,
/// or a float whose shortest decimal is the number. An integer of thirty digits that does
/// not end in zeros has none, and neither has a decimal of twenty digits.
pub(crate) fn written(value: &Rational) -> Option<Number> {
    let text = decimal(value)?;
    if value.is_integer() {
        if let Ok(integer) = text.parse::<i64>() {
            return Some(integer.into());
        }
        if let Ok(integer) = text.parse::<u64>() {
            return Some(integer.into());
        }
    }
    // The float next to the number, which names it only if it is read back as the same.
    let number = Number::from_f64(text.parse().ok()?)?;
    (read(&number).as_ref() == Some(value)).then_some(number)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn number(value: &serde_json::Value) -> Rational {
        read(value.as_number().unwrap()).unwrap()
    }

    fn ratio(numerator: i64, denominator: i64) -> Rational {
        whole(numerator) / whole(denominator)
    }

    #[test]
    fn a_number_is_the_decimal_that_was_written() {
        assert_eq!(number(&json!(3)), whole(3));
        assert_eq!(number(&json!(-3)), whole(-3));
        assert_eq!(
            number(&json!(u64::MAX)),
            ratio(i64::MAX, 1) * whole(2) + whole(1)
        );
        assert_eq!(number(&json!(3.0)), whole(3));
        assert_eq!(number(&json!(-0.0)), whole(0));
        assert_eq!(number(&json!(0.1)), ratio(1, 10));
        assert_eq!(number(&json!(-7.5e-3)), ratio(-3, 400));
        assert_eq!(number(&json!(1e30)), whole(10).pow(30));
        assert_eq!(number(&json!(5e-324)), whole(5) / whole(10).pow(324));
        assert_eq!(number(&json!(1.7976931348623157e308)), {
            whole(17_976_931_348_623_157) * whole(10).pow(292)
        });
        // As floats the two are not multiples of each other. As what was written they are.
        let multiple = number(&json!(0.0075)) / number(&json!(0.0001));
        assert_eq!(multiple, whole(75));
    }

    #[test]
    fn a_number_is_kept_once() {
        let mut rationals = Rationals::default();
        let one = rationals.whole(1);
        assert_eq!(rationals.read(json!(1.0).as_number().unwrap()), Some(one));
        assert_eq!(rationals.intern(ratio(2, 2)), one);
        assert_ne!(rationals.whole(2), one);
        assert_eq!(*rationals.get(one), whole(1));
    }

    #[test]
    fn a_number_is_shown_as_a_decimal() {
        let shown = |value: Rational| shown(&value);
        assert_eq!(shown(whole(0)), "0");
        assert_eq!(shown(whole(-12)), "-12");
        assert_eq!(shown(ratio(1, 2)), "0.5");
        assert_eq!(shown(ratio(-3, 400)), "-0.0075");
        assert_eq!(shown(ratio(1001, 8)), "125.125");
        assert_eq!(shown(whole(10).pow(30)), format!("1{}", "0".repeat(30)));
        assert_eq!(shown(whole(10).pow(-7)), "0.0000001");
        // No decimal ends, so the fraction it is.
        assert_eq!(shown(ratio(1, 3)), "1/3");
        assert_eq!(shown(ratio(-7, 6)), "-7/6");
    }

    #[test]
    fn a_number_is_written_as_json_if_json_holds_it() {
        let written = |value: Rational| written(&value).map(serde_json::Value::Number);
        assert_eq!(written(whole(0)), Some(json!(0)));
        assert_eq!(written(whole(-5)), Some(json!(-5)));
        assert_eq!(written(number(&json!(u64::MAX))), Some(json!(u64::MAX)));
        assert_eq!(written(whole(i64::MIN)), Some(json!(i64::MIN)));
        assert_eq!(written(ratio(1, 10)), Some(json!(0.1)));
        assert_eq!(written(ratio(-3, 400)), Some(json!(-0.0075)));
        assert_eq!(written(whole(10).pow(30)), Some(json!(1e30)));
        assert_eq!(written(whole(10).pow(-320)), Some(json!(1e-320)));

        // An integer beyond 64 bits that no float names, and a decimal with more digits than
        // a float holds: the float next to each is another number.
        assert_eq!(written(whole(10).pow(30) + whole(1)), None);
        assert_eq!(written(whole(10).pow(17) + ratio(1, 10)), None);
        // Beyond the largest float and below the smallest.
        assert_eq!(written(whole(10).pow(400)), None);
        assert_eq!(written(whole(10).pow(-330)), None);
        assert_eq!(written(ratio(1, 3)), None);
    }

    #[test]
    fn every_number_that_is_read_is_written_back() {
        let mut random = crate::testing::Random(7);
        for _ in 0..5_000 {
            let bits = random.next();
            let float = match random.below(3) {
                0 => f64::from_bits(bits),
                1 => (bits % 2_000_000) as f64 / 1000.0 - 1000.0,
                _ => (bits % 1000) as f64 * 10f64.powi(random.below(60) as i32 - 30),
            };
            let Some(number) = Number::from_f64(float) else {
                continue;
            };
            let value = read(&number).unwrap();
            let back = written(&value).unwrap();
            assert_eq!(back.as_f64(), number.as_f64(), "{number}");
        }
    }
}
