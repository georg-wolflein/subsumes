//! Counterexamples: an instance for a branch that the engine could not refute.

use serde_json::{Value, json};

use crate::canonical::number::Numbers;
use crate::context::{Budget, Exhausted};
use crate::rational::{Rationals, written};
use crate::term::{InstanceType, TypeSet};

/// An instance of one of the types in `free`: those about which a branch says nothing but
/// which boolean and which numbers an instance may be. There is none if the only instances
/// are numbers that no JSON value holds.
///
/// # Errors
///
/// When the budget does not cover the search for a number.
pub(crate) fn instance(
    free: TypeSet,
    may_be_true: bool,
    numbers: &Numbers,
    rationals: &Rationals,
    budget: &mut Budget,
) -> Result<Option<Value>, Exhausted> {
    for kind in free.iter() {
        let instance = match kind {
            InstanceType::Null => Some(Value::Null),
            InstanceType::Boolean => Some(Value::Bool(may_be_true)),
            InstanceType::Number => {
                let member = numbers.member(rationals, budget)?;
                member.and_then(|member| written(&member).map(Value::Number))
            }
            InstanceType::String => Some(json!("")),
            InstanceType::Array => Some(json!([])),
            InstanceType::Object => Some(json!({})),
        };
        if instance.is_some() {
            return Ok(instance);
        }
    }
    Ok(None)
}
