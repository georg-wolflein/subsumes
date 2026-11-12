//! Counterexamples: an instance for a branch that the engine could not refute.

use serde_json::{Value, json};

use crate::term::InstanceType;

/// An instance of a type about which a branch says nothing else, except which booleans it
/// may be.
pub(crate) fn instance(kind: InstanceType, may_be_true: bool) -> Value {
    match kind {
        InstanceType::Null => Value::Null,
        InstanceType::Boolean => Value::Bool(may_be_true),
        InstanceType::Number => json!(0),
        InstanceType::String => json!(""),
        InstanceType::Array => json!([]),
        InstanceType::Object => json!({}),
    }
}
