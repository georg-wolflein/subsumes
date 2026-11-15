//! JSON Schema inclusion for draft 2020-12: does schema A accept every instance that is valid
//! under schema B? If it does, A *subsumes* B.
//!
//! ```
//! use serde_json::json;
//! use subsumes::{Verdict, subsumes};
//!
//! let new = json!({"type": "integer"});
//! let old = json!({"type": "integer", "minimum": 0});
//!
//! match subsumes(&new, &old)? {
//!     Verdict::Yes => println!("the new schema accepts everything the old one did"),
//!     Verdict::No { counterexample } => println!("no longer accepted: {counterexample}"),
//!     Verdict::Unknown { reason } => println!("could not decide: {reason}"),
//! }
//! # Ok::<(), subsumes::Error>(())
//! ```
//!
//! A schema has to stand on its own. A `$ref` resolves inside the schema or to a meta-schema of
//! the draft, so a schema that is spread over several files is bundled into one first, as the
//! specification describes: each file goes under `$defs` with its URI as its `$id`.
//!
//! The engine is being built keyword by keyword. So far it models the types, `null`, the
//! booleans, numbers, strings, objects, `allOf`, `anyOf`, `oneOf`, `not`, `if`/`then`/`else`
//! and `$ref`. A check whose answer depends on another keyword, such as one about arrays,
//! returns [`Verdict::Unknown`] and names the keyword.
//! Two schemas that share such a keyword with the same value can still be decided, because
//! what both say cancels. A schema that uses a `$dynamicRef` is not decided yet, whatever
//! else it says.
//!
//! Numbers are compared exactly: a number stands for the decimal that it is written as, so
//! `0.0075` is a multiple of `0.0001`, which the two floats are not.
//!
//! A `pattern` is read in the dialect of the [`regex`](https://docs.rs/regex) crate and
//! matches anywhere in a string. `format` is asserted for the formats whose strings are a
//! regular language that can be written down exactly, such as `date`, `uuid` and `uri`.
//!
//! The value of a property is compared as an instance of its own. A schema that holds
//! itself in a property, as that of a list or a tree does, accepts the instances that can
//! be built in finitely many steps.

mod canonical;
mod checker;
mod context;
mod error;
mod formats;
mod generate;
mod inspect;
mod language;
mod lower;
mod meta_schemas;
mod normalize;
mod rational;
mod schema;
mod term;
#[cfg(test)]
mod testing;
mod verdict;

use serde_json::Value;

pub use checker::{Check, Checker};
pub use error::Error;
pub use verdict::{Reason, Side, Verdict};

/// Does `a` accept every instance that is valid under `b`?
///
/// This is [`Checker::subsumes`] with the default work budget.
///
/// # Errors
///
/// When `a` or `b` cannot be checked at all; see [`Error`].
pub fn subsumes(a: &Value, b: &Value) -> Result<Verdict, Error> {
    Checker::new().subsumes(a, b)
}
