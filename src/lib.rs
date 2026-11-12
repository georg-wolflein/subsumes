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
//! The library has no engine yet. It loads both schemas, so one that is not a valid schema is
//! an [`Error`], and every check of two valid schemas returns [`Verdict::Unknown`].

mod checker;
mod error;
// Nothing uses the meta-schemas until the library resolves references.
#[cfg_attr(not(test), expect(dead_code))]
mod meta_schemas;
mod schema;
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
