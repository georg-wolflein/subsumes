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
//! The library has no engine yet: every check of two schemas returns [`Verdict::Unknown`].

mod checker;
mod error;
mod verdict;

use serde_json::Value;

pub use checker::{Check, Checker};
pub use error::Error;
pub use verdict::{Reason, Side, Verdict};

/// Does `a` accept every instance that is valid under `b`?
///
/// This is [`Checker::subsumes`] with the default settings: the default work budget, and no
/// documents for references to point to.
///
/// # Errors
///
/// When `a` or `b` cannot be checked at all; see [`Error`].
pub fn subsumes(a: &Value, b: &Value) -> Result<Verdict, Error> {
    Checker::new().subsumes(a, b)
}
