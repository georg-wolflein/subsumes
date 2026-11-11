use std::fmt;

use crate::Side;

/// The input cannot be checked at all.
///
/// This is not [`Verdict::Unknown`](crate::Verdict::Unknown), which is the answer for two valid
/// schemas that the library cannot decide.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The value is neither an object nor a boolean, so it is not a schema.
    NotASchema {
        /// Which of the two arguments it is.
        schema: Side,
    },
    /// The schema declares a dialect other than draft 2020-12.
    UnsupportedDialect {
        /// Which of the two arguments it is.
        schema: Side,
        /// The value of its `$schema`.
        dialect: String,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotASchema { schema } => {
                write!(f, "schema {schema} is neither an object nor a boolean")
            }
            Self::UnsupportedDialect { schema, dialect } => {
                write!(
                    f,
                    "schema {schema} declares the dialect {dialect}, and only draft 2020-12 is supported"
                )
            }
        }
    }
}

impl std::error::Error for Error {}
