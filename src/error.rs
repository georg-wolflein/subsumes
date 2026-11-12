use std::fmt;

use crate::Side;

/// The input cannot be checked at all.
///
/// This is not [`Verdict::Unknown`](crate::Verdict::Unknown), which is the answer for two valid
/// schemas that the library cannot decide.
///
/// A location is a URI reference whose fragment is a JSON Pointer, such as
/// `#/properties/age/minimum`. Inside a meta-schema of the draft it starts with the URI of that
/// meta-schema.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The value is neither an object nor a boolean, so it is not a schema.
    NotASchema {
        /// Which of the two arguments it is.
        schema: Side,
    },
    /// A schema declares a dialect other than draft 2020-12.
    UnsupportedDialect {
        /// The argument whose check ran into it.
        schema: Side,
        /// Where the `$schema` is.
        location: String,
        /// The value of the `$schema`.
        dialect: String,
    },
    /// A keyword has a value that the draft does not allow, such as `"minLength": "3"`, two
    /// parts of a schema declare the same `$id` or the same anchor, or a reference points
    /// below an `$id` in a place where the draft puts no schema.
    ///
    /// This is an error wherever the keyword stands, even in a definition that nothing uses.
    InvalidKeyword {
        /// The argument whose check ran into it.
        schema: Side,
        /// Where the keyword is.
        location: String,
        /// What the value must be.
        message: String,
    },
    /// A reference resolves to nothing: the schema has no resource with that URI, or the
    /// fragment names nothing in the resource. A schema has to carry what it references, apart
    /// from the meta-schemas of the draft.
    UnresolvedReference {
        /// The argument whose check ran into it.
        schema: Side,
        /// Where the `$ref` or `$dynamicRef` is.
        location: String,
        /// The reference as written.
        reference: String,
    },
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotASchema { schema } => {
                write!(f, "schema {schema} is neither an object nor a boolean")
            }
            Self::UnsupportedDialect {
                schema,
                location,
                dialect,
            } => {
                write!(
                    f,
                    "{location} in schema {schema} declares the dialect {dialect}, and only draft 2020-12 is supported"
                )
            }
            Self::InvalidKeyword {
                schema,
                location,
                message,
            } => write!(f, "{location} in schema {schema} {message}"),
            Self::UnresolvedReference {
                schema,
                location,
                reference,
            } => {
                write!(
                    f,
                    "{location} in schema {schema} refers to {reference}, which resolves to nothing"
                )
            }
        }
    }
}

impl std::error::Error for Error {}
