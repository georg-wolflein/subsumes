use std::fmt;

use serde_json::Value;

/// The answer to "does A accept every instance that is valid under B?".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every instance valid under B is valid under A.
    Yes,
    /// Some instance is valid under B and invalid under A.
    No {
        /// Such an instance.
        counterexample: Value,
    },
    /// The library cannot decide.
    Unknown {
        /// Why it cannot.
        reason: Reason,
    },
}

/// Why a check ended in [`Verdict::Unknown`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Reason {
    /// The answer depends on a construct that the library does not model.
    Unsupported {
        /// The schema that contains the construct.
        schema: Side,
        /// Where the construct is: a URI reference whose fragment is a JSON Pointer, such as
        /// `#/properties/tags/uniqueItems`. `#` alone is the schema as a whole. For a schema
        /// that refers to itself in a way that is not modelled, it is the subschema in which
        /// the cycle closes.
        location: String,
    },
    /// An instance is valid under B and invalid under A, but the library found none that
    /// it can give. So A does not subsume B, and there is no counterexample.
    ///
    /// That is a number that no JSON value holds exactly: one between two floats that are
    /// next to each other has more digits than a float keeps. Or it is a value of more than
    /// 127 objects inside one another, which is deeper than `serde_json` reads back.
    Unrepresentable,
    /// The check ran out of its work budget.
    Budget,
}

impl fmt::Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported { schema, location } => {
                write!(f, "{location} in schema {schema} is not supported")
            }
            Self::Unrepresentable => f.write_str(
                "the schemas differ in an instance that cannot be given: a number that a JSON \
                 value does not hold exactly, or a value that is nested too deep",
            ),
            Self::Budget => f.write_str("the check ran out of its work budget"),
        }
    }
}

/// One of the two schemas of a check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    /// The schema that should accept everything: the first argument.
    A,
    /// The schema whose instances must be accepted: the second argument.
    B,
}

impl fmt::Display for Side {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::A => "A",
            Self::B => "B",
        })
    }
}
