//! The results file: one JSON object per line, one line per case and direction.

use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use subsumes::{Check, Error, Reason, Verdict};

/// Which way round the two schemas of a case were checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Direction {
    /// `subsumes(a, b)`, scored against the label `a_subsumes_b`.
    ASubsumesB,
    /// `subsumes(b, a)`, scored against the label `b_subsumes_a`.
    BSubsumesA,
}

impl Direction {
    pub const BOTH: [Self; 2] = [Self::ASubsumesB, Self::BSubsumesA];

    pub fn name(self) -> &'static str {
        match self {
            Self::ASubsumesB => "a_subsumes_b",
            Self::BSubsumesA => "b_subsumes_a",
        }
    }
}

/// What the library did with one check.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "verdict", rename_all = "snake_case")]
pub enum Outcome {
    Yes,
    No {
        counterexample: Value,
    },
    Unknown {
        /// What the reasons are counted by: `budget`, or the keyword that is not supported.
        reason: String,
        /// The reason in full.
        detail: String,
    },
    /// The library rejected a schema. The corpus holds only valid schemas, so this is a bug.
    Error {
        message: String,
    },
}

impl Outcome {
    pub fn of(result: &Result<Check, Error>) -> Self {
        match result {
            Ok(check) => match &check.verdict {
                Verdict::Yes => Self::Yes,
                Verdict::No { counterexample } => Self::No {
                    counterexample: counterexample.clone(),
                },
                Verdict::Unknown { reason } => Self::Unknown {
                    reason: group(reason),
                    detail: reason.to_string(),
                },
            },
            Err(error) => Self::Error {
                message: error.to_string(),
            },
        }
    }

    /// The verdict by its name, with the reason of an `Unknown` or the message of an error.
    pub fn label(&self) -> String {
        match self {
            Self::Yes => "Yes".to_owned(),
            Self::No { .. } => "No".to_owned(),
            Self::Unknown { reason, .. } => format!("Unknown ({reason})"),
            Self::Error { message } => format!("Error ({message})"),
        }
    }

    pub fn is_decided(&self) -> bool {
        matches!(self, Self::Yes | Self::No { .. })
    }
}

/// What the reasons for `Unknown` are counted by.
fn group(reason: &Reason) -> String {
    match reason {
        Reason::Budget => "budget".to_owned(),
        Reason::Unsupported { location, .. } => keyword(location),
        _ => "other".to_owned(),
    }
}

/// The last token of the JSON Pointer in a location, which names the keyword; a location
/// without one is the schema as a whole.
fn keyword(location: &str) -> String {
    let pointer = location.split_once('#').map_or("", |(_, pointer)| pointer);
    match pointer.rsplit_once('/') {
        Some((_, token)) => token.replace("~1", "/").replace("~0", "~"),
        None => "whole schema".to_owned(),
    }
}

/// One line of the results file.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Record {
    /// The folder of the case inside the corpus, such as `rb-testset/additional_items`.
    pub case: String,
    pub direction: Direction,
    /// The label of the corpus; `None` where it claims nothing.
    pub expected: Option<bool>,
    #[serde(flatten)]
    pub outcome: Outcome,
    /// The steps of the work budget that the check spent.
    pub steps: u64,
    /// The time the check took, in nanoseconds.
    pub nanos: u64,
}

impl Record {
    pub fn key(&self) -> (&str, Direction) {
        (&self.case, self.direction)
    }

    /// The collection of the case: the first folder of its path.
    pub fn collection(&self) -> &str {
        self.case.split('/').next().unwrap_or(&self.case)
    }

    /// A `Yes` or `No` that contradicts the label. An `Unknown` is never wrong.
    pub fn is_wrong(&self) -> bool {
        matches!(
            (self.expected, &self.outcome),
            (Some(true), Outcome::No { .. }) | (Some(false), Outcome::Yes)
        )
    }

    pub fn is_error(&self) -> bool {
        matches!(self.outcome, Outcome::Error { .. })
    }

    /// The check as a pull request comment names it.
    pub fn name(&self) -> String {
        format!("`{}` {}", self.case, self.direction.name())
    }
}

/// How many checks ended which way.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Counts {
    pub checks: u64,
    pub yes: u64,
    pub no: u64,
    pub unknown: u64,
    pub wrong: u64,
    pub errors: u64,
    pub steps: u64,
    pub nanos: u64,
}

impl Counts {
    pub fn of<'a>(records: impl IntoIterator<Item = &'a Record>) -> Self {
        let mut counts = Self::default();
        for record in records {
            counts.add(record);
        }
        counts
    }

    pub fn add(&mut self, record: &Record) {
        self.checks += 1;
        match record.outcome {
            Outcome::Yes => self.yes += 1,
            Outcome::No { .. } => self.no += 1,
            Outcome::Unknown { .. } => self.unknown += 1,
            Outcome::Error { .. } => self.errors += 1,
        }
        self.wrong += u64::from(record.is_wrong());
        self.steps += record.steps;
        self.nanos += record.nanos;
    }
}

pub fn write(path: &Path, records: &[Record]) -> Result<(), String> {
    let failed = |error: std::io::Error| format!("cannot write {}: {error}", path.display());
    let mut file = BufWriter::new(File::create(path).map_err(failed)?);
    for record in records {
        let line = serde_json::to_string(record).map_err(|error| error.to_string())?;
        writeln!(file, "{line}").map_err(failed)?;
    }
    file.flush().map_err(failed)
}

pub fn read(path: &Path) -> Result<Vec<Record>, String> {
    let failed = |error: &dyn std::fmt::Display| format!("cannot read {}: {error}", path.display());
    let file = BufReader::new(File::open(path).map_err(|error| failed(&error))?);
    let mut records = Vec::new();
    for line in file.lines() {
        let line = line.map_err(|error| failed(&error))?;
        records.push(serde_json::from_str(&line).map_err(|error| failed(&error))?);
    }
    Ok(records)
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    fn record(expected: Option<bool>, outcome: Outcome) -> Record {
        Record {
            case: "collection/group/case".to_owned(),
            direction: Direction::ASubsumesB,
            expected,
            outcome,
            steps: 7,
            nanos: 1200,
        }
    }

    fn unknown() -> Outcome {
        Outcome::Unknown {
            reason: "budget".to_owned(),
            detail: "the check ran out of its work budget".to_owned(),
        }
    }

    #[test]
    fn a_line_is_a_flat_object() {
        let no = Outcome::No {
            counterexample: json!({"a": 1}),
        };
        let line = serde_json::to_value(record(Some(false), no)).unwrap();
        assert_eq!(
            line,
            json!({
                "case": "collection/group/case",
                "direction": "a_subsumes_b",
                "expected": false,
                "verdict": "no",
                "counterexample": {"a": 1},
                "steps": 7,
                "nanos": 1200,
            })
        );
    }

    #[test]
    fn every_outcome_survives_the_file() {
        let outcomes = [
            Outcome::Yes,
            Outcome::No {
                counterexample: json!(null),
            },
            unknown(),
            Outcome::Error {
                message: "schema A is neither an object nor a boolean".to_owned(),
            },
        ];
        for outcome in outcomes {
            let record = record(None, outcome);
            let line = serde_json::to_string(&record).unwrap();
            assert_eq!(serde_json::from_str::<Record>(&line).unwrap(), record);
        }
    }

    #[test]
    fn only_a_verdict_against_the_label_is_wrong() {
        let no = || Outcome::No {
            counterexample: json!(0),
        };
        assert!(record(Some(true), no()).is_wrong());
        assert!(record(Some(false), Outcome::Yes).is_wrong());
        assert!(!record(Some(true), Outcome::Yes).is_wrong());
        assert!(!record(Some(false), no()).is_wrong());
        assert!(!record(None, Outcome::Yes).is_wrong());
        assert!(!record(Some(true), unknown()).is_wrong());
    }

    #[test]
    fn the_keyword_is_the_last_token_of_the_pointer() {
        assert_eq!(keyword("#/properties/tags/uniqueItems"), "uniqueItems");
        assert_eq!(
            keyword("https://example.com/a.json#/items/format"),
            "format"
        );
        assert_eq!(keyword("#/properties/a~1b/pattern"), "pattern");
        assert_eq!(keyword("#"), "whole schema");
    }

    #[test]
    fn the_collection_is_the_first_folder() {
        assert_eq!(record(None, Outcome::Yes).collection(), "collection");
    }
}
