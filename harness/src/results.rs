//! The results file: one JSON object per line, one line per case and direction.

use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use subsumes::{Check, Error, Reason, Verdict};

use crate::counterexample::Confirmation;

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

    /// The file of the wide schema, which was to accept everything, and the file of the
    /// narrow schema, whose instances it was to accept.
    pub fn files(self) -> (&'static str, &'static str) {
        match self {
            Self::ASubsumesB => ("a.json", "b.json"),
            Self::BSubsumesA => ("b.json", "a.json"),
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
        /// What a validator makes of the counterexample. A file that was written before
        /// counterexamples were checked does not say.
        #[serde(default)]
        confirmation: Confirmation,
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
    /// `confirmation` is asked about the counterexample of a `No`.
    pub fn of(
        result: &Result<Check, Error>,
        confirmation: impl FnOnce(&Value) -> Confirmation,
    ) -> Self {
        match result {
            Ok(check) => match &check.verdict {
                Verdict::Yes => Self::Yes,
                Verdict::No { counterexample } => Self::No {
                    confirmation: confirmation(counterexample),
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
        Reason::Unrepresentable => "unrepresentable number".to_owned(),
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

    /// A `Yes` or `No` that contradicts the label, or a `No` whose counterexample is none.
    /// An `Unknown` is never wrong.
    pub fn is_wrong(&self) -> bool {
        match (self.expected, &self.outcome) {
            (Some(true), Outcome::No { .. }) | (Some(false), Outcome::Yes) => true,
            (_, Outcome::No { confirmation, .. }) => confirmation.is_refuted(),
            _ => false,
        }
    }

    /// What is wrong with the verdict, if anything is.
    fn fault(&self) -> Option<String> {
        let mut faults = Vec::new();
        match (self.expected, &self.outcome) {
            (Some(true), Outcome::No { .. }) => faults.push("the corpus says Yes".to_owned()),
            (Some(false), Outcome::Yes) => faults.push("the corpus says No".to_owned()),
            _ => {}
        }
        if let Outcome::No {
            counterexample,
            confirmation,
        } = &self.outcome
        {
            let (wide, narrow) = self.direction.files();
            let instance = shortened(&counterexample.to_string());
            match confirmation {
                Confirmation::RejectedByNarrow => {
                    faults.push(format!(
                        "`{narrow}` rejects the counterexample `{instance}`"
                    ));
                }
                Confirmation::AcceptedByWide => {
                    faults.push(format!("`{wide}` accepts the counterexample `{instance}`"));
                }
                Confirmation::Confirmed | Confirmation::NotChecked(_) => {}
            }
        }
        (!faults.is_empty()).then(|| faults.join(", and "))
    }

    pub fn is_error(&self) -> bool {
        matches!(self.outcome, Outcome::Error { .. })
    }

    /// The check as a pull request comment names it.
    pub fn name(&self) -> String {
        format!("`{}` {}", self.case, self.direction.name())
    }

    /// The check with its outcome, and with what is wrong with the outcome if anything is.
    pub fn described(&self) -> String {
        let (name, outcome) = (self.name(), self.outcome.label());
        match self.fault() {
            Some(fault) => format!("{name}: {outcome}, and {fault}"),
            None => format!("{name}: {outcome}"),
        }
    }
}

/// At most this many characters of a counterexample are shown.
const SHOWN: usize = 60;

fn shortened(text: &str) -> String {
    match text.char_indices().nth(SHOWN) {
        Some((end, _)) => format!("{}…", &text[..end]),
        None => text.to_owned(),
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
    /// The counterexamples that a validator confirmed, and those that it did not look at.
    pub confirmed: u64,
    pub unchecked: u64,
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
        match &record.outcome {
            Outcome::Yes => self.yes += 1,
            Outcome::No { confirmation, .. } => {
                self.no += 1;
                self.confirmed += u64::from(*confirmation == Confirmation::Confirmed);
                self.unchecked += u64::from(matches!(confirmation, Confirmation::NotChecked(_)));
            }
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

    fn no(counterexample: Value, confirmation: Confirmation) -> Outcome {
        Outcome::No {
            counterexample,
            confirmation,
        }
    }

    #[test]
    fn a_line_is_a_flat_object() {
        let no = no(json!({"a": 1}), Confirmation::Confirmed);
        let line = serde_json::to_value(record(Some(false), no)).unwrap();
        assert_eq!(
            line,
            json!({
                "case": "collection/group/case",
                "direction": "a_subsumes_b",
                "expected": false,
                "verdict": "no",
                "counterexample": {"a": 1},
                "confirmation": "confirmed",
                "steps": 7,
                "nanos": 1200,
            })
        );
    }

    #[test]
    fn a_line_from_before_counterexamples_were_checked_is_read() {
        let line = json!({
            "case": "collection/group/case",
            "direction": "a_subsumes_b",
            "expected": false,
            "verdict": "no",
            "counterexample": 0,
            "steps": 7,
            "nanos": 1200,
        });
        let read: Record = serde_json::from_value(line).unwrap();
        let Outcome::No { confirmation, .. } = &read.outcome else {
            panic!("the line holds a No");
        };
        assert!(matches!(confirmation, Confirmation::NotChecked(_)));
        // Such a counterexample is not known to be none.
        assert!(!read.is_wrong());
        let counts = Counts::of([&read]);
        assert_eq!((counts.no, counts.confirmed, counts.unchecked), (1, 0, 1));
    }

    #[test]
    fn the_outcome_of_a_no_holds_what_the_validator_says() {
        let checker = subsumes::Checker::new();
        // `null` is no string.
        let check = checker.check(&json!({"type": "string"}), &json!(true));
        let outcome = Outcome::of(&check, |counterexample| {
            assert_eq!(counterexample, &json!(null));
            Confirmation::AcceptedByWide
        });
        assert_eq!(outcome, no(json!(null), Confirmation::AcceptedByWide));
        // Nothing is asked about any other verdict.
        let check = checker.check(&json!(true), &json!({"type": "string"}));
        let unasked = |_: &Value| panic!("a Yes has no counterexample");
        assert_eq!(Outcome::of(&check, unasked), Outcome::Yes);
    }

    #[test]
    fn every_outcome_survives_the_file() {
        let outcomes = [
            Outcome::Yes,
            no(json!(null), Confirmation::Confirmed),
            no(json!(1), Confirmation::RejectedByNarrow),
            no(json!(""), Confirmation::NotChecked("why".to_owned())),
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
    fn a_verdict_against_the_label_is_wrong() {
        let no = || no(json!(0), Confirmation::Confirmed);
        assert!(record(Some(true), no()).is_wrong());
        assert!(record(Some(false), Outcome::Yes).is_wrong());
        assert!(!record(Some(true), Outcome::Yes).is_wrong());
        assert!(!record(Some(false), no()).is_wrong());
        assert!(!record(None, Outcome::Yes).is_wrong());
        assert!(!record(Some(true), unknown()).is_wrong());
        assert_eq!(
            record(Some(true), no()).described(),
            "`collection/group/case` a_subsumes_b: No, and the corpus says Yes"
        );
        assert_eq!(
            record(Some(false), Outcome::Yes).described(),
            "`collection/group/case` a_subsumes_b: Yes, and the corpus says No"
        );
        assert_eq!(
            record(Some(false), no()).described(),
            "`collection/group/case` a_subsumes_b: No"
        );
    }

    #[test]
    fn a_no_with_a_counterexample_that_is_none_is_wrong() {
        // Whatever the label says, also where the corpus claims nothing.
        for expected in [None, Some(false)] {
            let rejected = record(expected, no(json!(0), Confirmation::RejectedByNarrow));
            assert!(rejected.is_wrong());
            assert_eq!(
                rejected.described(),
                "`collection/group/case` a_subsumes_b: No, and `b.json` rejects the counterexample `0`"
            );
            let accepted = record(expected, no(json!("x"), Confirmation::AcceptedByWide));
            assert!(accepted.is_wrong());
            assert_eq!(
                accepted.described(),
                "`collection/group/case` a_subsumes_b: No, and `a.json` accepts the counterexample `\"x\"`"
            );
        }
        // The other way round, the two files change places.
        let mut other = record(None, no(json!(0), Confirmation::RejectedByNarrow));
        other.direction = Direction::BSubsumesA;
        assert!(
            other
                .described()
                .ends_with("`a.json` rejects the counterexample `0`")
        );
        // Both faults are named.
        let both = record(Some(true), no(json!(0), Confirmation::AcceptedByWide));
        assert!(
            both.described().ends_with(
                "No, and the corpus says Yes, and `a.json` accepts the counterexample `0`"
            )
        );
        let counts = Counts::of([&both, &other]);
        assert_eq!((counts.no, counts.wrong), (2, 2));
        assert_eq!((counts.confirmed, counts.unchecked), (0, 0));
    }

    #[test]
    fn a_long_counterexample_is_cut() {
        let long = record(
            None,
            no(json!("é".repeat(100)), Confirmation::AcceptedByWide),
        );
        let shown = format!("`\"{}…`", "é".repeat(SHOWN - 1));
        assert!(long.described().ends_with(&shown), "{}", long.described());
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
