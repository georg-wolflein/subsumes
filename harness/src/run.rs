//! Running the library over the corpus.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use serde::Deserialize;
use serde::de::DeserializeOwned;
use serde_json::{Map, Value};
use subsumes::Checker;

use crate::results::{Direction, Outcome, Record};

/// The labels of a case, from its `case.json`.
#[derive(Deserialize)]
struct Labels {
    a_subsumes_b: Option<bool>,
    b_subsumes_a: Option<bool>,
}

/// Checks every case of the corpus in both directions, in the order of the case paths.
pub fn run(corpus: &Path) -> Result<Vec<Record>, String> {
    if !corpus.is_dir() {
        return Err(format!(
            "there is no corpus at {}; `make corpus` downloads it",
            corpus.display()
        ));
    }
    let checker = checker(corpus)?;
    let mut records = Vec::new();
    for case in cases(corpus)? {
        let folder = corpus.join(&case);
        let a: Value = json(&folder.join("a.json"))?;
        let b: Value = json(&folder.join("b.json"))?;
        let labels: Labels = json(&folder.join("case.json"))?;
        for direction in Direction::BOTH {
            let (wide, narrow, expected) = match direction {
                Direction::ASubsumesB => (&a, &b, labels.a_subsumes_b),
                Direction::BSubsumesA => (&b, &a, labels.b_subsumes_a),
            };
            let start = Instant::now();
            let result = checker.check(wide, narrow);
            let nanos = u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX);
            records.push(Record {
                case: case.clone(),
                direction,
                expected,
                outcome: Outcome::of(&result),
                steps: result.map_or(0, |check| check.steps),
                nanos,
            });
        }
    }
    Ok(records)
}

/// A checker that knows every document the schemas of the corpus refer to.
fn checker(corpus: &Path) -> Result<Checker, String> {
    let resources: Map<String, Value> = json(&corpus.join("resources.json"))?;
    Ok(resources
        .into_iter()
        .fold(Checker::new(), |checker, (uri, document)| {
            checker.resource(&uri, document)
        }))
}

/// The cases of the corpus: every folder that holds a `case.json`, as its path inside the
/// corpus, sorted.
fn cases(corpus: &Path) -> Result<Vec<String>, String> {
    let mut cases = Vec::new();
    let mut pending = vec![PathBuf::new()];
    while let Some(folder) = pending.pop() {
        let absolute = corpus.join(&folder);
        if absolute.join("case.json").is_file() {
            let case = folder.to_str().ok_or("a case path is not UTF-8")?;
            cases.push(case.replace(std::path::MAIN_SEPARATOR, "/"));
            continue;
        }
        let failed = |error| format!("cannot list {}: {error}", absolute.display());
        for entry in fs::read_dir(&absolute).map_err(failed)? {
            let entry = entry.map_err(failed)?;
            if entry.file_type().map_err(failed)?.is_dir() {
                pending.push(folder.join(entry.file_name()));
            }
        }
    }
    if cases.is_empty() {
        return Err(format!(
            "no cases under {}; `make corpus` downloads them",
            corpus.display()
        ));
    }
    cases.sort();
    Ok(cases)
}

fn json<T: DeserializeOwned>(path: &Path) -> Result<T, String> {
    let failed = |error: &dyn std::fmt::Display| format!("cannot read {}: {error}", path.display());
    let text = fs::read_to_string(path).map_err(|error| failed(&error))?;
    serde_json::from_str(&text).map_err(|error| failed(&error))
}
