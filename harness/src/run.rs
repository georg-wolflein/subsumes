//! Running the library over the corpus.

use std::fs;
use std::num::NonZeroUsize;
use std::panic::resume_unwind;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;
use std::time::Instant;

use serde::Deserialize;
use serde::de::DeserializeOwned;
use serde_json::Value;
use subsumes::Checker;

use crate::counterexample;
use crate::results::{Direction, Outcome, Record};

/// The labels of a case, from its `case.json`.
#[derive(Deserialize)]
struct Labels {
    a_subsumes_b: Option<bool>,
    b_subsumes_a: Option<bool>,
}

/// The stack of a job. It is what the main thread has where nothing else is set, so a case is
/// checked with the room that it has without jobs.
const STACK: usize = 8 << 20;

/// Checks every case of the corpus in both directions and asks a validator about every
/// counterexample. The records are in the order of the case paths, however many jobs there
/// are.
///
/// One job checks the cases one after the other, which is how the time of a check is measured.
/// More jobs check so many cases at once. That is faster, and the times are then no more than
/// a hint, since the checks share the machine.
pub fn run(corpus: &Path, jobs: NonZeroUsize) -> Result<Vec<Record>, String> {
    if !corpus.is_dir() {
        return Err(format!(
            "there is no corpus at {}; `make corpus` downloads it",
            corpus.display()
        ));
    }
    let checker = Checker::new();
    let cases = cases(corpus)?;
    let next = AtomicUsize::new(0);
    let failed = AtomicBool::new(false);
    // A job takes the next case that no job has taken, until none is left or one has failed.
    let job = || {
        let mut checked = Vec::new();
        while !failed.load(Ordering::Relaxed) {
            let index = next.fetch_add(1, Ordering::Relaxed);
            let Some(case) = cases.get(index) else {
                break;
            };
            let records = check(corpus, case, &checker);
            failed.fetch_or(records.is_err(), Ordering::Relaxed);
            checked.push((index, records));
        }
        checked
    };
    let mut checked = thread::scope(|scope| {
        let mut running = Vec::new();
        for _ in 0..jobs.get() {
            let builder = thread::Builder::new().stack_size(STACK);
            let started = builder.spawn_scoped(scope, job);
            running.push(started.map_err(|error| format!("cannot start a job: {error}"))?);
        }
        let mut checked = Vec::new();
        for started in running {
            checked.extend(started.join().unwrap_or_else(|panic| resume_unwind(panic)));
        }
        Ok::<_, String>(checked)
    })?;
    checked.sort_by_key(|(index, _)| *index);
    let mut records = Vec::with_capacity(2 * cases.len());
    for (_, of_case) in checked {
        records.extend(of_case?);
    }
    Ok(records)
}

/// Checks one case in both directions.
fn check(corpus: &Path, case: &str, checker: &Checker) -> Result<[Record; 2], String> {
    let folder = corpus.join(case);
    let a: Value = json(&folder.join("a.json"))?;
    let b: Value = json(&folder.join("b.json"))?;
    let labels: Labels = json(&folder.join("case.json"))?;
    Ok(Direction::BOTH.map(|direction| {
        let (wide, narrow, expected) = match direction {
            Direction::ASubsumesB => (&a, &b, labels.a_subsumes_b),
            Direction::BSubsumesA => (&b, &a, labels.b_subsumes_a),
        };
        let start = Instant::now();
        let result = checker.check(wide, narrow);
        let nanos = u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX);
        // The validator is asked after the clock has stopped.
        let outcome = Outcome::of(&result, |counterexample| {
            counterexample::confirmation(wide, narrow, counterexample)
        });
        Record {
            case: case.to_owned(),
            direction,
            expected,
            outcome,
            steps: result.map_or(0, |check| check.steps),
            nanos,
        }
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

pub fn json<T: DeserializeOwned>(path: &Path) -> Result<T, String> {
    let failed = |error: &dyn std::fmt::Display| format!("cannot read {}: {error}", path.display());
    let text = fs::read_to_string(path).map_err(|error| failed(&error))?;
    serde_json::from_str(&text).map_err(|error| failed(&error))
}

#[cfg(test)]
mod tests {
    use std::env;
    use std::process;

    use serde_json::json;

    use super::*;

    /// A corpus of so many cases in a folder of its own, which the test removes. In each
    /// case A takes strings of up to as many characters as the case has for a number, and B
    /// of one more, so no two cases have the same counterexample.
    fn corpus(name: &str, cases: u64) -> PathBuf {
        let corpus = env::temp_dir().join(format!("subsumes-harness-{}-{name}", process::id()));
        for case in 0..cases {
            let folder = corpus.join("strings").join(format!("{case:02}"));
            fs::create_dir_all(&folder).unwrap();
            let write = |file: &str, value: Value| {
                fs::write(folder.join(file), value.to_string()).unwrap();
            };
            write("a.json", json!({"type": "string", "maxLength": case}));
            write("b.json", json!({"type": "string", "maxLength": case + 1}));
            write(
                "case.json",
                json!({"a_subsumes_b": false, "b_subsumes_a": true}),
            );
        }
        corpus
    }

    fn jobs(count: usize) -> NonZeroUsize {
        NonZeroUsize::new(count).unwrap()
    }

    #[test]
    fn the_records_are_the_same_however_many_jobs_there_are() {
        let corpus = corpus("jobs", 12);
        // All but the time, which no two runs agree on.
        let records = |count: usize| {
            let records = run(&corpus, jobs(count)).unwrap();
            let timeless = records
                .into_iter()
                .map(|record| Record { nanos: 0, ..record });
            timeless.collect::<Vec<_>>()
        };
        let one = records(1);
        let (three, many) = (records(3), records(40));
        fs::remove_dir_all(&corpus).unwrap();

        // Both directions of each case, in the order of the case paths.
        let cases: Vec<&str> = one.iter().map(|record| record.case.as_str()).collect();
        let expected: Vec<String> = (0..12).map(|case| format!("strings/{case:02}")).collect();
        let twice = expected
            .iter()
            .flat_map(|case| [case.as_str(), case.as_str()]);
        assert_eq!(cases, twice.collect::<Vec<_>>());
        assert!(
            one.iter()
                .all(|record| !record.is_wrong() && !record.is_error())
        );
        assert_eq!(three, one);
        assert_eq!(many, one);
    }

    #[test]
    fn a_case_that_cannot_be_read_ends_the_run() {
        let corpus = corpus("unreadable", 6);
        fs::remove_file(corpus.join("strings/02/b.json")).unwrap();
        let results = [run(&corpus, jobs(1)), run(&corpus, jobs(3))];
        fs::remove_dir_all(&corpus).unwrap();
        for result in results {
            let error = result.unwrap_err();
            assert!(error.starts_with("cannot read "), "{error}");
            assert!(error.contains("b.json"), "{error}");
        }
    }
}
