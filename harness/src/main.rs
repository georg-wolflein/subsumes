//! Runs the library over the benchmark corpus and reports on the results.

mod compare;
mod results;
mod run;

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use compare::{Base, LABEL};
use results::Counts;

const USAGE: &str = "\
usage:
  harness run <corpus> <results>
      Check every case of the corpus in both directions and write one line per check.
      Fails when a verdict contradicts its label or the library rejects a schema.

  harness compare <results> [--base <results>] [--base-label <name>] [--allow-lost] [--output <file>]
      Render the results as the benchmark comment of a pull request, compared with the
      results of the base branch if there are any. Fails when a check that the base
      decided is UNKNOWN now, unless --allow-lost is given.";

/// At most this many failed checks are named on the terminal; the comment has its own limit.
const NAMED: usize = 20;

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let passed = match arguments.split_first() {
        Some((command, rest)) if command == "run" => run(rest),
        Some((command, rest)) if command == "compare" => compare(rest),
        _ => Err(USAGE.to_owned()),
    };
    match passed {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::from(1),
        Err(message) => {
            eprintln!("{message}");
            ExitCode::from(2)
        }
    }
}

fn run(arguments: &[String]) -> Result<bool, String> {
    let [corpus, output] = arguments else {
        return Err(USAGE.to_owned());
    };
    let records = run::run(Path::new(corpus))?;
    let output = Path::new(output);
    if let Some(folder) = output.parent() {
        fs::create_dir_all(folder)
            .map_err(|error| format!("cannot create {}: {error}", folder.display()))?;
    }
    results::write(output, &records)?;

    let counts = Counts::of(&records);
    println!(
        "{} checks: {} YES, {} NO, {} UNKNOWN, {} wrong, {} errors",
        counts.checks, counts.yes, counts.no, counts.unknown, counts.wrong, counts.errors
    );
    println!(
        "{} steps and {:.2} s in the checks",
        counts.steps,
        counts.nanos as f64 / 1e9
    );
    let failed = records
        .iter()
        .filter(|record| record.is_wrong() || record.is_error());
    for record in failed.take(NAMED) {
        eprintln!("{}: {}", record.name(), record.outcome.label());
    }
    Ok(counts.wrong == 0 && counts.errors == 0)
}

fn compare(arguments: &[String]) -> Result<bool, String> {
    let (mut head, mut base, mut base_label, mut output) = (None, None, None, None);
    let mut allow_lost = false;
    let mut arguments = arguments.iter();
    while let Some(argument) = arguments.next() {
        let mut value = || {
            arguments
                .next()
                .ok_or_else(|| format!("{argument} needs a value\n\n{USAGE}"))
        };
        match argument.as_str() {
            "--base" => base = Some(value()?),
            "--base-label" => base_label = Some(value()?),
            "--output" => output = Some(value()?),
            "--allow-lost" => allow_lost = true,
            _ if head.is_none() && !argument.starts_with("--") => head = Some(argument),
            _ => return Err(USAGE.to_owned()),
        }
    }
    let head = results::read(Path::new(head.ok_or(USAGE)?))?;
    let base_records = base
        .map(|path| results::read(Path::new(path)))
        .transpose()?;
    let base = base_records.as_deref().map(|records| Base {
        records,
        label: base_label.map_or("the base", String::as_str),
    });

    let comparison = compare::compare(&head, base.as_ref(), allow_lost);
    match output {
        Some(path) => fs::write(path, &comparison.comment)
            .map_err(|error| format!("cannot write {path}: {error}"))?,
        None => print!("{}", comparison.comment),
    }
    if comparison.lost > 0 && !allow_lost {
        eprintln!(
            "{} checks that the base decided are UNKNOWN now; the label `{LABEL}` on the pull request accepts that",
            comparison.lost
        );
        return Ok(false);
    }
    Ok(true)
}
