mod compare;
mod results;
mod run;

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand};
use compare::{Base, LABEL};
use results::Counts;

/// Runs the library over the benchmark corpus and reports on the results.
#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Check every case of the corpus in both directions and write one line per check.
    ///
    /// Fails when a verdict contradicts its label or the library rejects a schema.
    Run(RunArguments),
    /// Render the results as the benchmark comment of a pull request.
    ///
    /// Fails when a check that the base decided is UNKNOWN now, unless --allow-lost is given.
    Compare(CompareArguments),
}

#[derive(Args)]
struct RunArguments {
    /// The folder of the unpacked corpus.
    corpus: PathBuf,
    /// The results file to write.
    results: PathBuf,
}

#[derive(Args)]
struct CompareArguments {
    /// The results file of a run.
    results: PathBuf,
    /// The results file of the base branch, to compare with.
    #[arg(long, value_name = "RESULTS")]
    base: Option<PathBuf>,
    /// What the comment calls the base, such as its commit.
    #[arg(long, value_name = "NAME")]
    base_label: Option<String>,
    /// Pass even when a check that the base decided is UNKNOWN now.
    #[arg(long)]
    allow_lost: bool,
    /// Write the comment to this file and not to the terminal.
    #[arg(long, value_name = "FILE")]
    output: Option<PathBuf>,
}

/// At most this many failed checks are named on the terminal; the comment has its own limit.
const NAMED: usize = 20;

fn main() -> ExitCode {
    let passed = match Cli::parse().command {
        Command::Run(arguments) => run(&arguments),
        Command::Compare(arguments) => compare(&arguments),
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

fn run(arguments: &RunArguments) -> Result<bool, String> {
    let records = run::run(&arguments.corpus)?;
    if let Some(folder) = arguments.results.parent() {
        fs::create_dir_all(folder)
            .map_err(|error| format!("cannot create {}: {error}", folder.display()))?;
    }
    results::write(&arguments.results, &records)?;

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

fn compare(arguments: &CompareArguments) -> Result<bool, String> {
    let head = results::read(&arguments.results)?;
    let base_records = arguments.base.as_deref().map(results::read).transpose()?;
    let base = base_records.as_deref().map(|records| Base {
        records,
        label: arguments.base_label.as_deref().unwrap_or("the base"),
    });

    let comparison = compare::compare(&head, base.as_ref(), arguments.allow_lost);
    match &arguments.output {
        Some(path) => fs::write(path, &comparison.comment)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?,
        None => print!("{}", comparison.comment),
    }
    if comparison.lost > 0 && !arguments.allow_lost {
        eprintln!(
            "{} checks that the base decided are UNKNOWN now; the label `{LABEL}` on the pull request accepts that",
            comparison.lost
        );
        return Ok(false);
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use clap::CommandFactory;

    use super::*;

    #[test]
    fn the_arguments_are_declared_consistently() {
        Cli::command().debug_assert();
    }
}
