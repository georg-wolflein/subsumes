mod compare;
mod inspect;
mod results;
mod run;

use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use clap::{Args, Parser, Subcommand};
use compare::{Base, LABEL};
use results::Counts;

/// Runs the library over the benchmark corpus and reports on the results, and draws what the
/// library makes of two schemas.
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
    /// Fails when a check that the base decided is Unknown now, unless --allow-lost is given.
    Compare(CompareArguments),
    /// Draw the schema graph of two schemas and open the picture in the browser.
    ///
    /// The graph is what the library makes of the schemas before it compares them: every
    /// subschema with the keywords it asserts, and where each reference leads. The picture is
    /// one HTML page in the temporary folder, which loads Graphviz from a CDN. It opens in the
    /// program that BROWSER names, or else in the default browser.
    Inspect(InspectArguments),
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
    /// Pass even when a check that the base decided is Unknown now.
    #[arg(long)]
    allow_lost: bool,
    /// Write the comment to this file and not to the terminal.
    #[arg(long, value_name = "FILE")]
    output: Option<PathBuf>,
}

#[derive(Args)]
struct InspectArguments {
    /// The file of schema A.
    a: PathBuf,
    /// The file of schema B. Without it, B is the schema `true`.
    b: Option<PathBuf>,
}

/// At most this many failed checks are named on the terminal; the comment has its own limit.
const NAMED: usize = 20;

fn main() -> ExitCode {
    let passed = match Cli::parse().command {
        Command::Run(arguments) => run(&arguments),
        Command::Compare(arguments) => compare(&arguments),
        Command::Inspect(arguments) => inspect(&arguments),
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
        "{} checks: {} Yes, {} No, {} Unknown, {} wrong, {} errors",
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
            "{} checks that the base decided are Unknown now; the label `{LABEL}` on the pull request accepts that",
            comparison.lost
        );
        return Ok(false);
    }
    Ok(true)
}

fn inspect(arguments: &InspectArguments) -> Result<bool, String> {
    let page = inspect::page(&arguments.a, arguments.b.as_deref())?;
    let path = env::temp_dir().join("subsumes-inspect.html");
    fs::write(&path, page).map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    println!("{}", path.display());
    inspect::open(&path)?;
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
