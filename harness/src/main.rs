//! The tools of the repository that link the library: the adapter that the benchmark's runner
//! drives, and the viewer of what the library makes of two schemas.

mod adapter;
mod inspect;
#[cfg(test)]
mod validator;

use std::path::PathBuf;
use std::process::ExitCode;
use std::{env, fs};

use clap::{Args, Parser, Subcommand};

/// Answers the benchmark's runner for the library, and draws what the library makes of two
/// schemas.
#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Answer the requests of the benchmark's runner, one JSON line each.
    ///
    /// The runner starts this itself, as `checker.json` says: `make benchmark` runs the
    /// library over the corpus.
    Adapter,
    /// Draw the schema graph of two schemas and open the picture in the browser.
    ///
    /// The graph is what the library makes of the schemas before it compares them: every
    /// subschema with the keywords it asserts, and where each reference leads. The picture is
    /// one HTML page in the temporary folder, which loads Graphviz from a CDN. It opens in the
    /// program that BROWSER names, or else in the default browser.
    Inspect(InspectArguments),
}

#[derive(Args)]
struct InspectArguments {
    /// The file of schema A.
    a: PathBuf,
    /// The file of schema B. Without it, B is the schema `true`.
    b: Option<PathBuf>,
}

fn main() -> ExitCode {
    let done = match Cli::parse().command {
        Command::Adapter => adapter::serve().map_err(|error| error.to_string()),
        Command::Inspect(arguments) => inspect(&arguments),
    };
    match done {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::from(2)
        }
    }
}

fn inspect(arguments: &InspectArguments) -> Result<(), String> {
    let page = inspect::page(&arguments.a, arguments.b.as_deref())?;
    let path = env::temp_dir().join("subsumes-inspect.html");
    fs::write(&path, page).map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    println!("{}", path.display());
    inspect::open(&path)
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
