"""The step of the action: compare, report, and say whether the workflow is to fail.

It ends with 0 whatever the schemas are, and writes ``failed`` to the outputs of the step:
the action fails in a later step, after the comment is posted. It ends with 2 when it cannot
do its work, such as for an input that it does not understand.
"""

import argparse
import os
import sys
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING, Literal, assert_never

from subsumes_action.base import Base, GitError
from subsumes_action.compare import (
    Added,
    Broken,
    Changed,
    Deleted,
    Direction,
    Entry,
    Holds,
    Invalid,
    Settings,
    Undecided,
    compare,
)
from subsumes_action.policy import DIRECTIONS, Level, Policy, gravest
from subsumes_action.report import QUESTION, describe, example_text, render

if TYPE_CHECKING:
    from collections.abc import Sequence

ANNOTATED = 200
"""An example in an annotation is cut after this many characters."""


class InputError(Exception):
    """An input of the action has a value that it cannot work with."""


def main(arguments: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="subsumes-action", description=__doc__)
    parser.add_argument("--files", required=True, help="glob patterns, one on a line")
    parser.add_argument("--base", required=True, help="the commit to compare with")
    parser.add_argument(
        "--compatibility", required=True, choices=["backward", "forward", "full", "none"]
    )
    parser.add_argument("--unknown", required=True, choices=["fail", "warn"])
    parser.add_argument("--budget", default="", help="the steps of a check; empty for the default")
    parser.add_argument("--regex-dialect", required=True, choices=["ecma262", "rust"])
    parser.add_argument(
        "--report", required=True, type=Path, help="the file to write the report to"
    )
    parser.add_argument("--directory", default=Path(), type=Path, help="the checkout")
    options = parser.parse_args(arguments)
    policy = Policy(options.compatibility, options.unknown)
    try:
        settings = Settings(budget(options.budget), options.regex_dialect)
        entries = changes(options.directory, patterns(options.files), options.base, settings)
    except (InputError, GitError) as error:
        print(command("error", str(error)))
        return 2

    levels = [policy.judge(entry) for entry in entries]
    for entry in entries:
        for line in describe(entry):
            # A path may hold a line end, and a line of its own could be read as a command.
            print("- " + line.replace("\r", "\\r").replace("\n", "\\n"))
        for level, message in findings(entry, policy):
            print(command("error" if level == "fails" else "warning", message, file=entry.path))
    if not entries:
        print("No schema changed.")

    report = render(entries, policy)
    options.report.write_text(report, encoding="utf-8")
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(summary).open("a", encoding="utf-8") as file:
            file.write(report)
    if outputs := os.environ.get("GITHUB_OUTPUT"):
        failed = "true" if gravest(levels) == "fails" else "false"
        with Path(outputs).open("a", encoding="utf-8") as file:
            file.write(f"report={options.report}\nchanged={len(entries)}\nfailed={failed}\n")
    return 0


def patterns(text: str) -> Sequence[str]:
    """The patterns of the input ``files``: one on a line, relative to the checkout."""
    found = [line.strip() for line in text.splitlines() if line.strip()]
    if not found:
        raise InputError("the input `files` names no file")
    for pattern in found:
        path = PurePosixPath(pattern)
        if path.is_absolute() or ".." in path.parts or "\\" in pattern:
            raise InputError(
                f"the pattern {pattern!r} of the input `files` must be a path below the "
                "checkout, with `/` between its parts"
            )
    return found


def budget(text: str) -> int | None:
    """The input ``budget``: a number of steps, or nothing for the default of the library."""
    if not text.strip():
        return None
    if not text.strip().isascii() or not text.strip().isdecimal():
        raise InputError(f"the input `budget` must be a whole number of steps, not {text!r}")
    return int(text)


def changes(
    directory: Path, patterns: Sequence[str], ref: str, settings: Settings
) -> Sequence[Entry]:
    """What happened to each file that matches a pattern, between ``ref`` and the checkout.

    A file whose schema is the same on both sides is left out, also where its text is not:
    the order of the keys and the white space are no part of a schema.
    """
    if not ref.strip():
        raise InputError(
            "there is no commit to compare with: this event names none, so set the input `base`"
        )
    if set(ref.strip()) == {"0"}:
        # What a push gives as the commit before it when it creates the branch.
        print(command("notice", "There is no earlier commit to compare with."))
        return []
    base = Base.find(directory, ref.strip())
    before = {path for path in base.paths() if matches(path, patterns)}
    now = {
        path.relative_to(directory).as_posix()
        for pattern in patterns
        for path in directory.glob(pattern, case_sensitive=True)
        if path.is_file()
    }
    now = {path for path in now if PurePosixPath(path).parts[0] != ".git"}
    entries = [
        compare(
            path,
            old=base.read(path) if path in before else None,
            new=(directory / path).read_bytes() if path in now else None,
            settings=settings,
        )
        for path in sorted(before | now)
    ]
    return [entry for entry in entries if entry is not None]


def matches(path: str, patterns: Sequence[str]) -> bool:
    """Whether a path of the old commit is one that a pattern names."""
    return any(PurePosixPath(path).full_match(pattern, case_sensitive=True) for pattern in patterns)


def findings(entry: Entry, policy: Policy) -> Sequence[tuple[Level, str]]:
    """What is to be said next to a file in the pull request, each with its level."""
    match entry:
        case Changed():
            found: list[tuple[Level, str]] = []
            for direction in DIRECTIONS:
                outcome = entry.outcome(direction)
                if not isinstance(outcome, Holds):
                    found.append((policy.level(direction, outcome), finding(direction, outcome)))
        case Invalid():
            found = [(policy.judge(entry), f"No schema that the library reads: {entry.message}")]
        case Added() | Deleted():
            found = []
        case _ as never:
            assert_never(never)
    return [(level, message) for level, message in found if level != "passes"]


def finding(direction: Direction, outcome: Broken | Undecided) -> str:
    match direction:
        case "backward":
            verb = "no longer accepts"
        case "forward":
            verb = "newly accepts"
        case _ as never:
            assert_never(never)
    match outcome:
        case Broken():
            if outcome.example is None:
                return f"The schema {verb} some instance, of which no example can be given"
            text = example_text(outcome.example)
            return (
                f"The schema {verb} {text if len(text) <= ANNOTATED else text[:ANNOTATED] + ' …'}"
            )
        case Undecided():
            return f"Whether the schema {QUESTION[direction]} is not decided: {outcome.reason}"
        case _ as never:
            assert_never(never)


def command(
    kind: Literal["error", "warning", "notice"], message: str, *, file: str | None = None
) -> str:
    """A workflow command that shows ``message`` in the run, next to ``file`` if one is given."""
    data = message.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    if file is None:
        return f"::{kind}::{data}"
    name = file.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
    name = name.replace(":", "%3A").replace(",", "%2C")
    return f"::{kind} file={name},title=Schema compatibility::{data}"


if __name__ == "__main__":
    sys.exit(main())
