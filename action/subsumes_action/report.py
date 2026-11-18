"""The report of a run as Markdown, for the job summary and for the comment on a pull request.

Paths, examples and messages come from the files of a pull request, which anyone may open.
So none of them is written as Markdown: a path and an example stand in code, and a message
has its punctuation escaped.
"""

import json
import re
from typing import TYPE_CHECKING, assert_never

from subsumes_action.compare import (
    Added,
    Broken,
    Changed,
    Deleted,
    Direction,
    Entry,
    Example,
    Holds,
    Invalid,
    Outcome,
    Undecided,
)
from subsumes_action.policy import DIRECTIONS, Level, Policy, gravest

if TYPE_CHECKING:
    from collections.abc import Sequence

ROWS = 100
"""At most this many files are rows of the table."""

BLOCKS = 20
"""At most this many examples and reasons follow the table."""

EXAMPLE = 1000
"""An example is cut after this many characters.

With the two limits above it keeps a report below the 65,536 characters of a comment.
"""

HOMEPAGE = "https://github.com/georg-wolflein/subsumes"

QUESTION: dict[Direction, str] = {
    "backward": "accepts everything it did",
    "forward": "accepts nothing new",
}
"""What each direction asks of a schema, to follow its name in a sentence."""

MARK: dict[Level, str] = {"passes": "", "warns": ":warning: ", "fails": ":x: "}


def render(entries: Sequence[Entry], policy: Policy) -> str:
    """The report on the files that changed, which are ``entries``."""
    if not entries:
        return "### Schema changes\n\nNo schema changed.\n"
    rows = [_row(entry, policy) for entry in entries[:ROWS]]
    if len(entries) > ROWS:
        rows.append(f"| and {len(entries) - ROWS} more | | |")
    blocks = [block for entry in entries for block in _blocks(entry)]
    if len(blocks) > BLOCKS:
        left_out = len(blocks) - BLOCKS
        blocks = [*blocks[:BLOCKS], f"And {left_out} more, which the log of the job has."]
    parts = [
        "### Schema changes",
        _summary(entries, policy),
        "\n".join(
            [
                f"| Schema | {_heading('backward')} | {_heading('forward')} |",
                "| --- | --- | --- |",
                *rows,
            ]
        ),
        *blocks,
        f"<sub>Checked by [subsumes]({HOMEPAGE}).</sub>",
    ]
    return "\n\n".join(parts) + "\n"


def describe(entry: Entry) -> Sequence[str]:
    """What happened to a file as lines of plain text, with every example in full."""
    match entry:
        case Changed():
            return [
                f"{entry.path}: {QUESTION[direction]}: {_plainly(entry.outcome(direction))}"
                for direction in DIRECTIONS
            ]
        case Added():
            return [f"{entry.path}: new file, nothing to compare it with"]
        case Deleted():
            return [f"{entry.path}: deleted"]
        case Invalid():
            return [f"{entry.path}: no schema that the library reads: {entry.message}"]
        case _ as never:
            assert_never(never)


def example_text(example: Example) -> str:
    """An example as JSON on one line, with every character outside ASCII escaped."""
    return json.dumps(example.value, ensure_ascii=True)


def _plainly(outcome: Outcome) -> str:
    match outcome:
        case Holds():
            return "yes"
        case Broken():
            if outcome.example is None:
                return "no, and no example can be given"
            return f"no, as shows {example_text(outcome.example)}"
        case Undecided():
            return f"not decided: {outcome.reason}"
        case _ as never:
            assert_never(never)


def _heading(direction: Direction) -> str:
    question = QUESTION[direction]
    return question[0].upper() + question[1:]


def _summary(entries: Sequence[Entry], policy: Policy) -> str:
    """One sentence on whether the changes meet what the workflow requires."""
    match policy.compatibility:
        case "none":
            return "Nothing is required of these changes (`compatibility: none`)."
        case "backward":
            must = "accept everything it did"
        case "forward":
            must = "accept nothing new"
        case "full":
            must = "accept exactly what it did"
        case _ as never:
            assert_never(never)
    rule = f"`compatibility: {policy.compatibility}`"
    levels = [policy.judge(entry) for entry in entries]
    of = f"of {len(entries)} changed {'schema' if len(entries) == 1 else 'schemas'}"
    match gravest(levels):
        case "fails":
            count = levels.count("fails")
            verb = "does" if count == 1 else "do"
            return f":x: {count} {of} {verb} not meet {rule}: a schema must {must}."
        case "warns":
            count = levels.count("warns")
            return f":warning: {rule} is not decided for {count} {of}: a schema must {must}."
        case "passes":
            return f":white_check_mark: The changes meet {rule}: a schema must {must}."
        case _ as never:
            assert_never(never)


def _row(entry: Entry, policy: Policy) -> str:
    path = _code(entry.path).replace("|", "\\|")
    match entry:
        case Changed():
            cells = [
                MARK[policy.level(direction, entry.outcome(direction))]
                + _verdict(entry.outcome(direction))
                for direction in DIRECTIONS
            ]
        case Added():
            cells = ["new file", ""]
        case Deleted():
            cells = ["deleted", ""]
        case Invalid():
            cells = [MARK[policy.judge(entry)] + "not a schema", ""]
        case _ as never:
            assert_never(never)
    return f"| {path} | {cells[0]} | {cells[1]} |"


def _verdict(outcome: Outcome) -> str:
    match outcome:
        case Holds():
            return "Yes"
        case Broken():
            return "**No**"
        case Undecided():
            return "Unknown"
        case _ as never:
            assert_never(never)


def _blocks(entry: Entry) -> Sequence[str]:
    """The paragraphs below the table that say more about a file than its row does."""
    path = _code(entry.path)
    match entry:
        case Changed(backward=Undecided(reason), forward=Undecided(same)) if reason == same:
            return [f"What the change to {path} does is not decided: {_escape(reason)}."]
        case Changed():
            return [
                block
                for direction in DIRECTIONS
                if (block := _block(path, direction, entry.outcome(direction))) is not None
            ]
        case Invalid():
            return [f"{path} is no schema that the library reads: {_escape(entry.message)}."]
        case Added() | Deleted():
            return []
        case _ as never:
            assert_never(never)


def _block(path: str, direction: Direction, outcome: Outcome) -> str | None:
    match direction:
        case "backward":
            verb = "no longer accepts"
        case "forward":
            verb = "newly accepts"
        case _ as never:
            assert_never(never)
    match outcome:
        case Holds():
            return None
        case Broken():
            if outcome.example is None:
                return (
                    f"{path} {verb} some instance. The library knows that there is one and "
                    "cannot give it: a number that a JSON value does not hold exactly, or a "
                    "value that is nested too deep."
                )
            return f"{path} {verb}:\n\n{_fenced(example_text(outcome.example))}"
        case Undecided():
            asked = f"Whether {path} {QUESTION[direction]}"
            return f"{asked} is not decided: {_escape(outcome.reason)}."
        case _ as never:
            assert_never(never)


def _fenced(text: str) -> str:
    """A code block of JSON, cut at ``EXAMPLE`` characters, that no backtick in it can end."""
    note = ""
    if len(text) > EXAMPLE:
        text = text[:EXAMPLE] + " …"
        note = f"\n\nCut after {EXAMPLE:,} characters. The log of the job has all of it."
    fence = "`" * max(3, _longest_run(text) + 1)
    return f"{fence}json\n{text}\n{fence}{note}"


def _code(text: str) -> str:
    """Inline code that holds ``text``, whatever backticks are in it."""
    text = " ".join(text.splitlines()) or " "
    fence = "`" * (_longest_run(text) + 1)
    pad = " " if text.startswith("`") or text.endswith("`") else ""
    return f"{fence}{pad}{text}{pad}{fence}"


def _longest_run(text: str) -> int:
    """The length of the longest run of backticks in ``text``."""
    return max((len(run) for run in re.findall(r"`+", text)), default=0)


def _escape(text: str) -> str:
    """A message as plain text of one line: every character that Markdown reads is escaped."""
    return re.sub(r"([!-/:-@\[-`{-~])", r"\\\1", " ".join(text.splitlines()))
