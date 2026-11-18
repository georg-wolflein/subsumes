"""What a change does to a schema: the two checks, and what each of them says.

The old version of a schema is ``old`` and the changed one ``new`` in every name. The library
names its arguments ``a`` and ``b``, and which is which depends on the direction:

- ``backward`` is ``subsumes(new, old)``: the schema accepts everything it did.
- ``forward`` is ``subsumes(old, new)``: the schema accepts nothing new.
"""

import json
from dataclasses import dataclass
from typing import Literal, Self, assert_never

from subsumes import (
    Budget,
    Json,
    No,
    Reason,
    RegexDialect,
    SchemaError,
    Side,
    Unknown,
    Unrepresentable,
    Unsupported,
    Yes,
    subsumes,
)

type Direction = Literal["backward", "forward"]
"""One of the two questions that are asked of a change."""

type Version = Literal["old", "new"]
"""One of the two versions of a schema."""


@dataclass(frozen=True, slots=True)
class Holds:
    """The answer is yes."""


@dataclass(frozen=True, slots=True)
class Example:
    """An instance that one version accepts and the other does not.

    It has a class of its own because ``None`` is an instance too.
    """

    value: Json


@dataclass(frozen=True, slots=True)
class Broken:
    """The answer is no."""

    example: Example | None
    """An instance that shows it, or ``None`` where the library knows of one and cannot give it."""


@dataclass(frozen=True, slots=True)
class Undecided:
    """There is no answer."""

    reason: str
    """Why not, to follow "is not decided:" in a sentence."""


type Outcome = Holds | Broken | Undecided
"""What one check of a change says."""


@dataclass(frozen=True, slots=True)
class Settings:
    """How the library is to check, which the workflow may say. The defaults are its own."""

    budget: int | None = None
    """The work that each check may take, in steps, or ``None`` for the default."""

    regex_dialect: RegexDialect = "ecma262"
    """The dialect that every ``pattern`` is read in, in both versions of a schema."""


@dataclass(frozen=True, slots=True)
class Changed:
    """A schema that both commits have, with different text."""

    path: str
    backward: Outcome
    forward: Outcome

    def outcome(self, direction: Direction) -> Outcome:
        match direction:
            case "backward":
                return self.backward
            case "forward":
                return self.forward
            case _ as never:
                assert_never(never)


@dataclass(frozen=True, slots=True)
class Added:
    """A file that only the new commit has, so there is nothing to compare it with."""

    path: str


@dataclass(frozen=True, slots=True)
class Deleted:
    """A file that only the old commit has."""

    path: str


@dataclass(frozen=True, slots=True)
class Invalid:
    """A file whose new version is no schema that the library reads."""

    path: str
    message: str
    """Why not, as a sentence without its full stop."""


type Entry = Changed | Added | Deleted | Invalid
"""What happened to one file."""


@dataclass(frozen=True, slots=True)
class Refusal:
    """Why the text of a file is no schema that the library reads."""

    message: str


@dataclass(frozen=True, slots=True)
class Schema:
    """A schema that the library reads."""

    value: Json

    @classmethod
    def read(cls, text: bytes) -> Self | Refusal:
        """The schema that the text of a file holds, or why it holds none."""
        try:
            value: Json = json.loads(text.decode("utf-8-sig"))
        except UnicodeDecodeError:
            return Refusal("the file is not UTF-8")
        except json.JSONDecodeError as error:
            return Refusal(f"the file is not JSON: {error}")
        except RecursionError:
            return Refusal("the file is nested too deep")
        try:
            # The schema `true` accepts everything, so this asks nothing of the schema but
            # that the library reads it. A schema that it reads and cannot decide is one.
            subsumes(True, value)
        except SchemaError as error:
            if error.location is None:
                return Refusal("the file holds neither an object nor a boolean")
            return Refusal(_without_side(error))
        except ValueError as error:
            # A value that JSON does not have and that Python reads all the same, such as `NaN`.
            return Refusal(_without_side(error))
        return cls(value)

    def text(self) -> str:
        """The schema as text that two files share exactly when they hold the same schema.

        Neither white space nor the order of the keys tells two schemas apart. ``1`` and
        ``true`` do, which are equal as Python values.
        """
        return json.dumps(self.value, sort_keys=True)


def _without_side(error: ValueError) -> str:
    """The message of an error about the schema in :meth:`Schema.read`, which is schema B.

    The library says where the fault is as "<location> in schema B". A reader of the report
    knows of no schema B, and the file is named next to the message.
    """
    return str(error).replace(" in schema B", "", 1)


def version(direction: Direction, side: Side) -> Version:
    """The version that stands on ``side`` of the check in ``direction``."""
    match direction, side:
        case ("backward", "a") | ("forward", "b"):
            return "new"
        case ("backward", "b") | ("forward", "a"):
            return "old"
        case _ as never:
            assert_never(never)


def check(direction: Direction, old: Schema, new: Schema, settings: Settings) -> Outcome:
    """Asks the library the question of ``direction`` about a change from ``old`` to ``new``."""
    match direction:
        case "backward":
            a, b = new, old
        case "forward":
            a, b = old, new
        case _ as never:
            assert_never(never)
    verdict = subsumes(
        a.value, b.value, budget=settings.budget, regex_dialect=settings.regex_dialect
    )
    match verdict:
        case Yes():
            return Holds()
        case No(counterexample):
            return Broken(Example(counterexample))
        case Unknown(reason):
            return unknown(direction, reason)
        case _ as never:
            assert_never(never)


def unknown(direction: Direction, reason: Reason) -> Outcome:
    """What a check in ``direction`` says that the library did not decide for ``reason``."""
    match reason:
        case Unsupported(side, location):
            where = version(direction, side)
            return Undecided(f"{location} in the {where} version is not supported")
        case Unrepresentable():
            # The library knows that the answer is no, and has no instance to show it.
            return Broken(None)
        case Budget():
            return Undecided("the check ran out of its budget")
        case _ as never:
            assert_never(never)


def compare(path: str, old: bytes | None, new: bytes | None, settings: Settings) -> Entry | None:
    """What happened to the file at ``path``, or ``None`` if it holds the schema that it did.

    Args:
        path: The path of the file.
        old: Its text in the old commit, or ``None`` if the commit does not have it.
        new: Its text in the checkout, or ``None`` if it is not there.
        settings: How the library is to check.
    """
    if old == new:
        return None
    if new is None:
        return Deleted(path)
    if old is None:
        return Added(path)
    new_schema = Schema.read(new)
    if isinstance(new_schema, Refusal):
        return Invalid(path, new_schema.message)
    old_schema = Schema.read(old)
    if isinstance(old_schema, Refusal):
        # What the old version accepted is not known, so neither question has an answer.
        undecided = Undecided(f"the old version is no schema ({old_schema.message})")
        return Changed(path, undecided, undecided)
    if old_schema.text() == new_schema.text():
        return None
    return Changed(
        path,
        backward=check("backward", old_schema, new_schema, settings),
        forward=check("forward", old_schema, new_schema, settings),
    )
