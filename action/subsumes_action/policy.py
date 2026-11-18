"""What the workflow requires of a change, and which changes fall short of it."""

from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, assert_never

from subsumes_action.compare import (
    Added,
    Broken,
    Changed,
    Deleted,
    Direction,
    Entry,
    Holds,
    Invalid,
    Outcome,
    Undecided,
)

if TYPE_CHECKING:
    from collections.abc import Iterable, Sequence

type Compatibility = Literal["backward", "forward", "full", "none"]
"""Which of the two questions must be answered with yes."""

type OnUnknown = Literal["fail", "warn"]
"""What a required question without an answer does."""

type Level = Literal["passes", "warns", "fails"]
"""What an outcome means for the workflow."""

DIRECTIONS: Sequence[Direction] = ("backward", "forward")
"""Both questions, in the order in which a report has them."""


def gravest(levels: Iterable[Level]) -> Level:
    """The level that decides, where several outcomes each have one."""
    found = set(levels)
    if "fails" in found:
        return "fails"
    return "warns" if "warns" in found else "passes"


@dataclass(frozen=True, slots=True)
class Policy:
    """What the workflow requires.

    The action fails when a required question is not answered with yes: on a no, on a schema
    that the library does not read, and on a question without an answer unless ``unknown`` is
    ``warn``. Where nothing is required, nothing fails.
    """

    compatibility: Compatibility
    unknown: OnUnknown

    def required(self) -> Sequence[Direction]:
        """The questions that must be answered with yes."""
        match self.compatibility:
            case "backward":
                return ["backward"]
            case "forward":
                return ["forward"]
            case "full":
                return ["backward", "forward"]
            case "none":
                return []
            case _ as never:
                assert_never(never)

    def level(self, direction: Direction, outcome: Outcome) -> Level:
        """What ``outcome`` means as the answer to the question of ``direction``."""
        if direction not in self.required():
            return "passes"
        match outcome:
            case Holds():
                return "passes"
            case Broken():
                return "fails"
            case Undecided():
                return "fails" if self.unknown == "fail" else "warns"
            case _ as never:
                assert_never(never)

    def judge(self, entry: Entry) -> Level:
        """What happened to a file, as the workflow sees it."""
        match entry:
            case Changed():
                return gravest(self.level(d, entry.outcome(d)) for d in DIRECTIONS)
            case Invalid():
                return "fails" if self.required() else "passes"
            case Added() | Deleted():
                return "passes"
            case _ as never:
                assert_never(never)
