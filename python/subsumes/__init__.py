"""JSON Schema inclusion for draft 2020-12.

Does schema A accept every instance that is valid under schema B? If it does, A *subsumes* B::

    from subsumes import subsumes

    new = {"type": "integer"}
    old = {"type": "integer", "minimum": 0}

    verdict = subsumes(new, old)
    if not verdict:
        print("no longer accepted:", verdict.counterexample)

A check that the library cannot decide raises an :class:`UndecidedError`, so a verdict is
always a :class:`Yes` or a :class:`No`.
"""

from dataclasses import dataclass
from typing import Literal, assert_never

from subsumes import _native

__all__ = [
    "BudgetError",
    "Json",
    "No",
    "SchemaError",
    "Side",
    "UndecidedError",
    "UnrepresentableError",
    "UnsupportedError",
    "Verdict",
    "Yes",
    "subsumes",
]

type Json = dict[str, Json] | list[Json] | str | int | float | bool | None
"""A JSON value as ``json.load`` produces it."""

type Side = Literal["a", "b"]
"""One of the two schemas of a check.

``a`` is the schema that should accept everything, the first argument, and ``b`` the schema
whose instances must be accepted, the second.
"""


@dataclass(frozen=True, slots=True)
class Yes:
    """Every instance valid under B is valid under A. As a condition it is true."""

    def __bool__(self) -> Literal[True]:
        return True


@dataclass(frozen=True, slots=True)
class No:
    """Some instance is valid under B and invalid under A. As a condition it is false."""

    counterexample: Json
    """Such an instance. The library does not validate it against the two schemas."""

    def __bool__(self) -> Literal[False]:
        return False


type Verdict = Yes | No
"""The answer to "does A accept every instance that is valid under B?"."""


class UndecidedError(Exception):
    """The library cannot decide the check. The message says why.

    This is no fault of the two schemas, which are valid: see :class:`SchemaError` for
    schemas that are not.
    """


class UnsupportedError(UndecidedError):
    """The answer depends on a construct that the library does not model."""

    side: Side
    """The schema that contains the construct."""

    location: str
    """Where the construct is.

    A URI reference whose fragment is a JSON Pointer, such as
    ``#/properties/tags/uniqueItems``. ``#`` alone is the schema as a whole. For a schema that
    refers to itself in a way that is not modelled, it is the subschema in which the cycle
    closes.
    """

    def __init__(self, message: str, *, side: Side, location: str) -> None:
        super().__init__(message)
        self.side = side
        self.location = location


class UnrepresentableError(UndecidedError):
    """A does not subsume B, and the library found no counterexample that it can give.

    Some instance is valid under B and invalid under A, so the answer is known to be no. It
    is raised all the same, because a :class:`No` carries its counterexample. What cannot be
    given is a number that no JSON value holds exactly, such as one between two floats that
    are next to each other, or a value of more than 127 objects inside one another.
    """


class BudgetError(UndecidedError):
    """The check ran out of its work budget. A larger ``budget`` may decide it."""


class SchemaError(ValueError):
    """A schema cannot be checked at all.

    It is no schema, it declares a dialect other than draft 2020-12, a keyword has a value
    that the draft does not allow, or a reference resolves to nothing.
    """

    side: Side
    """The schema that is at fault."""

    location: str | None
    """Where the fault is, or ``None`` when the schema as a whole is no schema.

    A URI reference whose fragment is a JSON Pointer, such as ``#/properties/age/minimum``.
    Inside a meta-schema of the draft it starts with the URI of that meta-schema.
    """

    def __init__(self, message: str, *, side: Side, location: str | None) -> None:
        super().__init__(message)
        self.side = side
        self.location = location


def subsumes(a: Json, b: Json, *, budget: int | None = None) -> Verdict:
    """Does ``a`` accept every instance that is valid under ``b``?

    A schema is what ``json.load`` gives for its text. An ``int`` that 64 bits do not hold
    is read as the ``float`` nearest to it, and a ``float`` stands for the decimal that
    Python prints it as, so ``0.0075`` is a multiple of ``0.0001``.

    Other threads run while a check does.

    Args:
        a: The schema that should accept everything.
        b: The schema whose instances must be accepted.
        budget: The work that the check may take, in steps. Without one the check has the
            library's default, with which it takes a few seconds at most.

    Returns:
        :class:`Yes`, which is true as a condition, or :class:`No` with a counterexample,
        which is false.

    Raises:
        UndecidedError: The library cannot decide the check. It is an
            :class:`UnsupportedError`, an :class:`UnrepresentableError` or a
            :class:`BudgetError`.
        SchemaError: ``a`` or ``b`` cannot be checked at all.
        TypeError: ``a`` or ``b`` holds an object that is no JSON value, such as a ``set``.
        ValueError: ``a`` or ``b`` holds a value that JSON does not have, such as ``nan``,
            or is nested more than 127 deep.
    """
    outcome = _native.check(a, b, budget)
    match outcome[0]:
        case "yes":
            return Yes()
        case "no":
            return No(outcome[1])
        case "unsupported":
            raise UnsupportedError(outcome[1], side=outcome[2], location=outcome[3])
        case "unrepresentable":
            raise UnrepresentableError(outcome[1])
        case "budget":
            raise BudgetError(outcome[1])
        case "undecided":
            raise UndecidedError(outcome[1])
        case "invalid":
            raise SchemaError(outcome[1], side=outcome[2], location=outcome[3])
        case _ as never:
            assert_never(never)
