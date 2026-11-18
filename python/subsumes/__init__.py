"""JSON Schema inclusion for draft 2020-12.

Does schema A accept every instance that is valid under schema B? If it does, A *subsumes* B::

    from subsumes import subsumes

    new = {"type": "integer"}
    old = {"type": "integer", "minimum": 0}

    match subsumes(new, old):
        case Yes():
            print("compatible")
        case No(counterexample):
            print("no longer accepted:", counterexample)
        case Unknown(reason):
            print("not decided:", reason)

A :class:`Yes` and a :class:`No` are returned only when certain. A check that the library
cannot decide returns an :class:`Unknown` with the reason, which is no condition: asking
whether it is true raises.
"""

from dataclasses import dataclass
from typing import Literal, Never, assert_never

from subsumes import _native

__all__ = [
    "Budget",
    "Json",
    "No",
    "Reason",
    "RegexDialect",
    "SchemaError",
    "Side",
    "Unknown",
    "Unrepresentable",
    "Unsupported",
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

type RegexDialect = Literal["ecma262", "rust"]
"""The dialect of regular expressions that a ``pattern`` is read in.

``ecma262`` is ECMA-262 with the ``u`` flag, which the specification of JSON Schema
recommends. ``rust`` is the dialect of the Rust ``regex`` crate, which Pydantic validates a
``pattern`` with by default. The two read some patterns differently: ``\\d`` is one of the ten
digits of ASCII in the first and any decimal digit of Unicode in the second.
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


@dataclass(frozen=True, slots=True)
class Unsupported:
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

    def __str__(self) -> str:
        return f"{self.location} in schema {self.side.upper()} is not supported"


@dataclass(frozen=True, slots=True)
class Unrepresentable:
    """A does not subsume B, and the library found no counterexample that it can give.

    Some instance is valid under B and invalid under A, so the answer is known to be no. The
    verdict is an :class:`Unknown` all the same, because a :class:`No` carries its
    counterexample. What cannot be given is a number that no JSON value holds exactly, such
    as one between two floats that are next to each other, or a value of more than 127
    objects inside one another.
    """

    def __str__(self) -> str:
        return (
            "the schemas differ in an instance that cannot be given: a number that a JSON "
            "value does not hold exactly, or a value that is nested too deep"
        )


@dataclass(frozen=True, slots=True)
class Budget:
    """The check ran out of its work budget. A larger ``budget`` may decide it."""

    def __str__(self) -> str:
        return "the check ran out of its work budget"


type Reason = Unsupported | Unrepresentable | Budget
"""Why a check ended in :class:`Unknown`. As a string it is a sentence that says so."""


@dataclass(frozen=True, slots=True)
class Unknown:
    """The library cannot decide. As a condition it is neither true nor false, and raises.

    This is no fault of the two schemas, which are valid: see :class:`SchemaError` for
    schemas that are not.
    """

    reason: Reason
    """Why it cannot."""

    def __bool__(self) -> Never:
        """Raises, so that a check that is not decided never passes for an answer.

        Raises:
            TypeError: Always.
        """
        message = f"the verdict is Unknown, which is neither true nor false: {self.reason}"
        raise TypeError(message)


type Verdict = Yes | No | Unknown
"""The answer to "does A accept every instance that is valid under B?"."""


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


def subsumes(
    a: Json,
    b: Json,
    *,
    budget: int | None = None,
    regex_dialect: RegexDialect = "ecma262",
) -> Verdict:
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
        regex_dialect: The dialect that every ``pattern`` and every key of
            ``patternProperties`` is read in, in both schemas.

    Returns:
        :class:`Yes`, which is true as a condition, :class:`No` with a counterexample, which
        is false, or :class:`Unknown` with the reason, which is neither and raises as one.

    Raises:
        SchemaError: ``a`` or ``b`` cannot be checked at all.
        TypeError: ``a`` or ``b`` holds an object that is no JSON value, such as a ``set``.
        ValueError: ``a`` or ``b`` holds a value that JSON does not have, such as ``nan``,
            or is nested more than 127 deep, or ``regex_dialect`` is none of the two.
    """
    outcome = _native.check(a, b, budget, regex_dialect)
    match outcome[0]:
        case "yes":
            return Yes()
        case "no":
            return No(outcome[1])
        case "unsupported":
            return Unknown(Unsupported(side=outcome[1], location=outcome[2]))
        case "unrepresentable":
            return Unknown(Unrepresentable())
        case "budget":
            return Unknown(Budget())
        case "invalid":
            raise SchemaError(outcome[1], side=outcome[2], location=outcome[3])
        case _ as never:
            assert_never(never)
