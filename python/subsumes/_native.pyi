"""The native module, built from the crate in ``src/``."""

from typing import Literal

from subsumes import Json, RegexDialect, Side

type Outcome = (
    tuple[Literal["yes"]]
    | tuple[Literal["no"], Json]
    | tuple[Literal["unsupported"], Side, str]
    | tuple[Literal["unrepresentable"]]
    | tuple[Literal["budget"]]
    | tuple[Literal["invalid"], str, Side, str | None]
)
"""What a check came to: its kind, then what the kind carries.

An unsupported construct has its schema and its location in it. A schema that cannot be
checked has a message first, then the schema at fault and the location in it.
"""

def check(a: Json, b: Json, budget: int | None, regex_dialect: RegexDialect) -> Outcome: ...
