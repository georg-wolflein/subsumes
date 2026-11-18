"""The native module, built from the crate in ``src/``."""

from typing import Literal

from subsumes import Json, RegexDialect, Side

type Outcome = (
    tuple[Literal["yes"]]
    | tuple[Literal["no"], Json]
    | tuple[Literal["unsupported"], str, Side, str]
    | tuple[Literal["unrepresentable"], str]
    | tuple[Literal["budget"], str]
    | tuple[Literal["undecided"], str]
    | tuple[Literal["invalid"], str, Side, str | None]
)
"""What a check came to: its kind, then what the kind carries.

A message comes first where there is one, then the schema at fault and the location in it.
"""

def check(a: Json, b: Json, budget: int | None, regex_dialect: RegexDialect) -> Outcome: ...
