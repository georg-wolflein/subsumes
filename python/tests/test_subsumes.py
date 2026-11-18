"""The binding: what a check returns and raises, and how a schema crosses into the library.

What the library decides is tested in the crate. These tests hold only what the package adds.
"""

import math
from concurrent.futures import ThreadPoolExecutor
from typing import assert_never

import pytest

from subsumes import (
    BudgetError,
    Json,
    No,
    SchemaError,
    UndecidedError,
    UnrepresentableError,
    UnsupportedError,
    Yes,
    subsumes,
)

INTEGER: Json = {"type": "integer"}
NATURAL: Json = {"type": "integer", "minimum": 0}


def nested(depth: int) -> Json:
    """A schema of ``depth`` arrays inside one another."""
    schema: Json = True
    for _ in range(depth):
        schema = [schema]
    return {"enum": schema} if depth else schema


class TestVerdict:
    def test_yes_is_true(self) -> None:
        verdict = subsumes(INTEGER, NATURAL)
        assert verdict == Yes()
        assert verdict

    def test_no_is_false_and_carries_a_counterexample(self) -> None:
        verdict = subsumes(NATURAL, INTEGER)
        assert verdict == No(-1)
        assert not verdict

    def test_a_counterexample_may_be_none(self) -> None:
        verdict = subsumes({"type": "string"}, {"type": ["string", "null"]})
        assert isinstance(verdict, No)
        assert verdict.counterexample is None

    def test_a_verdict_is_matched_by_its_class(self) -> None:
        match subsumes(NATURAL, INTEGER):
            case Yes():
                pytest.fail("the schema of the naturals accepts no negative integer")
            case No(counterexample):
                assert counterexample == -1
            case _ as never:
                assert_never(never)

    @pytest.mark.parametrize(
        ("a", "b", "counterexample"),
        [
            ({"type": "string"}, {"const": True}, True),
            ({"type": "integer"}, {"const": 1.5}, 1.5),
            ({"type": "string"}, {"const": 2**64 - 1}, 2**64 - 1),
            ({"type": "string"}, {"const": -(2**63)}, -(2**63)),
            ({"type": "integer"}, {"const": "ü"}, "ü"),
            ({"type": "string"}, {"const": [1, [None]]}, [1, [None]]),
            ({"type": "string"}, {"const": {"a": {"b": False}}}, {"a": {"b": False}}),
        ],
    )
    def test_a_counterexample_is_what_json_loads_gives(
        self, a: Json, b: Json, counterexample: Json
    ) -> None:
        verdict = subsumes(a, b)
        assert isinstance(verdict, No)
        assert verdict.counterexample == counterexample
        assert type(verdict.counterexample) is type(counterexample)


class TestUndecided:
    def test_an_unsupported_construct_names_its_schema_and_location(self) -> None:
        with pytest.raises(UnsupportedError) as raised:
            subsumes({"properties": {"tags": {"uniqueItems": True}}}, {})
        assert raised.value.side == "a"
        assert raised.value.location == "#/properties/tags/uniqueItems"
        assert str(raised.value) == "#/properties/tags/uniqueItems in schema A is not supported"

    def test_the_side_is_that_of_the_argument(self) -> None:
        with pytest.raises(UnsupportedError) as raised:
            subsumes(False, {"uniqueItems": True, "type": "array"})
        assert raised.value.side == "b"

    def test_a_counterexample_that_cannot_be_given(self) -> None:
        between: Json = {
            "type": "number",
            "exclusiveMinimum": 0.1,
            "exclusiveMaximum": 0.10000000000000002,
        }
        with pytest.raises(UnrepresentableError, match="cannot be given"):
            subsumes(False, between)

    def test_a_budget_that_is_too_small(self) -> None:
        def chain(innermost: Json) -> Json:
            links: dict[str, Json] = {
                f"d{at}": {"type": "object", "properties": {"a": {"$ref": f"#/$defs/d{at + 1}"}}}
                for at in range(50)
            }
            links["d50"] = innermost
            return {"$ref": "#/$defs/d0", "$defs": links}

        integers, numbers = chain({"type": "integer"}), chain({"type": "number"})
        with pytest.raises(BudgetError, match="budget"):
            subsumes(numbers, integers, budget=10)
        assert subsumes(numbers, integers)
        assert subsumes(numbers, integers, budget=2**64 - 1)

    def test_every_reason_is_an_undecided_error_and_no_schema_error(self) -> None:
        for reason in (UnsupportedError, UnrepresentableError, BudgetError):
            assert issubclass(reason, UndecidedError)
            assert not issubclass(reason, ValueError)
        assert not issubclass(SchemaError, UndecidedError)


class TestSchemaError:
    def test_a_value_that_is_no_schema_has_no_location(self) -> None:
        with pytest.raises(SchemaError) as raised:
            subsumes(INTEGER, "integer")
        assert raised.value.side == "b"
        assert raised.value.location is None
        assert str(raised.value) == "schema B is neither an object nor a boolean"

    @pytest.mark.parametrize(
        ("schema", "location"),
        [
            ({"properties": {"name": {"minLength": "3"}}}, "#/properties/name/minLength"),
            ({"items": {"$ref": "#/$defs/missing"}}, "#/items/$ref"),
            ({"$schema": "http://json-schema.org/draft-07/schema#"}, "#/$schema"),
        ],
    )
    def test_a_fault_in_a_schema_has_its_location(self, schema: Json, location: str) -> None:
        with pytest.raises(SchemaError) as raised:
            subsumes(schema, True)
        assert raised.value.side == "a"
        assert raised.value.location == location
        assert str(raised.value).startswith(f"{location} in schema A ")

    def test_it_is_a_value_error(self) -> None:
        with pytest.raises(ValueError, match="neither an object nor a boolean"):
            subsumes(None, True)


class TestNumbers:
    def test_a_float_stands_for_the_decimal_that_it_prints_as(self) -> None:
        assert subsumes({"multipleOf": 0.0001}, {"const": 0.0075})
        assert math.fmod(0.0075, 0.0001) != 0

    def test_a_float_that_is_whole_is_that_integer(self) -> None:
        assert subsumes({"const": 1}, {"const": 1.0})
        assert subsumes({"type": "integer"}, {"const": 1.0})

    def test_a_boolean_is_no_number(self) -> None:
        assert subsumes({"const": 1}, {"const": True}) == No(True)
        assert subsumes({"const": False}, {"const": 0}) == No(0)

    def test_an_integer_of_64_bits_is_exact(self) -> None:
        assert subsumes({"const": 2**64 - 1}, {"const": 2**64 - 2}) == No(2**64 - 2)
        assert subsumes({"const": -(2**63)}, {"const": -(2**63) + 1}) == No(-(2**63) + 1)

    def test_a_larger_integer_is_the_float_nearest_to_it(self) -> None:
        assert float(2**64 + 1) == float(2**64)
        assert subsumes({"const": 2**64 + 1}, {"const": 2**64})
        assert subsumes({"const": 2**64}, {"const": float(2**64)})
        assert not subsumes({"const": 2**64}, {"const": 2**65})


class TestNoJsonValue:
    @pytest.mark.parametrize(
        ("schema", "message"),
        [
            ({"enum": {1, 2}}, "#/enum in schema A is of type set"),
            ({"enum": (1, 2)}, "#/enum in schema A is of type tuple"),
            ({"const": b"text"}, "#/const in schema A is of type bytes"),
            ({"properties": {"a": {1: True}}}, "#/properties/a in schema A has the key 1"),
            ({"anyOf": [True, {"const": 1j}]}, "#/anyOf/1/const in schema A is of type complex"),
            ({"properties": {"a/b~c": object()}}, "#/properties/a~1b~0c in schema A is of type"),
            (object(), "# in schema A is of type object"),
        ],
    )
    def test_an_object_of_another_type_is_a_type_error(self, schema: object, message: str) -> None:
        with pytest.raises(TypeError, match=message):
            subsumes(schema, True)  # ty: ignore[invalid-argument-type]

    @pytest.mark.parametrize(
        ("schema", "message"),
        [
            ({"maximum": math.nan}, "#/maximum in schema B is nan, which is not a JSON number"),
            ({"minimum": -math.inf}, "#/minimum in schema B is -inf, which is not a JSON number"),
            ({"const": 10**400}, "#/const in schema B is an integer too large for a JSON number"),
            ({"const": "\ud800"}, "#/const in schema B is a string with a surrogate"),
            (
                {"properties": {"\ud800": True}},
                "#/properties in schema B has a key with a surrogate",
            ),
        ],
    )
    def test_a_value_that_json_does_not_have_is_a_value_error(
        self, schema: Json, message: str
    ) -> None:
        with pytest.raises(ValueError, match=message) as raised:
            subsumes(True, schema)
        assert not isinstance(raised.value, SchemaError)

    def test_a_schema_is_nested_127_deep_at_most(self) -> None:
        assert subsumes(nested(126), nested(126))
        with pytest.raises(ValueError, match="in schema A is nested more than 127 deep"):
            subsumes(nested(127), True)

    def test_a_schema_far_deeper_raises_and_does_not_crash(self) -> None:
        with pytest.raises(ValueError, match="is nested more than 127 deep"):
            subsumes(True, nested(200_000))


def test_checks_run_in_threads() -> None:
    with ThreadPoolExecutor(max_workers=4) as pool:
        verdicts = list(pool.map(lambda _: subsumes(NATURAL, INTEGER), range(64)))
    assert verdicts == [No(-1)] * 64
