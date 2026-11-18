"""What a change does to a schema: which check is which, and what stands for each outcome.

What the library decides is tested in the crate. These tests hold only what the action adds.
"""

import json
from typing import TYPE_CHECKING

import pytest

from subsumes_action.compare import (
    Added,
    Broken,
    Changed,
    Deleted,
    Example,
    Holds,
    Invalid,
    Refusal,
    Schema,
    Settings,
    Undecided,
    check,
    compare,
)

if TYPE_CHECKING:
    from subsumes import Json

INTEGER: Json = {"type": "integer"}
NATURAL: Json = {"type": "integer", "minimum": 0}
TWO_OR_THREE: Json = {"type": "array", "items": {"enum": [2, 3]}}
UNIQUE: Json = {"type": "array", "items": {"enum": [1, 2]}, "uniqueItems": True}
DIGITS: Json = {"pattern": r"^\d+$"}
ASCII_DIGITS: Json = {"pattern": "^[0-9]+$"}


def text(schema: Json) -> bytes:
    return json.dumps(schema).encode()


class TestCheck:
    def test_backward_asks_whether_the_new_version_accepts_all_of_the_old(self) -> None:
        widened = check("backward", Schema(NATURAL), Schema(INTEGER), Settings())
        narrowed = check("backward", Schema(INTEGER), Schema(NATURAL), Settings())
        assert widened == Holds()
        assert narrowed == Broken(Example(-1))

    def test_forward_asks_whether_the_old_version_accepts_all_of_the_new(self) -> None:
        widened = check("forward", Schema(NATURAL), Schema(INTEGER), Settings())
        narrowed = check("forward", Schema(INTEGER), Schema(NATURAL), Settings())
        assert widened == Broken(Example(-1))
        assert narrowed == Holds()

    def test_an_example_may_be_none(self) -> None:
        nullable: Json = {"type": ["string", "null"]}
        outcome = check("backward", Schema(nullable), Schema({"type": "string"}), Settings())
        assert outcome == Broken(Example(None))

    def test_an_unsupported_construct_is_named_with_its_version(self) -> None:
        dropped = check("backward", Schema(UNIQUE), Schema(TWO_OR_THREE), Settings())
        added = check("forward", Schema(TWO_OR_THREE), Schema(UNIQUE), Settings())
        assert dropped == Undecided("#/uniqueItems in the old version is not supported")
        assert added == Undecided("#/uniqueItems in the new version is not supported")

    def test_a_check_out_of_budget_is_undecided(self) -> None:
        outcome = check("backward", Schema(INTEGER), Schema(NATURAL), Settings(budget=0))
        assert outcome == Undecided("the check ran out of its budget")

    def test_a_difference_without_an_example_is_still_a_no(self) -> None:
        # Between two floats that are next to each other lies no number that a float holds.
        wide: Json = {
            "type": "number",
            "exclusiveMinimum": 1.0,
            "exclusiveMaximum": 1.0000000000000004,
        }
        narrow: Json = {"const": 1.0000000000000002}
        assert check("backward", Schema(wide), Schema(narrow), Settings()) == Broken(None)

    def test_a_pattern_is_read_in_the_dialect_of_the_settings(self) -> None:
        old, new = Schema(DIGITS), Schema(ASCII_DIGITS)
        assert check("backward", old, new, Settings()) == Holds()
        rust = Settings(regex_dialect="rust")
        assert check("backward", old, new, rust) == Broken(Example("٠"))


class TestSchema:
    def test_a_schema_is_read(self) -> None:
        assert Schema.read(b'{"type": "integer"}') == Schema(INTEGER)

    def test_a_byte_order_mark_is_no_part_of_the_text(self) -> None:
        assert Schema.read(b"\xef\xbb\xbftrue") == Schema(True)

    @pytest.mark.parametrize(
        ("content", "message"),
        [
            (b"\xff", "the file is not UTF-8"),
            (b"{", "the file is not JSON: "),
            (b"1", "the file holds neither an object nor a boolean"),
            (b'{"type": 1}', "#/type "),
            (b'{"$ref": "#/nowhere"}', "#/$ref refers to #/nowhere, which resolves to nothing"),
            (
                b'{"$schema": "http://json-schema.org/draft-07/schema#"}',
                "#/$schema declares the dialect http://json-schema.org/draft-07/schema#, and only "
                "draft 2020-12 is supported",
            ),
            (b'{"const": NaN}', "#/const is nan, which is not a JSON number"),
        ],
    )
    def test_what_is_no_schema_is_refused_with_the_reason(
        self, content: bytes, message: str
    ) -> None:
        refusal = Schema.read(content)
        assert isinstance(refusal, Refusal)
        assert refusal.message.startswith(message)
        assert "schema B" not in refusal.message

    def test_a_schema_that_is_nested_deeper_than_the_library_reads_is_refused(self) -> None:
        refusal = Schema.read(b'{"const": ' + b"[" * 200 + b"]" * 200 + b"}")
        assert isinstance(refusal, Refusal)
        assert refusal.message.startswith("#/const/0/0/")
        assert refusal.message.endswith(" is nested more than 127 deep")

    def test_text_that_python_cannot_read_for_its_depth_is_refused(
        self, monkeypatch: pytest.MonkeyPatch
    ) -> None:
        def loads(text: str) -> Json:
            raise RecursionError

        monkeypatch.setattr(json, "loads", loads)
        assert Schema.read(b"[[]]") == Refusal("the file is nested too deep")

    def test_the_same_schema_has_the_same_text_whatever_the_order_of_its_keys(self) -> None:
        one = Schema.read(b'{"type": "integer", "minimum": 0}')
        other = Schema.read(b'{\n  "minimum": 0,\n  "type": "integer"\n}')
        assert isinstance(one, Schema)
        assert isinstance(other, Schema)
        assert one.text() == other.text()

    def test_values_that_python_holds_for_equal_are_told_apart(self) -> None:
        assert Schema({"const": 1}).text() != Schema({"const": True}).text()
        assert Schema({"const": 1}).text() != Schema({"const": 1.0}).text()


class TestCompare:
    def test_a_file_with_the_same_text_did_not_change(self) -> None:
        assert compare("s.json", text(INTEGER), text(INTEGER), Settings()) is None

    def test_a_file_with_the_same_schema_did_not_change(self) -> None:
        assert (
            compare("s.json", b'{"type":"integer"}', b'{ "type": "integer" }\r\n', Settings())
            is None
        )

    def test_a_changed_schema_is_asked_both_questions(self) -> None:
        entry = compare("s.json", old=text(INTEGER), new=text(NATURAL), settings=Settings())
        assert entry == Changed("s.json", backward=Broken(Example(-1)), forward=Holds())

    def test_a_change_that_no_instance_shows_is_still_a_change(self) -> None:
        described: Json = {"type": "integer", "description": "A whole number."}
        entry = compare("s.json", old=text(INTEGER), new=text(described), settings=Settings())
        assert entry == Changed("s.json", backward=Holds(), forward=Holds())

    def test_a_file_on_one_side_only_is_added_or_deleted(self) -> None:
        assert compare("s.json", None, text(INTEGER), Settings()) == Added("s.json")
        assert compare("s.json", text(INTEGER), None, Settings()) == Deleted("s.json")
        assert compare("s.json", None, None, Settings()) is None

    def test_an_added_file_is_not_read(self) -> None:
        assert compare("s.json", None, b"no schema", Settings()) == Added("s.json")

    def test_a_new_version_that_is_no_schema_is_invalid(self) -> None:
        entry = compare("s.json", old=text(INTEGER), new=b"1", settings=Settings())
        assert entry == Invalid("s.json", "the file holds neither an object nor a boolean")

    def test_an_old_version_that_is_no_schema_leaves_both_questions_open(self) -> None:
        entry = compare("s.json", old=b"1", new=text(INTEGER), settings=Settings())
        reason = "the old version is no schema (the file holds neither an object nor a boolean)"
        assert entry == Changed("s.json", Undecided(reason), Undecided(reason))
