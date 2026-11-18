"""What the workflow requires, and which outcomes fall short of it."""

import pytest

from subsumes_action.compare import (
    Added,
    Broken,
    Changed,
    Deleted,
    Entry,
    Example,
    Holds,
    Invalid,
    Undecided,
)
from subsumes_action.policy import Compatibility, Level, OnUnknown, Policy

NO = Broken(Example(1))
OPEN = Undecided("the check ran out of its budget")


class TestJudge:
    @pytest.mark.parametrize(
        ("compatibility", "entry", "level"),
        [
            ("backward", Changed("s", NO, Holds()), "fails"),
            ("backward", Changed("s", Holds(), NO), "passes"),
            ("forward", Changed("s", NO, Holds()), "passes"),
            ("forward", Changed("s", Holds(), NO), "fails"),
            ("full", Changed("s", NO, Holds()), "fails"),
            ("full", Changed("s", Holds(), NO), "fails"),
            ("full", Changed("s", Holds(), Holds()), "passes"),
            ("none", Changed("s", NO, NO), "passes"),
        ],
    )
    def test_only_a_required_question_fails(
        self, compatibility: Compatibility, entry: Entry, level: Level
    ) -> None:
        assert Policy(compatibility, "fail").judge(entry) == level

    @pytest.mark.parametrize(
        ("compatibility", "unknown", "level"),
        [
            ("backward", "fail", "fails"),
            ("backward", "warn", "warns"),
            ("forward", "fail", "passes"),
            ("none", "fail", "passes"),
        ],
    )
    def test_a_required_question_without_an_answer_fails_unless_it_may_warn(
        self, compatibility: Compatibility, unknown: OnUnknown, level: Level
    ) -> None:
        assert Policy(compatibility, unknown).judge(Changed("s", OPEN, Holds())) == level

    def test_a_no_fails_also_where_an_open_question_may_warn(self) -> None:
        assert Policy("full", "warn").judge(Changed("s", OPEN, NO)) == "fails"

    @pytest.mark.parametrize("unknown", ["fail", "warn"])
    def test_what_is_no_schema_fails_where_anything_is_required(self, unknown: OnUnknown) -> None:
        invalid = Invalid("s", "the file is not UTF-8")
        assert Policy("backward", unknown).judge(invalid) == "fails"
        assert Policy("none", unknown).judge(invalid) == "passes"

    def test_an_added_and_a_deleted_file_pass(self) -> None:
        assert Policy("full", "fail").judge(Added("s")) == "passes"
        assert Policy("full", "fail").judge(Deleted("s")) == "passes"
