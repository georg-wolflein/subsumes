"""The report as Markdown: what it says, and that nothing in a file is read as Markdown."""

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
from subsumes_action.policy import Policy
from subsumes_action.report import BLOCKS, EXAMPLE, ROWS, describe, render

UNSUPPORTED = Undecided("#/uniqueItems in the old version is not supported")


def test_a_report_has_a_row_for_each_file_and_says_more_below() -> None:
    entries: list[Entry] = [
        Changed("schemas/narrower.json", Broken(Example({"a": None})), Holds()),
        Changed("schemas/wider.json", Holds(), Broken(Example(-1))),
        Changed("schemas/open.json", UNSUPPORTED, Holds()),
        Changed("schemas/same.json", Holds(), Holds()),
        Added("schemas/added.json"),
        Deleted("schemas/deleted.json"),
        Invalid("schemas/invalid.json", "the file is not UTF-8"),
    ]
    assert render(entries, Policy("backward", "warn")) == (
        "### Schema changes\n"
        "\n"
        ":x: 2 of 7 changed schemas do not meet `compatibility: backward`: "
        "a schema must accept everything it did.\n"
        "\n"
        "| Schema | Accepts everything it did | Accepts nothing new |\n"
        "| --- | --- | --- |\n"
        "| `schemas/narrower.json` | :x: **No** | Yes |\n"
        "| `schemas/wider.json` | Yes | **No** |\n"
        "| `schemas/open.json` | :warning: Unknown | Yes |\n"
        "| `schemas/same.json` | Yes | Yes |\n"
        "| `schemas/added.json` | new file |  |\n"
        "| `schemas/deleted.json` | deleted |  |\n"
        "| `schemas/invalid.json` | :x: not a schema |  |\n"
        "\n"
        "`schemas/narrower.json` no longer accepts:\n"
        "\n"
        "```json\n"
        '{"a": null}\n'
        "```\n"
        "\n"
        "`schemas/wider.json` newly accepts:\n"
        "\n"
        "```json\n"
        "-1\n"
        "```\n"
        "\n"
        "Whether `schemas/open.json` accepts everything it did is not decided: "
        "\\#\\/uniqueItems in the old version is not supported.\n"
        "\n"
        "`schemas/invalid.json` is no schema that the library reads: the file is not UTF\\-8.\n"
        "\n"
        "<sub>Checked by [subsumes](https://github.com/georg-wolflein/subsumes).</sub>\n"
    )


class TestSummary:
    def test_changes_that_meet_what_is_required(self) -> None:
        report = render(
            [Changed("s.json", Holds(), Broken(Example(1)))], Policy("backward", "fail")
        )
        assert (
            ":white_check_mark: The changes meet `compatibility: backward`: "
            "a schema must accept everything it did."
        ) in report

    def test_one_schema_that_does_not(self) -> None:
        report = render([Changed("s.json", Holds(), Broken(Example(1)))], Policy("full", "fail"))
        assert (
            ":x: 1 of 1 changed schema does not meet `compatibility: full`: "
            "a schema must accept exactly what it did."
        ) in report

    def test_an_open_question_that_may_warn(self) -> None:
        report = render([Changed("s.json", Holds(), UNSUPPORTED)], Policy("forward", "warn"))
        assert (
            ":warning: `compatibility: forward` is not decided for 1 of 1 changed schema: "
            "a schema must accept nothing new."
        ) in report

    def test_nothing_is_marked_where_nothing_is_required(self) -> None:
        entries = [Changed("s.json", Broken(Example(1)), UNSUPPORTED), Invalid("t.json", "why")]
        report = render(entries, Policy("none", "fail"))
        assert "Nothing is required of these changes (`compatibility: none`)." in report
        assert "| `s.json` | **No** | Unknown |" in report
        assert "| `t.json` | not a schema |  |" in report
        assert ":x:" not in report
        assert ":warning:" not in report

    def test_no_schema_changed(self) -> None:
        assert (
            render([], Policy("backward", "fail")) == "### Schema changes\n\nNo schema changed.\n"
        )


class TestBlocks:
    def test_one_reason_for_both_questions_is_given_once(self) -> None:
        report = render([Changed("s.json", UNSUPPORTED, UNSUPPORTED)], Policy("none", "fail"))
        assert report.count("is not decided") == 1
        assert "What the change to `s.json` does is not decided: " in report

    def test_a_no_without_an_example_says_so(self) -> None:
        report = render([Changed("s.json", Broken(None), Holds())], Policy("none", "fail"))
        assert "`s.json` no longer accepts some instance. The library knows" in report

    def test_an_example_that_is_null_is_shown(self) -> None:
        report = render([Changed("s.json", Broken(Example(None)), Holds())], Policy("none", "fail"))
        assert "```json\nnull\n```" in report

    def test_a_long_example_is_cut(self) -> None:
        long = Example("a" * 2 * EXAMPLE)
        report = render([Changed("s.json", Broken(long), Holds())], Policy("none", "fail"))
        assert '```json\n"' + "a" * (EXAMPLE - 1) + " …\n```" in report
        assert "Cut after 1,000 characters. The log of the job has all of it." in report

    def test_a_report_of_many_files_stays_below_the_limit_of_a_comment(self) -> None:
        long = Example("a" * 2 * EXAMPLE)
        entries = [
            Changed(f"schemas/{number}.json", Broken(long), Broken(long)) for number in range(500)
        ]
        report = render(entries, Policy("full", "fail"))
        assert len(report) < 65_536
        assert f"| and {500 - ROWS} more | | |" in report
        assert f"And {2 * 500 - BLOCKS} more, which the log of the job has." in report
        assert ":x: 500 of 500 changed schemas do not meet" in report


class TestNothingIsReadAsMarkdown:
    def test_an_example_cannot_end_its_code_block(self) -> None:
        example = Example("```\n@someone [a link](https://example.com)")
        report = render([Changed("s.json", Broken(example), Holds())], Policy("none", "fail"))
        assert '````json\n"```\\n@someone [a link](https://example.com)"\n````' in report

    def test_an_example_holds_no_character_outside_ascii(self) -> None:
        report = render([Changed("s.json", Broken(Example("‮")), Holds())], Policy("none", "fail"))
        assert '"\\u202e"' in report

    def test_a_path_stands_in_code_whatever_it_holds(self) -> None:
        report = render([Added("a`b|c\n[d](e).json")], Policy("none", "fail"))
        assert "| ``a`b\\|c [d](e).json`` | new file |  |" in report

    def test_a_path_of_backticks_alone_stands_in_code(self) -> None:
        assert "| `` ` `` | deleted |  |" in render([Deleted("`")], Policy("none", "fail"))

    def test_a_message_has_its_punctuation_escaped(self) -> None:
        invalid = Invalid(
            "s.json", "#/$ref refers to [x](y)<b>`z`\n# big, which resolves to nothing"
        )
        report = render([invalid], Policy("none", "fail"))
        assert (
            "`s.json` is no schema that the library reads: \\#\\/\\$ref refers to "
            "\\[x\\]\\(y\\)\\<b\\>\\`z\\` \\# big\\, which resolves to nothing."
        ) in report

    def test_a_reason_has_its_punctuation_escaped(self) -> None:
        reason = Undecided("#/properties/*a*/uniqueItems in the new version is not supported")
        report = render([Changed("s.json", reason, Holds())], Policy("none", "fail"))
        assert "\\#\\/properties\\/\\*a\\*\\/uniqueItems in the new version" in report


class TestDescribe:
    def test_a_change_is_a_line_for_each_question_with_the_whole_example(self) -> None:
        long = Example("a" * 2 * EXAMPLE)
        lines = describe(Changed("s.json", Broken(long), UNSUPPORTED))
        assert lines == [
            f's.json: accepts everything it did: no, as shows "{"a" * 2 * EXAMPLE}"',
            "s.json: accepts nothing new: not decided: "
            "#/uniqueItems in the old version is not supported",
        ]

    def test_the_other_things_that_happen_to_a_file_are_a_line_each(self) -> None:
        assert describe(Changed("s.json", Holds(), Broken(None))) == [
            "s.json: accepts everything it did: yes",
            "s.json: accepts nothing new: no, and no example can be given",
        ]
        assert describe(Added("s.json")) == ["s.json: new file, nothing to compare it with"]
        assert describe(Deleted("s.json")) == ["s.json: deleted"]
        assert describe(Invalid("s.json", "why")) == [
            "s.json: no schema that the library reads: why"
        ]
