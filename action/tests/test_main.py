"""The step as the action runs it, in a checkout of a repository that the test makes."""

import json
import subprocess
from typing import TYPE_CHECKING

import pytest

from subsumes_action.__main__ import budget, command, main, matches, patterns

if TYPE_CHECKING:
    from pathlib import Path

    from subsumes import Json

INTEGER: Json = {"type": "integer"}
NATURAL: Json = {"type": "integer", "minimum": 0}
ZEROS = "0" * 40


def git(directory: Path, *arguments: str) -> str:
    done = subprocess.run(
        ["git", "-c", "user.name=test", "-c", "user.email=test@example.com", *arguments],
        cwd=directory,
        capture_output=True,
        check=True,
        text=True,
    )
    return done.stdout.strip()


def write(directory: Path, path: str, schema: Json) -> None:
    file = directory / path
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(json.dumps(schema), encoding="utf-8")


def commit(directory: Path) -> str:
    git(directory, "add", "--all")
    git(directory, "commit", "--quiet", "--allow-empty", "--message", "a change")
    return git(directory, "rev-parse", "HEAD")


@pytest.fixture(autouse=True)
def no_settings_of_the_machine(monkeypatch: pytest.MonkeyPatch) -> None:
    """Git reads no configuration but that of the repository of the test."""
    monkeypatch.setenv("GIT_CONFIG_GLOBAL", "/dev/null")
    monkeypatch.setenv("GIT_CONFIG_SYSTEM", "/dev/null")


@pytest.fixture
def checkout(tmp_path: Path) -> Path:
    """A repository with one commit, which has a schema of the integers."""
    directory = tmp_path / "checkout"
    directory.mkdir()
    git(directory, "init", "--quiet", "--initial-branch=main")
    write(directory, "schemas/number.json", INTEGER)
    write(directory, "schemas/other.json", INTEGER)
    write(directory, "elsewhere/number.json", INTEGER)
    commit(directory)
    return directory


@pytest.fixture
def files(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> dict[str, Path]:
    """The files that a runner gives a step to write to, and the one for the report."""
    paths = {name: tmp_path / name for name in ("summary", "outputs", "report")}
    monkeypatch.setenv("GITHUB_STEP_SUMMARY", str(paths["summary"]))
    monkeypatch.setenv("GITHUB_OUTPUT", str(paths["outputs"]))
    return paths


def run(
    checkout: Path,
    files: dict[str, Path],
    *,
    base: str = "HEAD",
    patterns: str = "schemas/*.json",
    compatibility: str = "backward",
    unknown: str = "fail",
    budget: str = "",
) -> int:
    return main(
        [
            *("--files", patterns),
            *("--base", base),
            *("--compatibility", compatibility),
            *("--unknown", unknown),
            *("--budget", budget),
            *("--report", str(files["report"])),
            *("--directory", str(checkout)),
        ]
    )


def outputs(files: dict[str, Path]) -> dict[str, str]:
    lines = files["outputs"].read_text(encoding="utf-8").splitlines()
    return dict(line.split("=", 1) for line in lines)


class TestMain:
    def test_a_change_that_breaks_what_is_required_fails(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)

        assert run(checkout, files) == 0

        assert outputs(files) == {"report": str(files["report"]), "changed": "1", "failed": "true"}
        report = files["report"].read_text(encoding="utf-8")
        assert "| `schemas/number.json` | :x: **No** | Yes |" in report
        assert "`schemas/number.json` no longer accepts:\n\n```json\n-1\n```" in report
        assert files["summary"].read_text(encoding="utf-8") == report
        assert capsys.readouterr().out.splitlines() == [
            "- schemas/number.json: accepts everything it did: no, as shows -1",
            "- schemas/number.json: accepts nothing new: yes",
            "::error file=schemas/number.json,title=Schema compatibility::"
            "The schema no longer accepts -1",
        ]

    def test_the_same_change_passes_where_it_is_not_required(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)

        assert run(checkout, files, compatibility="forward") == 0

        assert outputs(files)["failed"] == "false"
        assert "::" not in capsys.readouterr().out

    def test_only_the_files_of_the_patterns_are_looked_at(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        write(checkout, "elsewhere/number.json", NATURAL)

        assert run(checkout, files) == 0

        assert outputs(files) == {"report": str(files["report"]), "changed": "0", "failed": "false"}
        assert files["report"].read_text(encoding="utf-8") == (
            "### Schema changes\n\nNo schema changed.\n"
        )

    def test_several_patterns_stand_on_a_line_each(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)
        write(checkout, "elsewhere/number.json", NATURAL)

        assert run(checkout, files, patterns="schemas/*.json\n\n  **/number.json  \n") == 0

        assert outputs(files)["changed"] == "2"

    def test_added_and_deleted_files_are_reported_and_pass(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        write(checkout, "schemas/added.json", NATURAL)
        (checkout / "schemas/other.json").unlink()

        assert run(checkout, files, compatibility="full") == 0

        assert outputs(files)["failed"] == "false"
        report = files["report"].read_text(encoding="utf-8")
        assert "| `schemas/added.json` | new file |  |" in report
        assert "| `schemas/other.json` | deleted |  |" in report

    def test_an_open_question_fails_or_warns(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)

        assert run(checkout, files, budget="0") == 0
        assert outputs(files)["failed"] == "true"
        assert "::error file=schemas/number.json" in capsys.readouterr().out

        files["outputs"].unlink()
        assert run(checkout, files, budget="0", unknown="warn") == 0
        assert outputs(files)["failed"] == "false"
        assert capsys.readouterr().out.splitlines()[-1] == (
            "::warning file=schemas/number.json,title=Schema compatibility::Whether the schema "
            "accepts everything it did is not decided: the check ran out of its budget"
        )

    def test_a_file_that_is_no_schema_fails(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        (checkout / "schemas/number.json").write_text("{", encoding="utf-8")

        assert run(checkout, files) == 0

        assert outputs(files)["failed"] == "true"
        assert (
            "::error file=schemas/number.json,title=Schema compatibility::"
            "No schema that the library reads: the file is not JSON: "
        ) in capsys.readouterr().out

    def test_the_checkout_is_compared_with_an_earlier_commit(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        first = git(checkout, "rev-parse", "HEAD")
        write(checkout, "schemas/number.json", NATURAL)
        commit(checkout)

        assert run(checkout, files, base="HEAD") == 0
        assert outputs(files)["changed"] == "0"

        files["outputs"].unlink()
        assert run(checkout, files, base=first) == 0
        assert outputs(files)["changed"] == "1"

    def test_a_commit_that_the_clone_lacks_is_fetched(
        self, checkout: Path, files: dict[str, Path], tmp_path: Path
    ) -> None:
        first = git(checkout, "rev-parse", "HEAD")
        write(checkout, "schemas/number.json", NATURAL)
        commit(checkout)
        # A commit is fetched by its name only from a repository that allows it, as GitHub does.
        git(checkout, "config", "uploadpack.allowAnySHA1InWant", "true")
        shallow = tmp_path / "shallow"
        git(tmp_path, "clone", "--quiet", "--depth=1", checkout.as_uri(), str(shallow))
        assert git(shallow, "rev-list", "--count", "HEAD") == "1"

        assert run(shallow, files, base=first) == 0

        assert outputs(files) == {"report": str(files["report"]), "changed": "1", "failed": "true"}

    def test_the_step_works_in_a_folder_of_the_checkout(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)

        assert run(checkout / "schemas", files, patterns="*.json") == 0

        assert "| `number.json` | :x: **No** | Yes |" in files["report"].read_text(encoding="utf-8")

    def test_a_path_cannot_write_a_command_to_the_log(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        name = "schemas/a\n::error::b,c:d.json"
        write(checkout, name, INTEGER)
        commit(checkout)
        write(checkout, name, NATURAL)

        assert run(checkout, files) == 0

        out = capsys.readouterr().out.splitlines()
        assert out == [
            "- schemas/a\\n::error::b,c:d.json: accepts everything it did: no, as shows -1",
            "- schemas/a\\n::error::b,c:d.json: accepts nothing new: yes",
            "::error file=schemas/a%0A%3A%3Aerror%3A%3Ab%2Cc%3Ad.json,title=Schema compatibility::"
            "The schema no longer accepts -1",
        ]


class TestWhatTheStepCannotWorkWith:
    def test_a_push_that_creates_a_branch_has_nothing_to_compare_with(
        self, checkout: Path, files: dict[str, Path], capsys: pytest.CaptureFixture[str]
    ) -> None:
        write(checkout, "schemas/number.json", NATURAL)

        assert run(checkout, files, base=ZEROS) == 0

        assert outputs(files)["changed"] == "0"
        assert "::notice::There is no earlier commit to compare with." in capsys.readouterr().out

    @pytest.mark.parametrize(
        ("option", "value", "message"),
        [
            ("base", "", "::error::there is no commit to compare with: "),
            ("base", "no-such-branch", "::error::git fetch failed: "),
            ("patterns", " \n", "::error::the input `files` names no file"),
            ("patterns", "/etc/*.json", "::error::the pattern '/etc/*.json' of the input `files` "),
            ("patterns", "../*.json", "::error::the pattern '../*.json' of the input `files` "),
            ("budget", "many", "::error::the input `budget` must be a whole number of steps"),
        ],
    )
    def test_an_input_that_it_does_not_understand_ends_it(
        self,
        checkout: Path,
        files: dict[str, Path],
        capsys: pytest.CaptureFixture[str],
        option: str,
        value: str,
        message: str,
    ) -> None:
        assert run(checkout, files, **{option: value}) == 2

        assert message in capsys.readouterr().out
        assert not files["outputs"].exists()

    def test_a_value_that_is_none_of_the_choices_ends_it(
        self, checkout: Path, files: dict[str, Path]
    ) -> None:
        with pytest.raises(SystemExit) as exit:
            run(checkout, files, compatibility="sideways")
        assert exit.value.code == 2


class TestInputs:
    def test_patterns(self) -> None:
        assert patterns("a/*.json\r\n\n  b/**/*.schema.json  ") == [
            "a/*.json",
            "b/**/*.schema.json",
        ]

    def test_budget(self) -> None:
        assert budget("") is None
        assert budget(" 5000 ") == 5000

    @pytest.mark.parametrize(
        ("path", "matched"),
        [
            ("schemas/a.json", True),
            ("schemas/deep/a.json", False),
            ("schemas/a.yaml", False),
            ("Schemas/a.json", False),
            ("deep/down/b.schema.json", True),
            ("b.schema.json", True),
        ],
    )
    def test_a_path_of_the_old_commit_is_matched_as_a_file_is(
        self, path: str, matched: bool
    ) -> None:
        assert matches(path, ["schemas/*.json", "**/*.schema.json"]) == matched


class TestCommand:
    def test_a_message_is_one_line(self) -> None:
        assert command("warning", "50%\r\nof it") == "::warning::50%25%0D%0Aof it"

    def test_a_file_is_one_value(self) -> None:
        assert command("error", "why", file="a,b:c.json") == (
            "::error file=a%2Cb%3Ac.json,title=Schema compatibility::why"
        )
