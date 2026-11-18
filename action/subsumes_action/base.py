"""The commit that the checkout is compared with: which files it has, and what is in them."""

import subprocess
from dataclasses import dataclass
from typing import TYPE_CHECKING, Self

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path


class GitError(Exception):
    """Git could not do what the action needs. The message is what git said."""


def git(directory: Path, *arguments: str) -> bytes:
    """Runs git in ``directory`` and returns what it prints."""
    try:
        done = subprocess.run(["git", *arguments], cwd=directory, capture_output=True, check=False)
    except FileNotFoundError:
        raise GitError("git is not installed") from None
    if done.returncode != 0:
        said = done.stderr.decode(errors="replace").strip()
        raise GitError(f"git {arguments[0]} failed: {said}")
    return done.stdout


@dataclass(frozen=True, slots=True)
class Base:
    """A commit, seen from a folder of a checkout. Every path is relative to that folder."""

    directory: Path
    commit: str

    @classmethod
    def find(cls, directory: Path, ref: str) -> Self:
        """The commit that ``ref`` names, fetched from ``origin`` if the clone lacks it.

        A workflow checks out one commit and no history, so the commit that a pull request
        is based on is usually not there. It is fetched alone, without its history.
        """
        name = f"{ref}^{{commit}}"
        try:
            git(directory, "cat-file", "-e", name)
        except GitError:
            shallow = git(directory, "rev-parse", "--is-shallow-repository").strip() == b"true"
            # A clone that has its history keeps it: a depth would cut it off at this commit.
            depth = ["--depth=1"] if shallow else []
            git(directory, "fetch", "--quiet", "--no-tags", *depth, "origin", ref)
            name = "FETCH_HEAD^{commit}"
        return cls(directory, git(directory, "rev-parse", "--verify", name).decode().strip())

    def paths(self) -> Sequence[str]:
        """Every file of the commit below the folder, with ``/`` between the parts."""
        listed = git(self.directory, "ls-tree", "-r", "-z", "--name-only", self.commit)
        return [path.decode(errors="surrogateescape") for path in listed.split(b"\0") if path]

    def read(self, path: str) -> bytes:
        """What the file at ``path`` holds in the commit."""
        return git(self.directory, "show", f"{self.commit}:./{path}")
