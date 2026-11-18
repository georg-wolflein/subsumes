# The benchmark is a release of https://github.com/georg-wolflein/subsumes-benchmark, pinned
# by its version: the package `subsumes-benchmark` on PyPI, which holds the corpus of that
# version and the runner. uv fetches it, with the Python it needs.
BENCHMARK_VERSION := 0.8.1
BENCHMARK := uvx subsumes-benchmark==$(BENCHMARK_VERSION)

# How many tasks the benchmark asks at once. One, as CI runs it, measures the time of each
# check. More is faster, and its times are no more than a hint: `make benchmark JOBS=8`.
JOBS ?= 1

# What `make benchmark-comment` holds the run against: `DIFF="--base <the folder of a run>"`,
# with `--base-label` for what to call it and `--allow-lost` to accept lost verdicts.
DIFF ?=
# What the comment says about verdicts that are lost and not accepted.
LOST_HINT := To accept them, add the label `allow-lost-verdicts` to the pull request and run the job again.

# The Python package in python/ has its own environment, which uv keeps. `uv run` builds the
# native module anew when the binding or the library has changed.
PYTHON := uv --directory python run

.PHONY: ci lint format format-check typecheck test test-corpus corpus benchmark benchmark-comment

ci: format-check lint typecheck test  ## what CI runs on every change, without the benchmark

lint:
	cargo clippy --workspace --locked --all-targets -- --deny warnings
	$(PYTHON) ruff check .

format:
	cargo fmt --all
	$(PYTHON) ruff format .
	$(PYTHON) ruff check --fix .

format-check:
	cargo fmt --all --check
	$(PYTHON) ruff format --check .

typecheck:  ## the Python package only; the compiler checks the rest
	$(PYTHON) ty check

test:
	cargo test --workspace --locked
	$(PYTHON) pytest

corpus:  ## unpack the corpus of the pinned benchmark into benchmark/
	rm -rf benchmark
	$(BENCHMARK) corpus benchmark

test-corpus:  ## the tests that read the corpus in benchmark/
	cargo test --release --locked --lib -- --ignored

benchmark:  ## run the library of the working tree over the corpus in benchmark/, into target/results/harness/
	$(BENCHMARK) run harness --corpus benchmark --out target/results --jobs $(JOBS)
	$(BENCHMARK) diff target/results/harness

benchmark-comment:  ## hold that run against the run that DIFF names and write target/benchmark-comment.md
	$(BENCHMARK) diff target/results/harness $(DIFF) --lost-hint '$(LOST_HINT)' --out target/benchmark-comment.md
