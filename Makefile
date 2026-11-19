# The benchmark corpus is a release of https://github.com/georg-wolflein/subsumes-benchmark,
# pinned by its version and by the SHA-256 of its archive. A release of the benchmark opens a
# pull request that raises both: .github/workflows/benchmark-release.yml.
BENCHMARK_VERSION := 0.8.0
BENCHMARK_SHA256 := 6af8114ba8a1a25611309653056245e20c3231e36b550a56ed78002ec7fe32ad
BENCHMARK_URL := https://github.com/georg-wolflein/subsumes-benchmark/releases/download/v$(BENCHMARK_VERSION)/corpus.tar.zst

# How many cases the benchmark checks at once. One, as CI runs it, measures the time of each
# check. More is faster, and its times are no more than a hint: `make benchmark JOBS=8`.
JOBS ?= 1

# The Python package in python/ has its own environment, which uv keeps. `uv run` builds the
# native module anew when the binding or the library has changed.
PYTHON := uv --directory python run

.PHONY: ci lint format format-check typecheck test test-corpus corpus benchmark

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

corpus:  ## download the pinned benchmark corpus and unpack it into benchmark/
	mkdir -p target
	curl --fail --silent --show-error --location --output target/corpus.tar.zst $(BENCHMARK_URL)
	echo "$(BENCHMARK_SHA256)  target/corpus.tar.zst" | shasum -a 256 --check
	rm -rf benchmark
	mkdir benchmark
	zstd -dc target/corpus.tar.zst | tar -xf - -C benchmark --strip-components 1

test-corpus:  ## the tests that read the corpus in benchmark/
	cargo test --release --locked --lib -- --ignored

benchmark:  ## run the library over the corpus in benchmark/ and write target/results.jsonl
	cargo run --release --locked --package harness -- run --jobs $(JOBS) benchmark target/results.jsonl
