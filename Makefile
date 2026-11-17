# The benchmark corpus is a release of https://github.com/georg-wolflein/subsumes-benchmark,
# pinned by its version and by the SHA-256 of its archive.
BENCHMARK_VERSION := 0.4.0
BENCHMARK_SHA256 := 3df28b7c331295c73a439701310402fdcf0a7f9043c8b4c01d4990d272321589
BENCHMARK_URL := https://github.com/georg-wolflein/subsumes-benchmark/releases/download/v$(BENCHMARK_VERSION)/corpus.tar.zst

# How many cases the benchmark checks at once. One, as CI runs it, measures the time of each
# check. More is faster, and its times are no more than a hint: `make benchmark JOBS=8`.
JOBS ?= 1

.PHONY: ci lint format format-check test test-corpus corpus benchmark

ci: format-check lint test  ## what CI runs on every change, without the benchmark

lint:
	cargo clippy --workspace --locked --all-targets -- --deny warnings

format:
	cargo fmt --all

format-check:
	cargo fmt --all --check

test:
	cargo test --workspace --locked

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
