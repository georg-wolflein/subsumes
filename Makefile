# The benchmark corpus is a release of https://github.com/georg-wolflein/subsumes-benchmark,
# pinned by its version and by the SHA-256 of its archive.
BENCHMARK_VERSION := 0.3.0
BENCHMARK_SHA256 := 62f5fd2436515c8f98382e06c2db21c7b31e1117e20a32301ee82cd0bdd56c19
BENCHMARK_URL := https://github.com/georg-wolflein/subsumes-benchmark/releases/download/v$(BENCHMARK_VERSION)/corpus.tar.zst

.PHONY: ci lint format format-check test corpus benchmark

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

benchmark:  ## run the library over the corpus in benchmark/ and write target/results.jsonl
	cargo run --release --locked --package harness -- run benchmark target/results.jsonl
