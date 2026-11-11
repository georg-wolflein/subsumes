# The benchmark corpus is a release of https://github.com/georg-wolflein/subsumes-benchmark,
# pinned by its version and by the SHA-256 of its archive.
BENCHMARK_VERSION := 0.1.1
BENCHMARK_SHA256 := 2e2d57e6d8ae7650736a277250b6792c84e574449e1c7f75e68ce66d861e0c34
BENCHMARK_URL := https://github.com/georg-wolflein/subsumes-benchmark/releases/download/v$(BENCHMARK_VERSION)/corpus.tar.zst

.PHONY: benchmark

benchmark:  ## download the pinned benchmark corpus and unpack it into benchmark/
	mkdir -p target
	curl --fail --silent --show-error --location --output target/corpus.tar.zst $(BENCHMARK_URL)
	echo "$(BENCHMARK_SHA256)  target/corpus.tar.zst" | shasum -a 256 --check
	rm -rf benchmark
	mkdir benchmark
	zstd -dc target/corpus.tar.zst | tar -xf - -C benchmark --strip-components 1
