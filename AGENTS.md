# Notes for agents

## Tooling

`make ci` runs what CI runs on a pull request, without the benchmark: `cargo fmt --check`, `cargo clippy` and `cargo test` for the workspace, and for the Python package in `python/` `ruff check`, `ruff format --check`, `ty check` and `pytest`. `make format` fixes what the formatters can fix.

Everything Python runs through `uv`, from `python/`: `uv --directory python run pytest`. Its configuration is `python/pyproject.toml`. `uv run` builds the native module anew when the binding or the library has changed, so there is no build step to remember.

`.github/workflows/release.yml` runs release-please: it keeps a release pull request open, and merging that publishes the crate to crates.io and the Python package to PyPI. `.github/workflows/wheels.yml` builds the wheels and the source distribution for it, and runs on a pull request that changes how the package is built.

The release pull request raises the versions. Never change the version in `Cargo.toml`, `python/pyproject.toml`, `python/uv.lock` or `.release-please-manifest.json` by hand.

## Running the benchmark

The benchmark is the package `subsumes-benchmark` at the version that the `Makefile` pins, which `uvx` fetches: it holds the corpus of that version and the runner. `make corpus` unpacks the corpus into `benchmark/`. The runner drives the library through `harness adapter`, which it builds from the working tree first, and writes the run to `target/results/harness/`.

- **`make benchmark`** checks the cases of the corpus one after the other, prints how the run went, and fails on a wrong verdict or an error. Use it whenever the time of the checks matters: to measure speed, or for results whose times are held against those of another run. CI runs it this way.
- **`make benchmark JOBS=8`** checks eight cases at once and is several times faster. Use it when only the verdicts matter, such as to see that a change loses none. The times in its results are no more than a hint, since the checks share the machine.
- **`make benchmark-comment DIFF="--base <folder>"`** holds that run against another one, such as a copy of `target/results/harness/` from before a change, and writes `target/benchmark-comment.md`. It fails besides on a check that the other run decided and this one does not.

What a case, a task and a wrong answer are, and how a run is scored and reported, is decided in the benchmark. Change it there, release it, and raise the pin here.

## The README

Ask the user before you change `README.md`, and say what you would change and why.

## The Python package

`python/` holds the binding: the crate in `python/src/` is the native module `subsumes._native`, and `python/subsumes/` is the package that users import. [DESIGN.md](DESIGN.md#python) has its API and the reasons for it.

- The native module is one function that returns plain values. The verdicts, the reasons and the exception are classes of the package, in Python.
- A check that the library cannot decide returns `Unknown` and raises nothing. A reason that the crate gains needs a class in the package and an arm in the native module.
- What the library decides is tested in the crate. The tests in `python/tests/` hold only what the binding adds.
- `python/README.md` is the page of the package on PyPI, and `python/LICENSE` a link to `LICENSE`, so that the wheels carry the licence. Ask before you change that README, as for the other.
- `a` is the schema that should accept everything and `b` the one whose instances must be accepted, in every name: `subsumes(a, b)`, `Side`.

Coding conventions for the Python code:

- Use the narrowest practical type.
- `Sequence[T]` for variable-length collections. Use `tuple[...]` only for fixed-length positional data like `tuple[str, int]`, or where you actually need tuple behaviour. Don't write `tuple[T, ...]`.
- `Literal[...]` for small closed sets instead of bare `str`.
- PEP 695 type parameters: `def f[T: Base](x: T) -> T`, not a separate `TypeVar`. Applies to generic classes, functions, and aliases.
- Don't annotate with `dict` or `Any` when it is not really necessary. Don't annotate with `Any` when a better type is available or would be easy to create; a `dataclass` is usually that better type. JSON values are `subsumes.Json`.
- Dataclasses for data holders instead of hand-written `__init__` and `__repr__`.
- `match` for closed-set dispatch on a `Literal` or a sealed class hierarchy, with a `case _: assert_never(x)` arm, so exhaustiveness is a typecheck failure rather than a silent fall-through.
- Classmethod factories over module-level constructors: `ClassName.create(...) -> Self`, not `_create_class_name(...)`.
- Docstrings use Google style. Omit types from `Args`/`Returns` and skip `Raises` unless crucial.
