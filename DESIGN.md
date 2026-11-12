# Design

`subsumes(a, b)` decides whether every instance valid under B is valid under A, for JSON Schema draft 2020-12. The method is *refutational normalization*, the algorithm of Baazizi, Colazzo, Ghelli, Sartiani and Scherzinger, "JSON Schema Inclusion through Refutational Normalization" ([arXiv:2603.25306](https://arxiv.org/abs/2603.25306)).

The [README](README.md) states the goals, the verdicts and what is unsupported. This document is the plan for the implementation.

**Status:** the API and the benchmark harness exist, and every check returns `Unknown`. The [pipeline](#pipeline) is still to be built, in the [order of work](#order-of-work) below.

## Method

A subsumes B exactly when no instance satisfies `all[B, not A]`. The engine normalizes that conjunction into a disjunction of *canonical conjunctions*, each of them satisfiable by construction or refuted to `false`.

- No conjunction is left: `Yes`.
- A conjunction is left: a counterexample is generated from it, and the verdict is `No`.
- Every conjunction left contains something the engine cannot model, or the budget ran out: `Unknown`.

## Decisions

- **Sound before complete.** What cannot be modelled exactly becomes an `Unknown` leaf. A leaf never refutes a conjunction and never contributes to a counterexample.
- **Equal leaves cancel.** Two leaves from the same keyword with the same value are one predicate, so `u ∧ ¬u` is refuted. A schema subsumes itself even if it contains `uniqueItems: true`.
- **Two causes of the verdict `Unknown`.** An unsupported construct, reported with its schema and location, or the budget. A check that needs the infinite unfolding of a recursive schema counts as the first, at the reference that closes the cycle.
- **One budget, in steps.** Everything that can blow up charges it: insertions into canonical conjunctions, automaton states, `unevaluated*` scenarios, the search for a counterexample, nesting depth. There is no other limit. Steps do not depend on the machine, so a pair gets the same verdict everywhere. The default of 500,000 comes from the Python version and is set anew once there are measurements.
- **Invalid input is an error, not a verdict.** A root that is no schema, another dialect, a keyword of the wrong shape, a reference that resolves to nothing. Each error names the schema and the location. A pattern that the `regex` crate rejects is not an error but an `Unknown` leaf.
- **No validator in the library.** A counterexample is returned unchecked. Tooling outside the library checks counterexamples; see [Testing](#testing).
- **Patterns are parsed by `regex-syntax`**, so the dialect is that of the `regex` crate by construction. The automata are our own; see [String languages](#string-languages).
- **`format` is asserted** for the formats that are regular languages: `date`, `time`, `date-time`, `duration`, `uuid`, `ipv4`, `ipv6`, `hostname`, `email`, `uri`, `uri-reference`, `json-pointer`, `relative-json-pointer`. One table of patterns in the Rust dialect defines them. Any other format is an `Unknown` leaf.
- **Numbers are exact.** Every bound and `multipleOf` is a rational, taken from the shortest decimal of the number, so `0.0075` is a multiple of `0.0001`. Plain `serde_json` is enough.
- **Nothing is fetched.** A reference resolves within A, within B, to a document given to the checker, or to a meta-schema of the draft, which the library carries.
- **Pure Rust, no solver.** Dependencies: `serde_json`, `referencing`, `regex-syntax` and `num-rational`.

## API

```
subsumes(&a, &b) -> Result<Verdict, Error>

Checker::new().budget(steps).resource(uri, document)
    .subsumes(&a, &b) -> Result<Verdict, Error>
    .check(&a, &b)    -> Result<Check, Error>    // the verdict and the steps spent
```

Schemas and documents are `serde_json::Value`. A `Checker` does not change while it checks, so one can be shared between threads.

## Pipeline

```
load       Value          ->  schema graph      typed keywords per subschema, references resolved, locations kept
lower      schema graph   ->  terms             the rewrites, the unevaluated* scenarios, variables
normalize  all[B, not A]  ->  canonical DNF
generate   conjunction    ->  counterexample
```

### Load

- A subschema is a *node*: a boolean, or a struct with one typed field per keyword of the draft and its children as node ids. Nodes are parsed by hand from the `Value`, not derived with serde.
- Load parses every subschema of A, of B and of each document they reference, before the engine starts. A keyword of the wrong shape is an error wherever it stands, even in a definition that nothing uses. Input errors come from this stage only: lowering and the engine cannot fail on input.
- Every node keeps its location, a URI reference with a JSON Pointer fragment. Leaves and errors report it.
- Keywords that the draft does not define are ignored, as the specification says.
- References go through the `referencing` crate. The documents of the checker form one registry, built once. A check extends it twice, once with A and once with B, because two versions of a schema usually share an `$id`.

### Lower

The engine works on *terms*, not keywords:

| Type | Terms |
| --- | --- |
| any | `True`, `False`, `TypeIs`, `AllOf`, `AnyOf`, `Not`, `Ref`, `Unknown` |
| boolean | `BoolConst` |
| number | `Min`, `Max`, `ExMin`, `ExMax`, `Mof`, `NotMof` |
| string | `Patt` over a regular language, `MinLen`, `MaxLen` |
| object | `PProp`, `PReq`, `PNames`, `MinProps`, `MaxProps` |
| array | `Item`, `AddIts`, `Contains`, `MaxContains`, `MinIts`, `MaxIts` |

- **Variables.** Every nested subschema (a property, an item, a `contains`) is a *c-reference*: a set of variables that denotes their conjunction, never an inline term. This keeps canonical forms flat and lets results be shared.
- **Negation moves one level at a time.** `not(PProp(p, x))` is `PReq(p, ¬x)` and `not(Min(q))` is `ExMax(q)`. A negated c-reference `¬x` is a fresh variable whose body is `not(x)`.
- **`$ref` and `$dynamicRef`** targets are variables. A `$dynamicRef` variable is keyed by its target and the dynamic scope it was reached in, which models the dynamic scope without unfolding.
- **Rewrites.**
  - `prefixItems` and `items` become `Item` and `AddIts`; `contains`, `minContains` and `maxContains` become `Contains` and `MaxContains`.
  - `integer` is `number` with `multipleOf: 1`.
  - `const` and `enum` become the structural terms that denote exactly those values.
  - `oneOf`, `if`/`then`/`else`, `dependentRequired` and `dependentSchemas` become combinations of `AnyOf`, `AllOf` and `Not`.
  - `propertyNames` becomes `PNames(x)`, whose language is the string language of `x`.
- **`unevaluatedProperties` and `unevaluatedItems`** are expanded by *scenarios*: every combination of branches of the in-place applicators (`allOf`, `anyOf`, `oneOf`, `if`/`then`/`else`, `$ref`, `dependentSchemas`) that can hold, with the names or positions it evaluates. A scenario is the conjunction of the branches it takes, the negation of those it does not, and `additionalProperties` or `items` over what it leaves unevaluated. Scenarios that evaluate the same set are merged.

### Normalize

- **Canonical conjunctions**, one per type:
  - `CNum`: an interval, the multiple and the excluded multiples.
  - `CStr`: one language, the intersection of every pattern and format, plus length bounds.
  - `CObj`: the *fragment map*, a partition of all names into pattern fragments, each with the c-reference that every member satisfies and those that some member must satisfy, plus bounds on the property count.
  - `CArr`: a head of positional c-references, a tail, the `Contains` and `MaxContains` constraints and length bounds.
- **Lazy negation.** `not(S)` is pushed one level and the result inserted. Before a refutable `AnyOf` is expanded, each branch is tried in *fast mode*, which gives up instead of splitting; a branch refuted that way is dropped unexpanded.
- **Eager normalization of references.** When two c-references meet in a property, an item or a `contains`, their conjunction is normalized at once and memoized. A result equal to one operand is replaced by that operand, which keeps `b_i ∧ ¬b_j` equal to `b_i` for `oneOf` branches that a discriminator already separates.
- **Recursion is a least fixed point.** A reference whose expansion is in progress contributes `false` when positive and an `Unknown` leaf when negated, so recursive schemas terminate.

### Generate

- The normal form of B is computed first. Each of its conjunctions is conjoined with `not A` and searched for a counterexample before the next is touched, so a `No` usually comes long before the whole normal form exists.
- Generation is bottom-up and memoized per c-reference. A reference in progress has no counterexample, which is the same least fixed point.
- Numbers search the interval for a multiple that is none of the excluded ones. Strings take the shortest word within the length bounds. Objects choose members per fragment, arrays choose which positions satisfy which `contains`.

## String languages

Regular languages of strings are one module of the library, `language`. It uses no schema or engine types, and the rest of the library reaches it only through a narrow `pub(crate)` interface.

- **Interface.** A store of languages that the context of a check owns. It takes patterns, sets of words and the budget, and gives back languages by id. It offers intersection, complement and inclusion, and emptiness and the shortest word within length bounds.
- **Search semantics.** A `pattern` matches when the regex matches anywhere in the string, so the language of a pattern is every string that contains a match. `^` and `$` are modelled. Any other look-around assertion, such as `\b`, is reported as unsupported and becomes an `Unknown` leaf.
- **Representation.** A finite or cofinite language is a set of words. Anything else is a minimal DFA over ranges of Unicode scalar values.
- **Lengths stay symbolic.** Emptiness and shortest words walk the automaton by the number of characters left, so a bound of a million costs no more than a small one.
- **Why our own automata.** `regex-automata` works on bytes and has no intersection or complement, and `minLength` counts characters. `regexsolver` has the set operations, but we cannot use it as the engine: it does not count its iterations anywhere, so its work cannot be charged to the budget. Its only limits are a cap on the number of states and a wall-clock timeout. It also matches whole strings, where a `pattern` is a search. It serves as an oracle in the tests.
- **Formats stay outside the module.** A format is a JSON Schema concept; the table defines each as a pattern.
- **A module, not a crate.** As a crate, its interface would be public API while it still changes most. The module can move into a crate of its own later; a published crate cannot be taken back.

## Data layout

- One context per check owns everything: the arenas of nodes, terms, variables and c-references, the store of languages, the memo tables and the budget. Nothing mutable outlives a check or is shared between checks.
- Everything is interned and addressed by a `u32` id. Equality is equality of ids, and memo keys are small.
- Equal subschemas of A and B intern to one node when their references resolve alike. `x ∧ ¬x` is then refuted by identity, without normalizing what is inside. Two versions of one schema share most of their subschemas, so most of them are never opened.
- Fast mode and the budget are ordinary return values. Recursion depth is counted, because a stack overflow would abort the process.

## Testing

- **Unit tests** per module.
- **The corpus.** CI runs every pull request over the pinned [benchmark](https://github.com/georg-wolflein/subsumes-benchmark) release and comments the comparison with `main`. It fails on a wrong verdict, on an error, and on a check that `main` decided and the pull request answers `Unknown`, unless the pull request has the label `allow-lost-verdicts`. Steps and times are reported, not enforced.
- **Languages.** Property tests on random patterns compare the automata with two oracles: the `regex` crate on which strings match, and `regexsolver` on intersection, complement and inclusion. Both are dependencies of the tests only.
- **`No`.** A checker outside the library validates each counterexample against both schemas, with patterns matched by the `regex` crate. It is not built yet.
- **`Yes`** has nothing to validate. Beyond the labels of the corpus there are metamorphic tests: `a` subsumes `a`, `a` subsumes `allOf[a, x]`, and `anyOf[a, x]` subsumes `a`.

## Layout

```
src/
  lib.rs, checker.rs, verdict.rs, error.rs    the API (exists)
  context.rs      the state of one check: arenas, memo tables, budget
  schema.rs       load: nodes, typed keywords, locations, resolution
  term.rs         terms, variables, c-references, one-level negation
  lower.rs        schema graph to terms: rewrites and scenarios
  normalize.rs    the engine
  canonical/      numbers, strings, objects, arrays
  language/       string languages: automata over scalar ranges, word sets
  formats.rs      the format table
  meta_schemas.rs the meta-schema of draft 2020-12 and those of its vocabularies (exists)
  generate.rs     counterexamples
harness/          the benchmark runner (exists)
```

## Order of work

Each step goes through all four stages for the keywords it adds, and lands as its own pull request. The benchmark comment shows what the step decides, and its table of reasons for `Unknown` shows what blocks the most checks.

1. **Schema graph:** nodes, locations, errors, references through `referencing`.
2. **Engine skeleton:** context, budget, terms, variables, lazy negation and fast mode; `type`, booleans, `null`, the connectives, `$ref` with recursion. First `Yes` and `No`.
3. **Numbers.**
4. **Strings:** the `language` module, then patterns, formats and lengths in the engine.
5. **Objects.**
6. **Arrays.** `const` and `enum` are complete from here.
7. **`$dynamicRef`, `unevaluatedProperties`, `unevaluatedItems`.**
8. **Speed:** measure the checks on the corpus, then set the default budget.

## Not planned

- Drafts other than 2020-12.
- Explanations beyond the counterexample.
- For now: other regex dialects, a command line tool, bindings for other languages.
