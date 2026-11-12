# subsumes

A Rust library for JSON Schema inclusion: **does schema A accept every instance valid under schema B?**

If it does, A _subsumes_ B. Use it to check whether a new schema still accepts everything the old schema allowed.

## Why

If you store JSON data, such as [structured outputs](https://developers.openai.com/api/docs/guides/structured-outputs) from a language model, changing its schema can make existing records invalid. A subsumption check can establish that those records will still validate without checking each one.

The same check is useful for APIs, where it tells you whether a schema change is backward compatible.

## Verdicts

Each check returns one of three verdicts:

- **`Yes`**: Every instance valid under B is also valid under A.
- **`No`**: Some instance is valid under B but invalid under A. The verdict carries such an instance as a counterexample.
- **`Unknown`**: The library cannot decide and provides a reason: either the answer depends on an [unsupported construct](#unsupported-constructs), or the check ran out of its work budget.

## Status

The engine is being built keyword by keyword. So far it models the types, `null`, the booleans, `allOf`, `anyOf`, `oneOf`, `not`, `if`/`then`/`else` and `$ref`. A check whose answer depends on any other keyword returns `Unknown` and names the keyword. So does every check of a schema that uses a `$dynamicRef`, until the engine models it.

Two schemas that share such a keyword with the same value can still be decided, because what both say cancels. That is enough to decide about three in ten checks of the benchmark corpus.

## Goals

- **Soundness:** `Yes` and `No` are returned only when certain; whatever we cannot model exactly leads to `Unknown` with a reason.
- **Support JSON Schema draft 2020-12** (including [`format`](https://json-schema.org/understanding-json-schema/reference/type#format), which is asserted rather than treated as an annotation), with the exceptions listed under [Unsupported constructs](#unsupported-constructs).
- **Fast and efficient.** A check should be cheap enough to run on every save/commit.
- **Correctness and performance** are benchmarked on a large corpus of schema pairs with known answers, and a validator checks every counterexample.

## Regular expressions

JSON Schema recommends ECMA-262 regular expressions for `pattern` and `patternProperties`, but in practice a schema carries the dialect of whatever produced it. `subsumes` reads patterns in the dialect of the Rust [`regex`](https://docs.rs/regex/latest/regex/#syntax) crate, which is the engine that [Pydantic](https://docs.pydantic.dev/) uses by default to validate `pattern` constraints.

The dialect changes answers. In ECMA-262, `\d` matches only `0` to `9`; in the `regex` crate it matches every Unicode decimal digit. So `^\d+$` accepts `"٣"` here and `^[0-9]+$` does not subsume it, although the two patterns are equivalent under ECMA-262.

Other dialects may be supported later. For now this is the only one.

## References

A schema has to stand on its own. A `$ref` resolves inside the schema or to a meta-schema of draft 2020-12; nothing is fetched, and a reference that resolves to nothing is an error.

A schema that is spread over several files is bundled into one first, as [the specification describes](https://json-schema.org/draft/2020-12/json-schema-core#section-9.3): each file goes under `$defs` with its URI as its `$id`, and no reference has to change.

## Unsupported constructs

A few JSON schema constructs are not modelled. A check whose answer depends on one of them returns `Unknown` (and a reason why):

- `uniqueItems: true`.
- Patterns with lookaround or backreferences, which the `regex` crate does not accept either, and patterns with word boundaries (`\b`, `\B`).
- Formats that are not modelled as regular languages, such as `regex`, `idn-email`, `iri` and `uri-template`.
