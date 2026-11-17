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

## Goals

- **Soundness:** `Yes` and `No` are returned only when certain; whatever we cannot model exactly leads to `Unknown` with a reason.
- **Support JSON Schema draft 2020-12** (including [`format`](https://json-schema.org/understanding-json-schema/reference/type#format), which is asserted rather than treated as an annotation), with the exceptions listed under [Unsupported constructs](#unsupported-constructs).
- **Fast and efficient.** A check should be cheap enough to run on every save/commit, usually in milliseconds.
- **Correctness and performance** are benchmarked on a large corpus of schema pairs with known answers. For `No` results, the example is validated against both schemas.

## Regular expressions

JSON Schema recommends ECMA-262 regular expressions for `pattern` and `patternProperties`, but in practice a schema carries the dialect of whatever produced it. `subsumes` reads patterns in the dialect of the Rust [`regex`](https://docs.rs/regex/latest/regex/#syntax) crate, which is the engine that [Pydantic](https://docs.pydantic.dev/) uses by default to validate `pattern` constraints.

The dialect changes answers. In ECMA-262, `\d` matches only `0` to `9`; in the `regex` crate it matches every Unicode decimal digit. So `^\d+$` accepts `"٣"` here and `^[0-9]+$` does not subsume it, although the two patterns are equivalent under ECMA-262. A pattern matches a string when it matches anywhere in it, as the draft says, so `a` accepts `"banana"`.

The keys of `patternProperties` are read the same way, and so is a `pattern` under `propertyNames`.

Other dialects may be supported later. For now this is the only one.

## Numbers

Numbers are compared exactly, not as floats. A number in a schema stands for the decimal that it is written as, so `0.0075` is a multiple of `0.0001`, and `1.0` is the integer `1`.

A schema is a `serde_json` value, which keeps a number as a 64-bit integer or as a float. A number that was written with more digits than a float keeps, about 15, may have been rounded before the library sees it.

A float from 2^53 on, which is about 9e15, stands for the whole number that the float holds, as it does to a validator. That number has more digits than the float is printed with: `9.223372036854776e18` is 9223372036854775808.

A `Yes` holds for every number, however many digits it has. The counterexample of a `No` is a number that a `serde_json` value holds exactly. Where the library finds only numbers with more digits to tell two schemas apart, such as those between two floats that are next to each other, the verdict is `Unknown`.

## Formats

`format` is asserted for the formats whose strings are a regular language that can be written down exactly. Of the formats that draft 2020-12 [defines](https://json-schema.org/draft/2020-12/json-schema-validation#section-7.3), these are supported:

- [x] `date-time` (except with the second 60, which depends on whether a leap second was there)
- [x] `date`
- [x] `time` (except with the second 60, which depends on whether a leap second was there)
- [x] `duration` (except in lower-case letters, such as `p1d`, which the grammar allows and validators reject)
- [ ] `email`
- [ ] `idn-email`
- [ ] `hostname`
- [ ] `idn-hostname`
- [x] `ipv4`
- [x] `ipv6`
- [x] `uri`
- [x] `uri-reference`
- [ ] `iri`
- [ ] `iri-reference`
- [x] `uuid`
- [ ] `uri-template`
- [x] `json-pointer`
- [x] `relative-json-pointer`
- [ ] `regex`

A check whose answer depends on one of the exceptions returns `Unknown`.

## Unsupported constructs

A few JSON schema constructs are not modelled. A check whose answer depends on one of them returns `Unknown` (and a reason why):

- `uniqueItems: true`.
- `maxContains`, and a `minContains` of two or more.
- `unevaluatedProperties` and `unevaluatedItems` in a schema that leads back to itself without a property or an item in between, through `allOf`, `anyOf`, `$ref` and the like.
- Patterns with lookaround or backreferences, which the `regex` crate does not accept either, and patterns with word boundaries (`\b`, `\B`).
- Formats that are not ticked under [Formats](#formats), and formats that the draft does not define.
