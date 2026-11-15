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
- **`Unknown`**: The library cannot decide and provides a reason: the answer depends on an [unsupported construct](#unsupported-constructs), the check ran out of its work budget, or the schemas differ in a [number](#numbers) that cannot be written exactly.

## Status

The engine is being built keyword by keyword. So far it models the types, `null`, the booleans, numbers, strings, `allOf`, `anyOf`, `oneOf`, `not`, `if`/`then`/`else` and `$ref`. For numbers that is `minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`, `integer`, and a number in `const` or `enum`. For strings it is `minLength`, `maxLength`, `pattern`, `format`, and a string in `const` or `enum`. A check whose answer depends on any other keyword returns `Unknown` and names the keyword. So does every check of a schema that uses a `$dynamicRef`, until the engine models it.

Two schemas that share such a keyword with the same value can still be decided, because what both say cancels. That is enough to decide a good third of the checks of the benchmark corpus.

## Goals

- **Soundness:** `Yes` and `No` are returned only when certain; whatever we cannot model exactly leads to `Unknown` with a reason.
- **Support JSON Schema draft 2020-12** (including [`format`](https://json-schema.org/understanding-json-schema/reference/type#format), which is asserted rather than treated as an annotation), with the exceptions listed under [Unsupported constructs](#unsupported-constructs).
- **Fast and efficient.** A check should be cheap enough to run on every save/commit.
- **Correctness and performance** are benchmarked on a large corpus of schema pairs with known answers, and a validator checks every counterexample.

## Regular expressions

JSON Schema recommends ECMA-262 regular expressions for `pattern` and `patternProperties`, but in practice a schema carries the dialect of whatever produced it. `subsumes` reads patterns in the dialect of the Rust [`regex`](https://docs.rs/regex/latest/regex/#syntax) crate, which is the engine that [Pydantic](https://docs.pydantic.dev/) uses by default to validate `pattern` constraints.

The dialect changes answers. In ECMA-262, `\d` matches only `0` to `9`; in the `regex` crate it matches every Unicode decimal digit. So `^\d+$` accepts `"٣"` here and `^[0-9]+$` does not subsume it, although the two patterns are equivalent under ECMA-262.

A pattern matches a string when it matches anywhere in it, as the draft says, so `a` accepts `"banana"`. A counterexample that is a string is the shortest of the alternative in which the library finds one, such as `"A"` for a string of letters that is not one of lower-case letters. Where a schema has several alternatives, as an `enum` has, a later one may hold a shorter string.

Other dialects may be supported later. For now this is the only one.

## Formats

`format` is asserted for the formats whose strings are a regular language that can be written down exactly: `date`, `time`, `date-time`, `duration`, `uuid`, `ipv4`, `ipv6`, `uri`, `uri-reference`, `json-pointer` and `relative-json-pointer`. Each follows the grammar of the document that defines it, so a `date` has the days of its month, and February has 29 in a leap year.

A time may have the second 60 only where a leap second was, which no grammar says. So the library leaves open whether a `time` or a `date-time` with the second 60 is one, and a check whose answer depends on such a string returns `Unknown`.

Two more kinds of string are left open, because the grammar that the draft names allows them and validators do not take them: an `ipv4` address in which a number has a zero before it, such as `01.2.3.4`, and a `duration` in lower-case letters, such as `p1d`.

Any other format is an [unsupported construct](#unsupported-constructs).

## Numbers

Numbers are compared exactly, not as floats. A number in a schema stands for the decimal that it is written as, so `0.0075` is a multiple of `0.0001`, and `1.0` is the integer `1`.

A schema is a `serde_json` value, which keeps a number as a 64-bit integer or as a float. A number that was written with more digits than a float keeps, about 15, may have been rounded before the library sees it.

A `Yes` holds for every number, however many digits it has. The counterexample of a `No` is a number that a `serde_json` value holds exactly. Where the library finds only numbers with more digits to tell two schemas apart, such as those between two floats that are next to each other, the verdict is `Unknown`.

## References

A schema has to stand on its own. A `$ref` resolves inside the schema or to a meta-schema of draft 2020-12; nothing is fetched, and a reference that resolves to nothing is an error.

A schema that is spread over several files is bundled into one first, as [the specification describes](https://json-schema.org/draft/2020-12/json-schema-core#section-9.3): each file goes under `$defs` with its URI as its `$id`, and no reference has to change.

## Unsupported constructs

A few JSON schema constructs are not modelled. A check whose answer depends on one of them returns `Unknown` (and a reason why):

- `uniqueItems: true`.
- Patterns with lookaround or backreferences, which the `regex` crate does not accept either, and patterns that ask where a word or a line begins or ends (`\b`, `\B`, and `^` or `$` under `(?m)`).
- Formats other than those listed under [Formats](#formats), such as `hostname`, `email`, `regex` and `iri`.
