# subsumes

JSON Schema inclusion for Python: **does schema A accept every instance valid under schema B?**

If it does, A _subsumes_ B. Use it to check whether a new schema still accepts everything the old schema allowed, such as before you change the schema of stored records or of an API.

> [!WARNING]
> `subsumes` is still in beta. Until version 1.0, the API may change from one minor version to the next.

```
pip install subsumes
```

The package wraps the Rust library of the same name. It needs Python 3.12 or later and has no dependencies.

## Usage

```python
from subsumes import No, Unknown, Yes, subsumes

new = {"type": "integer", "minimum": 0}
old = {"type": "integer"}

match subsumes(new, old):
    case Yes():
        print("compatible")
    case No(counterexample):
        print("no longer accepted:", counterexample)  # -1
    case Unknown(reason):
        print("not decided:", reason)
```

A schema is a Python object as `json.load` gives it, for JSON Schema draft 2020-12. With [Pydantic](https://docs.pydantic.dev/), that is `Model.model_json_schema()`.

A check returns one of three verdicts:

- **`Yes`**: Every instance valid under B is also valid under A.
- **`No`**: Some instance is valid under B but invalid under A. It carries such an instance as `counterexample`.
- **`Unknown`**: The library cannot decide. It carries the `reason`.

A `Yes` and a `No` are returned only when certain.

## When the library cannot decide

The `reason` of an `Unknown` is one of three, and as a string it is a sentence that says why:

- **`Unsupported`**: The answer depends on a construct that the library does not model, such as `uniqueItems`. Its `side` is `"a"` or `"b"`, and its `location` says where the construct is.
- **`Budget`**: The check ran out of its work budget. A larger one may decide it: `subsumes(a, b, budget=100_000_000)`.
- **`Unrepresentable`**: A does not subsume B, but the library found no counterexample that it can give, such as a number that a float does not hold exactly.

As a condition, `Yes` is true and `No` is false. `Unknown` is neither and raises a `TypeError`, so a check that is not decided never passes for an answer:

```python
if subsumes(new, old):  # raises when the check is not decided
    print("compatible")
```

A schema that cannot be checked at all raises a `SchemaError`, which is a `ValueError`: it is no schema, it declares another dialect, a keyword has a value that the draft does not allow, or a reference resolves to nothing. A schema has to stand on its own, so one that is spread over several files is bundled into one first.

## Regular expressions

A `pattern` is read as an ECMA-262 regular expression, which is what JSON Schema recommends. For schemas whose patterns are written for the Rust `regex` crate, as those that Pydantic validates are by default, name that dialect: `subsumes(a, b, regex_dialect="rust")`.

## What is modelled

The [README of the repository](https://github.com/georg-wolflein/subsumes#readme) says how patterns, numbers and `format` are read, and which constructs are not supported.
