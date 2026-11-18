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
from subsumes import subsumes

new = {"type": "integer", "minimum": 0}
old = {"type": "integer"}

verdict = subsumes(new, old)
if not verdict:
    print("no longer accepted:", verdict.counterexample)  # -1
```

A schema is a Python object as `json.load` gives it, for JSON Schema draft 2020-12. With [Pydantic](https://docs.pydantic.dev/), that is `Model.model_json_schema()`.

A check returns one of two verdicts:

- **`Yes`**: Every instance valid under B is also valid under A. As a condition it is true.
- **`No`**: Some instance is valid under B but invalid under A. It carries such an instance as `counterexample`, and as a condition it is false.

```python
from subsumes import No, Yes

match subsumes(new, old):
    case Yes():
        print("compatible")
    case No(counterexample):
        print("no longer accepted:", counterexample)
```

## When the library cannot decide

A `Yes` and a `No` are returned only when certain. A check that the library cannot decide raises an `UndecidedError`, so it never passes for an answer:

- **`UnsupportedError`**: The answer depends on a construct that the library does not model, such as `uniqueItems`. Its `side` is `"a"` or `"b"`, and its `location` says where the construct is.
- **`BudgetError`**: The check ran out of its work budget. A larger one may decide it: `subsumes(a, b, budget=100_000_000)`.
- **`UnrepresentableError`**: A does not subsume B, but the library found no counterexample that it can give, such as a number that a float does not hold exactly.

```python
from subsumes import UndecidedError, subsumes

try:
    compatible = bool(subsumes(new, old))
except UndecidedError as undecided:
    print("could not decide:", undecided)
```

A schema that cannot be checked at all raises a `SchemaError`, which is a `ValueError`: it is no schema, it declares another dialect, a keyword has a value that the draft does not allow, or a reference resolves to nothing. A schema has to stand on its own, so one that is spread over several files is bundled into one first.

## What is modelled

The [README of the repository](https://github.com/georg-wolflein/subsumes#readme) says how patterns, numbers and `format` are read, and which constructs are not supported.
