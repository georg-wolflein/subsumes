//! The native half of the Python package `subsumes`: one function that takes two schemas as
//! Python objects, runs the check and hands the outcome back as a tuple of plain values. The
//! package makes its verdicts and its exception of that tuple, so no class is defined here.

use pyo3::exceptions::{PyRuntimeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBool, PyDict, PyFloat, PyInt, PyList, PyString, PyTuple};
use serde_json::{Map, Number, Value};
use subsumes::{Checker, Error, Reason, RegexDialect, Side, Verdict};

/// How many arrays and objects a schema may hold inside one another. `serde_json` reads no
/// text that is deeper, so a schema is taken here exactly when the library can be given it
/// as text. The limit also keeps the walk over a schema, and the drop of its value, off the
/// end of the stack, where the interpreter would crash instead of raising.
const DEEPEST: usize = 127;

#[pymodule]
mod _native {
    use super::*;

    /// Checks whether `a` accepts every instance that is valid under `b`.
    ///
    /// The outcome is a tuple that begins with what it is: `("yes",)`, `("no", counterexample)`,
    /// `("unsupported", side, location)`, `("unrepresentable",)`, `("budget",)`, or
    /// `("invalid", message, side, location)` for a schema that cannot be checked at all,
    /// where the location is `None` when the schema as a whole is at fault.
    ///
    /// Raises `TypeError` or `ValueError` for an argument that is no JSON value, and
    /// `ValueError` for a dialect that is none.
    #[pyfunction]
    fn check<'py>(
        py: Python<'py>,
        a: &Bound<'py, PyAny>,
        b: &Bound<'py, PyAny>,
        budget: Option<u64>,
        regex_dialect: &str,
    ) -> PyResult<Bound<'py, PyTuple>> {
        let a = schema(a, Side::A)?;
        let b = schema(b, Side::B)?;
        let regex_dialect = match regex_dialect {
            "ecma262" => RegexDialect::Ecma262,
            "rust" => RegexDialect::Rust,
            other => {
                let message = format!("regex_dialect is {other:?}, not \"ecma262\" or \"rust\"");
                return Err(PyValueError::new_err(message));
            }
        };
        let mut checker = Checker::new().regex_dialect(regex_dialect);
        if let Some(steps) = budget {
            checker = checker.budget(steps);
        }
        // The check touches no Python object, so other threads may run meanwhile.
        match py.detach(|| checker.subsumes(&a, &b)) {
            Ok(Verdict::Yes) => ("yes",).into_pyobject(py),
            Ok(Verdict::No { counterexample }) => {
                ("no", instance(py, &counterexample)?).into_pyobject(py)
            }
            Ok(Verdict::Unknown { reason }) => match reason {
                Reason::Unsupported { schema, location } => {
                    ("unsupported", name(schema), location).into_pyobject(py)
                }
                Reason::Unrepresentable => ("unrepresentable",).into_pyobject(py),
                Reason::Budget => ("budget",).into_pyobject(py),
                // `Reason` may grow, and the package has a class for each reason. One that
                // has none yet is a fault of the package. It raises, so that the check
                // passes for no answer.
                reason => Err(PyRuntimeError::new_err(format!(
                    "the package has no class for the reason: {reason}"
                ))),
            },
            Err(error) => {
                let message = error.to_string();
                let (side, location) = match error {
                    Error::NotASchema { schema } => (schema, None),
                    Error::UnsupportedDialect {
                        schema, location, ..
                    }
                    | Error::InvalidKeyword {
                        schema, location, ..
                    }
                    | Error::UnresolvedReference {
                        schema, location, ..
                    } => (schema, Some(location)),
                    _ => return Err(PyValueError::new_err(message)),
                };
                ("invalid", message, name(side), location).into_pyobject(py)
            }
        }
    }
}

/// A side as the package names it.
fn name(side: Side) -> &'static str {
    match side {
        Side::A => "a",
        Side::B => "b",
    }
}

/// The schema that a Python object stands for, or the exception that says why it is none.
fn schema(object: &Bound<'_, PyAny>, side: Side) -> PyResult<Value> {
    value(object, 0).map_err(|refusal| {
        let mut location = String::from("#");
        for part in refusal.path.iter().rev() {
            location.push('/');
            location.push_str(&part.replace('~', "~0").replace('/', "~1"));
        }
        let message = format!("{location} in schema {side} {}", refusal.message);
        if refusal.wrong_type {
            PyTypeError::new_err(message)
        } else {
            PyValueError::new_err(message)
        }
    })
}

/// Why a Python object is no JSON value.
struct Refusal {
    /// Whether the object is of a type that JSON does not have, which is a `TypeError`, or
    /// of the right type and with a value that JSON does not have, which is a `ValueError`.
    wrong_type: bool,
    /// What is wrong with the object, to follow its location in a sentence.
    message: String,
    /// The keys and indices that lead to the object, the innermost first.
    path: Vec<String>,
}

impl Refusal {
    fn of_type(message: String) -> Self {
        Self {
            wrong_type: true,
            message,
            path: Vec::new(),
        }
    }

    fn of_value(message: impl Into<String>) -> Self {
        Self {
            wrong_type: false,
            message: message.into(),
            path: Vec::new(),
        }
    }

    /// The same refusal, seen from the array or the object that holds the value under `part`.
    fn below(mut self, part: impl ToString) -> Self {
        self.path.push(part.to_string());
        self
    }
}

/// The JSON value that a Python object stands for: what `json.load` gives is taken, and
/// nothing else. `depth` is the number of arrays and objects around the object.
fn value(object: &Bound<'_, PyAny>, depth: usize) -> Result<Value, Refusal> {
    if object.is_none() {
        return Ok(Value::Null);
    }
    // A `bool` is an `int` to Python, so it is asked for first.
    if let Ok(boolean) = object.cast::<PyBool>() {
        return Ok(Value::Bool(boolean.is_true()));
    }
    if let Ok(integer) = object.cast::<PyInt>() {
        return number(integer);
    }
    if let Ok(float) = object.cast::<PyFloat>() {
        return Number::from_f64(float.value())
            .map(Value::Number)
            .ok_or_else(|| Refusal::of_value(format!("is {float}, which is not a JSON number")));
    }
    if let Ok(string) = object.cast::<PyString>() {
        return string.extract().map(Value::String).map_err(|_| {
            Refusal::of_value("is a string with a surrogate that stands alone, which is not text")
        });
    }
    let list = object.cast::<PyList>();
    let dict = object.cast::<PyDict>();
    if (list.is_ok() || dict.is_ok()) && depth == DEEPEST {
        return Err(Refusal::of_value(format!(
            "is nested more than {DEEPEST} deep"
        )));
    }
    if let Ok(list) = list {
        return list
            .iter()
            .enumerate()
            .map(|(index, item)| value(&item, depth + 1).map_err(|refusal| refusal.below(index)))
            .collect::<Result<_, _>>()
            .map(Value::Array);
    }
    if let Ok(dict) = dict {
        let mut members = Map::new();
        for (key, member) in dict.iter() {
            let Ok(key) = key.cast::<PyString>() else {
                return Err(Refusal::of_type(format!(
                    "has the key {}, and a key must be a str",
                    key.repr().map_or_else(|_| "?".into(), |r| r.to_string())
                )));
            };
            let key: String = key.extract().map_err(|_| {
                Refusal::of_value("has a key with a surrogate that stands alone, which is not text")
            })?;
            let member = value(&member, depth + 1).map_err(|refusal| refusal.below(&key))?;
            members.insert(key, member);
        }
        return Ok(Value::Object(members));
    }
    let kind = object
        .get_type()
        .name()
        .map_or_else(|_| "?".into(), |name| name.to_string());
    Err(Refusal::of_type(format!(
        "is of type {kind}, and a schema is made of dict, list, str, int, float, bool and None"
    )))
}

/// A Python integer as a JSON number. One that 64 bits hold stays an integer. A larger one
/// becomes the float that is nearest to it, as `serde_json` reads the same digits from text.
fn number(integer: &Bound<'_, PyInt>) -> Result<Value, Refusal> {
    if let Ok(small) = integer.extract::<i64>() {
        return Ok(Value::Number(small.into()));
    }
    if let Ok(large) = integer.extract::<u64>() {
        return Ok(Value::Number(large.into()));
    }
    integer
        .extract::<f64>()
        .ok()
        .and_then(Number::from_f64)
        .map(Value::Number)
        .ok_or_else(|| Refusal::of_value("is an integer too large for a JSON number"))
}

/// An instance as a Python object: what `json.loads` would make of its text.
fn instance<'py>(py: Python<'py>, value: &Value) -> PyResult<Bound<'py, PyAny>> {
    Ok(match value {
        Value::Null => py.None().into_bound(py),
        Value::Bool(boolean) => boolean.into_pyobject(py)?.to_owned().into_any(),
        Value::Number(number) => {
            if let Some(integer) = number.as_i64() {
                integer.into_pyobject(py)?.into_any()
            } else if let Some(integer) = number.as_u64() {
                integer.into_pyobject(py)?.into_any()
            } else {
                // A number of a `serde_json` value is one of the three.
                number.as_f64().into_pyobject(py)?.into_any()
            }
        }
        Value::String(string) => string.into_pyobject(py)?.into_any(),
        Value::Array(items) => {
            let list = PyList::empty(py);
            for item in items {
                list.append(instance(py, item)?)?;
            }
            list.into_any()
        }
        Value::Object(members) => {
            let dict = PyDict::new(py);
            for (key, member) in members {
                dict.set_item(key, instance(py, member)?)?;
            }
            dict.into_any()
        }
    })
}
