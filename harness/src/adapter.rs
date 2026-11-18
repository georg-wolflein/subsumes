//! The library as a checker of the benchmark.
//!
//! The runner of the [benchmark](https://github.com/georg-wolflein/subsumes-benchmark) drives a
//! checker through an adapter: a program that starts once, says that it is ready, and then
//! answers one request per line on its standard input with one line on its standard output.
//! This is the adapter for the library as it is in the working tree. `checker.json` in the
//! folder of the harness tells the runner how to build and to start it.
//!
//! A request holds two schemas, `a` and `b`, and asks whether `a` accepts every instance that
//! is valid under `b`, which is the library's own question. The reply has the answer, which is
//! `true`, `false` or `null` as the label of a case is, and the time. With a `No` goes its
//! counterexample, which the runner asks a validator about, and with an `Unknown` the reason
//! and what the benchmark comment counts the reasons by. Where the library rejects a schema
//! there is no answer, and the reply says that it failed.

use std::io::{self, BufRead, Write};
use std::time::Instant;

use serde_json::{Value, json};
use subsumes::{Checker, Reason, Verdict};

/// Answers the requests on the standard input until it ends.
pub fn serve() -> io::Result<()> {
    // The default work budget and dialect, which is what a user of the library gets.
    let checker = Checker::new();
    let mut out = io::stdout().lock();
    writeln!(out, "{}", json!({"ready": true}))?;
    out.flush()?;
    for line in io::stdin().lock().lines() {
        writeln!(out, "{}", answer(&line?, &checker))?;
        out.flush()?;
    }
    Ok(())
}

/// The reply to one request. Whatever goes wrong is an answer too, so that the next request
/// finds the adapter running.
fn answer(request: &str, checker: &Checker) -> Value {
    // The time of a check covers parsing each schema once, as the runner asks of every
    // checker. The library takes a schema as a parsed value, and the request is parsed into
    // the two, so the clock runs from the request as text to the answer.
    let start = Instant::now();
    let outcome = check(request, checker);
    let seconds = start.elapsed().as_secs_f64();
    let mut reply =
        outcome.unwrap_or_else(|message| json!({"failure": "error", "message": message}));
    reply["seconds"] = json!(seconds);
    reply
}

/// The two schemas of a request, which holds each as a JSON value.
fn schemas(request: &str) -> Result<(Value, Value), String> {
    let mut request: Value = serde_json::from_str(request).map_err(|error| error.to_string())?;
    let mut schema = |key: &str| {
        let schema = request.get_mut(key).map(Value::take);
        schema.ok_or(format!("no schema for {key}"))
    };
    Ok((schema("a")?, schema("b")?))
}

/// The reply to a request, without its time. The library rejecting a schema is an error: the
/// corpus holds only valid schemas.
fn check(request: &str, checker: &Checker) -> Result<Value, String> {
    let (a, b) = schemas(request)?;
    let verdict = checker
        .subsumes(&a, &b)
        .map_err(|error| error.to_string())?;
    Ok(match verdict {
        Verdict::Yes => json!({"answer": true}),
        Verdict::No { counterexample } => {
            json!({"answer": false, "counterexample": counterexample})
        }
        Verdict::Unknown { reason } => json!({
            "answer": null,
            "reason": kind(&reason),
            "message": reason.to_string(),
        }),
    })
}

/// What the reasons for `Unknown` are counted by: `budget`, or the keyword that is not
/// supported.
fn kind(reason: &Reason) -> String {
    match reason {
        Reason::Budget => "budget".to_owned(),
        Reason::Unrepresentable => "unrepresentable instance".to_owned(),
        Reason::Unsupported { location, .. } => keyword(location),
        _ => "other".to_owned(),
    }
}

/// The last token of the JSON Pointer in a location, which names the keyword; a location
/// without one is the schema as a whole.
fn keyword(location: &str) -> String {
    let pointer = location.split_once('#').map_or("", |(_, pointer)| pointer);
    match pointer.rsplit_once('/') {
        Some((_, token)) => token.replace("~1", "/").replace("~0", "~"),
        None => "whole schema".to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reply to a request about two schemas, as the runner sends it. The time is taken
    /// out, which no two runs agree on.
    fn reply(a: &Value, b: &Value) -> Value {
        let request = json!({"a": a, "b": b, "timeout": 10.0});
        let mut reply = answer(&request.to_string(), &Checker::new());
        let seconds = reply.as_object_mut().unwrap().remove("seconds").unwrap();
        assert!(seconds.as_f64().unwrap() >= 0.0);
        reply
    }

    #[test]
    fn a_reply_has_the_answer_and_what_belongs_to_it() {
        let (text, optional) = (
            json!({"type": "string"}),
            json!({"type": ["string", "null"]}),
        );
        assert_eq!(reply(&optional, &text), json!({"answer": true}));
        // `null` is a counterexample, and is in the reply as one.
        assert_eq!(
            reply(&text, &optional),
            json!({"answer": false, "counterexample": null})
        );
        let (list, set) = (
            json!({"type": "array"}),
            json!({"type": "array", "uniqueItems": true}),
        );
        assert_eq!(
            reply(&set, &list),
            json!({
                "answer": null,
                "reason": "uniqueItems",
                "message": "#/uniqueItems in schema A is not supported",
            })
        );
    }

    #[test]
    fn what_goes_wrong_is_a_reply_without_an_answer() {
        let failed = |reply: &Value| {
            let keys: Vec<&String> = reply.as_object().unwrap().keys().collect();
            assert_eq!(keys, ["failure", "message", "seconds"]);
            assert_eq!(reply["failure"], "error");
            assert!(reply["seconds"].is_number());
            reply["message"].as_str().unwrap().to_owned()
        };
        let checker = Checker::new();
        // The library rejects a schema.
        let request = json!({"a": {"minimum": "0"}, "b": true, "timeout": 10.0});
        assert!(failed(&answer(&request.to_string(), &checker)).contains("minimum"));
        // A request that is none, one without a schema, and one whose schema is the text
        // of a schema, which is a string and no schema.
        failed(&answer("no request", &checker));
        let without = answer(&json!({"a": true}).to_string(), &checker);
        assert_eq!(failed(&without), "no schema for b");
        failed(&answer(
            &json!({"a": true, "b": "{}"}).to_string(),
            &checker,
        ));
    }

    #[test]
    fn the_reasons_are_counted_by_the_keyword() {
        let unsupported = |location: &str| Reason::Unsupported {
            schema: subsumes::Side::A,
            location: location.to_owned(),
        };
        assert_eq!(kind(&Reason::Budget), "budget");
        assert_eq!(kind(&Reason::Unrepresentable), "unrepresentable instance");
        assert_eq!(kind(&unsupported("#/items/uniqueItems")), "uniqueItems");
        assert_eq!(kind(&unsupported("#/properties/a~1b")), "a/b");
        assert_eq!(
            kind(&unsupported("https://example.com/s#/format")),
            "format"
        );
        assert_eq!(kind(&unsupported("#")), "whole schema");
    }

    #[test]
    fn a_long_number_is_read_as_the_double_nearest_to_it() {
        // Without `float_roundtrip` serde_json reads this one off in the last place, and the
        // counterexample to the constant would be no instance of it.
        let long = "98249283749234923498293171823948729348710298301928331";
        let read: Value = serde_json::from_str(long).unwrap();
        assert_eq!(read, json!(9.824_928_374_923_492e52));
    }
}
