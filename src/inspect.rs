//! What the stages of a check make of the two schemas, as JSON for a tool that shows it.
//!
//! Each stage is a list of nodes, each with rows of what it says, and a list of the edges
//! between them. The shape follows the needs of the viewer and is not stable.

use serde_json::{Value, json};

use crate::context::Context;
use crate::language::Languages;
use crate::rational::shown;
use crate::schema::Graph;
use crate::term::{Term, TermId, Terms, VarId};

/// The stages of a check: the schema graph, and the terms if the two schemas were lowered.
pub(crate) fn stages(graph: &Graph, context: &Context, roots: Option<(VarId, VarId)>) -> Value {
    let mut stages = vec![named("Schema graph", graph.to_json())];
    if let Some((a, b)) = roots {
        stages.push(named("Terms", lowered(graph, context, a, b)));
    }
    json!({ "stages": stages })
}

fn named(name: &str, mut stage: Value) -> Value {
    stage["name"] = json!(name);
    stage
}

/// The terms: one node for each variable, with a row for each part of its term, and an edge
/// to each variable that the term refers to.
fn lowered(graph: &Graph, context: &Context, a: VarId, b: VarId) -> Value {
    let (terms, languages) = (&context.terms, &context.languages);
    let (mut nodes, mut edges) = (Vec::new(), Vec::new());
    for (id, variable) in terms.variables() {
        let side = match variable.sides {
            [true, true] => "A and B",
            [_, true] => "B",
            _ => "A",
        };
        let parts = match terms.term(variable.body) {
            Term::AllOf(parts) => parts.to_vec(),
            _ => vec![variable.body],
        };
        let row = |part: &TermId| row(graph, terms, languages, *part);
        let rows: Vec<Value> = parts.iter().map(row).collect();
        nodes.push(json!({
            "id": id.index(),
            "name": format!("x{}", id.index()),
            "side": side,
            "location": graph.location(variable.node),
            "keywords": rows,
        }));
        for (to, how) in referred(terms, variable.body) {
            edges.push(json!({
                "kind": "applies",
                "from": id.index(),
                "to": to.index(),
                "keyword": how,
            }));
        }
    }
    json!({
        "a": a.index(),
        "b": b.index(),
        "nodes": nodes,
        "edges": edges,
        // The rows hold text, not the values of keywords.
        "plain": true,
    })
}

/// One part of the term of a variable: what kind of term it is, and the term.
fn row(graph: &Graph, terms: &Terms, languages: &Languages, part: TermId) -> Value {
    match terms.term(part) {
        Term::True => json!(["accepts", "everything"]),
        Term::False => json!(["accepts", "nothing"]),
        Term::TypeIs(types) => {
            let names: Vec<&str> = types.iter().map(|kind| kind.name()).collect();
            json!(["type", names.join(", ")])
        }
        Term::BoolConst(value) => json!(["is", value.to_string()]),
        Term::NumConst(number) => json!(["is", shown(number)]),
        Term::Min(_) | Term::ExMin(_) | Term::Max(_) | Term::ExMax(_) | Term::Mof(_) => {
            json!(["number", terms.show_with(part, languages)])
        }
        Term::StrConst(word) => json!(["is", format!("{word:?}")]),
        Term::Patt(language) => json!(["string", languages.show(*language)]),
        Term::MinLen(_) | Term::MaxLen(_) => json!(["string", terms.show_with(part, languages)]),
        Term::PProp(..)
        | Term::PReq(_)
        | Term::PNames(_)
        | Term::MinProps(_)
        | Term::MaxProps(_) => json!(["object", terms.show_with(part, languages)]),
        Term::Unknown(leaf) => {
            let leaf = terms.leaf(*leaf);
            let about: Vec<&str> = leaf.domain.iter().map(|kind| kind.name()).collect();
            let side = graph.node(leaf.node).side;
            let place = leaf.location(graph);
            let (key, about) = (&leaf.key, about.join(", "));
            json!([
                "unknown",
                format!("{key}, about {about}, first at {place} in {side}")
            ])
        }
        Term::AllOf(_) => json!(["all of", terms.show_with(part, languages)]),
        Term::AnyOf(_) => json!(["any of", terms.show_with(part, languages)]),
        Term::OneOf(_) => json!(["one of", terms.show_with(part, languages)]),
        Term::Not(inner) => json!(["not", terms.show_with(*inner, languages)]),
        Term::Ref(_) => json!(["also", terms.show_with(part, languages)]),
    }
}

/// The variables that a term refers to, each with how: plainly, under a negation, in a
/// `OneOf`, which takes each of its parts both ways, or for the values or the names of the
/// properties of an object.
fn referred(terms: &Terms, term: TermId) -> Vec<(VarId, &'static str)> {
    let mut found: Vec<(VarId, &'static str)> = Vec::new();
    let mut pending = vec![(term, "")];
    while let Some((term, how)) = pending.pop() {
        match terms.term(term) {
            Term::Ref(variable) => {
                if !found.contains(&(*variable, how)) {
                    found.push((*variable, how));
                }
            }
            Term::AllOf(parts) | Term::AnyOf(parts) => {
                pending.extend(parts.iter().rev().map(|part| (*part, how)));
            }
            Term::OneOf(parts) => {
                pending.extend(parts.iter().rev().map(|part| (*part, "one of")));
            }
            Term::Not(inner) => {
                let how = match how {
                    "" => "not",
                    "not" => "",
                    other => other,
                };
                pending.push((*inner, how));
            }
            Term::True | Term::False | Term::TypeIs(_) | Term::BoolConst(_) | Term::Unknown(_) => {}
            Term::NumConst(_) => {}
            Term::Min(_) | Term::ExMin(_) | Term::Max(_) | Term::ExMax(_) | Term::Mof(_) => {}
            Term::StrConst(_) | Term::Patt(_) | Term::MinLen(_) | Term::MaxLen(_) => {}
            Term::PProp(_, variable) | Term::PNames(variable) => {
                let how = match terms.term(term) {
                    Term::PNames(_) => "names",
                    _ => "properties",
                };
                if !found.contains(&(*variable, how)) {
                    found.push((*variable, how));
                }
            }
            Term::PReq(_) | Term::MinProps(_) | Term::MaxProps(_) => {}
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{lower, schema};

    fn shown(a: &Value, b: &Value, budget: u64) -> Value {
        let graph = schema::parse(a, b).unwrap().link().unwrap();
        let mut context = Context::new(budget);
        let roots = lower::lower(&graph, &mut context).ok();
        stages(&graph, &context, roots)
    }

    #[test]
    fn there_is_a_picture_for_each_stage() {
        let shared = json!({"type": "array", "minItems": 1});
        let a = json!({"anyOf": [shared, {"type": "null"}]});
        let b = json!({"allOf": [shared], "not": {"type": "null"}});
        let shown = shown(&a, &b, u64::MAX);
        let stages = shown["stages"].as_array().unwrap();
        assert_eq!(stages[0]["name"], "Schema graph");
        assert_eq!(stages[0]["nodes"].as_array().unwrap().len(), 6);

        let terms = &stages[1];
        assert_eq!(terms["name"], "Terms");
        assert_eq!((&terms["a"], &terms["b"]), (&json!(0), &json!(1)));
        assert_eq!(
            terms["nodes"],
            json!([
                {
                    "id": 0,
                    "name": "x0",
                    "side": "A",
                    "location": "#",
                    "keywords": [["any of", "any(x2, x3)"]],
                },
                {
                    "id": 1,
                    "name": "x1",
                    "side": "B",
                    "location": "#",
                    "keywords": [["also", "x2"], ["not", "x3"]],
                },
                {
                    "id": 2,
                    "name": "x2",
                    "side": "A and B",
                    "location": "#/anyOf/0",
                    "keywords": [
                        ["type", "array"],
                        ["unknown", "minItems 1, about array, first at #/anyOf/0/minItems in A"],
                    ],
                },
                {
                    "id": 3,
                    "name": "x3",
                    "side": "A and B",
                    "location": "#/anyOf/1",
                    "keywords": [["type", "null"]],
                },
            ])
        );
        assert_eq!(
            terms["edges"],
            json!([
                {"kind": "applies", "from": 0, "to": 2, "keyword": ""},
                {"kind": "applies", "from": 0, "to": 3, "keyword": ""},
                {"kind": "applies", "from": 1, "to": 2, "keyword": ""},
                {"kind": "applies", "from": 1, "to": 3, "keyword": "not"},
            ])
        );
    }

    #[test]
    fn what_a_term_says_about_numbers_is_a_row_each() {
        let schema = json!({"type": "integer", "const": 2.0, "minimum": 0, "multipleOf": 0.5});
        let shown = shown(&schema, &json!(true), u64::MAX);
        assert_eq!(
            shown["stages"][1]["nodes"][0]["keywords"],
            json!([
                ["type", "number"],
                ["number", "mof(1)"],
                ["is", "2"],
                ["number", "min(0)"],
                ["number", "mof(0.5)"],
            ])
        );
    }

    #[test]
    fn what_a_term_says_about_strings_is_a_row_each() {
        let schema = json!({
            "enum": ["a", "é\n"],
            "minLength": 1,
            "maxLength": 2,
            "pattern": "^a",
            "format": "date",
            "not": {"pattern": "b$"},
        });
        let shown = shown(&schema, &json!(true), u64::MAX);
        let nodes = &shown["stages"][1]["nodes"];
        assert_eq!(
            nodes[0]["keywords"],
            json!([
                ["not", "x2"],
                ["any of", r#"any(is("a"), is("é\n"))"#],
                ["string", "minlen(1)"],
                ["string", "maxlen(2)"],
                ["string", r#""^a""#],
                ["string", "format date"],
            ])
        );
        assert_eq!(nodes[2]["keywords"], json!([["string", r#""b$""#]]));
        // A format that is modelled in part: what it accepts, or what it leaves open
        // together with a leaf. Inside a term a language is named as it is in a row.
        let time = json!({"format": "time"});
        let shown = self::shown(&time, &json!(true), u64::MAX);
        assert_eq!(
            shown["stages"][1]["nodes"][0]["keywords"],
            json!([[
                "any of",
                r#"any(patt(format time), all(patt(format time, where it is open), ?[format "time" where it is open]))"#
            ]])
        );
    }

    #[test]
    fn what_a_term_says_about_objects_is_a_row_each_with_an_edge_to_each_schema() {
        let schema = json!({
            "properties": {"a": {"type": "null"}},
            "additionalProperties": false,
            "propertyNames": {"maxLength": 3},
            "required": ["a"],
            "maxProperties": 2,
        });
        let shown = shown(&schema, &json!(true), u64::MAX);
        let terms = &shown["stages"][1];
        assert_eq!(
            terms["nodes"][0]["keywords"],
            json!([
                ["object", r#"pprop(one of ["a"]: x2)"#],
                ["object", r#"pprop(any string but "a": x3)"#],
                ["object", "pnames(x4)"],
                ["object", r#"preq(one of ["a"])"#],
                ["object", "maxprops(2)"],
            ])
        );
        let from_a: Vec<(&Value, &Value)> = terms["edges"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|edge| edge["from"] == 0)
            .map(|edge| (&edge["to"], &edge["keyword"]))
            .collect();
        assert_eq!(
            from_a,
            [
                (&json!(2), &json!("properties")),
                (&json!(3), &json!("properties")),
                (&json!(4), &json!("names")),
            ]
        );
    }

    #[test]
    fn without_the_budget_for_them_there_are_no_terms() {
        let cycle = json!({"not": {"not": {"not": {"$ref": "#"}}}});
        let shown = shown(&cycle, &json!(true), 1);
        assert_eq!(shown["stages"].as_array().unwrap().len(), 1);
    }
}
