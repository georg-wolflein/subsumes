//! What the stages of a check make of the two schemas, as JSON for a tool that shows it.
//!
//! Each stage is a list of nodes, each with rows of what it says, and a list of the edges
//! between them. The shape follows the needs of the viewer and is not stable.

use serde_json::{Value, json};

use crate::schema::Graph;
use crate::term::{Term, TermId, Terms, VarId};

/// The stages of a check: the schema graph, and the terms if the two schemas were lowered.
pub(crate) fn stages(graph: &Graph, terms: &Terms, roots: Option<(VarId, VarId)>) -> Value {
    let mut stages = vec![named("Schema graph", graph.to_json())];
    if let Some((a, b)) = roots {
        stages.push(named("Terms", lowered(graph, terms, a, b)));
    }
    json!({ "stages": stages })
}

fn named(name: &str, mut stage: Value) -> Value {
    stage["name"] = json!(name);
    stage
}

/// The terms: one node for each variable, with a row for each part of its term, and an edge
/// to each variable that the term refers to.
fn lowered(graph: &Graph, terms: &Terms, a: VarId, b: VarId) -> Value {
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
        let rows: Vec<Value> = parts.iter().map(|part| row(graph, terms, *part)).collect();
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
fn row(graph: &Graph, terms: &Terms, part: TermId) -> Value {
    match terms.term(part) {
        Term::True => json!(["accepts", "everything"]),
        Term::False => json!(["accepts", "nothing"]),
        Term::TypeIs(types) => {
            let names: Vec<&str> = types.iter().map(|kind| kind.name()).collect();
            json!(["type", names.join(", ")])
        }
        Term::BoolConst(value) => json!(["is", value.to_string()]),
        Term::NumConst(number) => json!(["is", number.to_string()]),
        Term::Min(_) | Term::ExMin(_) | Term::Max(_) | Term::ExMax(_) | Term::Mof(_) => {
            json!(["number", terms.show(part)])
        }
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
        Term::AllOf(_) => json!(["all of", terms.show(part)]),
        Term::AnyOf(_) => json!(["any of", terms.show(part)]),
        Term::OneOf(_) => json!(["one of", terms.show(part)]),
        Term::Not(inner) => json!(["not", terms.show(*inner)]),
        Term::Ref(_) => json!(["also", terms.show(part)]),
    }
}

/// The variables that a term refers to, each with how: plainly, under a negation, or in a
/// `OneOf`, which takes each of its parts both ways.
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
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Context;
    use crate::{lower, schema};

    fn shown(a: &Value, b: &Value, budget: u64) -> Value {
        let graph = schema::parse(a, b).unwrap().link().unwrap();
        let mut context = Context::new(budget);
        let roots = lower::lower(&graph, &mut context).ok();
        stages(&graph, &context.terms, roots)
    }

    #[test]
    fn there_is_a_picture_for_each_stage() {
        let shared = json!({"type": "string", "minLength": 1});
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
                        ["type", "string"],
                        ["unknown", "minLength 1, about string, first at #/anyOf/0/minLength in A"],
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
    fn without_the_budget_for_them_there_are_no_terms() {
        let cycle = json!({"not": {"not": {"not": {"$ref": "#"}}}});
        let shown = shown(&cycle, &json!(true), 1);
        assert_eq!(shown["stages"].as_array().unwrap().len(), 1);
    }
}
