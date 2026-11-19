//! Drawing what the library makes of two schemas, as a page for the browser.

use std::path::Path;
use std::process::Command;
use std::{env, fs};

use serde_json::{Value, json};
use subsumes::Checker;

/// The page without a graph. It draws with Graphviz, which it loads from a CDN.
const PAGE: &str = include_str!("viewer.html");
/// Where the graph goes in the page.
const PLACE: &str = "{{graph}}";

/// The page that shows the schema graph of the schemas in two files. Without a second file, B
/// is the schema `true`.
pub fn page(a: &Path, b: Option<&Path>) -> Result<String, String> {
    let schema_a = json(a)?;
    let schema_b = b.map_or(Ok(Value::Bool(true)), json)?;
    let mut graph = Checker::new()
        .inspect(&schema_a, &schema_b)
        .map_err(|error| error.to_string())?;
    let name = |path: &Path| path.display().to_string();
    graph["names"] = json!({"a": name(a), "b": b.map_or_else(|| "true".to_owned(), name)});
    Ok(with_graph(&graph))
}

/// The schema in a file.
fn json(path: &Path) -> Result<Value, String> {
    let failed = |error: &dyn std::fmt::Display| format!("cannot read {}: {error}", path.display());
    let text = fs::read_to_string(path).map_err(|error| failed(&error))?;
    serde_json::from_str(&text).map_err(|error| failed(&error))
}

/// The page with a graph in it. Every `<` of the graph is written as an escape, so that no
/// text of a schema can end the element that holds it.
fn with_graph(graph: &Value) -> String {
    PAGE.replace(PLACE, &graph.to_string().replace('<', "\\u003c"))
}

/// Opens a page in the program that the environment variable `BROWSER` names, or else in
/// whatever the system opens a page with.
pub fn open(page: &Path) -> Result<(), String> {
    let mut command = match env::var_os("BROWSER") {
        Some(browser) => Command::new(browser),
        None if cfg!(target_os = "macos") => Command::new("open"),
        None if cfg!(target_os = "windows") => {
            let mut command = Command::new("cmd");
            command.args(["/C", "start", ""]);
            command
        }
        None => Command::new("xdg-open"),
    };
    let status = command
        .arg(page)
        .status()
        .map_err(|error| format!("cannot open {}: {error}", page.display()))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("cannot open {}: {status}", page.display()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_page_has_one_place_for_the_graph() {
        assert_eq!(PAGE.matches(PLACE).count(), 1);
        let page = with_graph(&json!({"nodes": [], "edges": []}));
        assert!(page.contains(r#"id="graph">{"edges":[],"nodes":[]}</script>"#));
    }

    #[test]
    fn no_text_of_a_schema_ends_the_element_that_holds_the_graph() {
        let text = "</script><script>alert(1)</script>";
        let page = with_graph(&json!({"nodes": [{"location": text}]}));
        assert!(!page.contains(text));
        assert!(page.contains(r"\u003c/script>\u003cscript>alert(1)\u003c/script>"));
        // The escape is one that JSON reads back as the character.
        let read: Value = serde_json::from_str(r#""\u003c/script>""#).unwrap();
        assert_eq!(read, "</script>");
    }
}
