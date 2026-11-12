//! The meta-schemas of draft 2020-12: the only documents that a schema can reference without
//! carrying them.
//!
//! The files are the ones that json-schema.org serves, under the license next to them.

use std::sync::OnceLock;

use serde_json::Value;

/// Every meta-schema of the draft, by the URI it is served at, which is also its `$id`.
const SOURCES: [(&str, &str); 9] = [
    (
        "https://json-schema.org/draft/2020-12/schema",
        include_str!("draft2020-12/schema.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/core",
        include_str!("draft2020-12/meta/core.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/applicator",
        include_str!("draft2020-12/meta/applicator.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/unevaluated",
        include_str!("draft2020-12/meta/unevaluated.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/validation",
        include_str!("draft2020-12/meta/validation.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/meta-data",
        include_str!("draft2020-12/meta/meta-data.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/format-annotation",
        include_str!("draft2020-12/meta/format-annotation.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/format-assertion",
        include_str!("draft2020-12/meta/format-assertion.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/content",
        include_str!("draft2020-12/meta/content.json"),
    ),
];

/// The meta-schema with this URI, if the draft has one. All of them are read at the first call.
pub(super) fn document(uri: &str) -> Option<&'static Value> {
    static DOCUMENTS: OnceLock<Vec<Value>> = OnceLock::new();
    let position = SOURCES.iter().position(|(known, _)| *known == uri)?;
    let documents = DOCUMENTS.get_or_init(|| {
        let read = |(_, text): &(&str, &str)| {
            serde_json::from_str(text).expect("a meta-schema is valid JSON")
        };
        SOURCES.iter().map(read).collect()
    });
    Some(&documents[position])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_meta_schema_is_served_at_its_id() {
        for (uri, _) in SOURCES {
            let document = document(uri).unwrap();
            assert_eq!(document["$id"], uri);
        }
        assert_eq!(
            document("https://json-schema.org/draft/2019-09/schema"),
            None
        );
    }
}
