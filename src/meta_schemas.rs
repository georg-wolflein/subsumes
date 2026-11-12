//! The meta-schema of draft 2020-12 and those of its vocabularies: the only documents that a
//! schema can reference without carrying them.
//!
//! The draft publishes more: Hyper-Schema with its `links`, which is a dialect of its own, and
//! a schema for the output of a validator. The library does not read those, so they are not
//! here.
//!
//! The files are the ones that json-schema.org serves, under the license next to them.

use std::sync::OnceLock;

use serde_json::Value;

/// The meta-schema of the draft and the eight of its vocabularies, each by the URI it is served
/// at, which is also its `$id`.
pub(crate) const SOURCES: [(&str, &str); 9] = [
    (
        "https://json-schema.org/draft/2020-12/schema",
        include_str!("meta_schemas/draft2020-12/schema.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/core",
        include_str!("meta_schemas/draft2020-12/meta/core.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/applicator",
        include_str!("meta_schemas/draft2020-12/meta/applicator.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/unevaluated",
        include_str!("meta_schemas/draft2020-12/meta/unevaluated.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/validation",
        include_str!("meta_schemas/draft2020-12/meta/validation.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/meta-data",
        include_str!("meta_schemas/draft2020-12/meta/meta-data.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/format-annotation",
        include_str!("meta_schemas/draft2020-12/meta/format-annotation.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/format-assertion",
        include_str!("meta_schemas/draft2020-12/meta/format-assertion.json"),
    ),
    (
        "https://json-schema.org/draft/2020-12/meta/content",
        include_str!("meta_schemas/draft2020-12/meta/content.json"),
    ),
];

/// The meta-schema with this URI, if the draft has one. All of them are read at the first call.
pub(crate) fn document(uri: &str) -> Option<&'static Value> {
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

    const DRAFT: &str = "https://json-schema.org/draft/2020-12/";

    #[test]
    fn the_meta_schema_and_those_of_its_vocabularies_are_here() {
        let mut uris: Vec<&str> = SOURCES.iter().map(|(uri, _)| *uri).collect();
        uris.sort_unstable();
        let names = [
            "meta/applicator",
            "meta/content",
            "meta/core",
            "meta/format-annotation",
            "meta/format-assertion",
            "meta/meta-data",
            "meta/unevaluated",
            "meta/validation",
            "schema",
        ];
        assert_eq!(uris, names.map(|name| format!("{DRAFT}{name}")));

        // Whatever the meta-schema draws in is among them.
        let drawn_in = document(&format!("{DRAFT}schema")).unwrap()["allOf"]
            .as_array()
            .unwrap();
        assert_eq!(drawn_in.len(), 7);
        for part in drawn_in {
            let uri = format!("{DRAFT}{}", part["$ref"].as_str().unwrap());
            assert!(document(&uri).is_some(), "{uri}");
        }
    }

    #[test]
    fn every_meta_schema_is_served_at_its_id() {
        for (uri, _) in SOURCES {
            let document = document(uri).unwrap();
            assert_eq!(document["$id"], uri);
        }
        for other in ["draft/2019-09/schema", "draft/2020-12/hyper-schema"] {
            assert_eq!(document(&format!("https://json-schema.org/{other}")), None);
        }
    }
}
