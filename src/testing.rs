//! What several tests share.

use std::io::ErrorKind;
use std::path::{Path, PathBuf};

use serde_json::Value;

/// A source of numbers that is the same on every run.
pub(crate) struct Random(pub u64);

impl Random {
    /// The next number, by the SplitMix64 generator.
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut mixed = self.0;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        mixed ^ (mixed >> 31)
    }

    pub fn below(&mut self, limit: usize) -> usize {
        usize::try_from(self.next() % limit as u64).unwrap()
    }

    pub fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }

    pub fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len())]
    }
}

/// The file of every case of the corpus in `benchmark/`, which `make corpus` unpacks: every
/// JSON file in the folder of a collection listed in `manifest.json` or `collections.json`.
pub(crate) fn corpus_cases() -> Vec<PathBuf> {
    let corpus = Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmark");
    let collections: Value = match std::fs::read_to_string(corpus.join("manifest.json")) {
        Ok(text) => serde_json::from_str::<Value>(&text).unwrap()["collections"].take(),
        Err(error) if error.kind() == ErrorKind::NotFound => {
            let text = std::fs::read_to_string(corpus.join("collections.json")).unwrap();
            serde_json::from_str(&text).unwrap()
        }
        Err(error) => panic!("could not read benchmark/manifest.json: {error}"),
    };
    let collections = collections
        .as_object()
        .expect("collections must be an object");
    let mut cases = Vec::new();
    for collection in collections.keys() {
        for entry in std::fs::read_dir(corpus.join(collection)).unwrap() {
            let path = entry.unwrap().path();
            if path.is_file() && path.extension().is_some_and(|it| it == "json") {
                cases.push(path);
            }
        }
    }
    cases.sort();
    cases
}

/// The two schemas of a case, each with the key that the file of the case has it under.
pub(crate) fn schemas_of(case: &Path) -> [(&'static str, Value); 2] {
    let text = std::fs::read_to_string(case).unwrap();
    let mut case: Value = serde_json::from_str(&text).unwrap();
    ["a", "b"].map(|key| (key, case[key].take()))
}
