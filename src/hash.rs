//! The hash of the tables of a check.
//!
//! A check keeps everything once and by a small id, so its tables are looked up far more
//! often than anything else is done: a term by what it says, a c-reference by its
//! variables, an answer by the id of what was asked. The hash of the standard library,
//! SipHash, is made to stand up to keys that are chosen against it, and takes longer over
//! an id than the lookup that it is for.
//!
//! This one multiplies. Each word of a key is put into the state, the state is multiplied
//! by a factor, and the two halves of the product are folded into one another, so that
//! every bit of the word reaches every bit of the state. The factor and the first state are
//! drawn at random once for the process: a schema cannot be written so that its strings fall
//! into one bucket of a table, since nothing in the schema says which strings those are.
//!
//! No table of a check is gone through in an order that the search or the steps depend
//! on, so a hash that differs from one process to the next changes neither.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, Hasher, RandomState};
use std::sync::OnceLock;

/// A hash map with the hash of this module.
pub(crate) type Map<K, V> = HashMap<K, V, Keyed>;

/// A hash set with the hash of this module.
pub(crate) type Set<K> = HashSet<K, Keyed>;

/// What a table hashes its keys with: the two numbers that were drawn for the process.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Keyed {
    seed: u64,
    factor: u64,
}

impl Default for Keyed {
    fn default() -> Self {
        static DRAWN: OnceLock<Keyed> = OnceLock::new();
        *DRAWN.get_or_init(|| {
            // The standard library draws the keys of its own hash from the system. What
            // that hash makes of two numbers is as random as its keys.
            let random = RandomState::new();
            Self {
                seed: random.hash_one(0_u8),
                // Odd, so that no two states have one product, and with its highest bit
                // set, so that the product of a small number reaches the upper half.
                factor: random.hash_one(1_u8) | 1 | 1 << 63,
            }
        })
    }
}

impl BuildHasher for Keyed {
    type Hasher = Folded;

    fn build_hasher(&self) -> Folded {
        Folded {
            state: self.seed,
            factor: self.factor,
        }
    }
}

/// The state of a hash: every word of the key so far, folded into 64 bits.
#[derive(Debug)]
pub(crate) struct Folded {
    state: u64,
    factor: u64,
}

impl Folded {
    /// Takes in one word of a key.
    #[inline]
    fn mix(&mut self, word: u64) {
        let product = u128::from(self.state ^ word) * u128::from(self.factor);
        // The lower half of the product has the lower bits of the word well mixed, the
        // upper half the higher ones. A table takes bits from both ends of a hash.
        self.state = (product as u64) ^ ((product >> 64) as u64);
    }
}

impl Hasher for Folded {
    #[inline]
    fn finish(&self) -> u64 {
        self.state
    }

    /// Takes in bytes, eight at a time, and how many they were: without the count, a few
    /// bytes would hash like the same bytes with zeros after them.
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for word in words {
            self.mix(u64::from_le_bytes(*word));
        }
        if !rest.is_empty() {
            let mut last = [0; 8];
            last[..rest.len()].copy_from_slice(rest);
            self.mix(u64::from_le_bytes(last));
        }
        self.mix(bytes.len() as u64);
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.mix(u64::from(value));
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.mix(u64::from(value));
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.mix(u64::from(value));
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.mix(value);
    }

    #[inline]
    fn write_u128(&mut self, value: u128) {
        self.mix(value as u64);
        self.mix((value >> 64) as u64);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.mix(value as u64);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(key: impl std::hash::Hash) -> u64 {
        Keyed::default().hash_one(key)
    }

    #[test]
    fn equal_keys_have_one_hash_and_every_table_of_a_process_the_same() {
        assert_eq!(hash((7_u32, true)), hash((7_u32, true)));
        assert_eq!(hash("a word"), hash(String::from("a word")));
        let (one, other) = (Keyed::default(), Keyed::default());
        assert_eq!(one.hash_one(7_u32), other.hash_one(7_u32));
    }

    #[test]
    fn ids_in_a_row_fall_apart_at_both_ends_of_the_hash() {
        // A table takes its bucket from the low bits of a hash and tells the keys of a
        // bucket apart by the high ones. The ids of a check are small numbers in a row.
        let count = 1_u32 << 16;
        let mut low: Set<u64> = Set::default();
        let mut high: Set<u64> = Set::default();
        let mut whole: Set<u64> = Set::default();
        for id in 0..count {
            let hash = hash(id);
            low.insert(hash & 0xffff);
            high.insert(hash >> 48);
            whole.insert(hash);
        }
        assert_eq!(whole.len(), count as usize);
        // Numbers drawn at random fill about 63% of as many buckets as there are numbers.
        assert!(low.len() > 36_000, "{} low ends", low.len());
        assert!(high.len() > 36_000, "{} high ends", high.len());
    }

    #[test]
    fn what_differs_in_one_place_has_another_hash() {
        let pairs: Set<u64> = (0..256_u32)
            .flat_map(|first| (0..256_u32).map(move |second| hash((first, second))))
            .collect();
        assert_eq!(pairs.len(), 256 * 256);
        // Bytes are told from the same bytes with zeros after them, also where a string
        // ends within a word and where it ends with one.
        let words = [
            "",
            "\0",
            "\0\0",
            "ab",
            "ab\0",
            "abcdefgh",
            "abcdefgh\0",
            "abcdefg",
        ];
        let hashes: Set<u64> = words.iter().map(hash).collect();
        assert_eq!(hashes.len(), words.len());
        let lists: [&[u32]; 4] = [&[], &[0], &[0, 0], &[1]];
        let hashes: Set<u64> = lists.iter().map(hash).collect();
        assert_eq!(hashes.len(), lists.len());
    }
}
