//! Hash maps and sets for keys that are ids of our own.
//!
//! The maps of the standard library hash with SipHash under a random key, so that whoever
//! chooses the keys cannot make them collide. That protection is paid for on every lookup,
//! and nobody chooses the keys of most maps of a check: they are ids that the library hands
//! out one after the other, or pairs and lists of such ids. For those keys this module has
//! maps and sets with FxHash, the hash of the tables of the Rust compiler, which is a
//! rotation, an exclusive or and a multiplication for each word of a key. It ends with the
//! finalizer of MurmurHash3, which the compiler's does not: see [`FxHasher::finish`].
//!
//! A map whose keys hold text or numbers that a schema wrote keeps the hash of the standard
//! library: FxHash does nothing against keys that are made to collide.

use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

/// A hash map for keys that are made of ids of our own.
pub(crate) type IdMap<K, V> = HashMap<K, V, BuildHasherDefault<FxHasher>>;

/// A hash set of values that are made of ids of our own.
pub(crate) type IdSet<T> = HashSet<T, BuildHasherDefault<FxHasher>>;

/// FxHash, of 64 bits.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct FxHasher {
    hash: u64,
}

/// The multiplier of FxHash: an odd number near 2^64 divided by pi.
const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let (words, rest) = bytes.as_chunks::<8>();
        for word in words {
            self.add(u64::from_le_bytes(*word));
        }
        if !rest.is_empty() {
            let mut word = [0; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }

    #[inline]
    fn write_u8(&mut self, value: u8) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u16(&mut self, value: u16) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u32(&mut self, value: u32) {
        self.add(u64::from(value));
    }

    #[inline]
    fn write_u64(&mut self, value: u64) {
        self.add(value);
    }

    #[inline]
    fn write_usize(&mut self, value: usize) {
        self.add(value as u64);
    }

    /// A multiplication mixes upwards only: the low bits of a product depend on the low bits
    /// of what was multiplied and on nothing else, and a table looks at the low bits first.
    /// So lists that end alike, and sets of ids that are kept as bits and differ in their
    /// high bits, would crowd into a few places of a table. The finalizer of MurmurHash3
    /// lets every bit of the hash bear on every other.
    #[inline]
    fn finish(&self) -> u64 {
        let mut hash = self.hash;
        hash ^= hash >> 33;
        hash = hash.wrapping_mul(0xff51_afd7_ed55_8ccd);
        hash ^= hash >> 33;
        hash = hash.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
        hash ^ (hash >> 33)
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{BuildHasher, Hash};

    use super::*;

    /// In how many of 2^12 buckets keys fall, as a table of that size sorts them.
    fn buckets<K: Hash>(keys: impl IntoIterator<Item = K>) -> usize {
        let hasher = BuildHasherDefault::<FxHasher>::default();
        let low = |key: K| hasher.hash_one(key) & 0xfff;
        keys.into_iter().map(low).collect::<HashSet<u64>>().len()
    }

    #[test]
    fn a_map_of_ids_is_a_map() {
        let mut map: IdMap<(u32, bool), u32> = IdMap::default();
        for id in 0..10_000 {
            assert_eq!(map.insert((id, id % 3 == 0), id + 1), None);
        }
        assert_eq!(map.len(), 10_000);
        assert_eq!(map.get(&(77, false)), Some(&78));
        assert_eq!(map.get(&(77, true)), None);
        let set: IdSet<u32> = (0..100).chain(50..150).collect();
        assert_eq!(set.len(), 150);
    }

    #[test]
    fn keys_of_ids_spread_over_a_table() {
        // 2^12 keys thrown at 2^12 buckets by chance fill about 2,590 of them. Each kind of
        // key that a check has is to do about as well: ids as they are handed out, pairs of
        // them, lists of them that begin and end alike, and sets of them as bits, which
        // differ in a bit or two anywhere in a word.
        let fair = 2_300;
        let pairs = || (0..64_u32).flat_map(|first| (0..64_u32).map(move |second| (first, second)));
        assert!(buckets(0..4_096_u32) > fair);
        assert!(buckets(pairs()) > fair);
        assert!(buckets((0..2_048_u32).flat_map(|id| [(id, false), (id, true)])) > fair);
        assert!(buckets((0..4_096_u32).map(|id| vec![7, id, 7])) > fair);
        assert!(buckets((0..4_096_u64).map(|id| vec![id << 48])) > fair);
        assert!(buckets(pairs().map(|(first, second)| vec![1_u64 << first, 1 << second])) > fair);
        // Without the finalizer the lists fill 32 buckets and the sets of bits one.
    }

    #[test]
    fn bytes_are_hashed_eight_at_a_time_and_what_is_left_after_them() {
        let hash = |bytes: &[u8]| {
            let mut hasher = FxHasher::default();
            hasher.write(bytes);
            hasher.finish()
        };
        // The same words by one way and by the other.
        let mut words = FxHasher::default();
        words.write_u64(u64::from_le_bytes(*b"12345678"));
        words.write_u64(u64::from_le_bytes(*b"9a\0\0\0\0\0\0"));
        assert_eq!(hash(b"123456789a"), words.finish());
        assert_ne!(hash(b"123456789a"), hash(b"123456789b"));
        assert_ne!(hash(b"12345678"), hash(b"1234567"));
    }
}
