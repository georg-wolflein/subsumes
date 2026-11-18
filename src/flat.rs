//! A flat map and a flat set: sorted vectors that are read like the B-trees of the standard
//! library.
//!
//! A branch is copied for every alternative of a split, and most of the copies are dropped
//! at once. A B-tree is a node for every few entries, and each node is allocated when the
//! tree is copied and freed when it is dropped. A sorted vector is one allocation however
//! many entries it has. What it gives up is the insertion: an entry is put in its place by
//! moving every entry after it. An insertion charges the budget for the entries that it
//! moves, so one at the end, which is the usual one, costs nothing.
//!
//! The entries are in the order of their keys, as those of a B-tree are, so whatever goes
//! through them goes through them in the same order.

use std::ops::RangeInclusive;

use crate::context::{Budget, Exhausted};

/// How many entries an insertion moves for a step.
const MOVED: usize = 64;

/// A map whose entries are a vector in the order of their keys.
#[derive(Debug, Clone)]
pub(crate) struct FlatMap<K, V> {
    entries: Vec<(K, V)>,
}

impl<K: Ord, V> FlatMap<K, V> {
    pub const fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let at = self.at(key).ok()?;
        Some(&self.entries[at].1)
    }

    /// Puts a value at a key, and gives back the value that was there.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the entries after a new key, which are moved.
    pub fn insert(
        &mut self,
        key: K,
        value: V,
        budget: &mut Budget,
    ) -> Result<Option<V>, Exhausted> {
        match self.at(&key) {
            Ok(at) => Ok(Some(std::mem::replace(&mut self.entries[at].1, value))),
            Err(at) => {
                budget.charge(((self.entries.len() - at) / MOVED) as u64)?;
                self.entries.insert(at, (key, value));
                Ok(None)
            }
        }
    }

    /// Where a key is, or where it would be put.
    fn at(&self, key: &K) -> Result<usize, usize> {
        self.entries.binary_search_by(|(other, _)| other.cmp(key))
    }
}

/// A set whose values are a vector in their order.
#[derive(Debug, Clone)]
pub(crate) struct FlatSet<T> {
    values: Vec<T>,
}

impl<T> Default for FlatSet<T> {
    fn default() -> Self {
        Self { values: Vec::new() }
    }
}

impl<T: Ord> FlatSet<T> {
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Adds a value, and says whether it was new.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the values after a new one, which are moved.
    pub fn insert(&mut self, value: T, budget: &mut Budget) -> Result<bool, Exhausted> {
        match self.values.binary_search(&value) {
            Ok(_) => Ok(false),
            Err(at) => {
                budget.charge(((self.values.len() - at) / MOVED) as u64)?;
                self.values.insert(at, value);
                Ok(true)
            }
        }
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.values.iter()
    }

    /// The values from one to another, both included, in order.
    pub fn range(&self, range: RangeInclusive<T>) -> std::slice::Iter<'_, T> {
        let from = self.values.partition_point(|value| value < range.start());
        let to = self.values.partition_point(|value| value <= range.end());
        // A range that ends before it begins holds nothing.
        self.values[from..to.max(from)].iter()
    }
}

impl<'a, T> IntoIterator for &'a FlatSet<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    /// Numbers that look random and are the same on every run.
    fn numbers(seed: u64) -> impl Iterator<Item = u64> {
        let mut state = seed;
        std::iter::repeat_with(move || {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            state >> 33
        })
    }

    #[test]
    fn a_flat_map_says_what_a_b_tree_says() {
        let budget = &mut Budget::new(u64::MAX);
        let (mut flat, mut tree) = (FlatMap::new(), BTreeMap::new());
        assert_eq!(flat.len(), 0);
        assert_eq!(flat.get(&1), None);
        // Few keys, so that many of them are put a second time.
        let mut values = numbers(7);
        for key in numbers(1).take(2_000).map(|number| number % 300) {
            let value = values.next().unwrap();
            assert_eq!(flat.insert(key, value, budget), Ok(tree.insert(key, value)));
            assert_eq!(flat.len(), tree.len());
        }
        for key in 0..310 {
            assert_eq!(flat.get(&key), tree.get(&key));
        }
        // And the entries are in the order of the keys.
        let entries: Vec<(u64, u64)> = tree.into_iter().collect();
        assert_eq!(flat.entries, entries);
    }

    #[test]
    fn a_flat_set_says_what_a_b_tree_says() {
        let budget = &mut Budget::new(u64::MAX);
        let (mut flat, mut tree) = (FlatSet::default(), BTreeSet::new());
        assert_eq!(flat.len(), 0);
        for number in numbers(3).take(2_000) {
            // Pairs, as the sets of a branch hold them, with few first parts.
            let value = (number % 40, number / 40 % 25);
            assert_eq!(flat.insert(value, budget), Ok(tree.insert(value)));
            assert_eq!(flat.len(), tree.len());
        }
        assert!(flat.iter().eq(tree.iter()));
        assert!((&flat).into_iter().eq(&tree));
        // Every value with one first part, as a branch asks for them, and other ranges.
        for first in 0..42 {
            let range = (first, 0)..=(first, u64::MAX);
            assert!(flat.range(range.clone()).eq(tree.range(range)));
            let range = (first, 3)..=(first + 2, 7);
            assert!(flat.range(range.clone()).eq(tree.range(range)));
        }
        // A range of one value, and one that ends before it begins.
        assert_eq!(
            flat.range((5, 5)..=(5, 5)).count(),
            usize::from(tree.contains(&(5, 5)))
        );
        assert_eq!(flat.range((9, 0)..=(3, 0)).count(), 0);
    }

    #[test]
    fn an_insertion_costs_steps_for_the_entries_that_it_moves() {
        // At the end nothing is moved, so no budget is needed however many there are.
        let nothing = &mut Budget::new(0);
        let (mut map, mut set) = (FlatMap::new(), FlatSet::default());
        for number in 0..10_000 {
            assert_eq!(map.insert(number, (), nothing), Ok(None));
            assert_eq!(set.insert(number, nothing), Ok(true));
        }
        // What is there already is put again for nothing as well.
        assert_eq!(map.insert(5, (), nothing), Ok(Some(())));
        assert_eq!(set.insert(5, nothing), Ok(false));
        // At the front everything is moved. That is more and more work the more there is,
        // and a small budget ends it long before 2,000 entries are in.
        let small = &mut Budget::new(2_000);
        let mut map = FlatMap::new();
        let all = (0..2_000)
            .rev()
            .try_for_each(|number| map.insert(number, (), small).map(drop));
        assert_eq!(all, Err(Exhausted));
        assert!(map.len() < 1_000);
        let small = &mut Budget::new(2_000);
        let mut set = FlatSet::default();
        let all = (0..2_000)
            .rev()
            .try_for_each(|number| set.insert(number, small).map(drop));
        assert_eq!(all, Err(Exhausted));
        assert!(set.len() < 1_000);
    }
}
