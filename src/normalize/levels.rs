//! Sets of decision levels.
//!
//! The splits of a task are a stack, and the depth of a split on it is its *decision level*.
//! A fact that a branch takes in holds because of the alternatives that some of those splits
//! are at: its levels. A refutation holds because of the facts that it takes, and the levels
//! of those, with the levels that they come from in turn, are its *conflict set*.

/// A set of decision levels.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Levels {
    /// The levels below 64, a bit each.
    low: u64,
    /// The levels from 64 on, 64 to a word, with no word of zero at the end.
    high: Vec<u64>,
}

impl Levels {
    /// The set of one level.
    pub fn of(level: u32) -> Self {
        let mut levels = Self::default();
        levels.insert(level);
        levels
    }

    pub fn insert(&mut self, level: u32) {
        let (word, bit) = place(level);
        match word.checked_sub(1) {
            None => self.low |= bit,
            Some(word) => {
                if self.high.len() <= word {
                    self.high.resize(word + 1, 0);
                }
                self.high[word] |= bit;
            }
        }
    }

    pub fn remove(&mut self, level: u32) {
        let (word, bit) = place(level);
        match word.checked_sub(1) {
            None => self.low &= !bit,
            Some(word) => {
                if let Some(held) = self.high.get_mut(word) {
                    *held &= !bit;
                }
                while self.high.last() == Some(&0) {
                    self.high.pop();
                }
            }
        }
    }

    /// Adds every level of another set.
    pub fn union(&mut self, other: &Self) {
        self.low |= other.low;
        if self.high.len() < other.high.len() {
            self.high.resize(other.high.len(), 0);
        }
        for (held, more) in self.high.iter_mut().zip(&other.high) {
            *held |= more;
        }
    }

    /// The deepest level of the set.
    pub fn last(&self) -> Option<u32> {
        let (word, held) = match self.high.last() {
            Some(held) => (self.high.len(), *held),
            None if self.low != 0 => (0, self.low),
            None => return None,
        };
        let word = u32::try_from(word).expect("fewer than 2^26 words of levels");
        Some(word * 64 + 63 - held.leading_zeros())
    }

    /// Whether the set is below another: its deepest level that the two do not share is
    /// not in the other. Of two conflict sets, the one below lets a split that runs out of
    /// alternatives back up further.
    pub fn below(&self, other: &Self) -> bool {
        let words = self.high.len().max(other.high.len());
        let word = |levels: &Self, at: usize| levels.high.get(at).copied().unwrap_or(0);
        for at in (0..words).rev() {
            if word(self, at) != word(other, at) {
                return word(self, at) < word(other, at);
            }
        }
        self.low < other.low
    }
}

/// The word of a level, counting the low one as the first, and its bit in the word.
fn place(level: u32) -> (usize, u64) {
    let word = usize::try_from(level / 64).expect("a word of levels is addressable");
    (word, 1 << (level % 64))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_set_holds_what_was_put_in_and_not_what_was_taken_out() {
        let mut levels = Levels::default();
        assert_eq!(levels.last(), None);
        for level in [3, 0, 64, 200, 63] {
            levels.insert(level);
        }
        assert_eq!(levels.last(), Some(200));
        levels.remove(200);
        // A word of zero at the end is dropped, so equal sets are equal.
        let mut same = Levels::of(64);
        same.union(&Levels::of(0));
        same.union(&Levels::of(3));
        same.insert(63);
        assert_eq!(levels, same);
        assert_eq!(levels.last(), Some(64));
        // Below is what lets a split back up further: the deepest level that differs.
        assert!(Levels::of(63).below(&Levels::of(64)));
        assert!(!Levels::of(64).below(&Levels::of(63)));
        assert!(levels.below(&Levels::of(65)) && !levels.below(&levels));
        // Taken out from the deepest, each level leaves the one below it the deepest.
        for (level, below) in [(64, Some(63)), (63, Some(3)), (3, Some(0)), (0, None)] {
            levels.remove(level);
            assert_eq!(levels.last(), below);
        }
        assert_eq!(levels, Levels::default());
    }
}
