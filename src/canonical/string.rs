//! What a branch says about strings.
//!
//! A term about strings asks one of a few things of a string: to be in a language or not to
//! be in one, to be one string or not to be it, to have at least so many characters or at
//! most so many. However many terms a branch takes in, what they leave is of one shape: the
//! strings of one language whose length is between two bounds. The language is the
//! intersection of those that were asked for and of the complements of those that were asked
//! against.
//!
//! The languages are put together when the branch asks whether a string is left, and not
//! when a term comes in. A language that is asked for and asked against leaves no string,
//! and that is seen without a DFA.

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::context::{Budget, Exhausted};
use crate::language::{LanguageId, Languages, Lengths};
use crate::term::Term;

/// The strings that a branch still accepts.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Strings {
    /// The languages that a string is in, and those that it is not in.
    within: BTreeSet<LanguageId>,
    without: BTreeSet<LanguageId>,
    /// The same languages in the order in which they were asked: each with whether it is
    /// asked against, and whether it is one string.
    asked: Vec<(LanguageId, bool, Option<Rc<str>>)>,
    /// What the first of them leave together, and how many those are. The others are put
    /// together when the branch asks whether a string is left.
    left: LanguageId,
    together: usize,
    lengths: Lengths,
    /// Whether what was asked leaves no string on the face of it.
    none: bool,
}

/// The strings of a branch as they were at some time: what [`Strings::undo`] takes them
/// back to. The languages only grow in number, so of them it is how many there were.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Mark {
    asked: usize,
    left: LanguageId,
    together: usize,
    lengths: Lengths,
    none: bool,
}

impl Default for Strings {
    fn default() -> Self {
        Self {
            within: BTreeSet::new(),
            without: BTreeSet::new(),
            asked: Vec::new(),
            left: Languages::EVERYTHING,
            together: 0,
            lengths: Lengths::ANY,
            none: false,
        }
    }
}

impl Strings {
    /// Takes in what a term about strings asks of a string, as it stands or negated.
    pub fn take(&mut self, term: &Term, negated: bool, languages: &mut Languages) {
        match (term, negated) {
            (Term::StrConst(word), _) => {
                self.ask(languages.words([word.as_ref()]), negated, Some(word));
            }
            (Term::Patt(language), _) => self.ask(*language, negated, None),
            (Term::MinLen(least), false) => self.lengths.min = self.lengths.min.max(*least),
            // Shorter than the least.
            (Term::MinLen(least), true) => match least.checked_sub(1) {
                Some(most) => self.at_most(most),
                None => self.none = true,
            },
            (Term::MaxLen(most), false) => self.at_most(*most),
            // Longer than the most. Beyond the largest count this asks for one character
            // less than it should, which lets strings in and none out: a branch may then
            // stand that should not, and none is refuted that should stand.
            (Term::MaxLen(most), true) => {
                self.lengths.min = self.lengths.min.max(most.saturating_add(1));
            }
            (other, _) => unreachable!("{other:?} is not about strings"),
        }
    }

    /// Keeps the strings of a language, or with `negated` those that are not of it.
    /// `one_string` is the string of a language that is one string.
    fn ask(&mut self, language: LanguageId, negated: bool, one_string: Option<&str>) {
        let (asked, against) = if negated {
            (&mut self.without, &self.within)
        } else {
            (&mut self.within, &self.without)
        };
        if against.contains(&language) {
            self.none = true;
        } else if asked.insert(language) {
            self.asked
                .push((language, negated, one_string.map(Rc::from)));
        }
    }

    pub fn mark(&self) -> Mark {
        Mark {
            asked: self.asked.len(),
            left: self.left,
            together: self.together,
            lengths: self.lengths,
            none: self.none,
        }
    }

    /// Undoes everything that was asked since a mark.
    pub fn undo(&mut self, mark: Mark) {
        let Mark {
            asked,
            left,
            together,
            lengths,
            none,
        } = mark;
        for (language, negated, _) in self.asked.drain(asked..) {
            let asked = if negated {
                &mut self.without
            } else {
                &mut self.within
            };
            asked.remove(&language);
        }
        (self.left, self.together) = (left, together);
        (self.lengths, self.none) = (lengths, none);
    }

    fn at_most(&mut self, most: u64) {
        self.lengths.max = Some(self.lengths.max.map_or(most, |max| max.min(most)));
    }

    /// The language that is left when everything that was asked is put together.
    fn settled(
        &self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        // What came in since the last time is put together first, and of that the single
        // strings first. Those that are asked against are taken out all at once, as one
        // set of words however many they are. Taken out one at a time, each would leave a
        // set of its own with every word before it, which is the square of their number
        // in words, and a DFA would take them in one by one.
        let mut fresh = Languages::EVERYTHING;
        let mut taken_out: Vec<&str> = Vec::new();
        let asked = &self.asked[self.together..];
        for (language, negated, one_string) in asked {
            match one_string {
                Some(word) if *negated => taken_out.push(word),
                Some(_) => fresh = languages.intersection(fresh, *language, budget)?,
                None => {}
            }
        }
        if !taken_out.is_empty() {
            // A step for each word that the set is made of.
            budget.charge(taken_out.len() as u64)?;
            let these = languages.words(taken_out);
            let others = languages.complement(these, budget)?;
            fresh = languages.intersection(fresh, others, budget)?;
        }
        let patterns = asked.iter().filter(|asked| asked.2.is_none());
        for (language, negated, _) in patterns {
            // Once no string is left, the rest is not worth a DFA.
            if fresh == Languages::NOTHING {
                return Ok(fresh);
            }
            let language = if *negated {
                languages.complement(*language, budget)?
            } else {
                *language
            };
            fresh = languages.intersection(fresh, language, budget)?;
        }
        languages.intersection(self.left, fresh, budget)
    }

    /// Whether no string is in the set.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFAs.
    pub fn is_empty(
        &mut self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        if self.none {
            return Ok(true);
        }
        self.left = self.settled(languages, budget)?;
        self.together = self.asked.len();
        languages.is_empty(self.left, self.lengths, budget)
    }

    /// The language of the strings of the set, unless its bounds on the length are more
    /// than a pattern says.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFAs.
    pub fn language(
        &self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<Option<LanguageId>, Exhausted> {
        if self.none {
            return Ok(Some(Languages::NOTHING));
        }
        let Some(of_length) = languages.of_lengths(self.lengths) else {
            return Ok(None);
        };
        let left = self.settled(languages, budget)?;
        languages.intersection(left, of_length, budget).map(Some)
    }

    /// The shortest string of the set, if it has one. Of several it is one of plain
    /// characters.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFAs or the characters of the string.
    pub fn shortest(
        &self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<Option<String>, Exhausted> {
        if self.none {
            return Ok(None);
        }
        let left = self.settled(languages, budget)?;
        languages.shortest(left, self.lengths, budget)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Terms;
    use crate::testing::Random;

    /// The set that is left when these are asked: `in ^a` and `not in ^a` for a pattern,
    /// `= a` and `!= a` for one string, `>= 2` and `<= 2` for a length, and `not >= 2` and
    /// `not <= 2` for the two negated.
    fn strings(asked: &[&str], languages: &mut Languages) -> Strings {
        let mut strings = Strings::default();
        take(&mut strings, asked, languages);
        strings
    }

    /// Takes such terms into a set.
    fn take(strings: &mut Strings, asked: &[&str], languages: &mut Languages) {
        let mut terms = Terms::default();
        for asked in asked {
            let (what, of) = asked.rsplit_once(' ').unwrap();
            let count = || of.parse().unwrap();
            let (term, negated) = match what {
                "in" => (terms.patt(languages.pattern(of).unwrap()), false),
                "not in" => (terms.patt(languages.pattern(of).unwrap()), true),
                "=" => (terms.str_const(of), false),
                "!=" => (terms.str_const(of), true),
                ">=" => (terms.min_len(count()), false),
                "not >=" => (terms.min_len(count()), true),
                "<=" => (terms.max_len(count()), false),
                "not <=" => (terms.max_len(count()), true),
                other => panic!("{other} is nothing to ask"),
            };
            strings.take(terms.term(term), negated, languages);
        }
    }

    /// The shortest string of the set.
    fn given(asked: &[&str]) -> Option<String> {
        let languages = &mut Languages::default();
        let mut strings = strings(asked, languages);
        let mut budget = Budget::new(u64::MAX);
        let is_empty = strings.is_empty(languages, &mut budget).unwrap();
        let shortest = strings.shortest(languages, &mut budget).unwrap();
        assert_eq!(shortest.is_none(), is_empty, "{asked:?}");
        shortest
    }

    fn some(word: &str) -> Option<String> {
        Some(word.to_owned())
    }

    #[test]
    fn what_is_asked_is_put_together() {
        assert_eq!(given(&[]), some(""));
        assert_eq!(given(&["in ^a", "in b$"]), some("ab"));
        assert_eq!(given(&["in ^a", "not in ^ab", ">= 2"]), some("aa"));
        assert_eq!(given(&["in ^[ab]+$", "not in ^a", "not in b$"]), some("ba"));
        assert_eq!(given(&["in ^a+$", "in ^b+$"]), None);
        assert_eq!(given(&["in ^a*$", "in ^b*$"]), some(""));
        assert_eq!(given(&["in ^a*$", "in ^b*$", ">= 1"]), None);
    }

    #[test]
    fn a_length_is_asked_for_or_against() {
        assert_eq!(given(&[">= 2"]), some("aa"));
        assert_eq!(given(&[">= 2", ">= 3", "<= 5", "<= 4"]), some("aaa"));
        assert_eq!(given(&[">= 3", "<= 2"]), None);
        assert_eq!(given(&["not <= 2"]), some("aaa"));
        assert_eq!(given(&["not >= 2", "in a"]), some("a"));
        assert_eq!(given(&["not >= 1", "in a"]), None);
        assert_eq!(given(&["not >= 1"]), some(""));
        assert_eq!(given(&["not <= 2", "not >= 3"]), None);
        assert_eq!(given(&["in ^(?:ab)*$", "not <= 2", "<= 3"]), None);
        assert_eq!(given(&["in ^(?:ab)*$", "not <= 2", "<= 4"]), some("abab"));
    }

    #[test]
    fn one_string_is_asked_for_or_taken_out() {
        assert_eq!(given(&["= ab"]), some("ab"));
        assert_eq!(given(&["= ab", "= ab"]), some("ab"));
        assert_eq!(given(&["= ab", "= ba"]), None);
        assert_eq!(given(&["= ab", "in ^a"]), some("ab"));
        assert_eq!(given(&["= ab", "not in ^a"]), None);
        assert_eq!(given(&["= ab", ">= 3"]), None);
        assert_eq!(given(&["!= a", "!= b", "in ^[ab]?$"]), some(""));
        assert_eq!(given(&["!= a", "!= b", "in ^[ab]$"]), None);
        assert_eq!(given(&["!= a", ">= 1"]), some("b"));
        assert_eq!(given(&["!= a", "!= b", ">= 1", "<= 1"]), some("c"));
    }

    #[test]
    fn what_is_asked_for_and_against_leaves_nothing_without_a_dfa() {
        // Whether the set is empty, as far as that is seen without a step. A DFA costs steps.
        let is_empty = |asked: &[&str]| {
            let languages = &mut Languages::default();
            strings(asked, languages).is_empty(languages, &mut Budget::new(0))
        };
        let pattern = ["in ^(a|b)*c{3,9}$", "not in ^(a|b)*c{3,9}$"];
        assert_eq!(is_empty(&pattern), Ok(true));
        assert_eq!(is_empty(&["not in a", ">= 2", "in a"]), Ok(true));
        assert_eq!(is_empty(&["= a", "!= a"]), Ok(true));
        // Two patterns of one language are told to be one by their DFAs.
        let same = ["in ^a+$", "not in ^aa*$"];
        assert_eq!(is_empty(&same), Err(Exhausted));
        assert_eq!(given(&same), None);
        // What one string says is seen without a DFA too.
        assert_eq!(is_empty(&["= a", "<= 1"]), Ok(false));
    }

    #[test]
    fn what_was_asked_since_a_mark_is_undone() {
        // Each kind of term more than once, so that some of them ask nothing new.
        let all = [
            "in ^a",
            "not in ^a",
            "in b$",
            "not in b$",
            "= ab",
            "!= ab",
            "!= a",
            ">= 1",
            ">= 2",
            "not >= 3",
            "<= 4",
            "<= 3",
            "not <= 1",
        ];
        let (languages, random) = (&mut Languages::default(), &mut Random(5));
        let budget = &mut Budget::new(u64::MAX);
        for _ in 0..500 {
            let mut some = || -> (Vec<&str>, bool) {
                let count = random.below(5);
                let asked = (0..count).map(|_| random.pick(&all)).collect();
                (asked, random.chance(50))
            };
            let (first, second, third) = (some(), some(), some());
            // After some of what is asked, the set is asked whether a string is left,
            // which puts the languages together.
            let mut ask = |strings: &mut Strings, (asked, is_empty): &(Vec<&str>, bool)| {
                take(strings, asked, languages);
                if *is_empty {
                    strings.is_empty(languages, budget).unwrap();
                }
            };
            let mut strings = Strings::default();
            ask(&mut strings, &first);
            let (mark, was) = (strings.mark(), strings.clone());
            ask(&mut strings, &second);
            // A mark after a mark, which is undone first.
            let (inner, then) = (strings.mark(), strings.clone());
            ask(&mut strings, &third);
            strings.undo(inner);
            assert_eq!(strings, then, "{first:?} {second:?} {third:?}");
            strings.undo(mark);
            assert_eq!(strings, was, "{first:?} {second:?} {third:?}");
        }
    }

    #[test]
    fn many_strings_are_taken_out_as_one_set() {
        let languages = &mut Languages::default();
        let mut terms = Terms::default();
        let mut strings = Strings::default();
        let count = 2_000;
        for index in 0..count {
            let word = terms.str_const(&format!("x{index:04}"));
            strings.take(terms.term(word), true, languages);
        }
        let mut budget = Budget::new(u64::MAX);
        assert_eq!(strings.is_empty(languages, &mut budget), Ok(false));
        // Each word is kept twice: by itself, and in the one set of all. Taken out one at a
        // time, the sets on the way would hold two million words.
        assert_eq!(languages.words_kept(), 2 * count);
        assert_eq!(strings.shortest(languages, &mut budget), Ok(some("")));
        // A word costs a step, and the budget ends it before the set is made.
        let mut again = Strings::default();
        for index in 0..count {
            let word = terms.str_const(&format!("y{index:04}"));
            again.take(terms.term(word), true, languages);
        }
        let mut budget = Budget::new(100);
        assert_eq!(again.is_empty(languages, &mut budget), Err(Exhausted));
        assert_eq!(languages.words_kept(), 3 * count);
    }
}
