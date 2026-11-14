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
//! and that is seen without an automaton.

use std::collections::BTreeSet;

use crate::context::{Budget, Exhausted};
use crate::language::{LanguageId, Languages, Lengths};
use crate::term::Term;

/// The strings that a branch still accepts.
#[derive(Debug, Clone)]
pub(crate) struct Strings {
    /// The languages that a string is in, and those that it is not in.
    within: BTreeSet<LanguageId>,
    without: BTreeSet<LanguageId>,
    /// What those of them leave that were put together so far, and those that were not:
    /// each with whether it is asked against, and whether it is one string.
    left: LanguageId,
    fresh: Vec<(LanguageId, bool, bool)>,
    lengths: Lengths,
    /// Whether what was asked leaves no string on the face of it.
    none: bool,
}

impl Default for Strings {
    fn default() -> Self {
        Self {
            within: BTreeSet::new(),
            without: BTreeSet::new(),
            left: Languages::EVERYTHING,
            fresh: Vec::new(),
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
                self.ask(languages.words([word.as_ref()]), negated, true);
            }
            (Term::Patt(language), _) => self.ask(*language, negated, false),
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
    /// `one_string` says that the language is one string.
    fn ask(&mut self, language: LanguageId, negated: bool, one_string: bool) {
        let (asked, against) = if negated {
            (&mut self.without, &self.within)
        } else {
            (&mut self.within, &self.without)
        };
        if against.contains(&language) {
            self.none = true;
        } else if asked.insert(language) {
            self.fresh.push((language, negated, one_string));
        }
    }

    fn at_most(&mut self, most: u64) {
        self.lengths.max = Some(self.lengths.max.map_or(most, |max| max.min(most)));
    }

    /// How much there is to copy when the branch splits.
    pub fn weight(&self) -> u64 {
        (self.within.len() + self.without.len()) as u64
    }

    /// The language that is left when everything that was asked is put together.
    fn settled(
        &self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        // What came in since the last time is put together first, and of that the single
        // strings first. They make one set of words, however many they are, so an automaton
        // takes them in at once and not one by one.
        let mut fresh = Languages::EVERYTHING;
        for one_string in [true, false] {
            let of_a_kind = self.fresh.iter().filter(|asked| asked.2 == one_string);
            for (language, negated, _) in of_a_kind {
                // Once no string is left, the rest is not worth an automaton.
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
        }
        languages.intersection(self.left, fresh, budget)
    }

    /// Whether no string is in the set.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the automata.
    pub fn is_empty(
        &mut self,
        languages: &mut Languages,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        if self.none {
            return Ok(true);
        }
        self.left = self.settled(languages, budget)?;
        self.fresh.clear();
        languages.is_empty(self.left, self.lengths, budget)
    }

    /// The shortest string of the set, if it has one. Of several it is one of plain
    /// characters.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the automata or the characters of the string.
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

    /// The set that is left when these are asked: `in ^a` and `not in ^a` for a pattern,
    /// `= a` and `!= a` for one string, `>= 2` and `<= 2` for a length, and `not >= 2` and
    /// `not <= 2` for the two negated.
    fn strings(asked: &[&str], languages: &mut Languages) -> Strings {
        let mut terms = Terms::default();
        let mut strings = Strings::default();
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
        strings
    }

    /// The shortest string of the set, and how many steps it took to see whether there is
    /// one.
    fn shortest(asked: &[&str]) -> (Option<String>, u64) {
        let languages = &mut Languages::default();
        let mut strings = strings(asked, languages);
        let mut budget = Budget::new(u64::MAX);
        let is_empty = strings.is_empty(languages, &mut budget).unwrap();
        let spent = budget.spent();
        let shortest = strings.shortest(languages, &mut budget).unwrap();
        assert_eq!(shortest.is_none(), is_empty, "{asked:?}");
        (shortest, spent)
    }

    fn given(asked: &[&str]) -> Option<String> {
        shortest(asked).0
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
    fn what_is_asked_for_and_against_leaves_nothing_without_an_automaton() {
        assert_eq!(
            shortest(&["in ^(a|b)*c{3,9}$", "not in ^(a|b)*c{3,9}$"]),
            (None, 0)
        );
        assert_eq!(shortest(&["not in a", ">= 2", "in a"]), (None, 0));
        assert_eq!(shortest(&["= a", "!= a"]), (None, 0));
        // Two patterns of one language are told to be one by their automata.
        let (found, spent) = shortest(&["in ^a+$", "not in ^aa*$"]);
        assert_eq!(found, None);
        assert!(spent > 0);
        // What only sets of words say costs nothing either.
        assert_eq!(shortest(&["= a", "!= b", "<= 1"]), (some("a"), 0));
    }
}
