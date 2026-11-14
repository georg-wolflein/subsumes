//! Regular languages of strings.
//!
//! A check keeps its languages in one store and names them by id. A language comes into the
//! store as a pattern or as a set of words, and out of it come intersections and complements,
//! whether one language includes another, whether a language has a word of some length, and
//! the shortest such word.
//!
//! Nothing here knows of schemas or of the engine. A format is a pattern to this module.
//!
//! A language is kept in one of two ways:
//!
//! - As a set of words: these words and no other, or every string but these words.
//! - As an automaton, for anything else.
//!
//! A pattern is only parsed when it comes in. Its automaton is built when something is asked
//! that needs it, so a pattern that cancels against itself costs nothing.

mod automaton;
mod pattern;

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use regex_syntax::hir::Hir;

use self::automaton::{Automaton, CHARACTERS, LAST, character, plainness};
use crate::context::{Budget, Exhausted};

/// The id of a language in the store of a check.
///
/// Two equal ids are one language. Two ids that differ may be one language too: a pattern
/// and a set of words can say the same.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct LanguageId(u32);

#[cfg(test)]
impl LanguageId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// The lengths that a string may have, in characters: at least `min`, and at most `max` if
/// there is a most.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Lengths {
    pub min: u64,
    pub max: Option<u64>,
}

impl Lengths {
    pub const ANY: Self = Self { min: 0, max: None };

    fn hold(self, length: u128) -> bool {
        length >= self.min.into() && self.max.is_none_or(|max| length <= max.into())
    }
}

/// A pattern that is not read as a language: one that the `regex` crate does not take, or
/// one that asks where a word or a line begins or ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Unsupported;

type Words = Rc<BTreeSet<Box<str>>>;

#[derive(Debug)]
enum Language {
    /// These words and no other, or with `others` every string but these words.
    Words {
        words: Words,
        others: bool,
    },
    /// A pattern whose automaton nothing has asked for yet.
    Pattern(Box<Hir>),
    /// The pattern of a format, which is not even parsed until something asks for its
    /// automaton.
    Format(&'static str),
    Automaton(Rc<Automaton>),
}

/// The languages of a check.
#[derive(Debug)]
pub(crate) struct Languages {
    languages: Vec<Language>,
    /// What each language came in as, if it came in as a pattern or a format.
    sources: HashMap<LanguageId, String>,
    patterns: HashMap<Box<str>, Result<LanguageId, Unsupported>>,
    formats: HashMap<Box<str>, LanguageId>,
    of_words: HashMap<(Words, bool), LanguageId>,
    of_automata: HashMap<Rc<Automaton>, LanguageId>,
    /// The automaton of a set of words, once something has asked for it.
    as_automata: HashMap<LanguageId, Rc<Automaton>>,
    intersections: HashMap<(LanguageId, LanguageId), LanguageId>,
    complements: HashMap<LanguageId, LanguageId>,
}

impl Default for Languages {
    fn default() -> Self {
        let mut languages = Self {
            languages: Vec::new(),
            sources: HashMap::new(),
            patterns: HashMap::new(),
            formats: HashMap::new(),
            of_words: HashMap::new(),
            of_automata: HashMap::new(),
            as_automata: HashMap::new(),
            intersections: HashMap::new(),
            complements: HashMap::new(),
        };
        let none: [&str; 0] = [];
        assert_eq!(languages.words(none), Self::NOTHING);
        assert_eq!(languages.set(Rc::default(), true), Self::EVERYTHING);
        languages
    }
}

impl Languages {
    /// The language without a word.
    pub const NOTHING: LanguageId = LanguageId(0);
    /// The language of every string.
    pub const EVERYTHING: LanguageId = LanguageId(1);

    fn add(&mut self, language: Language) -> LanguageId {
        let id =
            u32::try_from(self.languages.len()).expect("a check has fewer than 2^32 languages");
        self.languages.push(language);
        LanguageId(id)
    }

    /// The language of every string that holds a match of the pattern, as the `regex` crate
    /// reads the pattern.
    ///
    /// # Errors
    ///
    /// When the pattern is not read as a language; see [`Unsupported`].
    pub fn pattern(&mut self, pattern: &str) -> Result<LanguageId, Unsupported> {
        if let Some(known) = self.patterns.get(pattern) {
            return *known;
        }
        let read = pattern::read(pattern).map(|read| {
            let id = self.add(Language::Pattern(Box::new(read)));
            self.sources.insert(id, format!("{pattern:?}"));
            id
        });
        self.patterns.insert(pattern.into(), read);
        read
    }

    /// The language of a format, which is that of its pattern. The pattern is one that is
    /// read as a language.
    pub fn format(&mut self, name: &str, pattern: &'static str) -> LanguageId {
        if let Some(known) = self.formats.get(name) {
            return *known;
        }
        let id = self.add(Language::Format(pattern));
        self.sources.insert(id, format!("format {name}"));
        self.formats.insert(name.into(), id);
        id
    }

    /// The language of these words and no other.
    pub fn words<'w>(&mut self, words: impl IntoIterator<Item = &'w str>) -> LanguageId {
        let words: BTreeSet<Box<str>> = words.into_iter().map(Box::from).collect();
        self.set(Rc::new(words), false)
    }

    fn set(&mut self, words: Words, others: bool) -> LanguageId {
        if let Some(known) = self.of_words.get(&(Rc::clone(&words), others)) {
            return *known;
        }
        let id = self.add(Language::Words {
            words: Rc::clone(&words),
            others,
        });
        self.of_words.insert((words, others), id);
        id
    }

    /// The id of an automaton that came out of others.
    fn keep(&mut self, automaton: Automaton) -> LanguageId {
        if automaton.is_empty() {
            return Self::NOTHING;
        }
        if automaton.is_everything() {
            return Self::EVERYTHING;
        }
        let automaton = Rc::new(automaton);
        if let Some(known) = self.of_automata.get(&automaton) {
            return *known;
        }
        let id = self.add(Language::Automaton(Rc::clone(&automaton)));
        self.of_automata.insert(automaton, id);
        id
    }

    /// The automaton of a language, which is built if it was not before.
    fn automaton(
        &mut self,
        id: LanguageId,
        budget: &mut Budget,
    ) -> Result<Rc<Automaton>, Exhausted> {
        let built = match &self.languages[id.0 as usize] {
            Language::Automaton(automaton) => return Ok(Rc::clone(automaton)),
            Language::Pattern(pattern) => pattern::automaton(pattern, budget)?,
            Language::Format(pattern) => {
                let read = pattern::read(pattern).expect("the pattern of a format is supported");
                pattern::automaton(&read, budget)?
            }
            Language::Words { words, others } => {
                if let Some(known) = self.as_automata.get(&id) {
                    return Ok(Rc::clone(known));
                }
                let listed = Automaton::of_words(words.iter().map(AsRef::as_ref), budget)?;
                let built = Rc::new(if *others { listed.complement() } else { listed });
                self.as_automata.insert(id, Rc::clone(&built));
                return Ok(built);
            }
        };
        // Two patterns of one language share the automaton.
        let built = Rc::new(built);
        let shared = match self.of_automata.entry(Rc::clone(&built)) {
            Entry::Occupied(known) => Rc::clone(known.key()),
            Entry::Vacant(new) => {
                new.insert(id);
                built
            }
        };
        self.languages[id.0 as usize] = Language::Automaton(Rc::clone(&shared));
        Ok(shared)
    }

    /// The language of every string that is not in this one.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the automaton of a pattern.
    pub fn complement(
        &mut self,
        id: LanguageId,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        if let Some(known) = self.complements.get(&id) {
            return Ok(*known);
        }
        let complement = match &self.languages[id.0 as usize] {
            Language::Words { words, others } => self.set(Rc::clone(words), !others),
            _ => {
                let complement = self.automaton(id, budget)?.complement();
                self.keep(complement)
            }
        };
        self.complements.insert(id, complement);
        self.complements.insert(complement, id);
        Ok(complement)
    }

    /// The language of the strings that are in both.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the automata.
    pub fn intersection(
        &mut self,
        a: LanguageId,
        b: LanguageId,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        let (a, b) = (a.min(b), a.max(b));
        if a == b || b == Self::EVERYTHING {
            return Ok(a);
        }
        if a == Self::NOTHING {
            return Ok(a);
        }
        if a == Self::EVERYTHING {
            return Ok(b);
        }
        if let Some(known) = self.intersections.get(&(a, b)) {
            return Ok(*known);
        }
        let both = match (&self.languages[a.0 as usize], &self.languages[b.0 as usize]) {
            (
                Language::Words { words, others },
                Language::Words {
                    words: more,
                    others: more_others,
                },
            ) => {
                let both: BTreeSet<Box<str>> = match (others, more_others) {
                    (false, false) => words.intersection(more).cloned().collect(),
                    (false, true) => words.difference(more).cloned().collect(),
                    (true, false) => more.difference(words).cloned().collect(),
                    (true, true) => words.union(more).cloned().collect(),
                };
                self.set(Rc::new(both), *others && *more_others)
            }
            // Of a few words, those that the other language holds.
            (
                Language::Words {
                    words,
                    others: false,
                },
                _,
            ) => {
                let words = Rc::clone(words);
                self.held(&words, b, budget)?
            }
            (
                _,
                Language::Words {
                    words,
                    others: false,
                },
            ) => {
                let words = Rc::clone(words);
                self.held(&words, a, budget)?
            }
            _ => {
                let (of_a, of_b) = (self.automaton(a, budget)?, self.automaton(b, budget)?);
                let both = of_a.intersection(&of_b, budget)?;
                self.keep(both)
            }
        };
        self.intersections.insert((a, b), both);
        Ok(both)
    }

    /// The language of those of the words that another language holds.
    fn held(
        &mut self,
        words: &Words,
        by: LanguageId,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        let automaton = self.automaton(by, budget)?;
        let mut held = BTreeSet::new();
        for word in words.iter() {
            budget.charge(1 + word.len() as u64 / 32)?;
            if automaton.accepts(word) {
                held.insert(word.clone());
            }
        }
        Ok(self.set(Rc::new(held), false))
    }

    /// Whether every string of `narrow` is in `wide`.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the automata.
    // The engine compares languages by their intersections so far. Objects will ask this.
    #[cfg_attr(not(test), expect(dead_code))]
    pub fn includes(
        &mut self,
        wide: LanguageId,
        narrow: LanguageId,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        let outside = self.complement(wide, budget)?;
        let left = self.intersection(narrow, outside, budget)?;
        self.is_empty(left, Lengths::ANY, budget)
    }

    /// Whether the language has no word whose length is within the bounds.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search.
    pub fn is_empty(
        &mut self,
        id: LanguageId,
        lengths: Lengths,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        match &self.languages[id.0 as usize] {
            Language::Words { words, others } => {
                Ok(length_of_a_word(words, *others, lengths).is_none())
            }
            _ => Ok(!self.automaton(id, budget)?.has_word(lengths, budget)?),
        }
    }

    /// The shortest word of the language whose length is within the bounds, if it has one.
    /// Of several it is one of plain characters.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search or the characters of the word.
    pub fn shortest(
        &mut self,
        id: LanguageId,
        lengths: Lengths,
        budget: &mut Budget,
    ) -> Result<Option<String>, Exhausted> {
        let Language::Words { words, others } = &self.languages[id.0 as usize] else {
            return self.automaton(id, budget)?.shortest(lengths, budget);
        };
        let Some(length) = length_of_a_word(words, *others, lengths) else {
            return Ok(None);
        };
        if !others {
            // Of the words of this length, the one of the plainest characters.
            let of_length = words.iter().map(AsRef::as_ref);
            let of_length = of_length.filter(|word: &&str| word.chars().count() as u128 == length);
            let shortest = of_length.min_by_key(|word| {
                let plainness: Vec<u32> = word.chars().map(plainness).collect();
                plainness
            });
            return Ok(shortest.map(str::to_owned));
        }
        // A step for each character, before any is written.
        budget.charge(u64::try_from(length).unwrap_or(u64::MAX))?;
        let length = usize::try_from(length).map_err(|_| Exhausted)?;
        // The words of this length in a fixed order, until one is not among those left out.
        // There are more words of the length than are left out, so one is found.
        let mut places: Vec<u32> = Vec::new();
        // A word that memory does not hold is one that the budget does not cover.
        places.try_reserve_exact(length).map_err(|_| Exhausted)?;
        places.resize(length, 0);
        loop {
            let word: String = places.iter().map(|place| by_plainness(*place)).collect();
            if !words.contains(word.as_str()) {
                return Ok(Some(word));
            }
            budget.charge(1)?;
            // The next word: the last character that can still change does.
            let mut at = length;
            loop {
                at -= 1;
                if places[at] < LAST {
                    places[at] += 1;
                    break;
                }
                places[at] = 0;
            }
        }
    }

    /// A language as text, for tests and for the viewer.
    pub fn show(&self, id: LanguageId) -> String {
        if let Some(source) = self.sources.get(&id) {
            return source.clone();
        }
        match &self.languages[id.0 as usize] {
            Language::Words { words, others } => {
                let listed: Vec<String> = words.iter().map(|word| format!("{word:?}")).collect();
                let listed = listed.join(", ");
                match (others, words.is_empty()) {
                    (true, true) => "any string".to_owned(),
                    (true, false) => format!("any string but {listed}"),
                    (false, _) => format!("one of [{listed}]"),
                }
            }
            _ => format!("language {}", id.0),
        }
    }
}

/// The least length within the bounds of which a set of words has a word, if there is one.
fn length_of_a_word(words: &BTreeSet<Box<str>>, others: bool, lengths: Lengths) -> Option<u128> {
    let counts = words.iter().map(|word| word.chars().count() as u128);
    if !others {
        return counts.filter(|length| lengths.hold(*length)).min();
    }
    // Every string but these: a length has a word unless every word of that length is left
    // out. There are as many words of a length as that many characters can be chosen.
    let mut left_out: HashMap<u128, u128> = HashMap::new();
    for length in counts {
        *left_out.entry(length).or_default() += 1;
    }
    let mut length = u128::from(lengths.min);
    loop {
        if !lengths.hold(length) {
            return None;
        }
        let all = u32::try_from(length).map_or(u128::MAX, |length| {
            CHARACTERS.checked_pow(length).unwrap_or(u128::MAX)
        });
        if left_out.get(&length).is_none_or(|left_out| *left_out < all) {
            return Some(length);
        }
        length += 1;
    }
}

/// The characters in the order in which a word that is made up takes them: the letters and
/// digits of ASCII, then every other character.
fn by_plainness(place: u32) -> char {
    const FIRST: &[u8; 62] = b"abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    if let Some(first) = FIRST.get(place as usize) {
        return char::from(*first);
    }
    // The others in their own order, with the letters and digits passed over.
    let mut at = place - 62;
    for skipped in [b'0'..=b'9', b'A'..=b'Z', b'a'..=b'z'] {
        if at >= u32::from(*skipped.start()) {
            at += u32::from(skipped.end() - skipped.start()) + 1;
        }
    }
    character(at)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::Random;

    fn unlimited() -> Budget {
        Budget::new(u64::MAX)
    }

    fn between(min: u64, max: u64) -> Lengths {
        Lengths {
            min,
            max: Some(max),
        }
    }

    fn from(min: u64) -> Lengths {
        Lengths { min, max: None }
    }

    /// A store with a way to ask it things without a budget.
    struct Store(Languages);

    impl Store {
        fn new() -> Self {
            Self(Languages::default())
        }

        fn pattern(&mut self, pattern: &str) -> LanguageId {
            let read = self.0.pattern(pattern);
            read.unwrap_or_else(|_| panic!("{pattern:?} is not supported"))
        }

        fn not(&mut self, id: LanguageId) -> LanguageId {
            self.0.complement(id, &mut unlimited()).unwrap()
        }

        fn both(&mut self, a: LanguageId, b: LanguageId) -> LanguageId {
            self.0.intersection(a, b, &mut unlimited()).unwrap()
        }

        fn includes(&mut self, wide: LanguageId, narrow: LanguageId) -> bool {
            self.0.includes(wide, narrow, &mut unlimited()).unwrap()
        }

        fn is_empty(&mut self, id: LanguageId, lengths: Lengths) -> bool {
            self.0.is_empty(id, lengths, &mut unlimited()).unwrap()
        }

        fn shortest(&mut self, id: LanguageId, lengths: Lengths) -> Option<String> {
            self.0.shortest(id, lengths, &mut unlimited()).unwrap()
        }

        fn holds(&mut self, id: LanguageId, word: &str) -> bool {
            let word = self.0.words([word]);
            let held = self.both(id, word);
            assert!(held == word || held == Languages::NOTHING);
            held == word
        }
    }

    fn some(word: &str) -> Option<String> {
        Some(word.to_owned())
    }

    #[test]
    fn a_language_that_comes_in_twice_is_one() {
        let mut store = Store::new();
        assert_eq!(store.pattern("^a"), store.pattern("^a"));
        assert_ne!(store.pattern("^a"), store.pattern("^(?:a)"));
        assert_eq!(store.0.words(["a", "b"]), store.0.words(["b", "a", "a"]));
        assert_ne!(store.0.words(["a"]), store.0.words(["b"]));
        let none: [&str; 0] = [];
        assert_eq!(store.0.words(none), Languages::NOTHING);
        // What is not read as a language is refused each time.
        assert_eq!(store.0.pattern(r"a\b"), Err(Unsupported));
        assert_eq!(store.0.pattern(r"a\b"), Err(Unsupported));
        assert_eq!(store.0.pattern("a(?=b)"), Err(Unsupported));
    }

    #[test]
    fn sets_of_words_are_combined_as_sets() {
        let mut store = Store::new();
        let (ab, bc) = (store.0.words(["a", "b"]), store.0.words(["b", "c"]));
        let b = store.0.words(["b"]);
        assert_eq!(store.both(ab, bc), b);
        let not_bc = store.not(bc);
        assert_eq!(store.0.show(not_bc), r#"any string but "b", "c""#);
        assert_eq!(store.both(ab, not_bc), store.0.words(["a"]));
        assert_eq!(store.both(not_bc, ab), store.0.words(["a"]));
        let not_ab = store.not(ab);
        let neither = store.both(not_ab, not_bc);
        assert_eq!(store.0.show(neither), r#"any string but "a", "b", "c""#);
        assert_eq!(store.not(not_ab), ab);
        assert_eq!(store.both(ab, not_ab), Languages::NOTHING);
        assert_eq!(store.both(ab, Languages::EVERYTHING), ab);
        assert_eq!(store.both(Languages::NOTHING, not_ab), Languages::NOTHING);
        assert_eq!(store.not(Languages::NOTHING), Languages::EVERYTHING);
        assert_eq!(store.0.show(Languages::EVERYTHING), "any string");
        assert_eq!(store.0.show(ab), r#"one of ["a", "b"]"#);
    }

    #[test]
    fn words_and_patterns_are_combined() {
        let mut store = Store::new();
        let (words, starts_with_a) = (store.0.words(["a", "ab", "ba"]), store.pattern("^a"));
        assert_eq!(store.both(words, starts_with_a), store.0.words(["a", "ab"]));
        let other = store.not(starts_with_a);
        assert_eq!(store.both(other, words), store.0.words(["ba"]));
        // Every string but a few that begins with the letter.
        let not_words = store.not(words);
        let rest = store.both(not_words, starts_with_a);
        for (word, held) in [
            ("a", false),
            ("ab", false),
            ("ac", true),
            ("abc", true),
            ("b", false),
        ] {
            assert_eq!(store.holds(rest, word), held, "{word:?}");
        }
        assert_eq!(store.shortest(rest, Lengths::ANY), some("aa"));
        // What comes out is the pattern itself where nothing was taken from it.
        let b = store.0.words(["b"]);
        let not_b = store.not(b);
        let same = store.both(starts_with_a, not_b);
        assert!(store.includes(same, starts_with_a) && store.includes(starts_with_a, same));
        assert_eq!(store.0.show(starts_with_a), r#""^a""#);
    }

    #[test]
    fn one_language_includes_another() {
        let mut store = Store::new();
        let (letters, lower) = (store.pattern("^[a-zA-Z]+$"), store.pattern("^[a-z]+$"));
        assert!(store.includes(letters, lower));
        assert!(!store.includes(lower, letters));
        assert!(store.includes(letters, letters));
        // To the `regex` crate a digit is any digit of Unicode.
        let (digits, ascii) = (store.pattern(r"^\d+$"), store.pattern("^[0-9]+$"));
        assert!(store.includes(digits, ascii));
        assert!(!store.includes(ascii, digits));
        let outside = store.not(ascii);
        let told_apart = store.both(digits, outside);
        assert_eq!(store.shortest(told_apart, Lengths::ANY), some("٠"));
        let words = store.0.words(["ab", "c"]);
        assert!(store.includes(lower, words));
        assert!(!store.includes(words, lower));
        assert!(store.includes(Languages::EVERYTHING, letters));
        assert!(store.includes(letters, Languages::NOTHING));
        // A search and the pattern that spells the search out.
        let (search, spelled) = (store.pattern("b"), store.pattern("(?s)^.*b.*$"));
        assert!(store.includes(search, spelled) && store.includes(spelled, search));
    }

    #[test]
    fn a_word_is_looked_for_within_the_lengths() {
        let mut store = Store::new();
        let lower = store.pattern("^[a-z]{2,4}$");
        assert_eq!(store.shortest(lower, Lengths::ANY), some("aa"));
        assert_eq!(store.shortest(lower, from(3)), some("aaa"));
        assert_eq!(store.shortest(lower, between(0, 1)), None);
        assert!(store.is_empty(lower, from(5)));
        assert!(!store.is_empty(lower, between(4, 9)));
        // Every other length, with a bound that is far out.
        let even = store.pattern("^(?:ab)*$");
        assert_eq!(store.shortest(even, from(5)), some("ababab"));
        assert!(store.is_empty(even, between(5, 5)));
        assert!(!store.is_empty(even, from(1_000_000_000_001)));
        assert!(store.is_empty(even, between(1_000_000_000_001, 1_000_000_000_001)));
        // A few words.
        let words = store.0.words(["abc", "é", "zz", "ab"]);
        assert_eq!(store.shortest(words, Lengths::ANY), some("é"));
        assert_eq!(store.shortest(words, from(2)), some("ab"));
        assert_eq!(store.shortest(words, between(3, 3)), some("abc"));
        assert!(store.is_empty(words, from(4)));
        assert!(store.is_empty(Languages::NOTHING, Lengths::ANY));
    }

    #[test]
    fn every_string_but_a_few_has_a_word_of_almost_every_length() {
        let mut store = Store::new();
        assert_eq!(
            store.shortest(Languages::EVERYTHING, Lengths::ANY),
            some("")
        );
        assert_eq!(store.shortest(Languages::EVERYTHING, from(3)), some("aaa"));
        let few = store.0.words(["", "a", "b", "aa"]);
        let others = store.not(few);
        assert_eq!(store.shortest(others, Lengths::ANY), some("c"));
        assert_eq!(store.shortest(others, from(2)), some("ab"));
        assert_eq!(store.shortest(others, between(0, 0)), None);
        assert!(store.is_empty(others, between(0, 0)));
        assert!(!store.is_empty(others, between(0, 1)));
        assert!(store.is_empty(others, between(3, 2)));
        assert!(!store.is_empty(others, from(u64::MAX)));
        // The word costs a step for each character.
        let mut budget = Budget::new(10);
        assert_eq!(
            store.0.shortest(others, from(100), &mut budget),
            Err(Exhausted)
        );
    }

    #[test]
    fn the_characters_come_by_plainness_and_each_comes_once() {
        let first: String = (0..64).map(by_plainness).collect();
        assert_eq!(
            first,
            "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ\0\u{1}"
        );
        assert_eq!(by_plainness(62 + 47), '/');
        assert_eq!(by_plainness(62 + 48), ':');
        assert_eq!(by_plainness(62 + 48 + 6), '@');
        assert_eq!(by_plainness(62 + 48 + 7), '[');
        assert_eq!(by_plainness(62 + 48 + 7 + 5), '`');
        assert_eq!(by_plainness(62 + 48 + 7 + 6), '{');
        assert_eq!(by_plainness(LAST), '\u{10ffff}');
    }

    /// A pattern made at random, over three letters and a few other characters.
    fn pattern(random: &mut Random, depth: usize) -> String {
        let atoms = [
            "a", "b", "c", "[ab]", "[^a]", ".", r"\d", r"\w", "é", "(?:)", "[a-c]", r"\s",
        ];
        if depth == 0 || random.chance(30) {
            return random.pick(&atoms).to_owned();
        }
        let below = |random: &mut Random| pattern(random, depth - 1);
        match random.below(9) {
            0 | 1 => format!("{}{}", below(random), below(random)),
            2 => format!("(?:{}|{})", below(random), below(random)),
            3 => format!("(?:{})*", below(random)),
            4 => format!("(?:{})+", below(random)),
            5 => format!("(?:{})?", below(random)),
            6 => format!(
                "(?:{}){{{},{}}}",
                below(random),
                random.below(2),
                1 + random.below(3)
            ),
            7 => format!("^{}", below(random)),
            _ => format!("{}$", below(random)),
        }
    }

    /// Every string of up to four of these characters.
    fn strings() -> Vec<String> {
        let characters = ['a', 'b', 'c', '7', 'é', '\n'];
        let mut strings = vec![String::new()];
        let mut from = 0;
        for _ in 0..4 {
            let end = strings.len();
            for at in from..end {
                for character in characters {
                    let mut longer = strings[at].clone();
                    longer.push(character);
                    strings.push(longer);
                }
            }
            from = end;
        }
        strings
    }

    #[test]
    fn the_automata_agree_with_the_regex_crate() {
        let random = &mut Random(2);
        let strings = strings();
        let mut store = Store::new();
        for _ in 0..300 {
            let (one, other) = (pattern(random, 3), pattern(random, 3));
            let (of_one, of_other) = (store.pattern(&one), store.pattern(&other));
            let expected = [&one, &other].map(|pattern| regex::Regex::new(pattern).unwrap());
            let not_other = store.not(of_other);
            let (both, only_one) = (store.both(of_one, of_other), store.both(of_one, not_other));
            let mut told_apart = false;
            for string in &strings {
                let held = expected
                    .each_ref()
                    .map(|expected| expected.is_match(string));
                let context = format!("{one:?} and {other:?} on {string:?}");
                assert_eq!(store.holds(of_one, string), held[0], "{context}");
                assert_eq!(store.holds(not_other, string), !held[1], "not {context}");
                assert_eq!(
                    store.holds(both, string),
                    held[0] && held[1],
                    "both {context}"
                );
                assert_eq!(
                    store.holds(only_one, string),
                    held[0] && !held[1],
                    "only {context}"
                );
                told_apart |= held[0] && !held[1];
            }
            // A string of the one that the other does not hold, if there is one, shows that
            // the other does not include the one.
            let includes = store.includes(of_other, of_one);
            assert!(!(includes && told_apart), "{other:?} includes {one:?}");
            match store.shortest(only_one, Lengths::ANY) {
                Some(word) => {
                    assert!(!includes);
                    assert!(expected[0].is_match(&word), "{one:?} on {word:?}");
                    assert!(!expected[1].is_match(&word), "{other:?} on {word:?}");
                }
                None => assert!(includes && store.is_empty(only_one, Lengths::ANY)),
            }
            // The shortest word of at least two characters is one, and none is shorter.
            let shortest = store.shortest(of_one, from(2));
            let mut long = strings.iter().filter(|string| string.chars().count() >= 2);
            let listed = long.find(|string| expected[0].is_match(string));
            match &shortest {
                Some(word) => {
                    assert!(expected[0].is_match(word), "{one:?} on {word:?}");
                    let length = word.chars().count();
                    assert!(length >= 2);
                    assert!(listed.is_none_or(|listed| listed.chars().count() >= length));
                }
                None => assert!(listed.is_none(), "{one:?} holds {listed:?}"),
            }
            assert_eq!(shortest.is_none(), store.is_empty(of_one, from(2)));
        }
    }

    #[test]
    fn the_automata_agree_with_regexsolver() {
        // That crate matches a pattern against the whole string, so each pattern is held
        // between the two ends here. To it `.` is any character, which `(?s)` says here.
        let random = &mut Random(3);
        let mut store = Store::new();
        let (mut included, mut empty) = (0, 0);
        for _ in 0..300 {
            let (one, other) = (pattern(random, 2), pattern(random, 2));
            if [&one, &other]
                .iter()
                .any(|pattern| pattern.contains(['^', '$']))
            {
                continue;
            }
            let whole = |pattern: &str| format!("(?s)^(?:{pattern})$");
            let (of_one, of_other) = (store.pattern(&whole(&one)), store.pattern(&whole(&other)));
            let term = |pattern: &str| regexsolver::Term::from_pattern(pattern).unwrap();
            let (expected_one, expected_other) = (term(&one), term(&other));
            let context = format!("{one:?} and {other:?}");

            let subset = expected_one.subset(&expected_other).unwrap();
            assert_eq!(store.includes(of_other, of_one), subset, "{context}");
            included += usize::from(subset);

            let both = store.both(of_one, of_other);
            let expected = expected_one.intersection([&expected_other]).unwrap();
            let is_empty = expected.is_empty().unwrap();
            assert_eq!(store.is_empty(both, Lengths::ANY), is_empty, "{context}");
            empty += usize::from(is_empty);
            if let Some(word) = store.shortest(both, Lengths::ANY) {
                assert!(expected.is_match(&word).unwrap(), "{context} on {word:?}");
            }

            let not_one = store.not(of_one);
            let expected = expected_one.complement().unwrap();
            let word = store.shortest(not_one, Lengths::ANY);
            assert_eq!(word.is_none(), expected.is_empty().unwrap(), "{context}");
            if let Some(word) = word {
                assert!(expected.is_match(&word).unwrap(), "not {one:?} on {word:?}");
            }
        }
        assert!(included > 10 && empty > 20, "{included} {empty}");
    }
}
