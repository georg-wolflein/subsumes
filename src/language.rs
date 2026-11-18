//! Regular languages of strings.
//!
//! A check keeps its languages in one store and names them by id. A language comes into the
//! store as a pattern or as a set of words, and out of it come intersections and complements,
//! whether one language includes another, whether a language has a word of some length, and
//! the shortest such word.
//!
//! Nothing here knows of schemas or of the engine. A format is a pattern to this module.
//!
//! A pattern is read in the dialect of the check: as ECMA-262 reads it, or as the `regex`
//! crate does. The dialect only says what a pattern means. Whatever it is, a language is
//! one of strings of Unicode scalar values, and everything after the parser is the same.
//!
//! A language is kept in one of two ways:
//!
//! - As a set of words: these words and no other, or every string but these words.
//! - As a DFA, a deterministic finite automaton, for anything else.
//!
//! A pattern that is one word between `^` and `$`, such as `^type$`, comes in as the set of
//! that word, by the id that the word has, and no DFA is built from it. Any other pattern
//! is only parsed when it comes in. Its DFA is built when something is asked that needs it,
//! so a pattern that cancels against itself before that costs nothing. So it is with the
//! strings that are in none of a few languages: they are kept as those languages, and who
//! asks for [the shape](Languages::shape) of the language gets them.

mod dfa;
mod ecma;
mod pattern;

use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

use regex_syntax::hir::Hir;

use self::dfa::{CHARACTERS, Dfa, LAST, character, plainness};
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

/// The dialect of regular expressions that a `pattern` and the keys of `patternProperties`
/// are read in.
///
/// The two read some patterns differently, so the answer of a check may depend on the
/// dialect. `\d` is one of the ten digits of ASCII in ECMA-262 and any decimal digit of
/// Unicode in the `regex` crate, so `^[0-9]+$` accepts every string that `^\d+$` accepts in
/// the first and not in the second.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum RegexDialect {
    /// [ECMA-262](https://tc39.es/ecma262/#sec-patterns) with the `u` flag, which is what
    /// the specification of JSON Schema recommends. A character is a code point, and a
    /// pattern that the flag forbids is none, such as one that escapes a character that
    /// needs no escape.
    #[default]
    Ecma262,
    /// The dialect of the Rust [`regex`](https://docs.rs/regex/latest/regex/#syntax) crate,
    /// which is what Pydantic validates a `pattern` with by default.
    Rust,
}

/// A pattern that is not read as a language: one that is no pattern of the dialect, or one
/// that asks for something that is not modelled, such as where a word begins or ends.
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
    /// A pattern whose DFA nothing has asked for yet.
    Pattern(Box<Hir>),
    /// The pattern of a format, which is not even parsed until something asks for its
    /// DFA.
    Format(&'static str),
    /// Every string that is in none of these languages, of which nothing has asked for the
    /// DFA yet.
    Outside(Box<[LanguageId]>),
    Dfa(Rc<Dfa>),
}

/// How a language is kept, for who can make use of it.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Shape<'l> {
    /// These words and no other, or with `others` every string but these words.
    Words {
        words: &'l BTreeSet<Box<str>>,
        others: bool,
    },
    /// Every string that is in none of these languages.
    Outside(&'l [LanguageId]),
    /// A pattern, a format or a DFA.
    Other,
}

/// The languages of a check.
#[derive(Debug)]
pub(crate) struct Languages {
    /// The dialect that the patterns of the check are read in.
    dialect: RegexDialect,
    languages: Vec<Language>,
    /// What each language came in as, if it came in as a pattern or a format.
    sources: HashMap<LanguageId, String>,
    /// The patterns that came in, by the dialect that each was read in.
    patterns: HashMap<RegexDialect, HashMap<Box<str>, Result<LanguageId, Unsupported>>>,
    formats: HashMap<Box<str>, LanguageId>,
    of_words: HashMap<(Words, bool), LanguageId>,
    of_dfas: HashMap<Rc<Dfa>, LanguageId>,
    outsides: HashMap<Box<[LanguageId]>, LanguageId>,
    /// The DFA of a set of words, or of what is outside a few languages, once
    /// something has asked for it.
    as_dfas: HashMap<LanguageId, Rc<Dfa>>,
    intersections: HashMap<(LanguageId, LanguageId), LanguageId>,
    complements: HashMap<LanguageId, LanguageId>,
    /// How many words a language has that is no set of words, once that was asked.
    sizes: HashMap<LanguageId, Option<u64>>,
}

impl Default for Languages {
    fn default() -> Self {
        Self::new(RegexDialect::default())
    }
}

impl Languages {
    /// The store of a check that reads its patterns in a dialect.
    pub fn new(dialect: RegexDialect) -> Self {
        let mut languages = Self {
            dialect,
            languages: Vec::new(),
            sources: HashMap::new(),
            patterns: HashMap::new(),
            formats: HashMap::new(),
            of_words: HashMap::new(),
            of_dfas: HashMap::new(),
            outsides: HashMap::new(),
            as_dfas: HashMap::new(),
            intersections: HashMap::new(),
            complements: HashMap::new(),
            sizes: HashMap::new(),
        };
        let none: [&str; 0] = [];
        assert_eq!(languages.words(none), Self::NOTHING);
        assert_eq!(languages.set(Rc::default(), true), Self::EVERYTHING);
        languages
    }

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

    /// The language of every string that holds a match of the pattern, as the dialect of
    /// the check reads the pattern. For a pattern that is one word between `^` and `$` that
    /// is the set of this word, by the id that [`Self::words`] gives it.
    ///
    /// # Errors
    ///
    /// When the pattern is not read as a language; see [`Unsupported`].
    pub fn pattern(&mut self, pattern: &str) -> Result<LanguageId, Unsupported> {
        self.pattern_of(pattern, self.dialect)
    }

    /// The language of a pattern as a dialect reads it. The patterns that the library
    /// writes itself are of the `regex` crate, whatever the dialect of the check.
    fn pattern_of(
        &mut self,
        pattern: &str,
        dialect: RegexDialect,
    ) -> Result<LanguageId, Unsupported> {
        let known = self.patterns.get(&dialect);
        if let Some(known) = known.and_then(|known| known.get(pattern)) {
            return *known;
        }
        let read = pattern::read(pattern, dialect).map(|read| {
            // A word between `^` and `$` is that word, and needs no DFA.
            if let Some(word) = pattern::one_word(&read) {
                return self.words([word]);
            }
            let id = self.add(Language::Pattern(Box::new(read)));
            self.sources.insert(id, format!("{pattern:?}"));
            id
        });
        let known = self.patterns.entry(dialect).or_default();
        known.insert(pattern.into(), read);
        read
    }

    /// The language of a format, which is that of its pattern. The pattern is one of the
    /// `regex` crate, whatever the dialect of the check, and one that is read as a language.
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

    /// The language of every string that is in none of these languages. With a pattern
    /// among them it costs nothing until something asks for its DFA.
    pub fn outside(&mut self, of: impl IntoIterator<Item = LanguageId>) -> LanguageId {
        let mut of: Vec<LanguageId> = of.into_iter().collect();
        of.sort_unstable();
        of.dedup();
        of.retain(|language| *language != Self::NOTHING);
        match of.as_slice() {
            [] => return Self::EVERYTHING,
            [only] => {
                if let Language::Words { words, others } = &self.languages[only.0 as usize] {
                    let (words, others) = (Rc::clone(words), !*others);
                    return self.set(words, others);
                }
            }
            _ => {}
        }
        if let Some(known) = self.outsides.get(of.as_slice()) {
            return *known;
        }
        let of: Box<[LanguageId]> = of.into();
        let id = self.add(Language::Outside(of.clone()));
        self.outsides.insert(of, id);
        id
    }

    /// How a language is kept.
    pub fn shape(&self, id: LanguageId) -> Shape<'_> {
        match &self.languages[id.0 as usize] {
            Language::Words { words, others } => Shape::Words {
                words,
                others: *others,
            },
            Language::Outside(of) => Shape::Outside(of),
            _ => Shape::Other,
        }
    }

    /// The id of a DFA that came out of others.
    fn keep(&mut self, dfa: Dfa) -> LanguageId {
        if dfa.is_empty() {
            return Self::NOTHING;
        }
        if dfa.is_everything() {
            return Self::EVERYTHING;
        }
        let dfa = Rc::new(dfa);
        if let Some(known) = self.of_dfas.get(&dfa) {
            return *known;
        }
        let id = self.add(Language::Dfa(Rc::clone(&dfa)));
        self.of_dfas.insert(dfa, id);
        id
    }

    /// The DFA of a language, which is built if it was not before.
    fn dfa(&mut self, id: LanguageId, budget: &mut Budget) -> Result<Rc<Dfa>, Exhausted> {
        let built = match &self.languages[id.0 as usize] {
            Language::Dfa(dfa) => return Ok(Rc::clone(dfa)),
            Language::Pattern(pattern) => pattern::dfa(pattern, budget)?,
            Language::Format(pattern) => {
                let read =
                    pattern::read_rust(pattern).expect("the pattern of a format is supported");
                pattern::dfa(&read, budget)?
            }
            Language::Words { words, others } => {
                if let Some(known) = self.as_dfas.get(&id) {
                    return Ok(Rc::clone(known));
                }
                let listed = Dfa::of_words(words.iter().map(AsRef::as_ref), budget)?;
                let built = Rc::new(if *others { listed.complement() } else { listed });
                self.as_dfas.insert(id, Rc::clone(&built));
                return Ok(built);
            }
            Language::Outside(of) => {
                if let Some(known) = self.as_dfas.get(&id) {
                    return Ok(Rc::clone(known));
                }
                // What is left of every string when each of the languages is taken out.
                // None of them is kept this way itself, so this goes one level deep.
                let of = of.clone();
                let mut left = Self::EVERYTHING;
                for language in of.iter() {
                    let other = self.complement(*language, budget)?;
                    left = self.intersection(left, other, budget)?;
                }
                let built = self.dfa(left, budget)?;
                self.as_dfas.insert(id, Rc::clone(&built));
                return Ok(built);
            }
        };
        // Two patterns of one language share the DFA.
        let built = Rc::new(built);
        let shared = match self.of_dfas.entry(Rc::clone(&built)) {
            Entry::Occupied(known) => Rc::clone(known.key()),
            Entry::Vacant(new) => {
                new.insert(id);
                built
            }
        };
        self.languages[id.0 as usize] = Language::Dfa(Rc::clone(&shared));
        Ok(shared)
    }

    /// The language of every string that is not in this one.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFA of a pattern.
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
                let complement = self.dfa(id, budget)?.complement();
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
    /// When the budget does not cover the DFAs.
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
                // A step for every sixteen words that are looked at, so that a few cost
                // none.
                budget.charge(((words.len() + more.len()) / 16) as u64)?;
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
                let (of_a, of_b) = (self.dfa(a, budget)?, self.dfa(b, budget)?);
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
        let dfa = self.dfa(by, budget)?;
        let mut held = BTreeSet::new();
        for word in words.iter() {
            budget.charge(1 + word.len() as u64 / 32)?;
            if dfa.accepts(word) {
                held.insert(word.clone());
            }
        }
        Ok(self.set(Rc::new(held), false))
    }

    /// The language of the strings that are in either.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFAs.
    pub fn union(
        &mut self,
        a: LanguageId,
        b: LanguageId,
        budget: &mut Budget,
    ) -> Result<LanguageId, Exhausted> {
        if a == Self::NOTHING || a == b {
            return Ok(b);
        }
        if b == Self::NOTHING {
            return Ok(a);
        }
        // What is in neither is outside both.
        let (not_a, not_b) = (self.complement(a, budget)?, self.complement(b, budget)?);
        let neither = self.intersection(not_a, not_b, budget)?;
        self.complement(neither, budget)
    }

    /// The language of every string whose length is within the bounds, unless the bounds
    /// are larger than a pattern can say.
    pub fn of_lengths(&mut self, lengths: Lengths) -> Option<LanguageId> {
        let pattern = match lengths {
            Lengths::ANY => return Some(Self::EVERYTHING),
            Lengths { min, max: None } => format!("(?s)^.{{{min},}}$"),
            Lengths {
                min,
                max: Some(max),
            } if max < min => return Some(Self::NOTHING),
            Lengths {
                min,
                max: Some(max),
            } => format!("(?s)^.{{{min},{max}}}$"),
        };
        self.pattern_of(&pattern, RegexDialect::Rust).ok()
    }

    /// Whether the language holds the word.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFA of a pattern.
    pub fn contains(
        &mut self,
        id: LanguageId,
        word: &str,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        if let Language::Words { words, others } = &self.languages[id.0 as usize] {
            return Ok(words.contains(word) != *others);
        }
        budget.charge(1 + word.len() as u64 / 32)?;
        Ok(self.dfa(id, budget)?.accepts(word))
    }

    /// How many words the language has, or `None` if there is no end of them, or more than
    /// a `u64` counts.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFA or the count.
    pub fn size(&mut self, id: LanguageId, budget: &mut Budget) -> Result<Option<u64>, Exhausted> {
        match &self.languages[id.0 as usize] {
            Language::Words { others: true, .. } => Ok(None),
            Language::Words { words, .. } => Ok(Some(words.len() as u64)),
            _ => {
                if let Some(known) = self.sizes.get(&id) {
                    return Ok(*known);
                }
                let size = self.dfa(id, budget)?.size(budget)?;
                self.sizes.insert(id, size);
                Ok(size)
            }
        }
    }

    /// Whether every string of `narrow` is in `wide`.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the DFAs.
    // The engine compares languages by their intersections, and the tests ask this.
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
            _ => Ok(!self.dfa(id, budget)?.has_word(lengths, budget)?),
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
            return self.dfa(id, budget)?.shortest(lengths, budget);
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

    /// How many words the sets of words hold together, each set counted once.
    #[cfg(test)]
    pub fn words_kept(&self) -> usize {
        let mut sets: Vec<&Words> = Vec::new();
        for language in &self.languages {
            if let Language::Words { words, .. } = language
                && !sets.iter().any(|known| Rc::ptr_eq(known, words))
            {
                sets.push(words);
            }
        }
        sets.iter().map(|words| words.len()).sum()
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
            Language::Outside(of) => {
                let listed: Vec<String> = of.iter().map(|language| self.show(*language)).collect();
                format!("none of [{}]", listed.join(", "))
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
        /// A store for patterns of the `regex` crate, which most of the tests here write.
        fn new() -> Self {
            Self::of(RegexDialect::Rust)
        }

        fn of(dialect: RegexDialect) -> Self {
            Self(Languages::new(dialect))
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
    fn a_word_between_the_two_ends_is_that_word_and_no_pattern() {
        let mut store = Store::new();
        assert_eq!(store.pattern("^type$"), store.0.words(["type"]));
        assert_eq!(store.pattern(r"^a\.b$"), store.0.words(["a.b"]));
        assert_eq!(store.pattern("^é𝄞$"), store.0.words(["é𝄞"]));
        assert_eq!(store.pattern("^$"), store.0.words([""]));
        // Anything else between them is a pattern, and so is a word without one of them,
        // or with something else in the place of one.
        for pattern in [
            "^a|b$", "^a", "a$", "a", "^[ab]$", "^a?$", "(?i)^a$", "^a$|^b$", "^ab*", "a*b$",
            "^a^", "$a$", "^a$b", "^$a",
        ] {
            let read = store.pattern(pattern);
            assert_eq!(store.0.show(read), format!("{pattern:?}"));
        }
    }

    #[test]
    fn a_pattern_is_read_in_the_dialect_of_the_store() {
        let (mut ecma, mut rust) = (Store::of(RegexDialect::Ecma262), Store::new());
        assert_eq!(Languages::default().dialect, RegexDialect::Ecma262);
        // To ECMA-262 a digit is one of ASCII, and to the `regex` crate any of Unicode.
        for (store, same) in [(&mut ecma, true), (&mut rust, false)] {
            let (digits, ascii) = (store.pattern(r"^\d+$"), store.pattern("^[0-9]+$"));
            assert!(store.includes(digits, ascii));
            assert_eq!(store.includes(ascii, digits), same);
            assert_eq!(store.holds(digits, "٣"), !same);
        }
        // What is a pattern of one dialect may be none of the other.
        for only_rust in ["(?i)^a$", r"^a\-b$", r"^\p{Greek}$"] {
            assert_eq!(ecma.0.pattern(only_rust), Err(Unsupported), "{only_rust:?}");
            assert!(rust.0.pattern(only_rust).is_ok(), "{only_rust:?}");
        }
        for only_ecma in [r"^\cJ$", r"^[^]$", r"^\uD83D\uDE00$"] {
            assert!(ecma.0.pattern(only_ecma).is_ok(), "{only_ecma:?}");
            assert_eq!(rust.0.pattern(only_ecma), Err(Unsupported), "{only_ecma:?}");
        }
        // And a pattern of both may say one thing in the one and another in the other.
        let (of_ecma, of_rust) = (ecma.pattern("^[a&&b]$"), rust.pattern("^[a&&b]$"));
        assert!(ecma.holds(of_ecma, "&") && !rust.holds(of_rust, "&"));
        // A word between the two ends is that word in either.
        for store in [&mut ecma, &mut rust] {
            assert_eq!(store.pattern("^type$"), store.0.words(["type"]));
            assert_eq!(store.pattern(r"^a\.b$"), store.0.words(["a.b"]));
            assert_eq!(store.pattern("^$"), store.0.words([""]));
        }
        assert_eq!(ecma.pattern(r"^a\x62(c)$"), ecma.0.words(["abc"]));
        // The pattern of some lengths is one that the library writes, as the `regex` crate
        // reads it: any character, a line feed too, so many times.
        for store in [&mut ecma, &mut rust] {
            let short = store.0.of_lengths(between(1, 2)).unwrap();
            for (word, held) in [("", false), ("a", true), ("é\n", true), ("abc", false)] {
                assert_eq!(store.holds(short, word), held, "{word:?}");
            }
        }
        // Written in a schema, the same pattern is none of ECMA-262.
        assert_eq!(ecma.0.pattern("(?s)^.{1,2}$"), Err(Unsupported));
        assert_eq!(
            rust.0.pattern("(?s)^.{1,2}$"),
            rust.0.of_lengths(between(1, 2)).ok_or(Unsupported)
        );
    }

    /// Every pattern of the corpus: what stands under `pattern`, and the keys of what stands
    /// under `patternProperties`, wherever the two are.
    fn corpus_patterns() -> BTreeSet<String> {
        let mut patterns = BTreeSet::new();
        let cases = crate::testing::corpus_cases();
        for (_, schema) in cases
            .iter()
            .flat_map(|case| crate::testing::schemas_of(case))
        {
            let mut pending: Vec<serde_json::Value> = vec![schema];
            while let Some(value) = pending.pop() {
                match value {
                    serde_json::Value::Array(items) => pending.extend(items),
                    serde_json::Value::Object(members) => {
                        if let Some(serde_json::Value::String(pattern)) = members.get("pattern") {
                            patterns.insert(pattern.clone());
                        }
                        if let Some(serde_json::Value::Object(named)) =
                            members.get("patternProperties")
                        {
                            patterns.extend(named.keys().cloned());
                        }
                        pending.extend(members.into_iter().map(|(_, member)| member));
                    }
                    _ => {}
                }
            }
        }
        patterns
    }

    #[test]
    #[ignore = "needs the corpus in benchmark/, which `make corpus` downloads"]
    fn the_patterns_of_the_corpus_are_read_as_ecma_262() {
        let patterns = corpus_patterns();
        let mut store = Store::of(RegexDialect::Ecma262);
        let (mut invalid, mut not_modelled) = (Vec::new(), Vec::new());
        let (mut matched, mut unmatched, mut too_large) = (0, 0, 0);
        for pattern in &patterns {
            // The parser of `oxc` says which are patterns of ECMA-262.
            let valid = ecma::tests::valid(pattern);
            match ecma::read(pattern) {
                Ok(_) => assert!(valid, "{pattern:?}"),
                Err(ecma::Refusal::Invalid) => {
                    assert!(!valid, "{pattern:?}");
                    invalid.push(pattern);
                    continue;
                }
                Err(ecma::Refusal::NotModelled) => {
                    assert!(valid, "{pattern:?}");
                    not_modelled.push(pattern);
                    continue;
                }
            }
            // And `regress` matches the plainest string of the language of each that is read,
            // and does not match the plainest string outside it.
            let expected = Matcher::new(RegexDialect::Ecma262, pattern);
            let budget = &mut Budget::new(1_000_000);
            let language = store.pattern(pattern);
            let words = store
                .0
                .shortest(language, Lengths::ANY, budget)
                .and_then(|inside| {
                    let outside = store.0.complement(language, budget)?;
                    Ok((inside, store.0.shortest(outside, Lengths::ANY, budget)?))
                });
            let Ok((inside, outside)) = words else {
                too_large += 1;
                continue;
            };
            if let Some(word) = inside {
                assert!(expected.is_match(&word), "{pattern:?} on {word:?}");
                matched += 1;
            }
            if let Some(word) = outside {
                assert!(!expected.is_match(&word), "{pattern:?} on {word:?}");
                unmatched += 1;
            }
        }
        println!(
            "{} patterns: {} are none of ECMA-262, {} are not modelled, {} are too large; \
             {matched} strings matched and {unmatched} not\nnot modelled: {not_modelled:?}",
            patterns.len(),
            invalid.len(),
            not_modelled.len(),
            too_large,
        );
        assert!(patterns.len() > 15_000, "{} patterns", patterns.len());
        assert!(invalid.len() < 50 && not_modelled.len() < 20);
        assert!(matched > 15_000 && unmatched > 15_000 && too_large < 20);
    }

    #[test]
    fn what_is_outside_a_few_languages_is_built_when_it_is_asked_for() {
        let mut store = Store::new();
        let (words, begins) = (store.0.words(["a", "b"]), store.pattern("^x-"));
        let ends = store.pattern("y$");
        // Of nothing, and of sets of words only, it is a set of words.
        assert_eq!(store.0.outside([]), Languages::EVERYTHING);
        assert_eq!(store.0.outside([Languages::NOTHING]), Languages::EVERYTHING);
        assert_eq!(store.0.outside([Languages::EVERYTHING]), Languages::NOTHING);
        assert_eq!(store.0.outside([words]), store.not(words));
        // With a pattern it is kept as the languages, in one order.
        let outside = store.0.outside([begins, words, ends, begins]);
        assert_eq!(outside, store.0.outside([ends, words, begins]));
        assert_eq!(
            store.0.show(outside),
            r#"none of [one of ["a", "b"], "^x-", "y$"]"#
        );
        let Shape::Outside(of) = store.0.shape(outside) else {
            panic!("it is kept as what it is outside of");
        };
        assert_eq!(of, [words, begins, ends]);
        assert!(matches!(store.0.shape(begins), Shape::Other));
        // And it is what its DFA says.
        for (word, held) in [
            ("c", true),
            ("", true),
            ("a", false),
            ("x-c", false),
            ("cy", false),
            ("x", true),
        ] {
            assert_eq!(store.holds(outside, word), held, "{word:?}");
            assert_eq!(
                store.0.contains(outside, word, &mut unlimited()),
                Ok(held),
                "{word:?}"
            );
        }
        let not_outside = store.not(outside);
        assert!(store.includes(not_outside, begins) && store.includes(not_outside, words));
        assert_eq!(store.shortest(outside, from(1)), some("c"));
    }

    #[test]
    fn either_of_two_languages_is_what_is_outside_neither() {
        let mut store = Store::new();
        let either = |store: &mut Store, a, b| store.0.union(a, b, &mut unlimited()).unwrap();
        let (a, bc) = (store.0.words(["a"]), store.0.words(["b", "c"]));
        assert_eq!(either(&mut store, a, bc), store.0.words(["a", "b", "c"]));
        assert_eq!(either(&mut store, a, Languages::NOTHING), a);
        assert_eq!(either(&mut store, Languages::NOTHING, a), a);
        assert_eq!(
            either(&mut store, a, Languages::EVERYTHING),
            Languages::EVERYTHING
        );
        let (begins, ends) = (store.pattern("^a"), store.pattern("b$"));
        let both = either(&mut store, begins, ends);
        let said = store.pattern("^a|b$");
        assert!(store.includes(both, said) && store.includes(said, both));
        let with_words = either(&mut store, begins, bc);
        assert!(store.holds(with_words, "c") && store.holds(with_words, "ab"));
        assert!(!store.holds(with_words, "d"));
    }

    #[test]
    fn a_language_holds_a_word_or_does_not() {
        let mut store = Store::new();
        let holds =
            |store: &mut Store, id, word| store.0.contains(id, word, &mut unlimited()).unwrap();
        let words = store.0.words(["a", "b"]);
        assert!(holds(&mut store, words, "a") && !holds(&mut store, words, "c"));
        let others = store.not(words);
        assert!(!holds(&mut store, others, "a") && holds(&mut store, others, "c"));
        let lower = store.pattern("^[a-z]+$");
        assert!(holds(&mut store, lower, "abc") && !holds(&mut store, lower, "aBc"));
        assert!(!holds(&mut store, lower, ""));
        // A set of words costs nothing, and a pattern its DFA.
        let mut budget = Budget::new(0);
        assert_eq!(store.0.contains(words, "a", &mut budget), Ok(true));
        let digits = store.pattern("^[0-9]+$");
        assert_eq!(store.0.contains(digits, "1", &mut budget), Err(Exhausted));
    }

    #[test]
    fn the_words_of_a_language_are_counted() {
        let mut store = Store::new();
        let size = |store: &mut Store, pattern: &str| {
            let read = store.pattern(pattern);
            store.0.size(read, &mut unlimited()).unwrap()
        };
        assert_eq!(size(&mut store, "^(a|b)$"), Some(2));
        assert_eq!(size(&mut store, "^[a-c]{2}$"), Some(9));
        assert_eq!(size(&mut store, "^[a-c]{0,2}$"), Some(13));
        assert_eq!(size(&mut store, "^(a|ab|abc)?$"), Some(4));
        assert_eq!(size(&mut store, "^a*$"), None);
        assert_eq!(size(&mut store, "a"), None);
        assert_eq!(size(&mut store, "^a[^a]$"), Some(u64::from(LAST)));
        // More words than can be counted are as good as no end of them. The count is never
        // rounded: one less than too many is counted exactly.
        assert_eq!(size(&mut store, "(?s)^.{9}$"), None);
        assert_eq!(size(&mut store, "^[ab]{64}$"), None);
        assert_eq!(size(&mut store, "^[ab]{63}$"), Some(1 << 63));
        assert_eq!(size(&mut store, "^[ab]{1,63}$"), Some(u64::MAX - 1));
        assert_eq!(size(&mut store, "$a"), Some(0));
        let (few, others) = (store.0.words(["a", "b", "c"]), store.0.words(["a"]));
        let others = store.not(others);
        assert_eq!(store.0.size(few, &mut unlimited()), Ok(Some(3)));
        assert_eq!(store.0.size(others, &mut unlimited()), Ok(None));
        assert_eq!(
            store.0.size(Languages::NOTHING, &mut unlimited()),
            Ok(Some(0))
        );
    }

    #[test]
    fn the_strings_of_some_lengths_are_a_language() {
        let mut store = Store::new();
        assert_eq!(
            store.0.of_lengths(Lengths::ANY),
            Some(Languages::EVERYTHING)
        );
        assert_eq!(store.0.of_lengths(between(3, 2)), Some(Languages::NOTHING));
        let short = store.0.of_lengths(between(1, 2)).unwrap();
        for (word, held) in [("", false), ("a", true), ("é\n", true), ("abc", false)] {
            assert_eq!(store.holds(short, word), held, "{word:?}");
        }
        let long = store.0.of_lengths(from(2)).unwrap();
        assert!(!store.holds(long, "a") && store.holds(long, "abcdef"));
        // A count that no pattern holds.
        assert_eq!(store.0.of_lengths(from(u64::MAX)), None);
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

    /// Says whether a pattern matches a string, by a crate that matches in the dialect: the
    /// `regex` crate, or `regress` for ECMA-262.
    struct Matcher(Box<dyn Fn(&str) -> bool>);

    impl Matcher {
        fn new(dialect: RegexDialect, pattern: &str) -> Self {
            match dialect {
                RegexDialect::Ecma262 => {
                    let read = regress::Regex::with_flags(pattern, "u").unwrap();
                    Self(Box::new(move |string| read.find(string).is_some()))
                }
                RegexDialect::Rust => {
                    let read = regex::Regex::new(pattern).unwrap();
                    Self(Box::new(move |string| read.is_match(string)))
                }
            }
        }

        fn is_match(&self, string: &str) -> bool {
            (self.0)(string)
        }
    }

    #[test]
    fn the_dfas_agree_with_the_regex_crate() {
        the_dfas_agree_with_a_matcher(RegexDialect::Rust);
    }

    #[test]
    fn the_dfas_agree_with_regress() {
        the_dfas_agree_with_a_matcher(RegexDialect::Ecma262);
    }

    /// The random patterns are ones of both dialects. The two read some of them differently,
    /// such as `\w` on `é`.
    fn the_dfas_agree_with_a_matcher(dialect: RegexDialect) {
        let random = &mut Random(2);
        let strings = strings();
        let mut store = Store::of(dialect);
        for _ in 0..300 {
            let (one, other) = (pattern(random, 3), pattern(random, 3));
            let (of_one, of_other) = (store.pattern(&one), store.pattern(&other));
            let expected = [&one, &other].map(|pattern| Matcher::new(dialect, pattern));
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
    fn the_dfas_agree_with_regexsolver() {
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
