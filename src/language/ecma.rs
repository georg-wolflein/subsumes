//! Patterns of ECMA-262.
//!
//! A pattern is read as the specification of JSON Schema recommends: as a regular expression
//! of ECMA-262 that is built with the `u` flag and with no other. So a character is a code
//! point, `\d` and `\w` are those of ASCII, `.` matches every character but the four line
//! terminators, and what the flag forbids is no pattern, such as an escape of a character
//! that needs none or a `{` that begins no quantifier.
//!
//! The parser is a recursive descent parser for the grammar of the standard. It makes the
//! `Hir` of `regex-syntax` that says the same as the pattern, and a DFA is built from that as
//! from a pattern of the `regex` crate. Which characters have a property of Unicode, the
//! tables of `regex-syntax` say.
//!
//! A string of a JSON document holds no surrogate, so a surrogate in a pattern matches no
//! character, and a set of characters is one of scalar values.

mod names;

use std::collections::HashMap;
use std::str::Chars;

use regex_syntax::hir::{Class, ClassUnicode, ClassUnicodeRange, Hir, Look, Repetition};

/// Why a pattern is not read as a language.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Refusal {
    /// It is no pattern of ECMA-262 with the `u` flag.
    Invalid,
    /// It is one, and asks for something that is not modelled: a look-around, where a word
    /// begins or ends, a backreference, the modifiers of a group, or more than fits.
    NotModelled,
}

/// How many groups a pattern may hold inside one another. A group adds three levels to the
/// `Hir` at most, and what is built from the `Hir` recurses on its levels.
const DEEPEST: u32 = 80;

/// How often a pattern may give one name to a group. Groups of one name are held against
/// each other, two by two.
const MOST_OF_A_NAME: usize = 64;

/// The first surrogate and the first character after the last.
const SURROGATES: (u32, u32) = (0xD800, 0xE000);

/// Parses a pattern as ECMA-262 does with the `u` flag.
///
/// # Errors
///
/// When it is no such pattern, or asks for something that is not modelled. A pattern that
/// is both is refused as no pattern.
pub(super) fn read(pattern: &str) -> Result<Hir, Refusal> {
    let mut parser = Parser {
        rest: pattern.chars(),
        depth: 0,
        groups: 0,
        disjunctions: 0,
        within: Vec::new(),
        names: HashMap::new(),
        referenced: 0,
        referenced_names: Vec::new(),
        not_modelled: false,
        identifiers: None,
    };
    let read = parser.disjunction()?;
    // What is left begins with a `)` that closes no group.
    if parser.peek().is_some() {
        return Err(Refusal::Invalid);
    }
    // A backreference names a group that the pattern has, before it or after it.
    let named = |name| parser.names.contains_key(name);
    if parser.referenced > parser.groups || !parser.referenced_names.iter().all(named) {
        return Err(Refusal::Invalid);
    }
    if parser.not_modelled {
        return Err(Refusal::NotModelled);
    }
    Ok(read)
}

/// A place in a pattern: an alternative of a disjunction, by the number of the disjunction
/// and the position of the alternative in it.
type Alternative = (u32, usize);

struct Parser<'p> {
    /// What of the pattern is still to be read.
    rest: Chars<'p>,
    /// How many groups are around the place at hand.
    depth: u32,
    /// How many capturing groups were read.
    groups: u64,
    /// How many disjunctions were begun, which numbers them.
    disjunctions: u32,
    /// The alternatives around the place at hand, from the outermost.
    within: Vec<Alternative>,
    /// The names of the groups, each with the alternatives around every group of the name.
    names: HashMap<String, Vec<Vec<Alternative>>>,
    /// The largest number of a group that a backreference asks for.
    referenced: u64,
    /// The names of the groups that backreferences ask for.
    referenced_names: Vec<String>,
    /// Whether something was read that is valid and not modelled. The rest is still read,
    /// since it may be no pattern at all.
    not_modelled: bool,
    /// The characters that begin a name and those that go on with it, once a name was read.
    identifiers: Option<(ClassUnicode, ClassUnicode)>,
}

/// What an escape stands for, and what stands in a class: one character by its code point,
/// which may be a surrogate, or a set of characters.
enum Escaped {
    Character(u32),
    Set(ClassUnicode),
}

impl Parser<'_> {
    fn peek(&self) -> Option<char> {
        self.rest.clone().next()
    }

    fn eat(&mut self, expected: char) -> bool {
        let found = self.peek() == Some(expected);
        if found {
            self.rest.next();
        }
        found
    }

    fn eat_all(&mut self, expected: &str) -> bool {
        let rest = self.rest.as_str().strip_prefix(expected);
        if let Some(rest) = rest {
            self.rest = rest.chars();
        }
        rest.is_some()
    }

    /// Alternatives between `|`, up to the end of the pattern or to a `)`.
    fn disjunction(&mut self) -> Result<Hir, Refusal> {
        let number = self.disjunctions;
        self.disjunctions += 1;
        let mut alternatives = Vec::new();
        loop {
            self.within.push((number, alternatives.len()));
            let mut terms = Vec::new();
            while !matches!(self.peek(), None | Some('|' | ')')) {
                terms.push(self.term()?);
            }
            self.within.pop();
            alternatives.push(Hir::concat(terms));
            if !self.eat('|') {
                return Ok(Hir::alternation(alternatives));
            }
        }
    }

    /// An assertion, or an atom with the quantifier that follows it.
    fn term(&mut self) -> Result<Hir, Refusal> {
        let atom = match self.rest.next().expect("a term begins with a character") {
            '^' => return Ok(Hir::look(Look::Start)),
            '$' => return Ok(Hir::look(Look::End)),
            '(' => match self.group()? {
                Some(group) => group,
                // A look-around, which takes no quantifier.
                None => return Ok(Hir::empty()),
            },
            '.' => {
                let line_terminators = ['\n', '\r', '\u{2028}', '\u{2029}'];
                let mut all_but = ClassUnicode::new(line_terminators.map(one));
                all_but.negate();
                Hir::class(Class::Unicode(all_but))
            }
            '[' => self.class()?,
            '\\' => match self.peek() {
                // Where a word begins or ends, or does neither. It takes no quantifier.
                Some('b' | 'B') => {
                    self.rest.next();
                    self.not_modelled = true;
                    return Ok(Hir::empty());
                }
                Some('1'..='9') => {
                    self.referenced = self.referenced.max(self.number());
                    self.not_modelled = true;
                    Hir::empty()
                }
                Some('k') => {
                    self.rest.next();
                    if !self.eat('<') {
                        return Err(Refusal::Invalid);
                    }
                    let name = self.name()?;
                    self.referenced_names.push(name);
                    self.not_modelled = true;
                    Hir::empty()
                }
                _ => match self.escape()? {
                    Escaped::Character(code_point) => character(code_point),
                    Escaped::Set(set) => Hir::class(Class::Unicode(set)),
                },
            },
            // With the `u` flag none of these stands for itself.
            '*' | '+' | '?' | '{' | '}' | ']' => return Err(Refusal::Invalid),
            other => character(other.into()),
        };
        self.quantified(atom)
    }

    /// A group or a look-around, after its `(`. A look-around is `None`.
    fn group(&mut self) -> Result<Option<Hir>, Refusal> {
        let mut look_around = false;
        if !self.eat('?') {
            self.groups += 1;
        } else if ["=", "!", "<=", "<!"].iter().any(|kind| self.eat_all(kind)) {
            look_around = true;
            self.not_modelled = true;
        } else if self.eat('<') {
            let name = self.name()?;
            let around = self.names.entry(name).or_default();
            // Two groups may have one name if no match goes through both: if they are in
            // two alternatives of one disjunction.
            let apart = |other: &Vec<Alternative>| {
                let pairs = other.iter().zip(&self.within);
                pairs.into_iter().any(|(a, b)| a.0 == b.0 && a.1 != b.1)
            };
            if !around.iter().all(apart) {
                return Err(Refusal::Invalid);
            }
            if around.len() == MOST_OF_A_NAME {
                return Err(Refusal::NotModelled);
            }
            around.push(self.within.clone());
            self.groups += 1;
        } else if !self.eat(':') {
            self.modifiers()?;
            self.not_modelled = true;
        }
        if self.depth == DEEPEST {
            return Err(Refusal::NotModelled);
        }
        self.depth += 1;
        let inside = self.disjunction()?;
        self.depth -= 1;
        if !self.eat(')') {
            return Err(Refusal::Invalid);
        }
        Ok((!look_around).then_some(inside))
    }

    /// The flags that a group turns on and off for what is inside it, up to its `:`. Each
    /// is one of `i`, `m` and `s` and stands once, and there is one at least.
    fn modifiers(&mut self) -> Result<(), Refusal> {
        let mut seen = String::new();
        let mut off = false;
        loop {
            match self.rest.next() {
                Some(':') if !seen.is_empty() => return Ok(()),
                Some('-') if !off => off = true,
                Some(flag @ ('i' | 'm' | 's')) if !seen.contains(flag) => seen.push(flag),
                _ => return Err(Refusal::Invalid),
            }
        }
    }

    /// The name of a group, after its `<` and up to its `>`: an identifier.
    fn name(&mut self) -> Result<String, Refusal> {
        let mut name = String::new();
        loop {
            let next = match self.rest.next().ok_or(Refusal::Invalid)? {
                '>' if !name.is_empty() => return Ok(name),
                '\\' if self.eat('u') => {
                    char::from_u32(self.unicode_escape()?).ok_or(Refusal::Invalid)?
                }
                other => other,
            };
            if self.identifiers.is_none() {
                let begin = names::characters(None, "ID_Start")?;
                let go_on = names::characters(None, "ID_Continue")?;
                self.identifiers = Some((begin, go_on));
            }
            let (begin, go_on) = self.identifiers.as_ref().expect("they were just set");
            let holds = |set: &ClassUnicode| {
                let ranges = set.ranges().iter();
                ranges
                    .into_iter()
                    .any(|range| (range.start()..=range.end()).contains(&next))
            };
            let allowed = match next {
                '$' | '_' => true,
                '\u{200c}' | '\u{200d}' => !name.is_empty(),
                _ if name.is_empty() => holds(begin),
                _ => holds(go_on),
            };
            if !allowed {
                return Err(Refusal::Invalid);
            }
            name.push(next);
        }
    }

    /// The decimal digits at hand as a number. One that 64 bits do not hold is their most.
    fn number(&mut self) -> u64 {
        let mut number = 0_u64;
        while let Some(digit) = self.peek().and_then(|digit| digit.to_digit(10)) {
            self.rest.next();
            number = number.saturating_mul(10).saturating_add(digit.into());
        }
        number
    }

    /// So many hexadecimal digits as a number.
    fn hexadecimal(&mut self, digits: usize) -> Result<u32, Refusal> {
        let mut number = 0;
        for _ in 0..digits {
            let digit = self.rest.next().and_then(|digit| digit.to_digit(16));
            number = number * 16 + digit.ok_or(Refusal::Invalid)?;
        }
        Ok(number)
    }

    /// The code point of an escape, after its `\u`: four digits, the eight of the two
    /// surrogates of a pair, or any number of digits in braces.
    fn unicode_escape(&mut self) -> Result<u32, Refusal> {
        if self.eat('{') {
            let mut code_point = 0_u32;
            let mut digits = 0;
            while !self.eat('}') {
                let digit = self.rest.next().and_then(|digit| digit.to_digit(16));
                code_point = code_point * 16 + digit.ok_or(Refusal::Invalid)?;
                digits += 1;
                if code_point > char::MAX.into() {
                    return Err(Refusal::Invalid);
                }
            }
            return if digits == 0 {
                Err(Refusal::Invalid)
            } else {
                Ok(code_point)
            };
        }
        let first = self.hexadecimal(4)?;
        // A surrogate that begins a pair, and the one that ends it if it follows.
        if (0xD800..0xDC00).contains(&first) {
            let after = self.rest.clone();
            if self.eat_all("\\u")
                && let Ok(second @ 0xDC00..0xE000) = self.hexadecimal(4)
            {
                return Ok(0x1_0000 + ((first - 0xD800) << 10) + (second - 0xDC00));
            }
            self.rest = after;
        }
        Ok(first)
    }

    /// What an escape stands for, after its `\`. The escapes that only an atom may be, and
    /// those that only a class may hold, were looked for before.
    fn escape(&mut self) -> Result<Escaped, Refusal> {
        let set = |ranges: &[(char, char)], negated: bool| {
            let ranges = ranges
                .iter()
                .map(|(first, last)| ClassUnicodeRange::new(*first, *last));
            let mut set = ClassUnicode::new(ranges);
            if negated {
                set.negate();
            }
            Ok(Escaped::Set(set))
        };
        let code_point = match self.rest.next().ok_or(Refusal::Invalid)? {
            kind @ ('d' | 'D') => return set(&DIGITS, kind == 'D'),
            kind @ ('w' | 'W') => return set(&WORD, kind == 'W'),
            kind @ ('s' | 'S') => return set(&SPACE, kind == 'S'),
            kind @ ('p' | 'P') => {
                let mut set = self.property()?;
                if kind == 'P' {
                    set.negate();
                }
                return Ok(Escaped::Set(set));
            }
            'f' => 0x0C,
            'n' => 0x0A,
            'r' => 0x0D,
            't' => 0x09,
            'v' => 0x0B,
            'c' => match self.rest.next() {
                Some(letter) if letter.is_ascii_alphabetic() => u32::from(letter) % 32,
                _ => return Err(Refusal::Invalid),
            },
            '0' if !matches!(self.peek(), Some('0'..='9')) => 0,
            'x' => self.hexadecimal(2)?,
            'u' => self.unicode_escape()?,
            // A character of the syntax stands for itself, and so does a `/`.
            same @ ('^' | '$' | '\\' | '.' | '*' | '+' | '?' | '(' | ')' | '[' | ']' | '{'
            | '}' | '|' | '/') => same.into(),
            _ => return Err(Refusal::Invalid),
        };
        Ok(Escaped::Character(code_point))
    }

    /// The characters of a property of Unicode, after `\p` or `\P`.
    fn property(&mut self) -> Result<ClassUnicode, Refusal> {
        if !self.eat('{') {
            return Err(Refusal::Invalid);
        }
        let inside = self.rest.as_str();
        let end = inside.find('}').ok_or(Refusal::Invalid)?;
        self.rest = inside[end + 1..].chars();
        let (name, value) = match inside[..end].split_once('=') {
            Some((name, value)) => (Some(name), value),
            None => (None, &inside[..end]),
        };
        // A name is of letters and `_`, and a value may hold digits too. Every name of the
        // tables is so, and nothing else is looked up.
        let plain = |text: &str| {
            text.bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        };
        if !plain(value) || !name.is_none_or(plain) {
            return Err(Refusal::Invalid);
        }
        names::characters(name, value)
    }

    /// A class, after its `[`.
    fn class(&mut self) -> Result<Hir, Refusal> {
        let negated = self.eat('^');
        let mut set = ClassUnicode::empty();
        while let Some(first) = self.class_atom()? {
            // A `-` makes a range, unless it is the last character of the class.
            let rest = self.rest.as_str();
            let last = if rest.starts_with('-') && !rest.starts_with("-]") {
                self.rest.next();
                self.class_atom()?
            } else {
                None
            };
            match (first, last) {
                (Escaped::Character(first), None) => add(&mut set, first, first),
                (Escaped::Set(characters), None) => set.union(&characters),
                // A range goes from a character to one that is not before it.
                (Escaped::Character(first), Some(Escaped::Character(last))) if first <= last => {
                    add(&mut set, first, last);
                }
                _ => return Err(Refusal::Invalid),
            }
        }
        if negated {
            set.negate();
        }
        Ok(Hir::class(Class::Unicode(set)))
    }

    /// What stands in a class next, or `None` at the `]` that ends the class.
    fn class_atom(&mut self) -> Result<Option<Escaped>, Refusal> {
        let atom = match self.rest.next().ok_or(Refusal::Invalid)? {
            ']' => return Ok(None),
            '\\' if self.eat('b') => Escaped::Character(0x08),
            '\\' if self.eat('-') => Escaped::Character('-'.into()),
            '\\' => self.escape()?,
            other => Escaped::Character(other.into()),
        };
        Ok(Some(atom))
    }

    /// An atom with the quantifier that follows it, if one does.
    fn quantified(&mut self, atom: Hir) -> Result<Hir, Refusal> {
        let (min, max) = match self.peek() {
            Some('*') => (0, None),
            Some('+') => (1, None),
            Some('?') => (0, Some(1)),
            Some('{') => {
                self.rest.next();
                let digit = |parser: &Self| matches!(parser.peek(), Some('0'..='9'));
                if !digit(self) {
                    return Err(Refusal::Invalid);
                }
                let min = self.number();
                let max = match self.peek() {
                    Some('}') => Some(min),
                    Some(',') => {
                        self.rest.next();
                        digit(self).then(|| self.number())
                    }
                    _ => return Err(Refusal::Invalid),
                };
                if self.peek() != Some('}') || max.is_some_and(|max| max < min) {
                    return Err(Refusal::Invalid);
                }
                (min, max)
            }
            _ => return Ok(atom),
        };
        self.rest.next();
        // A quantifier that takes as little as it can says the same of which strings match.
        self.eat('?');
        let (Ok(min), Ok(max)) = (u32::try_from(min), max.map(u32::try_from).transpose()) else {
            self.not_modelled = true;
            return Ok(Hir::empty());
        };
        Ok(Hir::repetition(Repetition {
            min,
            max,
            greedy: true,
            sub: Box::new(atom),
        }))
    }
}

/// The digits that `\d` matches.
const DIGITS: [(char, char); 1] = [('0', '9')];

/// The characters that `\w` matches.
const WORD: [(char, char); 4] = [('0', '9'), ('A', 'Z'), ('_', '_'), ('a', 'z')];

/// The characters that `\s` matches: the white space and the line terminators of ECMA-262.
/// Those from U+00A0 on are the byte order mark, the two separators of lines and of
/// paragraphs, and the characters of the category `Space_Separator`.
const SPACE: [(char, char); 10] = [
    ('\t', '\r'),
    (' ', ' '),
    ('\u{a0}', '\u{a0}'),
    ('\u{1680}', '\u{1680}'),
    ('\u{2000}', '\u{200a}'),
    ('\u{2028}', '\u{2029}'),
    ('\u{202f}', '\u{202f}'),
    ('\u{205f}', '\u{205f}'),
    ('\u{3000}', '\u{3000}'),
    ('\u{feff}', '\u{feff}'),
];

fn one(character: char) -> ClassUnicodeRange {
    ClassUnicodeRange::new(character, character)
}

/// One character by its code point. A surrogate matches nothing.
fn character(code_point: u32) -> Hir {
    match char::from_u32(code_point) {
        Some(character) => Hir::literal(character.encode_utf8(&mut [0; 4]).as_bytes()),
        None => Hir::fail(),
    }
}

/// Adds the code points from the first to the last to a set, but for the surrogates.
fn add(set: &mut ClassUnicode, first: u32, last: u32) {
    let (surrogates, after) = SURROGATES;
    for (first, last) in [(first, last.min(surrogates - 1)), (first.max(after), last)] {
        if let (Some(first), Some(last)) = (char::from_u32(first), char::from_u32(last))
            && first <= last
        {
            set.push(ClassUnicodeRange::new(first, last));
        }
    }
}

#[cfg(test)]
pub(super) mod tests {
    use oxc_allocator::Allocator;
    use oxc_regular_expression::ast::{BoundaryAssertion, BoundaryAssertionKind};
    use oxc_regular_expression::visit::Visit;
    use oxc_regular_expression::{LiteralParser, Options};

    use super::super::dfa::Dfa;
    use super::super::pattern;
    use super::*;
    use crate::context::Budget;
    use crate::testing::Random;

    fn of(pattern: &str) -> Dfa {
        let read = read(pattern).unwrap_or_else(|refusal| panic!("{pattern:?} is {refusal:?}"));
        pattern::dfa(&read, &mut Budget::new(u64::MAX)).unwrap()
    }

    /// Whether `regress`, an engine for ECMA-262, finds a match of the pattern in the string.
    fn matches(pattern: &str, string: &str) -> bool {
        let read = regress::Regex::with_flags(pattern, "u");
        let read = read.unwrap_or_else(|error| panic!("{pattern:?}: {error}"));
        read.find(string).is_some()
    }

    /// Holds the DFA of each pattern against `regress` on each string.
    fn agree(patterns: &[&str], strings: &[&str]) {
        for pattern in patterns {
            let dfa = of(pattern);
            for string in strings {
                let expected = matches(pattern, string);
                assert_eq!(dfa.accepts(string), expected, "{pattern:?} on {string:?}");
            }
        }
    }

    /// Whether a pattern is one of ECMA-262 with the `u` flag, by the parser of `oxc`.
    ///
    /// That parser also takes `\A`, `\z` and `\Z` for the two ends of the string, which a
    /// proposal has and the standard has not.
    pub fn valid(pattern: &str) -> bool {
        struct Proposed(bool);
        impl Visit<'_> for Proposed {
            fn visit_boundary_assertion(&mut self, assertion: &BoundaryAssertion) {
                self.0 |= !matches!(
                    assertion.kind,
                    BoundaryAssertionKind::Start
                        | BoundaryAssertionKind::End
                        | BoundaryAssertionKind::Boundary
                        | BoundaryAssertionKind::NegativeBoundary
                );
            }
        }
        let allocator = Allocator::default();
        let parser = LiteralParser::new(&allocator, pattern, Some("u"), Options::default());
        parser.parse().is_ok_and(|read| {
            let mut proposed = Proposed(false);
            proposed.visit_pattern(&read);
            !proposed.0
        })
    }

    const STRINGS: [&str; 34] = [
        "",
        "3",
        "٣",
        "a",
        "B",
        "é",
        "_",
        "-",
        " ",
        "\t",
        "\n",
        "\r",
        "\u{b}",
        "\u{85}",
        "\u{a0}",
        "\u{2028}",
        "\u{2029}",
        "\u{feff}",
        "\u{3000}",
        "ß",
        "K",
        "\u{212a}",
        "\u{d7ff}",
        "\u{e000}",
        "\u{10ffff}",
        "\0",
        "λ",
        "😀",
        "ab",
        "a3",
        "a\nb",
        "😀😀",
        "a b",
        "/",
    ];

    #[test]
    fn a_pattern_matches_anywhere_in_the_string() {
        let strings = [
            "", "a", "b", "ab", "ba", "aab", "abb", "xabx", "ax", "xb", "abab",
        ];
        agree(
            &[
                "",
                "a",
                "ab",
                "^a",
                "a$",
                "^ab$",
                "^$",
                "a|b",
                "^a|b$",
                "(^a|b)b",
                "a(b$|x)",
                "a*",
                "^a*$",
                "^a+b?$",
                "a{2}",
                "^(ab){1,2}$",
                "^a{0,2}$",
                "^(a|b){2,}$",
                "a^b",
                "a$b",
                "$^",
                "^^a$$",
                "(^)*a",
                "($)+",
                "^(a*)*$",
                "(a|)+b",
                "^[^a]*$",
                "^.$",
                "^(?:a|ab)(?:b|)$",
                "a{0}",
                "^a{0}$",
                "(?:){5}",
                "^(?:^a|b)+$",
                "^a+?b*?$",
                "^(?<first>a)(?<second>b)?$",
                "a||b",
                "()",
            ],
            &strings,
        );
    }

    #[test]
    fn a_class_is_the_characters_that_ecma_262_gives_it() {
        agree(
            &[
                r"^\d$",
                r"^\D$",
                r"^\w+$",
                r"^\W$",
                r"^\s$",
                r"^\S*$",
                "^.$",
                "^.*$",
                r"^[\d-]+$",
                r"^[\w.]$",
                r"^[^\s\S]$",
                r"^[^]$",
                r"[]",
                r"^[a-z]+$",
                r"^[^a]$",
                r"^[\b]$",
                r"^[\-a]$",
                r"^[--a]$",
                r"^[a-]$",
                r"^\p{L}\p{N}$",
                r"^\p{Script=Greek}+$",
                r"^\p{scx=Grek}+$",
                r"^\P{Lu}$",
                r"^[\p{Lu}\d]$",
                r"^[^\p{L}]$",
                r"^\p{White_Space}$",
                r"^\p{Any}$",
                r"^\p{ASCII}$",
                r"^\p{Zl}$",
                r"^é$",
                r"^\u{e9}$",
                r"^\u{1F600}$",
                r"^😀$",
                r"^[😀-🙏]+$",
                "^[\u{d7ff}-\u{e000}]$",
                r"^[퟿-]$",
                r"^\x61\cJ?\0?$",
                r"^[\x00-\x1f]$",
                r"^\/$",
                r"^[\/]$",
                r"^[.*+?^$|(){}\[\]\\]$",
                r"^\t|\n|\v|\f|\r$",
            ],
            &STRINGS,
        );
    }

    #[test]
    fn the_classes_are_those_of_ascii_and_a_character_is_a_code_point() {
        let same = [
            (r"^\d$", "^[0-9]$"),
            (r"^\w$", "^[A-Za-z0-9_]$"),
            (r"^\W$", "^[^A-Za-z0-9_]$"),
            (
                r"^\s$",
                "^[\t\n\u{b}\u{c}\r \u{a0}\u{1680}\u{2000}-\u{200a}\u{2028}\u{2029}\u{202f}\u{205f}\u{3000}\u{feff}]$",
            ),
            ("^.$", "^[^\n\r\u{2028}\u{2029}]$"),
            ("^[^]$", r"^[\s\S]$"),
            ("[]", "a^"),
            (r"^\u{1F600}$", "^😀$"),
            (r"^😀$", "^😀$"),
            ("^a$", "^(a)$"),
            ("^a$", "^(?<name>a)$"),
            ("^a*$", "^a*?$"),
            ("^(a|b)$", "^[ab]$"),
        ];
        for (one, other) in same {
            assert_eq!(of(one), of(other), "{one:?} and {other:?}");
        }
        // The white space of `\s` is the category `Space_Separator` and nine more.
        let separators = names::characters(None, "Zs").unwrap();
        let mut space =
            ClassUnicode::new(SPACE.map(|(first, last)| ClassUnicodeRange::new(first, last)));
        let others = [
            '\t', '\n', '\u{b}', '\u{c}', '\r', '\u{2028}', '\u{2029}', '\u{feff}',
        ];
        space.difference(&ClassUnicode::new(others.map(one)));
        assert_eq!(space, separators);
        // A string holds no surrogate, so one in a pattern matches nothing.
        assert!(of(r"\uD83D").is_empty());
        assert_eq!(of(r"^a\uD83D?$"), of("^a$"));
        assert!(of(r"[\uD800-\uDFFF]").is_empty());
        assert_eq!(of(r"^[^\uD800-\uDFFF]$"), of("^[^]$"));
        assert_eq!(of(r"^[\u{D7FF}-\u{E000}]$"), of("^[\u{d7ff}\u{e000}]$"));
    }

    #[test]
    fn what_the_u_flag_forbids_is_no_pattern() {
        let invalid = [
            // An escape of a character that needs none.
            r"\-",
            r"\_",
            r"\:",
            r"\%",
            r"\ ",
            r"\a",
            r"[\_]",
            r"[\,]",
            // A character of the syntax that stands alone.
            "{",
            "}",
            "]",
            "a{",
            "a{1",
            "a{1,",
            "a{,2}",
            "a{ 1}",
            "(",
            ")",
            "(?",
            "[a",
            // A quantifier with nothing to repeat, or with an assertion.
            "*",
            "a**",
            "^*",
            "$+",
            r"\b?",
            "(?=a)*",
            "(?<!a){2}",
            "a{2,1}",
            // Escapes that are cut short or out of range.
            r"\",
            r"\c",
            r"\c1",
            r"\x6",
            r"\u006",
            r"\u{}",
            r"\u{110000}",
            r"\u{61",
            r"\00",
            r"\07",
            r"\p",
            r"\pL",
            r"\p{L",
            r"\p{}",
            // Properties by a name that is not theirs.
            r"\p{greek}",
            r"\p{Greek}",
            r"\p{letter}",
            r"\p{Script=greek}",
            r"\p{sc=}",
            r"\p{Nonsense}",
            // Classes.
            r"[\d-a]",
            r"[a-\d]",
            r"[\w-/_]",
            "[b-a]",
            r"[\B]",
            r"[\1]",
            r"[\k<n>]",
            // Groups and what refers to them.
            r"\1",
            r"(a)\2",
            r"\k<n>",
            r"\k",
            r"(?<n>a)\k<m>",
            "(?<n>a)(?<n>b)",
            "(?<n>a(?<n>b))",
            "(?<1>a)",
            "(?<>a)",
            "(?<a-b>c)",
            "(?<n",
            // What other dialects have.
            "(?i)a",
            "(?P<n>a)",
            "(?#comment)",
            r"\A",
            r"\z",
            "[[:alpha:]]",
            "(?-:a)",
            "(?ii:a)",
            "(?i-i:a)",
            "(?x:a)",
        ];
        for pattern in invalid {
            assert_eq!(read(pattern), Err(Refusal::Invalid), "{pattern:?}");
            assert!(!valid(pattern), "{pattern:?}");
        }
    }

    #[test]
    fn what_is_not_modelled_is_refused_and_is_a_pattern_all_the_same() {
        let not_modelled = [
            r"a\b",
            r"\Ba",
            "a(?=b)",
            "(?!a)b",
            "(?<=a)b",
            "(?<!a)b",
            r"(a)\1",
            r"\1(a)",
            r"(?<n>a)\k<n>",
            r"\k<n>(?<n>a)",
            "(?i:a)",
            "(?s:.)",
            "(?m-i:^a)",
            "(?-s:.)",
            "a{4294967296}",
            r"\p{CWKCF}",
            r"\p{Script=Zzzz}",
        ];
        for pattern in not_modelled {
            assert_eq!(read(pattern), Err(Refusal::NotModelled), "{pattern:?}");
            assert!(valid(pattern), "{pattern:?}");
        }
        // A count of any size is one, though `oxc` takes none that 64 bits do not hold.
        let large = "a{1,99999999999999999999999999}";
        assert_eq!(read(large), Err(Refusal::NotModelled));
        assert_eq!(
            read("a{99999999999999999999999999,1}"),
            Err(Refusal::Invalid)
        );
        // A pattern that is both is no pattern.
        assert_eq!(read(r"a\b{"), Err(Refusal::Invalid));
        assert_eq!(read(r"(?=a)\_"), Err(Refusal::Invalid));
        assert_eq!(read(r"(?=a))"), Err(Refusal::Invalid));
    }

    #[test]
    fn a_name_of_a_group_is_an_identifier_and_stands_once_on_a_way() {
        for pattern in [
            "(?<a>x)",
            "(?<$_a1>x)",
            "(?<é>x)",
            r"(?<ab>x)",
            r"(?<\u{1d4d1}>x)",
            "(?<a\u{200d}>x)",
            // Two alternatives of one disjunction, at any depth.
            "(?<n>a)|(?<n>b)",
            "(?:(?<n>a)|(?<n>b))c",
            "((?<n>a)x|y(?<n>b))|(?<n>c)",
            r"(?<n>a)|(?<n>b)\k<n>",
        ] {
            assert_ne!(read(pattern), Err(Refusal::Invalid), "{pattern:?}");
            assert!(valid(pattern), "{pattern:?}");
        }
        for pattern in [
            "(?<1a>x)",
            "(?<a b>x)",
            "(?<\u{200d}a>x)",
            r"(?<1>x)",
            r"(?<\x61>x)",
            "(?<n>a)(?<n>b)",
            "(?<n>a)|(?<n>b)(?<n>c)",
            "(?:(?<n>a)|b)(?<n>c)",
        ] {
            assert_eq!(read(pattern), Err(Refusal::Invalid), "{pattern:?}");
            assert!(!valid(pattern), "{pattern:?}");
        }
        // A name that is given more often than is looked at is not modelled.
        let often = |times: usize| vec!["(?<n>a)"; times].join("|");
        assert!(read(&often(MOST_OF_A_NAME)).is_ok());
        assert_eq!(read(&often(MOST_OF_A_NAME + 1)), Err(Refusal::NotModelled));
    }

    #[test]
    fn groups_go_so_deep_and_no_deeper() {
        let nested = |depth: usize| format!("{}a{}", "(".repeat(depth), ")".repeat(depth));
        let deepest = usize::try_from(DEEPEST).unwrap();
        assert_eq!(of(&nested(deepest)), of("a"));
        assert_eq!(read(&nested(deepest + 1)), Err(Refusal::NotModelled));
        // A pattern of any length is read without the stack growing with it.
        let long = "(a|b)*c?".repeat(20_000);
        assert!(read(&long).is_ok());
    }

    /// What a random pattern is made of: atoms of ECMA-262 that are modelled, some that are
    /// not, and some that are no pattern.
    const ATOMS: [&str; 104] = [
        "a",
        "a",
        "b",
        "b",
        "-",
        "7",
        "é",
        "😀",
        ".",
        "/",
        ",",
        ":",
        " ",
        "_",
        r"\d",
        r"\D",
        r"\w",
        r"\W",
        r"\s",
        r"\S",
        r"\n",
        r"\t",
        r"\v",
        r"\f",
        r"\r",
        r"\0",
        r"\cJ",
        r"\x61",
        r"a",
        r"\u{1F600}",
        r"😀",
        r"\uD83D",
        r"\uDE00",
        r"\/",
        r"\.",
        r"\$",
        r"\\",
        r"\[",
        r"\]",
        r"\{",
        r"\}",
        r"\p{L}",
        r"\P{Lu}",
        r"\p{Script=Greek}",
        r"\p{scx=Latn}",
        r"\p{ASCII}",
        r"\p{Nd}",
        "[ab]",
        "[^a]",
        "[a-c]",
        "[]",
        "[^]",
        r"[\d-]",
        r"[a\-b]",
        r"[\b]",
        r"[\w.]",
        "[--a]",
        "[😀-😂]",
        r"[\u{1F600}-\u{1F602}]",
        "[a-]",
        "[-a]",
        r"[^\s\S]",
        "[{}]",
        "[(]",
        "^",
        "$",
        // Valid and not modelled.
        r"\b",
        r"\B",
        "(?=a)",
        "(?!a)",
        "(?<=a)",
        "(?<!a)",
        r"\1",
        r"\k<x>",
        "(?i:a)",
        // No pattern, most of them. Some are one after a group or a name that they refer to.
        r"\-",
        r"\_",
        r"\a",
        r"\:",
        "{",
        "}",
        "]",
        "a{",
        r"\00",
        r"\c1",
        r"\x6",
        r"\u006",
        r"\u{110000}",
        r"\p{greek}",
        r"\p{Greek}",
        r"\pL",
        r"[\d-a]",
        r"[a-\d]",
        "[b-a]",
        "[a",
        r"[\B]",
        r"[\1]",
        "(?i)",
        "(?",
        "*",
        "(",
        ")",
        r"\A",
        r"\z",
    ];

    fn random_pattern(random: &mut Random, depth: usize) -> String {
        if depth == 0 || random.chance(25) {
            return random.pick(&ATOMS).to_owned();
        }
        let below = |random: &mut Random| random_pattern(random, depth - 1);
        match random.below(12) {
            0..=2 => format!("{}{}", below(random), below(random)),
            3 => format!("{}|{}", below(random), below(random)),
            4 => format!("({})", below(random)),
            5 => format!("(?:{}|{})", below(random), below(random)),
            6 => format!("(?<{}>{})", random.pick(&["x", "y"]), below(random)),
            7 => format!("(?:{})*", below(random)),
            8 => format!("(?:{})+?", below(random)),
            9 => format!("{}?", below(random)),
            10 => format!(
                "{}{{{},{}}}",
                below(random),
                random.below(2),
                random.below(3)
            ),
            _ => format!("{}{{{}}}", below(random), random.below(3)),
        }
    }

    #[test]
    fn the_parser_takes_the_patterns_that_oxc_takes() {
        let random = &mut Random(5);
        let (mut taken, mut refused) = (0, 0);
        for _ in 0..20_000 {
            let pattern = random_pattern(random, 3);
            let expected = valid(&pattern);
            assert_eq!(
                read(&pattern) != Err(Refusal::Invalid),
                expected,
                "{pattern:?}"
            );
            taken += usize::from(expected);
            refused += usize::from(!expected);
        }
        assert!(taken > 2_000 && refused > 2_000, "{taken} {refused}");
    }

    #[test]
    fn the_dfas_match_the_strings_that_regress_matches() {
        let characters = [
            "a", "b", "-", "7", "é", "😀", "😁", ".", "/", ",", ":", " ", "_", "\n", "\r", "\t",
            "\u{2028}", "\u{feff}", "\u{85}", "A", "α", "٣", "\0", "\u{8}", "\\", "[", "{", "$",
        ];
        let mut strings = vec![String::new()];
        for first in characters {
            strings.push(first.to_owned());
            strings.extend(characters.iter().map(|second| format!("{first}{second}")));
        }
        let random = &mut Random(6);
        let mut compared = 0;
        for _ in 0..3_000 {
            let pattern = random_pattern(random, 3);
            // `regress` finds no match where a surrogate that stands alone may be left out,
            // as in `a\uD83D?`, so such a pattern is not held against it.
            let alone = pattern.replace(r"\uD83D\uDE00", "");
            if alone.contains(r"\uD83D") || alone.contains(r"\uDE00") {
                continue;
            }
            let Ok(read) = read(&pattern) else {
                continue;
            };
            let dfa = pattern::dfa(&read, &mut Budget::new(u64::MAX)).unwrap();
            for string in &strings {
                let expected = matches(&pattern, string);
                assert_eq!(dfa.accepts(string), expected, "{pattern:?} on {string:?}");
            }
            compared += 1;
        }
        assert!(compared > 300, "{compared}");
    }

    #[test]
    fn the_characters_of_a_property_are_those_that_regress_gives_it() {
        // Every 251st code point, which is one of every block of 256 in turn. The tables of
        // the two crates are of two versions of Unicode, so a character that the older one
        // does not have is left out.
        let unassigned = of(r"^\p{Cn}$");
        let sample = (0..=u32::from(char::MAX))
            .step_by(251)
            .filter_map(char::from_u32);
        let sample: Vec<char> = sample
            .filter(|character| !unassigned.accepts(&character.to_string()))
            .collect();
        for pattern in [
            r"\p{L}",
            r"\p{Lu}",
            r"\p{gc=Nd}",
            r"\p{General_Category=Punctuation}",
            r"\p{Zs}",
            r"\p{Script=Latin}",
            r"\p{sc=Grek}",
            r"\p{Script_Extensions=Arabic}",
            r"\p{scx=Hira}",
            r"\p{Alphabetic}",
            r"\p{Alpha}",
            r"\p{Lowercase}",
            r"\p{White_Space}",
            r"\p{space}",
            r"\p{ID_Start}",
            r"\p{IDC}",
            r"\p{Emoji}",
            r"\p{Hex_Digit}",
            r"\p{Any}",
            r"\p{ASCII}",
            r"\p{Assigned}",
            r"\P{L}",
            r"\P{Script=Cyrillic}",
        ] {
            let (dfa, anchored) = (of(&format!("^{pattern}$")), format!("^{pattern}$"));
            let mut differing = Vec::new();
            for character in &sample {
                let string = character.to_string();
                if dfa.accepts(&string) != matches(&anchored, &string) {
                    differing.push(*character);
                }
            }
            assert!(differing.is_empty(), "{pattern:?} on {differing:?}");
        }
    }
}
