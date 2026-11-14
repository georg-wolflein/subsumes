//! From a pattern to an automaton.
//!
//! A pattern is parsed by `regex-syntax`, the parser of the `regex` crate, so it means here
//! what it means there. It matches a string when it matches anywhere in the string: the
//! language of a pattern is every string that holds a match. `^` and `$` hold only at the two
//! ends of the string.
//!
//! The way is the usual one. The pattern becomes a machine that may be in several states at
//! once, and the automaton has a state for each set of them that a string can lead to.

use std::collections::HashMap;
use std::collections::hash_map::Entry;

use regex_syntax::hir::{Class, Hir, HirKind, Look};

use super::Unsupported;
use super::automaton::{Automaton, Classes, LAST, Place, cost, place};
use crate::context::{Budget, Exhausted};

/// Parses a pattern as the `regex` crate does.
///
/// # Errors
///
/// When that crate does not take the pattern, or the pattern asks for something that is
/// not modelled: where a word begins or ends, or a line.
pub(super) fn read(pattern: &str) -> Result<Hir, Unsupported> {
    let read = regex_syntax::Parser::new().parse(pattern);
    let read = read.map_err(|_| Unsupported)?;
    let mut pending = vec![&read];
    while let Some(part) = pending.pop() {
        let supported = match part.kind() {
            HirKind::Look(look) => matches!(look, Look::Start | Look::End),
            HirKind::Literal(literal) => std::str::from_utf8(&literal.0).is_ok(),
            // The parser lets a class of bytes through only where it is one of ASCII.
            HirKind::Class(Class::Bytes(class)) => class.is_ascii(),
            _ => true,
        };
        if !supported {
            return Err(Unsupported);
        }
        pending.extend(part.kind().subs());
    }
    Ok(read)
}

/// What a state of the machine does.
#[derive(Debug)]
enum Step {
    /// Goes on to each of these states without a character.
    Free(Vec<u32>),
    /// Reads a character of a set and goes on.
    Read { set: u32, then: u32 },
    /// Goes on where the string begins.
    Start(u32),
    /// Goes on where the string ends.
    End(u32),
    /// The pattern has matched.
    Match,
}

/// A set of characters, as ranges of places that neither meet nor overlap.
type Set = Vec<(Place, Place)>;

#[derive(Debug, Default)]
struct Machine {
    steps: Vec<Step>,
    /// The sets of characters that the steps read. A set is kept once.
    sets: Vec<Set>,
    ids: HashMap<Set, u32>,
}

impl Machine {
    fn add(&mut self, step: Step, budget: &mut Budget) -> Result<u32, Exhausted> {
        budget.charge(1)?;
        self.steps.push(step);
        Ok(u32::try_from(self.steps.len() - 1).expect("fewer than 2^32 states"))
    }

    fn set(&mut self, set: Set) -> u32 {
        let next = u32::try_from(self.sets.len()).expect("fewer than 2^32 sets");
        *self.ids.entry(set).or_insert_with_key(|set| {
            self.sets.push(set.clone());
            next
        })
    }

    /// Adds the states that match a part of the pattern and then go on to `then`, and
    /// returns the first of them.
    ///
    /// The parser lets parts be nested 250 deep at most, which bounds how deep this goes.
    fn build(&mut self, part: &Hir, then: u32, budget: &mut Budget) -> Result<u32, Exhausted> {
        match part.kind() {
            HirKind::Empty => Ok(then),
            HirKind::Literal(literal) => {
                let text = std::str::from_utf8(&literal.0).expect("the pattern was read");
                let mut then = then;
                for character in text.chars().rev() {
                    let at = place(character);
                    let set = self.set(vec![(at, at)]);
                    then = self.add(Step::Read { set, then }, budget)?;
                }
                Ok(then)
            }
            HirKind::Class(class) => {
                let set = match class {
                    Class::Unicode(class) => {
                        let ranges = class.ranges().iter();
                        ranges
                            .map(|range| (place(range.start()), place(range.end())))
                            .collect()
                    }
                    Class::Bytes(class) => {
                        let ranges = class.ranges().iter();
                        ranges
                            .map(|range| (range.start().into(), range.end().into()))
                            .collect()
                    }
                };
                let set = self.set(set);
                self.add(Step::Read { set, then }, budget)
            }
            HirKind::Look(Look::Start) => self.add(Step::Start(then), budget),
            HirKind::Look(Look::End) => self.add(Step::End(then), budget),
            HirKind::Look(other) => unreachable!("{other:?} was refused when the pattern was read"),
            HirKind::Capture(capture) => self.build(&capture.sub, then, budget),
            HirKind::Concat(parts) => {
                let mut then = then;
                for part in parts.iter().rev() {
                    then = self.build(part, then, budget)?;
                }
                Ok(then)
            }
            HirKind::Alternation(parts) => {
                let mut firsts = Vec::with_capacity(parts.len());
                for part in parts {
                    firsts.push(self.build(part, then, budget)?);
                }
                self.add(Step::Free(firsts), budget)
            }
            HirKind::Repetition(repetition) => {
                let mut first = match repetition.max {
                    // Any number of times: a state that goes round once more or goes on.
                    None => {
                        let again = self.add(Step::Free(Vec::new()), budget)?;
                        let round = self.build(&repetition.sub, again, budget)?;
                        self.steps[again as usize] = Step::Free(vec![round, then]);
                        again
                    }
                    // Up to so many times more than it must: each time it may go on instead.
                    Some(max) => {
                        let mut first = then;
                        for _ in repetition.min..max {
                            let once = self.build(&repetition.sub, first, budget)?;
                            first = self.add(Step::Free(vec![once, then]), budget)?;
                        }
                        first
                    }
                };
                for _ in 0..repetition.min {
                    // A step for each time, also where the part adds no state.
                    budget.charge(1)?;
                    first = self.build(&repetition.sub, first, budget)?;
                }
                Ok(first)
            }
        }
    }

    /// The characters in classes that no set tells apart, and for each set its classes.
    fn classes(&self) -> (Classes, Vec<Vec<u32>>) {
        // Where a set begins to hold the characters, and where it ceases to.
        let mut turns: Vec<(Place, usize)> = Vec::new();
        for (set, ranges) in self.sets.iter().enumerate() {
            for (first, last) in ranges {
                turns.push((*first, set));
                if *last < LAST {
                    turns.push((*last + 1, set));
                }
            }
        }
        turns.sort_unstable();
        // The sets that hold the characters of a run, as bits, are what makes its class.
        let mut holding = vec![0_u64; self.sets.len().div_ceil(64)];
        let mut ids: HashMap<Vec<u64>, u32> = HashMap::new();
        let mut held: Vec<Vec<u32>> = vec![Vec::new(); self.sets.len()];
        let mut runs = Vec::new();
        let (mut at, mut turn) = (0, 0);
        loop {
            while turns.get(turn).is_some_and(|(place, _)| *place == at) {
                let set = turns[turn].1;
                holding[set / 64] ^= 1 << (set % 64);
                turn += 1;
            }
            let next = u32::try_from(ids.len()).expect("fewer than 2^32 classes");
            let class = *ids.entry(holding.clone()).or_insert_with(|| {
                for (set, held) in held.iter_mut().enumerate() {
                    if holding[set / 64] >> (set % 64) & 1 == 1 {
                        held.push(next);
                    }
                }
                next
            });
            runs.push((at, class));
            match turns.get(turn) {
                Some((place, _)) => at = *place,
                None => break,
            }
        }
        (Classes::new(runs), held)
    }

    /// The states that are reached from some states without a character: those that read
    /// one, and whether the pattern has matched.
    ///
    /// `at_start` says that no character came before. A state that was reached by way of
    /// `$` holds only if no character follows, so it reads none.
    ///
    /// The search costs a step, and one more for every eight states that it passes.
    fn reach(
        &self,
        from: &[u32],
        at_start: bool,
        marks: &mut Marks,
        budget: &mut Budget,
    ) -> Result<Reached, Exhausted> {
        marks.round += 1;
        let mut reached = Reached::default();
        let mut pending: Vec<(u32, bool)> = from.iter().map(|state| (*state, false)).collect();
        let mut passed = 0_u64;
        while let Some((state, at_end)) = pending.pop() {
            let mark = &mut marks.seen[state as usize * 2 + usize::from(at_end)];
            if std::mem::replace(mark, marks.round) == marks.round {
                continue;
            }
            passed += 1;
            if passed.is_multiple_of(8) {
                budget.charge(1)?;
            }
            match &self.steps[state as usize] {
                Step::Free(then) => pending.extend(then.iter().map(|then| (*then, at_end))),
                Step::Read { .. } if at_end => {}
                Step::Read { .. } => reached.reading.push(state),
                Step::Start(then) if at_start => pending.push((*then, at_end)),
                Step::Start(_) => {}
                Step::End(then) => pending.push((*then, true)),
                Step::Match if at_end => reached.matched_at_end = true,
                // Whatever follows a match, the string holds one.
                Step::Match => return Ok(Reached::MATCHED),
            }
        }
        budget.charge(1)?;
        reached.reading.sort_unstable();
        Ok(reached)
    }
}

/// Which states were seen in the search at hand.
struct Marks {
    seen: Vec<u32>,
    round: u32,
}

/// The states of the automaton that were found so far, each numbered once.
#[derive(Default)]
struct Found {
    states: Vec<Reached>,
    ids: HashMap<Reached, u32>,
}

impl Found {
    /// The number of a state, which costs steps if the state is new: one, and more where
    /// there are many classes of characters to say something about. `width` is how many.
    fn number(
        &mut self,
        reached: Reached,
        width: usize,
        budget: &mut Budget,
    ) -> Result<u32, Exhausted> {
        let id = u32::try_from(self.states.len()).expect("fewer than 2^32 states");
        match self.ids.entry(reached) {
            Entry::Occupied(known) => Ok(*known.get()),
            Entry::Vacant(new) => {
                budget.charge(cost(0, width))?;
                self.states.push(new.key().clone());
                Ok(*new.insert(id))
            }
        }
    }
}

/// A state of the automaton: the states that the machine may be in after some string.
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
struct Reached {
    /// The states that read a character next.
    reading: Vec<u32>,
    /// The pattern has matched if the string ends here.
    matched_at_end: bool,
    /// The pattern has matched, whatever follows.
    matched: bool,
}

impl Reached {
    const MATCHED: Self = Self {
        reading: Vec::new(),
        matched_at_end: false,
        matched: true,
    };
}

/// The automaton of every string that holds a match of the pattern.
///
/// # Errors
///
/// When the budget does not cover the states of the machine and of the automaton.
pub(super) fn automaton(pattern: &Hir, budget: &mut Budget) -> Result<Automaton, Exhausted> {
    let mut machine = Machine::default();
    let matched = machine.add(Step::Match, budget)?;
    let first = machine.build(pattern, matched, budget)?;
    let (classes, held) = machine.classes();
    let (next, accepts) = determinized(&machine, first, &classes, &held, budget)?;
    Ok(Automaton::canonical(&classes, &next, &accepts))
}

/// The states of the automaton of a machine: where each class leads from each, and which
/// accept.
fn determinized(
    machine: &Machine,
    first: u32,
    classes: &Classes,
    held: &[Vec<u32>],
    budget: &mut Budget,
) -> Result<(Vec<u32>, Vec<bool>), Exhausted> {
    let width = classes.count();
    let mut marks = Marks {
        seen: vec![0; machine.steps.len() * 2],
        round: 0,
    };

    let mut found = Found::default();
    let reached = machine.reach(&[first], true, &mut marks, budget)?;
    found.number(reached, width, budget)?;
    let (mut next, mut accepts) = (Vec::new(), Vec::new());
    let mut at = 0;
    // Where each class leads from the state at hand, by the states that read it.
    let mut read: Vec<Vec<u32>> = vec![Vec::new(); width];
    let mut led: HashMap<Vec<u32>, u32> = HashMap::new();
    // The state after a character that nothing reads: a match may still begin after it.
    let mut afresh = None;
    while let Some(reached) = found.states.get(at).cloned() {
        accepts.push(reached.matched || reached.matched_at_end);
        if reached.matched {
            next.extend(std::iter::repeat_n(at as u32, width));
            at += 1;
            continue;
        }
        for from in &reached.reading {
            let Step::Read { set, then } = &machine.steps[*from as usize] else {
                unreachable!("only a state that reads is kept");
            };
            for class in &held[*set as usize] {
                read[*class as usize].push(*then);
            }
        }
        led.clear();
        for then in &mut read {
            let mut reach = |then: &[u32]| {
                let reached = machine.reach(then, false, &mut marks, budget)?;
                found.number(reached, width, budget)
            };
            // A match may begin at every character, so the first state is always among them.
            let to = if then.is_empty() {
                match afresh {
                    Some(to) => to,
                    None => *afresh.insert(reach(&[first])?),
                }
            } else {
                then.push(first);
                let then = std::mem::take(then);
                match led.get(&then) {
                    Some(to) => *to,
                    None => {
                        let to = reach(&then)?;
                        led.insert(then, to);
                        to
                    }
                }
            };
            next.push(to);
        }
        at += 1;
    }
    Ok((next, accepts))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn of(pattern: &str) -> Automaton {
        let read = read(pattern).unwrap_or_else(|_| panic!("{pattern:?} is not supported"));
        automaton(&read, &mut Budget::new(u64::MAX)).unwrap()
    }

    /// Holds the automaton of each pattern against the `regex` crate on each string.
    fn agree(patterns: &[&str], strings: &[&str]) {
        for pattern in patterns {
            let (automaton, expected) = (of(pattern), regex::Regex::new(pattern).unwrap());
            for string in strings {
                assert_eq!(
                    automaton.accepts(string),
                    expected.is_match(string),
                    "{pattern:?} on {string:?}"
                );
            }
        }
    }

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
            ],
            &strings,
        );
    }

    #[test]
    fn a_class_is_the_characters_that_the_regex_crate_reads() {
        let strings = [
            "",
            "3",
            "٣",
            "a",
            "B",
            "é",
            "_",
            "-",
            " ",
            "\n",
            "\r",
            "\u{85}",
            "\u{2028}",
            "ß",
            "ẞ",
            "K",
            "\u{212a}",
            "\u{d7ff}",
            "\u{e000}",
            "\u{10ffff}",
            "\0",
            "λ",
            "ab",
            "a3",
            "ss",
            "SS",
        ];
        agree(
            &[
                r"^\d$",
                r"^\D$",
                r"^\w+$",
                r"^\W$",
                r"^\s$",
                r"^\S*$",
                "^.$",
                "(?s)^.$",
                r"^[\d-]+$",
                r"^[a-z&&[^b]]$",
                r"^[\w--\d]$",
                r"^[[:alpha:]]$",
                r"[^\s\S]",
                r"\P{any}",
                r"^\p{Greek}+$",
                "(?i)^k$",
                "(?i)^straße$",
                "(?i)^SS$",
                r"^\x{10FFFF}$",
                "^[\u{d7ff}-\u{e000}]$",
                r"^(?-u:[a-z])+$",
                r"^(?-u:\w)$",
                r"^[^a]$",
                r"^\pL\pN$",
                "(?x) ^ a 3 $ # and no more",
            ],
            &strings,
        );
    }

    #[test]
    fn what_is_not_modelled_is_refused() {
        // A place between two characters that is not one of the two ends of the string.
        for pattern in [
            r"a\b",
            r"\Ba",
            "(?m)^a",
            "(?m)a$",
            r"\b{start}a",
            r"a\b{end}",
        ] {
            assert!(read(pattern).is_err(), "{pattern:?}");
            assert!(regex::Regex::new(pattern).is_ok(), "{pattern:?}");
        }
        // What the `regex` crate does not take either.
        for pattern in ["a(?=b)", r"(a)\1", "(", "a{2,1}", r"(?-u:\xff)", r"\cC"] {
            assert!(read(pattern).is_err(), "{pattern:?}");
            assert!(regex::Regex::new(pattern).is_err(), "{pattern:?}");
        }
        // `\A` and `\z` are the two ends under other names.
        assert_eq!(of(r"\Aa\z"), of("^a$"));
    }

    #[test]
    fn patterns_of_one_language_have_one_automaton() {
        let same = [
            ("^a$", "^(?:a)$"),
            ("(?s)a", "(?s)^.*a.*$"),
            ("^(a|b)$", "^[ab]$"),
            ("^a+$", "^aa*$"),
            ("^(ab)*$", "^(?:(?:ab)+)?$"),
            ("", "^"),
            ("a^b", r"\P{any}"),
            ("^[a-c][a-c]$", "^[a-c]{2}$"),
            ("x|^$", "^$|x"),
        ];
        for (one, other) in same {
            assert_eq!(of(one), of(other), "{one:?} and {other:?}");
        }
        assert_ne!(of("^a$"), of("a"));
        assert_ne!(of("^a*$"), of("^a+$"));
        // Three states: before the letter, after it, and after anything else.
        assert_eq!(of("^a$").states(), 3);
        assert_eq!(of("").states(), 1);
        assert!(of("").is_everything());
        assert!(of("a^").is_empty());
    }

    #[test]
    fn the_states_cost_steps() {
        let spent = |pattern: &str| {
            let mut budget = Budget::new(u64::MAX);
            automaton(&read(pattern).unwrap(), &mut budget).unwrap();
            budget.spent()
        };
        assert!(spent("^a{100}$") > 200);
        assert!(spent("^a{100}$") < 1_000);
        // Each repetition in a repetition multiplies the states, and the budget ends that.
        let nested = read("^((a{100}){100}){100}$").unwrap();
        let mut budget = Budget::new(100_000);
        assert_eq!(automaton(&nested, &mut budget), Err(Exhausted));
    }
}
