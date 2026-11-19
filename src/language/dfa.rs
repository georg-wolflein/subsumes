//! DFAs: deterministic finite automata, which read a string character by character.
//!
//! A DFA here is complete: every state says where each character leads. It is kept in one
//! shape only, the minimal DFA of its language, with its states and its classes of characters
//! numbered in one fixed way. So two DFAs are equal exactly when their languages are, and the
//! complement of one is the same DFA with the other states accepting.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::rc::Rc;

use super::{Lengths, Parts};
use crate::context::{Budget, Exhausted};

/// A character by its place among the Unicode scalar values. The surrogates are no scalar
/// values and are left out, so the places run from 0 to [`LAST`] without a gap.
pub(super) type Place = u32;

/// The place of U+10FFFF.
pub(super) const LAST: Place = 0x10_FFFF - 0x800;

/// How many characters there are.
pub(super) const CHARACTERS: u128 = LAST as u128 + 1;

pub(super) fn place(character: char) -> Place {
    let scalar = u32::from(character);
    if scalar < 0xD800 {
        scalar
    } else {
        scalar - 0x800
    }
}

pub(super) fn character(place: Place) -> char {
    let scalar = if place < 0xD800 { place } else { place + 0x800 };
    char::from_u32(scalar).expect("a place up to LAST is a scalar value")
}

/// How early a character is taken for a word that is shown to somebody: letters first, then
/// digits, then what else of ASCII is printed, then the rest.
pub(super) fn plainness(character: char) -> u32 {
    match character {
        'a'..='z' => u32::from(character) - u32::from('a'),
        '0'..='9' => 26 + u32::from(character) - u32::from('0'),
        'A'..='Z' => 36 + u32::from(character) - u32::from('A'),
        ' '..='~' => 62 + u32::from(character),
        // Control characters come last of all.
        '\0'..='\u{9f}' => u32::MAX,
        other => 200 + u32::from(other),
    }
}

/// The steps that a new state costs: one, and more where it has much to write down. A state
/// is written down as where each class of characters leads, and that is worked out from its
/// members where it stands for several states of an NFA.
pub(super) fn cost(members: usize, classes: usize) -> u64 {
    1 + ((members + classes) / 4) as u64
}

/// The characters in classes: those of one class are alike to a DFA, which says where
/// each class leads and not where each character does.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Classes {
    /// The place at which each run of characters of one class begins, from 0 upwards, and
    /// the class of the run. Two runs that are next to each other are of two classes.
    runs: Vec<(Place, u32)>,
    count: u32,
}

impl Classes {
    /// The classes of a list of runs. Runs of one class that are next to each other become
    /// one run.
    pub fn new(runs: impl IntoIterator<Item = (Place, u32)>) -> Self {
        let mut merged: Vec<(Place, u32)> = Vec::new();
        let mut count = 0;
        for (first, class) in runs {
            count = count.max(class + 1);
            if merged.last().is_none_or(|last| last.1 != class) {
                merged.push((first, class));
            }
        }
        Self {
            runs: merged,
            count,
        }
    }

    pub fn count(&self) -> usize {
        self.count as usize
    }

    fn of(&self, at: Place) -> usize {
        let run = self.runs.partition_point(|run| run.0 <= at) - 1;
        self.runs[run].1 as usize
    }

    /// The classes that tell apart what either of two tells apart, and for each of them the
    /// class of the first and of the second that it is part of.
    fn common(&self, other: &Self) -> (Self, Vec<(u32, u32)>) {
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        let mut ids: HashMap<(u32, u32), u32> = HashMap::new();
        let mut runs = Vec::new();
        let (mut mine, mut theirs) = (0, 0);
        let mut at = 0;
        loop {
            let pair = (self.runs[mine].1, other.runs[theirs].1);
            let class = *ids.entry(pair).or_insert_with(|| {
                pairs.push(pair);
                u32::try_from(pairs.len() - 1).expect("fewer than 2^32 classes")
            });
            runs.push((at, class));
            // The next place at which one of the two begins a run.
            let after = |runs: &[(Place, u32)], run: usize| runs.get(run + 1).map(|run| run.0);
            at = match (after(&self.runs, mine), after(&other.runs, theirs)) {
                (None, None) => break,
                (Some(a), None) => a,
                (None, Some(b)) => b,
                (Some(a), Some(b)) => a.min(b),
            };
            mine += usize::from(after(&self.runs, mine) == Some(at));
            theirs += usize::from(after(&other.runs, theirs) == Some(at));
        }
        (Self::new(runs), pairs)
    }

    /// The classes that tell apart what any of a list tells apart, and for each of them
    /// the class of each of the list that it is part of: those of class 0 in the order of
    /// the list, then those of class 1, and so on. The list is not empty.
    ///
    /// # Errors
    ///
    /// When the budget does not cover a look at each of the list for every run.
    fn common_of(all: &[&Self], budget: &mut Budget) -> Result<(Self, Vec<u32>), Exhausted> {
        // The places at which one of them begins a run. Each begins one at 0.
        let starts = all.iter().flat_map(|classes| &classes.runs);
        let mut starts: Vec<Place> = starts.map(|run| run.0).collect();
        budget.charge((starts.len() / 8) as u64)?;
        starts.sort_unstable();
        starts.dedup();
        let mut ids: HashMap<Vec<u32>, u32> = HashMap::new();
        let mut parts: Vec<u32> = Vec::new();
        let mut runs = Vec::with_capacity(starts.len());
        // The run of each that the place at hand is in.
        let mut within = vec![0_usize; all.len()];
        for start in starts {
            budget.charge((all.len() / 8) as u64)?;
            let mut column = Vec::with_capacity(all.len());
            for (classes, run) in all.iter().zip(&mut within) {
                let after = classes.runs.get(*run + 1);
                *run += usize::from(after.is_some_and(|after| after.0 == start));
                column.push(classes.runs[*run].1);
            }
            let id = u32::try_from(ids.len()).expect("fewer than 2^32 classes");
            let class = *ids.entry(column).or_insert_with_key(|column| {
                parts.extend_from_slice(column);
                id
            });
            runs.push((start, class));
        }
        Ok((Self::new(runs), parts))
    }
}

/// A DFA in its one shape; see the top of this file.
#[derive(Debug, PartialEq, Eq, Hash)]
pub(super) struct Dfa {
    classes: Classes,
    /// Where each class leads from each state: the classes of state 0, then those of state
    /// 1, and so on. A word is read from state 0.
    next: Vec<u32>,
    accepts: Vec<bool>,
    /// The state from which no word is accepted, if there is one. There is at most one.
    dead: Option<u32>,
    /// A character of each class, the plainest that it has among those that were looked at.
    shown: Vec<char>,
}

impl Dfa {
    /// The DFA in its one shape, for one that is given in any: `next` and `accepts` as
    /// in the DFA itself, with every state reached from state 0.
    pub fn canonical(classes: &Classes, next: &[u32], accepts: &[bool]) -> Self {
        let width = classes.count();
        let blocks = blocks(width, next, accepts);
        // One state of each block stands for the block.
        let count = blocks.iter().max().map_or(0, |last| *last as usize + 1);
        let mut member = vec![u32::MAX; count];
        for (state, block) in blocks.iter().enumerate().rev() {
            member[*block as usize] = u32::try_from(state).expect("fewer than 2^32 states");
        }
        let leads = |block: usize, class: usize| {
            blocks[next[member[block] as usize * width + class] as usize]
        };

        // Classes that lead to the same state from every state are one class. They are
        // numbered in the order in which their first characters come.
        let mut columns: HashMap<Vec<u32>, u32> = HashMap::new();
        let mut merged = vec![u32::MAX; width];
        let mut kept = Vec::new();
        for (_, class) in &classes.runs {
            let class = *class as usize;
            if merged[class] != u32::MAX {
                continue;
            }
            let column: Vec<u32> = (0..count).map(|block| leads(block, class)).collect();
            let id = u32::try_from(columns.len()).expect("fewer than 2^32 classes");
            merged[class] = *columns.entry(column).or_insert_with(|| {
                kept.push(class);
                id
            });
        }
        let classes = Classes::new(
            classes
                .runs
                .iter()
                .map(|(first, class)| (*first, merged[*class as usize])),
        );

        // The states in the order in which they are first reached, class by class.
        let mut number = vec![u32::MAX; count];
        let mut order = vec![blocks[0] as usize];
        number[order[0]] = 0;
        let mut at = 0;
        while at < order.len() {
            for class in &kept {
                let to = leads(order[at], *class) as usize;
                if number[to] == u32::MAX {
                    number[to] = u32::try_from(order.len()).expect("fewer than 2^32 states");
                    order.push(to);
                }
            }
            at += 1;
        }
        let width = kept.len();
        let mut table = Vec::with_capacity(order.len() * width);
        for block in &order {
            table.extend(
                kept.iter()
                    .map(|class| number[leads(*block, *class) as usize]),
            );
        }
        let accepts: Vec<bool> = order
            .iter()
            .map(|block| accepts[member[*block] as usize])
            .collect();

        let shown = shown(&classes);
        Self {
            dead: dead(&table, &accepts),
            classes,
            next: table,
            accepts,
            shown,
        }
    }

    /// The DFA of a few words: it accepts these and no other.
    ///
    /// # Errors
    ///
    /// When the budget does not cover its states.
    pub fn of_words<'w>(
        words: impl IntoIterator<Item = &'w str> + Clone,
        budget: &mut Budget,
    ) -> Result<Self, Exhausted> {
        // Every character of the words is a class of its own, and class 0 is all the others.
        let characters: BTreeSet<char> = words.clone().into_iter().flat_map(str::chars).collect();
        let mut runs = vec![(0, 0)];
        let mut class_of = HashMap::new();
        for (index, character) in characters.iter().enumerate() {
            let class = u32::try_from(index + 1).expect("fewer than 2^32 characters");
            class_of.insert(*character, class as usize);
            let at = place(*character);
            if at == 0 {
                runs.clear();
            }
            runs.push((at, class));
            if at < LAST {
                runs.push((at + 1, 0));
            }
        }
        // A later character that follows at once takes the place of the run of the others.
        let mut kept: Vec<(Place, u32)> = Vec::new();
        for run in runs {
            if kept.last().is_some_and(|last| last.0 == run.0) {
                kept.pop();
            }
            kept.push(run);
        }
        let classes = Classes {
            runs: kept,
            count: u32::try_from(characters.len() + 1).expect("fewer than 2^32 characters"),
        };

        // A tree of the words, and state 1 for everything that is the beginning of none.
        let width = classes.count();
        let (mut next, mut accepts) = (vec![1; 2 * width], vec![false; 2]);
        for word in words {
            let mut state = 0;
            for character in word.chars() {
                let slot = state * width + class_of[&character];
                if next[slot] == 1 {
                    budget.charge(cost(0, width))?;
                    next[slot] = u32::try_from(accepts.len()).expect("fewer than 2^32 states");
                    next.resize(next.len() + width, 1);
                    accepts.push(false);
                }
                state = next[slot] as usize;
            }
            accepts[state] = true;
        }
        Ok(Self::canonical(&classes, &next, &accepts))
    }

    /// The DFA of every string that this one does not accept.
    pub fn complement(&self) -> Self {
        let accepts: Vec<bool> = self.accepts.iter().map(|accepts| !accepts).collect();
        // It has the same states, which the same words tell apart, so it is in its one
        // shape too. Only the dead state is another.
        Self {
            dead: dead(&self.next, &accepts),
            classes: self.classes.clone(),
            next: self.next.clone(),
            accepts,
            shown: self.shown.clone(),
        }
    }

    /// The DFA of the strings that both accept, by the product construction.
    ///
    /// # Errors
    ///
    /// When the budget does not cover its states.
    pub fn intersection(&self, other: &Self, budget: &mut Budget) -> Result<Self, Exhausted> {
        let (classes, pairs) = self.classes.common(&other.classes);
        let (mine, theirs) = (self.classes.count(), other.classes.count());
        let mut ids: HashMap<(u32, u32), u32> = HashMap::from([((0, 0), 0)]);
        let mut pending = VecDeque::from([(0, 0)]);
        let (mut next, mut accepts) = (Vec::new(), Vec::new());
        while let Some((a, b)) = pending.pop_front() {
            accepts.push(self.accepts[a as usize] && other.accepts[b as usize]);
            for (class_a, class_b) in &pairs {
                let to = (
                    self.next[a as usize * mine + *class_a as usize],
                    other.next[b as usize * theirs + *class_b as usize],
                );
                let id = u32::try_from(ids.len()).expect("fewer than 2^32 states");
                let id = match ids.entry(to) {
                    std::collections::hash_map::Entry::Occupied(known) => *known.get(),
                    std::collections::hash_map::Entry::Vacant(new) => {
                        budget.charge(cost(0, pairs.len()))?;
                        pending.push_back(to);
                        *new.insert(id)
                    }
                };
                next.push(id);
            }
        }
        Ok(Self::canonical(&classes, &next, &accepts))
    }

    /// The parts that a list of DFAs cuts every string into: one for each way of being
    /// accepted by some of them and by none of the others, unless no string is that way.
    /// Each part comes with whether each DFA of the list accepts its strings. Of two parts,
    /// the one comes first that the first DFA which tells them apart accepts. The list is
    /// not empty.
    ///
    /// The parts are read off one product of all the DFAs. A state of the product is the
    /// state that each DFA is in after some string, and which of them accept there says
    /// which part the string is of. Each DFA is minimal, so two strings lead to one state
    /// exactly when, whatever follows them, both come to be of one part: the product is
    /// the smallest DFA that says which part a string is of. To cut by one DFA after the
    /// other instead makes two products for every part and DFA, which for a hundred
    /// patterns that share no string is ten thousand products where this is one.
    ///
    /// The product is small where the DFAs share few strings. It may be far larger than
    /// every part where each DFA keeps track of something of its own, as counters of
    /// different lengths do: then it has a state for every combination. DFAs that share no
    /// string have a product of no more states than they have together. So the product is
    /// given up when it has more states than that, and the answer is `None`: the list is
    /// then cut by one DFA after the other.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the states of the product and of the parts.
    pub fn cut(all: &[&Self], budget: &mut Budget) -> Result<Option<Parts<Self>>, Exhausted> {
        let narrow = |index: usize| u32::try_from(index).expect("fewer than 2^32 states");
        let of_all: Vec<&Classes> = all.iter().map(|dfa| &dfa.classes).collect();
        let (classes, columns) = Classes::common_of(&of_all, budget)?;
        let (width, count) = (classes.count(), all.len());

        // A state of the product is kept as the states of the DFAs that are not in their
        // dead state, each with the place of its DFA in the list. A DFA that is in its dead
        // state stays there and accepts nothing, and most states are of a few DFAs.
        let live = (0..count).filter(|which| all[*which].dead != Some(0));
        let first: Rc<[(u32, u32)]> = live.map(|which| (narrow(which), 0)).collect();
        budget.charge(cost(0, first.len() * width))?;
        let mut ids: HashMap<Rc<[(u32, u32)]>, u32> = HashMap::from([(Rc::clone(&first), 0)]);
        let most: usize = all.iter().map(|dfa| dfa.accepts.len()).sum();
        let mut states = vec![first];
        let mut next: Vec<u32> = Vec::new();
        let mut to: Vec<(u32, u32)> = Vec::new();
        let mut at = 0;
        while at < states.len() {
            for class in 0..width {
                let column = &columns[class * count..(class + 1) * count];
                to.clear();
                for (which, state) in states[at].iter() {
                    let dfa = all[*which as usize];
                    let class = column[*which as usize] as usize;
                    let leads = dfa.next[*state as usize * dfa.classes.count() + class];
                    if Some(leads) != dfa.dead {
                        to.push((*which, leads));
                    }
                }
                let id = match ids.get(to.as_slice()) {
                    Some(known) => *known,
                    None => {
                        // A new state costs what it takes to say where each class leads
                        // from it: a look at each of its DFAs for every class.
                        if states.len() >= most {
                            return Ok(None);
                        }
                        budget.charge(cost(0, to.len() * width))?;
                        let new: Rc<[(u32, u32)]> = to.as_slice().into();
                        let id = narrow(states.len());
                        ids.insert(Rc::clone(&new), id);
                        states.push(new);
                        id
                    }
                };
                next.push(id);
            }
            at += 1;
        }

        // The DFAs that accept in a state say which part a string is of that leads there.
        let mut parts: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
        let mut places: HashMap<Vec<u32>, usize> = HashMap::new();
        for (state, of) in states.iter().enumerate() {
            let accepting = of
                .iter()
                .filter(|(which, at)| all[*which as usize].accepts[*at as usize]);
            let accepting: Vec<u32> = accepting.map(|(which, _)| *which).collect();
            let place = *places.entry(accepting).or_insert_with_key(|accepting| {
                parts.push((accepting.clone(), Vec::new()));
                parts.len() - 1
            });
            parts[place].1.push(narrow(state));
        }

        // The states that lead into each state, each of them once: those of state 0, then
        // those of state 1, and so on, with where those of each state begin. What leads
        // from one state comes together, so a state that leads into another by several
        // classes is seen to have been noted.
        let total = states.len();
        let leading = || {
            let all = next.iter().enumerate();
            all.map(|(slot, to)| (narrow(slot / width), *to as usize))
        };
        let mut starts = vec![0_usize; total + 1];
        let mut last = vec![u32::MAX; total];
        for (from, to) in leading() {
            if std::mem::replace(&mut last[to], from) != from {
                starts[to + 1] += 1;
            }
        }
        for state in 0..total {
            starts[state + 1] += starts[state];
        }
        let mut sources = vec![0_u32; starts[total]];
        let (mut filled, mut last) = (starts.clone(), vec![u32::MAX; total]);
        for (from, to) in leading() {
            if std::mem::replace(&mut last[to], from) != from {
                sources[filled[to]] = from;
                filled[to] += 1;
            }
        }

        // The DFA of a part is the product with the states of the part accepting. Only
        // the states that lead to one of those are written down, so that a part costs what
        // it has to say and not all of the product: every other state is its dead state.
        let mut numbers = vec![u32::MAX; total];
        let mut cut = Vec::with_capacity(parts.len());
        for (accepting, ends) in parts {
            budget.charge(1 + (count / 8) as u64)?;
            let mut kept = ends.clone();
            for state in &kept {
                numbers[*state as usize] = 0;
            }
            let mut at = 0;
            while let Some(&state) = kept.get(at) {
                let from = &sources[starts[state as usize]..starts[state as usize + 1]];
                budget.charge(cost(from.len(), width))?;
                for from in from {
                    if numbers[*from as usize] == u32::MAX {
                        numbers[*from as usize] = 0;
                        kept.push(*from);
                    }
                }
                at += 1;
            }
            // The first state of the product leads to every state, so it is among them,
            // and it is the first of these.
            kept.sort_unstable();
            for (number, state) in kept.iter().enumerate() {
                numbers[*state as usize] = narrow(number);
            }
            let dead = narrow(kept.len());
            let mut leads = Vec::with_capacity((kept.len() + 1) * width);
            for state in &kept {
                let row = &next[*state as usize * width..(*state as usize + 1) * width];
                leads.extend(row.iter().map(|to| numbers[*to as usize].min(dead)));
            }
            let mut accepts = vec![false; kept.len()];
            for end in &ends {
                accepts[numbers[*end as usize] as usize] = true;
            }
            if leads.contains(&dead) {
                leads.extend(std::iter::repeat_n(dead, width));
                accepts.push(false);
            }
            for state in &kept {
                numbers[*state as usize] = u32::MAX;
            }
            let mut within = vec![false; count];
            for which in accepting {
                within[which as usize] = true;
            }
            let part = Self::canonical(&classes, &leads, &accepts);
            cut.push((part, within.into_boxed_slice()));
        }
        cut.sort_by(|one, other| other.1.cmp(&one.1));
        Ok(Some(cut))
    }

    pub fn accepts(&self, word: &str) -> bool {
        let width = self.classes.count();
        let mut state = 0;
        for character in word.chars() {
            state = self.next[state * width + self.classes.of(place(character))] as usize;
        }
        self.accepts[state]
    }

    /// How many words are accepted, or `None` if there is no end of them, or more than a
    /// `u64` counts. A count is exact, so that what is taken from it is exact too.
    ///
    /// # Errors
    ///
    /// When the budget does not cover a look at every state.
    pub fn size(&self, budget: &mut Budget) -> Result<Option<u64>, Exhausted> {
        let (width, count) = (self.classes.count(), self.accepts.len());
        let dead = self.dead.map(|dead| dead as usize);
        let row = |state: usize| &self.next[state * width..(state + 1) * width];
        // Every state but the dead one leads to an accepted word. So there is no end of
        // words exactly when some way through those states comes back to where it was. The
        // states are put in an order in which each comes before those it leads to, which
        // there is unless one leads back.
        let mut leads_here = vec![0_usize; count];
        for state in (0..count).filter(|state| Some(*state) != dead) {
            budget.charge(cost(0, width))?;
            for to in row(state) {
                leads_here[*to as usize] += 1;
            }
        }
        let live = (0..count).filter(|state| Some(*state) != dead);
        let mut order: Vec<usize> = live.filter(|state| leads_here[*state] == 0).collect();
        let mut at = 0;
        while let Some(&state) = order.get(at) {
            for to in row(state).iter().map(|to| *to as usize) {
                leads_here[to] -= 1;
                if leads_here[to] == 0 && Some(to) != dead {
                    order.push(to);
                }
            }
            at += 1;
        }
        if order.len() + usize::from(dead.is_some()) < count {
            return Ok(None);
        }
        // How many characters each class has.
        let mut characters = vec![0_u64; width];
        for (index, (first, class)) in self.classes.runs.iter().enumerate() {
            let after = self
                .classes
                .runs
                .get(index + 1)
                .map_or(LAST + 1, |next| next.0);
            characters[*class as usize] += u64::from(after - first);
        }
        // The words that are accepted from a state: none more if it accepts, and for each
        // character those from the state that the character leads to.
        let mut words = vec![0_u64; count];
        for &state in order.iter().rev() {
            let mut from_here = u64::from(self.accepts[state]);
            for (class, to) in row(state).iter().enumerate() {
                let onward = characters[class].checked_mul(words[*to as usize]);
                let Some(more) = onward.and_then(|onward| from_here.checked_add(onward)) else {
                    return Ok(None);
                };
                from_here = more;
            }
            words[state] = from_here;
        }
        Ok(Some(words[0]))
    }

    /// Whether no string is accepted.
    pub fn is_empty(&self) -> bool {
        self.dead == Some(0)
    }

    /// Whether every string is accepted.
    pub fn is_everything(&self) -> bool {
        self.accepts.len() == 1 && self.accepts[0]
    }

    #[cfg(test)]
    pub fn states(&self) -> usize {
        self.accepts.len()
    }

    /// The length of the shortest accepted word whose length is within the bounds, if there
    /// is such a word, and what was found on the way to it.
    ///
    /// The states that a word of some length may end in are worked out length by length. They
    /// repeat after a while, and from then on nothing is worked out any more: a bound of a
    /// million costs no more than a small one.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the lengths that are looked at.
    fn walk(&self, lengths: Lengths, budget: &mut Budget) -> Result<Option<Walk>, Exhausted> {
        if lengths.max.is_some_and(|max| max < lengths.min) || self.is_empty() {
            return Ok(None);
        }
        let width = self.classes.count();
        let words = self.accepts.len().div_ceil(64);
        let accepted = |ends: &[u64]| members(ends).any(|state| self.accepts[state]);
        let mut seen: HashMap<Vec<u64>, usize> = HashMap::new();
        let mut reached: Vec<Vec<u64>> = Vec::new();
        let mut ends = vec![0_u64; words];
        ends[0] = 1;
        loop {
            let length = reached.len();
            budget.charge(cost(members(&ends).count(), width))?;
            if length as u64 >= lengths.min && accepted(&ends) {
                reached.push(ends);
                return Ok(Some(Walk {
                    length: length as u128,
                    reached,
                    repeats: None,
                }));
            }
            if lengths.max == Some(length as u64) {
                return Ok(None);
            }
            if let Some(&first) = seen.get(&ends) {
                // From `first` on the ends repeat with this period, so the lengths that end
                // in an accepting state do too. The least of them that is long enough:
                let period = length - first;
                let least = u128::from(lengths.min).max(length as u128);
                let fitting = (first..length)
                    .filter(|at| accepted(&reached[*at]))
                    .map(|at| {
                        let (at, period) = (at as u128, period as u128);
                        at + (least - at).div_ceil(period) * period
                    })
                    .min();
                let within = |length: &u128| lengths.max.is_none_or(|max| *length <= max.into());
                return Ok(fitting.filter(within).map(|length| Walk {
                    length,
                    reached,
                    repeats: Some((first, period)),
                }));
            }
            seen.insert(ends.clone(), length);
            let mut after = vec![0_u64; words];
            for state in members(&ends) {
                for to in &self.next[state * width..(state + 1) * width] {
                    if Some(*to) != self.dead {
                        after[*to as usize / 64] |= 1 << (*to % 64);
                    }
                }
            }
            reached.push(ends);
            // No word is longer than this and accepted.
            if after.iter().all(|word| *word == 0) {
                return Ok(None);
            }
            ends = after;
        }
    }

    /// Whether a word is accepted whose length is within the bounds.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search.
    pub fn has_word(&self, lengths: Lengths, budget: &mut Budget) -> Result<bool, Exhausted> {
        Ok(self.walk(lengths, budget)?.is_some())
    }

    /// The shortest accepted word whose length is within the bounds, if there is one. Of
    /// several it is one of plain characters.
    ///
    /// # Errors
    ///
    /// When the budget does not cover the search or the characters of the word.
    pub fn shortest(
        &self,
        lengths: Lengths,
        budget: &mut Budget,
    ) -> Result<Option<String>, Exhausted> {
        let Some(walk) = self.walk(lengths, budget)? else {
            return Ok(None);
        };
        // A step for each character, before any is written.
        budget.charge(u64::try_from(walk.length).unwrap_or(u64::MAX))?;
        let length = usize::try_from(walk.length).map_err(|_| Exhausted)?;
        let width = self.classes.count();
        let row = |state: usize| &self.next[state * width..(state + 1) * width];
        // From the end backwards: the states at each place in the word from which the rest
        // of the word can still lead to an accepting state.
        let mut leads_on: Vec<Vec<usize>> = Vec::new();
        // A word that memory does not hold is one that the budget does not cover.
        let places = length.checked_add(1).ok_or(Exhausted)?;
        leads_on.try_reserve_exact(places).map_err(|_| Exhausted)?;
        leads_on.resize(places, Vec::new());
        let ends = members(walk.ends(length));
        leads_on[length] = ends.filter(|state| self.accepts[*state]).collect();
        let mut marked = vec![false; self.accepts.len()];
        for at in (0..length).rev() {
            let here = walk.ends(at);
            budget.charge(cost(members(here).count(), width))?;
            for state in &leads_on[at + 1] {
                marked[*state] = true;
            }
            let on =
                members(here).filter(|state| row(*state).iter().any(|to| marked[*to as usize]));
            leads_on[at] = on.collect();
            for state in &leads_on[at + 1] {
                marked[*state] = false;
            }
        }
        // And forwards: at each place the plainest character that leads on.
        let mut word = String::with_capacity(length);
        let mut state = 0;
        for after in &leads_on[1..] {
            let classes = (0..width).filter(|class| after.contains(&(row(state)[*class] as usize)));
            let class = classes.min_by_key(|class| plainness(self.shown[*class]));
            let class = class.expect("the state leads on");
            word.push(self.shown[class]);
            state = row(state)[class] as usize;
        }
        Ok(Some(word))
    }
}

/// The state that does not accept and that every character leads back to, if there is one.
fn dead(next: &[u32], accepts: &[bool]) -> Option<u32> {
    let width = next.len() / accepts.len();
    let stays = |state: usize| {
        let row = &next[state * width..(state + 1) * width];
        row.iter().all(|to| *to as usize == state)
    };
    let dead = (0..accepts.len()).find(|state| !accepts[*state] && stays(*state));
    dead.map(|dead| u32::try_from(dead).expect("fewer than 2^32 states"))
}

/// What a search for an accepted length found: the length, and the states that a word of
/// each length may end in, as far as they were worked out.
struct Walk {
    length: u128,
    /// The states by length, as a set of bits each.
    reached: Vec<Vec<u64>>,
    /// Where the ends begin to repeat and with which period, if the search got that far.
    repeats: Option<(usize, usize)>,
}

impl Walk {
    /// The states that a word of this length may end in.
    fn ends(&self, length: usize) -> &[u64] {
        match self.repeats {
            Some((first, period)) if length >= first => {
                &self.reached[first + (length - first) % period]
            }
            _ => &self.reached[length],
        }
    }
}

/// The members of a set of bits.
fn members(set: &[u64]) -> impl Iterator<Item = usize> + '_ {
    set.iter().enumerate().flat_map(|(index, word)| {
        let mut word = *word;
        std::iter::from_fn(move || {
            (word != 0).then(|| {
                let bit = word.trailing_zeros() as usize;
                word &= word - 1;
                index * 64 + bit
            })
        })
    })
}

/// A character of each class to show in a word: the plainest of ASCII if the class has one,
/// or else the first of the class that is no control character.
fn shown(classes: &Classes) -> Vec<char> {
    let mut shown: Vec<Option<char>> = vec![None; classes.count()];
    for candidate in ' '..='~' {
        let class = classes.of(place(candidate));
        if shown[class].is_none_or(|known| plainness(candidate) < plainness(known)) {
            shown[class] = Some(candidate);
        }
    }
    let ends = classes.runs.iter().skip(1).map(|run| run.0 - 1);
    let ends = ends.chain([LAST]);
    for ((first, class), last) in classes.runs.iter().zip(ends) {
        // The characters up to U+009F that are not of ASCII are control characters.
        let first = if *first < 0xa0 && last >= 0xa0 {
            0xa0
        } else {
            *first
        };
        let candidate = character(first);
        let known = &mut shown[*class as usize];
        if known.is_none_or(|known| plainness(candidate) < plainness(known)) {
            *known = Some(candidate);
        }
    }
    let shown = shown.into_iter();
    shown
        .map(|shown| shown.expect("every class has a run"))
        .collect()
}

/// The block of each state, where two states are in one block exactly when the same words
/// are accepted from both. The blocks are numbered from 0 without a gap.
///
/// This is Hopcroft's algorithm: the states begin as those that accept and those that do not,
/// and a block is split whenever a class leads some of its states into a block and others
/// not.
fn blocks(width: usize, next: &[u32], accepts: &[bool]) -> Vec<u32> {
    let count = accepts.len();
    // The states that each class leads into each state from.
    let mut starts = vec![0_u32; width * count + 1];
    for (slot, to) in next.iter().enumerate() {
        starts[slot % width * count + *to as usize + 1] += 1;
    }
    for slot in 1..starts.len() {
        starts[slot] += starts[slot - 1];
    }
    let mut sources = vec![0_u32; next.len()];
    let mut filled = starts.clone();
    for (slot, to) in next.iter().enumerate() {
        let (from, class) = (slot / width, slot % width);
        let place = &mut filled[class * count + *to as usize];
        sources[*place as usize] = u32::try_from(from).expect("fewer than 2^32 states");
        *place += 1;
    }

    // The states in the order of their blocks, with where each state is in that order.
    let mut order: Vec<u32> = (0..count as u32).collect();
    order.sort_by_key(|state| accepts[*state as usize]);
    let mut position = vec![0_u32; count];
    for (at, state) in order.iter().enumerate() {
        position[*state as usize] = at as u32;
    }
    let rejecting = accepts.iter().filter(|accepts| !**accepts).count();
    // Where each block begins and ends in the order, and the block of each state.
    let mut bounds: Vec<(usize, usize)> = Vec::new();
    for bound in [(0, rejecting), (rejecting, count)] {
        if bound.0 < bound.1 {
            bounds.push(bound);
        }
    }
    let mut block_of = vec![0_u32; count];
    for state in &order[rejecting..] {
        block_of[*state as usize] = (bounds.len() - 1) as u32;
    }

    // The blocks and classes that may still split a block, and whether each is among them.
    let mut waiting: Vec<(u32, usize)> = Vec::new();
    let mut waits = vec![false; count * width];
    if bounds.len() == 2 {
        let smaller = u32::from(count - rejecting < rejecting);
        for class in 0..width {
            waiting.push((smaller, class));
            waits[smaller as usize * width + class] = true;
        }
    }
    // How many states of each block were found to lead into the block at hand.
    let mut marked = vec![0_usize; count];
    let mut touched: Vec<u32> = Vec::new();
    let mut into: Vec<u32> = Vec::new();
    while let Some((splitter, class)) = waiting.pop() {
        waits[splitter as usize * width + class] = false;
        // The block may be split while it is at hand, so its states are listed first.
        let (first, end) = bounds[splitter as usize];
        into.clear();
        into.extend_from_slice(&order[first..end]);
        for to in &into {
            let slot = class * count + *to as usize;
            for from in &sources[starts[slot] as usize..starts[slot + 1] as usize] {
                // The state moves to the front of its block, among those that were found.
                let block = block_of[*from as usize] as usize;
                let front = bounds[block].0 + marked[block];
                let at = position[*from as usize] as usize;
                order.swap(front, at);
                position[order[at] as usize] = at as u32;
                position[order[front] as usize] = front as u32;
                if marked[block] == 0 {
                    touched.push(block as u32);
                }
                marked[block] += 1;
            }
        }
        for block in touched.drain(..) {
            let block = block as usize;
            let found = std::mem::take(&mut marked[block]);
            let (first, end) = bounds[block];
            if found == end - first {
                continue;
            }
            // Those that were found become a block of their own.
            let new = bounds.len();
            bounds.push((first, first + found));
            bounds[block] = (first + found, end);
            for state in &order[first..first + found] {
                block_of[*state as usize] = new as u32;
            }
            let smaller = if found <= end - first - found {
                new
            } else {
                block
            };
            for class in 0..width {
                // A block that waits is split in two that both wait. Of one that does not,
                // the smaller half is enough.
                let add = if waits[block * width + class] {
                    new
                } else {
                    smaller
                };
                waiting.push((add as u32, class));
                waits[add * width + class] = true;
            }
        }
    }
    block_of
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unlimited() -> Budget {
        Budget::new(u64::MAX)
    }

    fn of(words: &[&str]) -> Dfa {
        Dfa::of_words(words.iter().copied(), &mut unlimited()).unwrap()
    }

    const ANY: Lengths = Lengths { min: 0, max: None };

    fn between(min: u64, max: u64) -> Lengths {
        Lengths {
            min,
            max: Some(max),
        }
    }

    #[test]
    fn the_places_of_the_characters_have_no_gap() {
        assert_eq!(place('\0'), 0);
        assert_eq!(place('\u{d7ff}') + 1, place('\u{e000}'));
        assert_eq!(place('\u{10ffff}'), LAST);
        for at in [0, 0x61, 0xd7ff, 0xd800, 0xffff, LAST] {
            assert_eq!(place(character(at)), at);
        }
    }

    #[test]
    fn a_dfa_of_words_accepts_them_and_no_other() {
        let words = ["", "a", "ab", "b\u{10ffff}", "\0"];
        let dfa = of(&words);
        for word in words {
            assert!(dfa.accepts(word), "{word:?}");
        }
        for other in ["b", "aa", "abc", "\u{10ffff}", "\u{1}", "é"] {
            assert!(!dfa.accepts(other), "{other:?}");
        }
        assert!(of(&[]).is_empty());
        assert!(!of(&[""]).is_empty());
        assert!(of(&[]).complement().is_everything());
    }

    #[test]
    fn two_dfas_of_one_language_are_equal() {
        assert_eq!(of(&["a", "b"]), of(&["b", "a", "a"]));
        assert_ne!(of(&["a", "b"]), of(&["a"]));
        let both = of(&["a", "b", "c"])
            .intersection(&of(&["b", "c", "d"]), &mut unlimited())
            .unwrap();
        assert_eq!(both, of(&["c", "b"]));
        assert_eq!(of(&["a"]).complement().complement(), of(&["a"]));
        // Words that end alike share their states: the two letters lead to one state.
        assert_eq!(of(&["ax", "bx"]).states(), 4);
    }

    #[test]
    fn the_complement_accepts_what_the_dfa_does_not() {
        let dfa = of(&["a", "ab"]);
        let complement = dfa.complement();
        for word in ["", "a", "ab", "abc", "b", "é"] {
            assert_ne!(dfa.accepts(word), complement.accepts(word), "{word:?}");
        }
        let nothing = dfa.intersection(&complement, &mut unlimited()).unwrap();
        assert!(nothing.is_empty());
    }

    #[test]
    fn a_list_of_dfas_cuts_every_string_into_parts() {
        let cut = |all: &[&Dfa]| Dfa::cut(all, &mut unlimited()).unwrap().unwrap();
        // A part for each way of being accepted by some that a string has, and the part
        // that the first DFA accepts first.
        let (ab, bc) = (of(&["a", "b"]), of(&["b", "c"]));
        let within = |held: &[bool]| -> Box<[bool]> { held.into() };
        let expected = vec![
            (of(&["b"]), within(&[true, true])),
            (of(&["a"]), within(&[true, false])),
            (of(&["c"]), within(&[false, true])),
            (of(&["a", "b", "c"]).complement(), within(&[false, false])),
        ];
        assert_eq!(cut(&[&ab, &bc]), expected);
        // Two that share no string leave no part for both.
        let (a, b) = (of(&["a", "ab"]), of(&["b", ""]));
        let expected = vec![
            (of(&["a", "ab"]), within(&[true, false])),
            (of(&["b", ""]), within(&[false, true])),
            (of(&["a", "ab", "b", ""]).complement(), within(&[false; 2])),
        ];
        assert_eq!(cut(&[&a, &b]), expected);
        // One that accepts nothing, one that accepts everything and one that is there
        // twice cut nothing.
        let (nothing, everything) = (of(&[]), of(&[]).complement());
        let expected = vec![
            (of(&["a", "b"]), within(&[false, true, true, true])),
            (ab.complement(), within(&[false, false, true, false])),
        ];
        assert_eq!(cut(&[&nothing, &ab, &everything, &ab]), expected);
        let all = vec![(of(&[]).complement(), within(&[false, true]))];
        assert_eq!(cut(&[&nothing, &everything]), all);
    }

    #[test]
    fn the_shortest_word_is_within_the_lengths() {
        let dfa = of(&["abc", "ab", "abcde"]);
        let shortest = |lengths| dfa.shortest(lengths, &mut unlimited()).unwrap();
        assert_eq!(shortest(ANY), Some("ab".to_owned()));
        assert_eq!(shortest(between(3, 9)), Some("abc".to_owned()));
        assert_eq!(shortest(between(4, 9)), Some("abcde".to_owned()));
        assert_eq!(shortest(between(4, 4)), None);
        assert_eq!(shortest(between(0, 1)), None);
        assert_eq!(shortest(between(6, 3)), None);
        assert_eq!(shortest(Lengths { min: 6, max: None }), None);
        // Every string but a few: the plainest characters come first.
        let others = of(&["", "a", "b"]).complement();
        let shortest = |lengths| others.shortest(lengths, &mut unlimited()).unwrap();
        assert_eq!(shortest(ANY), Some("c".to_owned()));
        assert_eq!(shortest(between(2, 2)), Some("aa".to_owned()));
        assert_eq!(shortest(between(0, 0)), None);
    }

    #[test]
    fn a_long_bound_costs_no_more_than_a_short_one() {
        // Whether there is a word of a million million characters takes a few steps.
        let others = of(&["a"]).complement();
        let lengths = Lengths {
            min: 1_000_000_000_000,
            max: None,
        };
        assert_eq!(others.has_word(lengths, &mut Budget::new(100)), Ok(true));
        // The word itself costs a step for each character.
        let lengths = Lengths {
            min: 1_000,
            max: None,
        };
        let word = others.shortest(lengths, &mut unlimited()).unwrap();
        assert_eq!(word, Some("a".repeat(1_000)));
        let mut budget = Budget::new(100);
        assert_eq!(others.shortest(lengths, &mut budget), Err(Exhausted));
        let lengths = Lengths {
            min: u64::MAX,
            max: None,
        };
        assert!(others.has_word(lengths, &mut unlimited()).unwrap());
        assert_eq!(others.shortest(lengths, &mut unlimited()), Err(Exhausted));
    }

    #[test]
    fn the_states_cost_steps() {
        // A word of a thousand characters is a thousand states, and so is what the DFAs of
        // two sets with that word share.
        let long = "a".repeat(1_000);
        let mut budget = Budget::new(100);
        assert!(Dfa::of_words([long.as_str()], &mut budget).is_err());
        let (a, b) = (of(&[&long, "b"]), of(&[&long, "c"]));
        let mut budget = Budget::new(100);
        assert!(a.intersection(&b, &mut budget).is_err());
        // And so is the product of the two that cuts every string by both.
        let mut budget = Budget::new(100);
        assert!(Dfa::cut(&[&a, &b], &mut budget).is_err());
    }
}
