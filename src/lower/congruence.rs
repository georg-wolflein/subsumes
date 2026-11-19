//! Which variables say the same.
//!
//! Schemas of one class share a variable, and a class is schemas with the same keywords and
//! the same values. Two schemas may say the same in other words: one closes an object with
//! `additionalProperties`, and the other with a second schema beside the first under an
//! `allOf`. Lowered, the two are the same conjunction of the same terms, only that one
//! reaches it through the variables of the schemas in between, in another order, and with
//! terms that say nothing. The engine would find that out by search. Here it is read off
//! the terms, and the two are one variable, so that `x` and `not x` cancel.
//!
//! # The canonical term
//!
//! Every variable gets a *canonical term*: its term, written so that two terms which differ
//! only in the following are written alike.
//!
//! - A reference to a variable is the canonical term of that variable, unless the variable
//!   is *pinned*: it is on a cycle of references with nothing in between, or leads to one
//!   by such references. Then it stays a reference; see below.
//! - A conjunction in a conjunction is part of it, and so is a disjunction in a disjunction.
//!   The types that the parts of a conjunction allow are one part, and so are those of a
//!   disjunction.
//! - The parts of a conjunction and of a disjunction are a set: in one order, and each there
//!   once. Those of a `OneOf` are in one order too, and each is there as often as it was:
//!   exactly one of them holds, so a part that is there twice never holds.
//! - What says nothing is left out: `true` in a conjunction, `false` in a disjunction or in
//!   a `OneOf`, and a term that every property or item of some kind is to satisfy a schema
//!   that is `true`. A connective of one part is that part. A negation of a negation is
//!   what was negated, and a negation of types is the other types.
//! - A term that names the variable of a value inside the instance, as that of a property
//!   does, names it by its class here, and the language of the names of the properties that
//!   no other keyword names is the set of names that it leaves out, however it was made.
//! - Everything else is the term that it is. Two leaves are one only by their key, as
//!   everywhere.
//!
//! Each of these leaves the instances that a term accepts as they are, given the terms of
//! the variables. The canonical terms are kept in a table of their own, which is gone when
//! the pass is done: the terms and the languages of the check stay as they were.
//!
//! # The classes
//!
//! Two variables are of one class when their canonical terms are equal. For variables that
//! are on no cycle of references of any kind that is one pass from the leaves up, as hash
//! consing is. Variables that are on such a cycle through a property or an item are told
//! apart in rounds: all are one block at first, and each round separates those of a block
//! whose canonical terms differ when the variables on cycles are named by their blocks of
//! the round before. A round that separates nothing ends the work. That is partition
//! refinement, and the blocks it ends with are the coarsest bisimulation. A value is finite,
//! so the terms of variables of one block say the same of every value: of one that holds no
//! other value they say what their equal canonical terms say, and of a larger one what
//! those say given what the variables say of the values inside it.
//!
//! A pinned variable is a class by itself. The least fixed point of a cycle of references
//! with nothing in between is what the engine works out as it unfolds the variables on the
//! way to the cycle and around it, and where a schema is negated inside itself, whether a
//! branch is refuted or depends on a leaf turns on the order in which those unfoldings are
//! met. A variable that was put in the place of another on that way would change the order,
//! and a check that was decided could become one that is not. So the engine unfolds the
//! pinned variables as they were, and a variable that leads to none is all that is merged.
//!
//! # What the engine gets
//!
//! The terms stay as they were. One variable of each class stands for the others, and the
//! engine takes it wherever a term names one of them. The order of the parts of a term is
//! the order in which the engine meets its disjunctions, which the canonical terms do not
//! keep.
//!
//! The variable that stands for a class is the first of its members in an order in which a
//! variable comes after those that it refers to with nothing in between. So a reference
//! with nothing in between leads to a variable that comes before the one that it stands
//! in, or to a pinned one on its own cycle, and the engine meets no cycle that the terms
//! did not have: of `x`, whose term is a reference to `y`, and `y`, it is `y` that stands
//! for both. Were it `x`, the term of `x` would refer to `x` itself.
//!
//! # What it costs
//!
//! One pass over the terms, and one more for each round. A reference with nothing in
//! between is replaced by the canonical term of its variable, whose parts are copied, so a
//! chain of schemas that each add a keyword to the one before takes the square of its
//! length. The pass therefore counts its work and gives up at a multiple of the number of
//! terms and variables: then no variables are merged, and the check goes on as it would
//! have without the pass. The count is of the work alone, so the pass does the same on every
//! machine. It charges nothing to the budget, since its work is no more than that multiple
//! of the size of the terms, as the work of the load stage is no more than a multiple of the
//! size of the schemas.

use std::hash::{BuildHasher, Hash, Hasher};

use super::classes::components;
use crate::hash::{Keyed, Map};
use crate::language::{LanguageId, Languages, Shape};
use crate::term::{Term, TermId, Terms, TypeSet, VarId};

/// How many times the number of terms and variables the pass may count before it gives up.
const TIMES: u64 = 256;

/// No canonical term, no block and no place.
const NONE: u32 = u32::MAX;

/// The ids of the canonical terms `true` and `false`, which are made first.
const TRUE: u32 = 0;
const FALSE: u32 = 1;

/// A canonical term. Its parts are the ids of canonical terms.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Canonical {
    True,
    False,
    /// The instance has one of these types, which are neither none nor all.
    Types(TypeSet),
    /// A term that names no variable and is no connective, as it is.
    Plain(TermId),
    /// A term about the values inside the instance, and what the variable that it names is.
    Inside(About, Name),
    /// A variable that leads with nothing in between to a cycle of references with
    /// nothing in between, which is a class by itself.
    Pinned(VarId),
    Not(u32),
    /// The parts, in the order of their ids.
    Connective(Connective, Box<[u32]>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Connective {
    All,
    Any,
    One,
}

/// What a term about the values inside an instance is about.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum About {
    /// The properties with a name of a language, by the language as [`Pass::language`]
    /// gives it.
    Properties(u32),
    /// The names of the properties.
    Names,
    /// The item at a position.
    Item(u64),
    /// Every item from a position on.
    Items(u64),
    /// Some item.
    Contains,
}

/// What a variable that a term names is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Name {
    /// Of the class of this canonical term.
    Class(u32),
    /// Of this block of variables on cycles, of the round before.
    Block(u32),
}

/// A language as it is compared: by its id, or as every name but these.
#[derive(PartialEq, Eq, Hash)]
enum Language<'l> {
    Id(LanguageId),
    Others(Vec<&'l str>),
}

/// Something whose canonical term is wanted.
#[derive(Debug, Clone, Copy)]
enum Wanted {
    Term(TermId),
    Variable(VarId),
}

/// The pass gave up: its work went beyond what it may count.
#[derive(Debug)]
pub(super) struct GaveUp;

/// The hash of a connective by its parts, which is what it is in [`Table`] too.
fn connective_hash(connective: Connective, parts: &[u32]) -> u64 {
    let mut hasher = Keyed::default().build_hasher();
    hasher.write_u64(connective as u64 + 1);
    for part in parts {
        hasher.write_u32(*part);
    }
    hasher.finish()
}

/// The canonical terms, each once, by id. A connective is looked up by its parts, so that a
/// connective that is there already costs no copy of them.
struct Table {
    canonical: Vec<Canonical>,
    /// For each hash, the last canonical term with it, and for each canonical term the one
    /// with the same hash before it.
    last: Map<u64, u32>,
    before: Vec<u32>,
}

impl Table {
    /// A table with room for so many canonical terms.
    fn with_capacity(capacity: usize) -> Self {
        Self {
            canonical: Vec::with_capacity(capacity),
            last: Map::with_capacity_and_hasher(capacity, Keyed::default()),
            before: Vec::with_capacity(capacity),
        }
    }

    fn get(&self, id: u32) -> &Canonical {
        &self.canonical[id as usize]
    }

    /// The id of a canonical term with a hash, which `is` tells apart from the others with
    /// it. One that is not there yet is made of `make`.
    fn find(
        &mut self,
        hash: u64,
        is: impl Fn(&Canonical) -> bool,
        make: impl FnOnce() -> Canonical,
    ) -> u32 {
        let mut at = self.last.get(&hash).copied().unwrap_or(NONE);
        while at != NONE {
            if is(&self.canonical[at as usize]) {
                return at;
            }
            at = self.before[at as usize];
        }
        let id = u32::try_from(self.canonical.len()).expect("fewer than 2^32 canonical terms");
        self.canonical.push(make());
        self.before.push(self.last.insert(hash, id).unwrap_or(NONE));
        id
    }

    fn id(&mut self, canonical: Canonical) -> u32 {
        let hash = match &canonical {
            Canonical::Connective(connective, parts) => connective_hash(*connective, parts),
            other => Keyed::default().hash_one(other),
        };
        let is = |other: &Canonical| *other == canonical;
        self.find(hash, is, || canonical.clone())
    }

    fn connective(&mut self, connective: Connective, parts: &[u32]) -> u32 {
        let hash = connective_hash(connective, parts);
        let is = |other: &Canonical| match other {
            Canonical::Connective(kind, these) => *kind == connective && **these == *parts,
            _ => false,
        };
        self.find(hash, is, || Canonical::Connective(connective, parts.into()))
    }
}

/// The state of the pass.
struct Pass<'t> {
    terms: &'t Terms,
    languages: &'t Languages,
    table: Table,
    /// The languages as they are compared, each once, by id, and for each language that
    /// was looked at its id among them.
    compared: Map<Language<'t>, u32>,
    seen_languages: Map<LanguageId, u32>,
    /// Whether each variable leads with nothing in between to a cycle of references with
    /// nothing in between, and whether it is on a cycle of references of any kind.
    pinned: Vec<bool>,
    cyclic: Vec<bool>,
    /// The block of each variable that is on a cycle and not pinned, of the round before.
    blocks: Vec<u32>,
    /// The canonical term of each term and of each variable, where it was worked out in
    /// this round.
    memo: Vec<u32>,
    of: Vec<u32>,
    /// For each variable, when its canonical term was worked out in this round: after those
    /// of the variables that it refers to with nothing in between.
    place: Vec<u32>,
    placed: u32,
    /// What is being worked out, each after what it needs.
    wanted: Vec<Wanted>,
    /// The canonical parts of the connective at hand, and those parts flattened.
    parts: Vec<u32>,
    flat: Vec<u32>,
    /// How much work was done, and how much may be.
    work: u64,
    limit: u64,
}

impl<'t> Pass<'t> {
    /// The id of a canonical term, which is a new one if it was not made before.
    fn id(&mut self, canonical: Canonical) -> u32 {
        self.table.id(canonical)
    }

    /// The canonical term of types: `true` for all of them and `false` for none.
    fn types(&mut self, types: TypeSet) -> u32 {
        match types {
            TypeSet::ALL => TRUE,
            TypeSet::NONE => FALSE,
            _ => self.id(Canonical::Types(types)),
        }
    }

    /// A language as it is compared. Every name but some words is one language, whether it
    /// is kept as the complement of one set of words or as what is outside several.
    fn language(&mut self, id: LanguageId) -> u32 {
        if let Some(&seen) = self.seen_languages.get(&id) {
            return seen;
        }
        let languages = self.languages;
        let words_of = |of: &LanguageId| match languages.shape(*of) {
            Shape::Words {
                words,
                others: false,
            } => Some(words),
            _ => None,
        };
        let compared = match languages.shape(id) {
            Shape::Words {
                words,
                others: true,
            } => Language::Others(words.iter().map(|word| &**word).collect()),
            Shape::Outside(of) if of.iter().all(|of| words_of(of).is_some()) => {
                let words = of.iter().filter_map(words_of).flatten();
                let mut all: Vec<&str> = words.map(|word| &**word).collect();
                self.work += all.len() as u64;
                all.sort_unstable();
                all.dedup();
                Language::Others(all)
            }
            _ => Language::Id(id),
        };
        let next = u32::try_from(self.compared.len()).expect("fewer than 2^32 languages");
        let compared = *self.compared.entry(compared).or_insert(next);
        self.seen_languages.insert(id, compared);
        compared
    }

    /// Works out the canonical term of a variable, and those of everything that it needs
    /// first. Nothing here recurses, however deep the terms go.
    fn work_out(&mut self, of: VarId) -> Result<(), GaveUp> {
        self.wanted.push(Wanted::Variable(of));
        while let Some(&wanted) = self.wanted.last() {
            self.work += 1;
            if self.work > self.limit {
                return Err(GaveUp);
            }
            match wanted {
                Wanted::Variable(variable) => {
                    let index = variable.index();
                    if self.of[index] != NONE {
                        self.wanted.pop();
                        continue;
                    }
                    let canonical = if self.pinned[index] {
                        self.id(Canonical::Pinned(variable))
                    } else {
                        let body = self.terms.variable(variable).body;
                        match self.memo[body.index()] {
                            NONE => {
                                self.wanted.push(Wanted::Term(body));
                                continue;
                            }
                            canonical => canonical,
                        }
                    };
                    self.of[index] = canonical;
                    self.place[index] = self.placed;
                    self.placed += 1;
                    self.wanted.pop();
                }
                Wanted::Term(term) => {
                    if self.memo[term.index()] != NONE {
                        self.wanted.pop();
                    } else if let Some(canonical) = self.canonical(term) {
                        self.memo[term.index()] = canonical;
                        self.wanted.pop();
                    }
                }
            }
        }
        Ok(())
    }

    /// The canonical term of a variable that a reference with nothing in between leads to,
    /// or `None` with the variable wanted first.
    fn referred(&mut self, variable: VarId) -> Option<u32> {
        if self.pinned[variable.index()] {
            return Some(self.id(Canonical::Pinned(variable)));
        }
        match self.of[variable.index()] {
            NONE => {
                self.wanted.push(Wanted::Variable(variable));
                None
            }
            canonical => Some(canonical),
        }
    }

    /// The name of a variable that a term about the values inside an instance names, or
    /// `None` with the variable wanted first. A variable on a cycle through a value is named
    /// by its block, and any other by the class of its canonical term.
    fn name(&mut self, variable: VarId) -> Option<Name> {
        let index = variable.index();
        if self.cyclic[index] && !self.pinned[index] {
            return Some(Name::Block(self.blocks[index]));
        }
        self.referred(variable).map(Name::Class)
    }

    /// The canonical term of a term about the values inside an instance. What every such
    /// value is to satisfy says nothing if the variable is `true`.
    fn inside(&mut self, about: About, variable: VarId, every: bool) -> Option<u32> {
        let name = self.name(variable)?;
        Some(if every && name == Name::Class(TRUE) {
            TRUE
        } else {
            self.id(Canonical::Inside(about, name))
        })
    }

    /// The canonical term of a term whose parts have theirs, or `None` with what it needs
    /// first wanted.
    fn canonical(&mut self, term: TermId) -> Option<u32> {
        let terms = self.terms;
        match terms.term(term) {
            Term::True => Some(TRUE),
            Term::False => Some(FALSE),
            Term::TypeIs(types) => Some(self.types(*types)),
            Term::Ref(variable) => self.referred(*variable),
            Term::PProp(names, variable) => {
                let names = self.language(*names);
                self.inside(About::Properties(names), *variable, true)
            }
            Term::PNames(variable) => self.inside(About::Names, *variable, true),
            Term::Item(position, variable) => self.inside(About::Item(*position), *variable, true),
            Term::AddIts(from, variable) => self.inside(About::Items(*from), *variable, true),
            // An array with an item that a schema which is `true` accepts is an array with an
            // item, so this says something.
            Term::Contains(variable) => self.inside(About::Contains, *variable, false),
            Term::Not(inner) => match self.memo[inner.index()] {
                NONE => {
                    self.wanted.push(Wanted::Term(*inner));
                    None
                }
                inner => Some(self.negation(inner)),
            },
            Term::AllOf(inner) | Term::AnyOf(inner) | Term::OneOf(inner) => {
                let before = self.wanted.len();
                self.parts.clear();
                self.work += inner.len() as u64;
                for part in inner {
                    match self.memo[part.index()] {
                        NONE => self.wanted.push(Wanted::Term(*part)),
                        canonical => self.parts.push(canonical),
                    }
                }
                if self.wanted.len() > before {
                    return None;
                }
                Some(match terms.term(term) {
                    Term::AllOf(_) => self.connective(true),
                    Term::AnyOf(_) => self.connective(false),
                    _ => self.one_of(),
                })
            }
            _ => Some(self.id(Canonical::Plain(term))),
        }
    }

    fn negation(&mut self, of: u32) -> u32 {
        match self.table.get(of) {
            Canonical::True => FALSE,
            Canonical::False => TRUE,
            Canonical::Types(types) => self.types(types.complement()),
            Canonical::Not(inner) => *inner,
            _ => self.id(Canonical::Not(of)),
        }
    }

    /// The canonical conjunction of the parts at hand, or with `all` false their
    /// disjunction.
    fn connective(&mut self, all: bool) -> u32 {
        // What ends the connective, and what says nothing in it.
        let (ends, nothing) = if all { (FALSE, TRUE) } else { (TRUE, FALSE) };
        let kind = if all {
            Connective::All
        } else {
            Connective::Any
        };
        let mut types = if all { TypeSet::ALL } else { TypeSet::NONE };
        let Self {
            table, parts, flat, ..
        } = self;
        flat.clear();
        // A part that is a connective of the same kind is its parts, and the types that the
        // parts allow are one part.
        let mut take = |part: u32, flat: &mut Vec<u32>| match table.get(part) {
            Canonical::Types(these) if all => types = types.intersection(*these),
            Canonical::Types(these) => types = types.union(*these),
            _ => flat.push(part),
        };
        for &part in parts.iter() {
            if part == ends {
                return ends;
            }
            match table.get(part) {
                _ if part == nothing => {}
                Canonical::Connective(inner_kind, inner) if *inner_kind == kind => {
                    inner.iter().for_each(|part| take(*part, flat));
                }
                _ => take(part, flat),
            }
        }
        self.work += self.flat.len() as u64;
        match self.types(types) {
            types if types == ends => return ends,
            types if types == nothing => {}
            types => self.flat.push(types),
        }
        self.flat.sort_unstable();
        self.flat.dedup();
        match self.flat.as_slice() {
            [] => nothing,
            [only] => *only,
            parts => self.table.connective(kind, parts),
        }
    }

    /// The canonical `OneOf` of the parts at hand. A part that is `false` never holds, and
    /// every other part is kept as often as it is there.
    fn one_of(&mut self) -> u32 {
        let Self { parts, flat, .. } = self;
        flat.clear();
        flat.extend(parts.iter().filter(|part| **part != FALSE));
        flat.sort_unstable();
        match self.flat.as_slice() {
            [] => FALSE,
            [only] => *only,
            parts => self.table.connective(Connective::One, parts),
        }
    }
}

/// For each variable, the variables that its term refers to with nothing in between, and
/// those that it names in any way.
fn successors(terms: &Terms) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let count = terms.variables().count();
    let mut in_place = vec![Vec::new(); count];
    let mut all = vec![Vec::new(); count];
    // The variable in whose term a term was last seen.
    let mut seen = vec![NONE; terms.len()];
    let mut pending = Vec::new();
    for (id, variable) in terms.variables() {
        let from = id.index();
        let mark = u32::try_from(from).expect("fewer than 2^32 variables");
        pending.push(variable.body);
        while let Some(term) = pending.pop() {
            if std::mem::replace(&mut seen[term.index()], mark) == mark {
                continue;
            }
            match terms.term(term) {
                Term::AllOf(parts) | Term::AnyOf(parts) | Term::OneOf(parts) => {
                    pending.extend(parts.iter().copied());
                }
                Term::Not(inner) => pending.push(*inner),
                Term::Ref(other) => {
                    in_place[from].push(other.index());
                    all[from].push(other.index());
                }
                Term::PProp(_, other)
                | Term::PNames(other)
                | Term::Item(_, other)
                | Term::AddIts(_, other)
                | Term::Contains(other) => all[from].push(other.index()),
                _ => {}
            }
        }
    }
    (in_place, all)
}

/// Which variables lead to one of these: the variables themselves, and those that refer to
/// one of them, or to a variable that does.
fn leading_to(successors: &[Vec<usize>], mut found: Vec<bool>) -> Vec<bool> {
    let mut predecessors = vec![Vec::new(); successors.len()];
    for (from, successors) in successors.iter().enumerate() {
        for to in successors {
            predecessors[*to].push(from);
        }
    }
    let mut pending: Vec<usize> = (0..found.len()).filter(|index| found[*index]).collect();
    while let Some(to) = pending.pop() {
        for from in &predecessors[to] {
            if !std::mem::replace(&mut found[*from], true) {
                pending.push(*from);
            }
        }
    }
    found
}

/// Finds the variables that say the same, and lets one of each class stand for the others.
///
/// `recursive` is whether a schema leads back to itself. Without one, no variable is on a
/// cycle, and the work is one pass.
///
/// # Errors
///
/// When the work goes beyond what the pass may count. Then nothing is merged.
pub(super) fn merge(
    terms: &mut Terms,
    languages: &Languages,
    recursive: bool,
) -> Result<(), GaveUp> {
    let same = classes(terms, languages, recursive)?;
    for (index, stands) in same.into_iter().enumerate() {
        terms.variable_mut(VarId::at(index)).same = stands;
    }
    Ok(())
}

/// The variable that stands for each variable.
fn classes(terms: &Terms, languages: &Languages, recursive: bool) -> Result<Vec<VarId>, GaveUp> {
    let count = terms.variables().count();
    // The order in which a variable comes after those that it refers to with nothing in
    // between, those on one cycle of such references together, and which variables are
    // pinned and which are on cycles. Without a cycle, the order in which the canonical
    // terms are worked out is such an order.
    let (order, pinned, cyclic) = if recursive {
        let (in_place, all) = successors(terms);
        let (order, looped) = components(&in_place);
        let (_, cyclic) = components(&all);
        (Some(order), leading_to(&in_place, looped), cyclic)
    } else {
        (None, vec![false; count], vec![false; count])
    };
    let size = (terms.len() + count) as u64;
    let mut pass = Pass {
        terms,
        languages,
        // There are about as many canonical terms as there are terms.
        table: Table::with_capacity(terms.len()),
        compared: Map::default(),
        seen_languages: Map::default(),
        pinned,
        cyclic,
        blocks: vec![0; count],
        memo: Vec::new(),
        of: Vec::new(),
        place: vec![NONE; count],
        placed: 0,
        wanted: Vec::with_capacity(64),
        parts: Vec::new(),
        flat: Vec::new(),
        work: 0,
        limit: TIMES * size,
    };
    assert_eq!(pass.id(Canonical::True), TRUE);
    assert_eq!(pass.id(Canonical::False), FALSE);

    // The variables on cycles through values are one block at first.
    let on_cycles: Vec<usize> = (0..count)
        .filter(|index| pass.cyclic[*index] && !pass.pinned[*index])
        .collect();
    let mut told_apart = usize::from(!on_cycles.is_empty());
    let mut blocks: Map<(u32, u32), u32> = Map::default();
    loop {
        pass.memo.clear();
        pass.memo.resize(terms.len(), NONE);
        pass.of.clear();
        pass.of.resize(count, NONE);
        pass.placed = 0;
        for index in 0..count {
            if pass.of[index] == NONE {
                pass.work_out(VarId::at(index))?;
            }
        }
        if on_cycles.is_empty() {
            break;
        }
        // The blocks of this round: those of the round before, each cut by the canonical
        // terms of its variables.
        blocks.clear();
        let mut next = pass.blocks.clone();
        for &index in &on_cycles {
            let found = u32::try_from(blocks.len()).expect("fewer than 2^32 blocks");
            next[index] = *blocks
                .entry((pass.blocks[index], pass.of[index]))
                .or_insert(found);
        }
        pass.work += on_cycles.len() as u64;
        if blocks.len() == told_apart {
            break;
        }
        told_apart = blocks.len();
        pass.blocks = next;
    }

    // The variable that stands for each class: the first of its members in the order.
    let mut rank = pass.place;
    if let Some(order) = order {
        for (at, index) in order.into_iter().enumerate() {
            rank[index] = u32::try_from(at).expect("fewer than 2^32 variables");
        }
    }
    // But a variable whose term is `true` or `false` itself stands for the class of `true` or
    // `false` where there is one. Another member may be a large term that comes to the same,
    // and the engine knows `true` and `false` at once where it would unfold that one, which
    // may lead to leaves and to schemas of which nothing definite is said.
    let plain = |index: usize, canonical: u32| {
        (canonical == TRUE || canonical == FALSE)
            && matches!(
                terms.term(terms.variable(VarId::at(index)).body),
                Term::True | Term::False
            )
    };
    let mut stands = vec![NONE; pass.table.canonical.len()];
    for (index, canonical) in pass.of.iter().enumerate() {
        let first = &mut stands[*canonical as usize];
        let before = *first == NONE || {
            let (this, that) = (plain(index, *canonical), plain(*first as usize, *canonical));
            (this && !that) || (this == that && rank[index] < rank[*first as usize])
        };
        if before {
            *first = u32::try_from(index).expect("fewer than 2^32 variables");
        }
    }
    let of = pass.of;
    Ok(of
        .into_iter()
        .map(|canonical| VarId::at(stands[canonical as usize] as usize))
        .collect())
}

#[cfg(test)]
mod tests {
    use serde_json::{Map, Value, json};

    use super::*;
    use crate::context::Context;
    use crate::lower::lower;
    use crate::schema::parse;
    use crate::term::CRefId;
    use crate::{Checker, RegexDialect, Verdict};

    /// Whether the engine takes A and B for one variable.
    fn one_variable(a: &Value, b: &Value) -> bool {
        let graph = parse(a, b).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX, RegexDialect::default());
        let (a, b) = lower(&graph, &mut context).unwrap();
        let terms = &mut context.terms;
        terms.literal(a, false) == terms.literal(b, false)
    }

    #[test]
    fn schemas_that_say_the_same_in_other_words_are_one_variable() {
        // An object closed in the schema itself, and closed by a second schema beside it,
        // under an `anyOf` of one.
        let open = json!({
            "type": "object",
            "properties": {"a": {"type": "string"}, "b": {}},
            "required": ["a"],
        });
        let mut closed = open.clone();
        closed["additionalProperties"] = json!(false);
        let named = json!({"^a$": true, "^b$": true});
        let beside = json!({"patternProperties": named, "additionalProperties": false});
        let in_two = json!({"anyOf": [{"allOf": [open, beside]}]});
        assert!(one_variable(&closed, &in_two));
        // Parts in another order, a disjunction in a disjunction, and what says nothing.
        let (string, positive) = (json!({"type": "string"}), json!({"minimum": 1}));
        let either = json!({"anyOf": [string, positive]});
        let other = json!({"anyOf": [positive, {"anyOf": [string, false]}, {"not": {}}]});
        assert!(one_variable(&either, &other));
        // A negation of a negation, and types that are asked twice.
        assert!(one_variable(&json!({"not": {"not": string}}), &string));
        let types = json!({"type": ["string", "null"], "allOf": [{"type": ["string", "number"]}]});
        assert!(one_variable(&types, &string));
        // What says something else is not.
        let less = json!({"anyOf": [string, {"minimum": 2}]});
        assert!(!one_variable(&either, &less));
        let more = json!({"allOf": [open, beside, {"minProperties": 1}]});
        assert!(!one_variable(&closed, &more));
    }

    /// The literals of A and B, as the engine takes them.
    fn literals(a: &Value, b: &Value) -> (CRefId, CRefId) {
        let graph = parse(a, b).unwrap().link().unwrap();
        let mut context = Context::new(u64::MAX, RegexDialect::default());
        let (a, b) = lower(&graph, &mut context).unwrap();
        let terms = &mut context.terms;
        (terms.literal(a, false), terms.literal(b, false))
    }

    #[test]
    fn true_and_false_are_stood_for_by_themselves() {
        // Schemas that come to `false` or to `true` with many keywords are of one class with
        // `false` or `true`, and whichever comes first, the engine takes the class for
        // `false` or `true` itself, which it knows without unfolding anything.
        let never = json!({
            "type": "string",
            "allOf": [{"type": "number"}],
            "properties": {"x": {"contains": {"type": "string"}, "minContains": 2}},
        });
        let always = json!({"properties": {"x": true}, "anyOf": [{}, {"type": "string"}]});
        for (a, b, both) in [
            (&never, &json!(false), Terms::NOTHING),
            (&json!(false), &never, Terms::NOTHING),
            (&always, &json!({}), Terms::ANYTHING),
            (&json!(true), &always, Terms::ANYTHING),
        ] {
            assert_eq!(literals(a, b), (both, both));
        }
    }

    #[test]
    fn an_object_closed_beside_its_properties_is_closed_to_the_names_that_it_lists() {
        // The names that are left open are every name but a few words, however those words
        // are written down. One word more is another language.
        let closed = json!({
            "type": "object",
            "properties": {"a": {}, "b": {}},
            "additionalProperties": false,
        });
        let named = |names: &[&str]| {
            let named: Map<String, Value> = names
                .iter()
                .map(|name| (format!("^{name}$"), json!(true)))
                .collect();
            json!({"type": "object", "patternProperties": named, "additionalProperties": false})
        };
        assert!(one_variable(&closed, &named(&["a", "b"])));
        assert!(one_variable(&closed, &named(&["b", "a"])));
        let more = named(&["a", "b", "c"]);
        assert!(!one_variable(&closed, &more));
        let checker = Checker::new();
        assert!(matches!(
            checker.subsumes(&closed, &more).unwrap(),
            Verdict::No { .. }
        ));
        assert_eq!(checker.subsumes(&more, &closed).unwrap(), Verdict::Yes);
    }

    #[test]
    fn a_one_of_keeps_every_part() {
        // Exactly one of two schemas that are the same never holds.
        let string = json!({"type": "string"});
        let (once, twice) = (
            json!({"oneOf": [string]}),
            json!({"oneOf": [string, string]}),
        );
        assert!(!one_variable(&once, &twice));
        let checker = Checker::new();
        assert_eq!(
            checker.subsumes(&json!(false), &twice).unwrap(),
            Verdict::Yes
        );
        assert!(matches!(
            checker.subsumes(&twice, &once).unwrap(),
            Verdict::No { .. }
        ));
        // Their order is free.
        let positive = json!({"minimum": 1});
        let one_of = json!({"oneOf": [string, positive]});
        let other = json!({"oneOf": [positive, {"allOf": [string]}]});
        assert!(one_variable(&one_of, &other));
    }

    /// A list of objects along the property `next`, defined as one schema or, with `in_two`,
    /// as two that refer to each other, the one in other words. With `required` every
    /// object of the one schema, or every second of the two, has to have a next one.
    fn list(in_two: bool, required: bool) -> Value {
        let mut last = json!({"type": "object", "properties": {"next": {"$ref": "#/$defs/odd"}}});
        if required {
            last["required"] = json!(["next"]);
        }
        if !in_two {
            return json!({"$defs": {"odd": last}, "$ref": "#/$defs/odd"});
        }
        let next = json!({"properties": {"next": {"$ref": "#/$defs/even"}}});
        let odd = json!({"allOf": [{"type": "object"}, next]});
        json!({"$defs": {"odd": odd, "even": last}, "$ref": "#/$defs/odd"})
    }

    #[test]
    fn schemas_that_hold_each_other_in_properties_are_one_variable_where_they_say_the_same() {
        assert!(one_variable(&list(false, false), &list(true, false)));
        // Every second object of the list has to have a next one: that is another list.
        assert!(!one_variable(&list(false, false), &list(true, true)));
        // And every object: a list that accepts nothing, since it would have no end.
        assert!(!one_variable(&list(false, true), &list(true, true)));
        let checker = Checker::new();
        assert_eq!(
            checker.subsumes(&json!(false), &list(false, true)).unwrap(),
            Verdict::Yes
        );
    }

    #[test]
    fn a_schema_that_leads_to_itself_with_nothing_in_between_stays_itself() {
        // Strings, or what the schema itself accepts: its least fixed point is the strings,
        // which the engine works out by unfolding the schema, so it is merged with no other
        // schema, and neither is a schema that leads to it.
        let string = json!({"type": "string"});
        let x = json!({"anyOf": [{"$ref": "#/$defs/x"}, string]});
        let a = json!({"$defs": {"x": x}, "$ref": "#/$defs/x"});
        let y = json!({"anyOf": [string, {"allOf": [{"$ref": "#/$defs/y"}]}]});
        let b = json!({"$defs": {"y": y}, "$ref": "#/$defs/y"});
        assert!(!one_variable(&a, &b));
        let x = json!({"anyOf": [{"$ref": "#/$defs/x"}, string]});
        let around = json!({"$defs": {"x": x}, "allOf": [{"$ref": "#/$defs/x"}, {}]});
        assert!(!one_variable(&a, &around));
        let checker = Checker::new();
        for (a, b) in [
            (&a, &b),
            (&b, &a),
            (&string, &b),
            (&a, &around),
            (&around, &a),
        ] {
            assert_eq!(checker.subsumes(a, b).unwrap(), Verdict::Yes);
        }
    }

    #[test]
    fn what_leads_to_a_schema_that_is_negated_inside_itself_is_unfolded_as_it_was() {
        // `e` is one of three schemas, one of them `e` itself, and so negated inside
        // itself. Whether a branch that meets it is refuted or depends on a leaf turns on
        // the order in which the engine unfolds the variables on the way there. The
        // schemas that lead to `e` with nothing in between are each a class of their own,
        // so that order is the one that it would be without the pass, and so is the
        // verdict.
        let definitions = json!({
            "e": {
                "oneOf": [
                    {"$ref": "#/$defs/f"},
                    {"maxProperties": 1, "type": "object"},
                    {"$ref": "#/$defs/e"},
                ],
                "pattern": "^a",
            },
            "f": {"$ref": "#/$defs/e"},
        });
        let (e, f) = (json!({"$ref": "#/$defs/e"}), json!({"$ref": "#/$defs/f"}));
        let short = json!({"pattern": "b$", "type": "string", "maxLength": 2, "minLength": 1});
        let some = json!({"anyOf": [
            {"anyOf": [{"not": e, "type": ["string", "null"]}]},
            {
                "if": {"const": true},
                "then": {"if": {"required": ["a"]}, "then": e, "else": e},
                "else": f,
            },
            {"allOf": [f, {"allOf": [short]}], "maximum": 1},
        ]});
        let mut a = some.clone();
        a["$defs"] = definitions.clone();
        let b = json!({"$defs": definitions, "oneOf": [some, e]});
        assert_eq!(Checker::new().subsumes(&a, &b).unwrap(), Verdict::Yes);
    }

    #[test]
    fn schemas_that_say_the_same_in_other_words_take_no_search() {
        // 32 kinds of object, written in two ways: each kind closed in its schema, or by a
        // second schema beside it. With each kind a variable of its own, the engine takes
        // hundreds of thousands of steps to see that the two say the same.
        let kinds = |in_two: bool| {
            let kind = |kind: usize| {
                let name = format!("k{kind}");
                let mut schema = json!({
                    "type": "object",
                    "properties": {"kind": {"const": name}, "value": {"type": "integer"}},
                    "required": ["kind"],
                });
                if !in_two {
                    schema["additionalProperties"] = json!(false);
                    return schema;
                }
                let named = json!({"^kind$": true, "^value$": true});
                let closed = json!({"patternProperties": named, "additionalProperties": false});
                json!({"allOf": [schema, closed]})
            };
            json!({"oneOf": (0..32).map(kind).collect::<Vec<_>>()})
        };
        let (plain, in_two) = (kinds(false), kinds(true));
        let few = Checker::new().budget(1_000);
        assert_eq!(few.subsumes(&plain, &in_two).unwrap(), Verdict::Yes);
        assert_eq!(few.subsumes(&in_two, &plain).unwrap(), Verdict::Yes);
    }

    /// A chain of schemas that each add a bound to the one before.
    fn chain(length: usize) -> Value {
        let mut definitions = Map::new();
        definitions.insert("s0".to_owned(), json!({"minimum": 0}));
        for at in 1..length {
            let before = json!({"$ref": format!("#/$defs/s{}", at - 1)});
            let schema = json!({"allOf": [before], "maximum": at});
            definitions.insert(format!("s{at}"), schema);
        }
        let last = format!("#/$defs/s{}", length - 1);
        json!({"$defs": definitions, "$ref": last})
    }

    #[test]
    fn the_pass_gives_up_at_a_multiple_of_the_size_of_the_terms() {
        // Each schema of a chain has the bounds of all before it in its canonical term,
        // which takes the square of the length of the chain.
        let gives_up = |length: usize| {
            let (a, b) = (chain(length), json!({"type": "string"}));
            let graph = parse(&a, &b).unwrap().link().unwrap();
            let mut context = Context::new(u64::MAX, RegexDialect::default());
            lower(&graph, &mut context).unwrap();
            classes(&context.terms, &context.languages, false).is_err()
        };
        assert!(!gives_up(100));
        assert!(gives_up(4_000));
        // A check goes on without it.
        let checker = Checker::new().budget(1_000_000);
        let long = chain(4_000);
        assert_eq!(checker.subsumes(&long, &long).unwrap(), Verdict::Yes);
        assert_eq!(
            checker.subsumes(&json!({"maximum": 0}), &long).unwrap(),
            Verdict::No {
                counterexample: json!(1)
            }
        );
    }
}
