//! Terms: what the engine works on in place of keywords.
//!
//! A term says which instances it accepts. Terms are kept once each: two that are written
//! alike have one id, so equal ids mean equal terms.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::schema::{Graph, NodeId};

/// One of the six types that an instance has. `integer` is none of them: an integer is a
/// number that is a multiple of one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InstanceType {
    Null,
    Boolean,
    Number,
    String,
    Array,
    Object,
}

impl InstanceType {
    pub const ALL: [Self; 6] = [
        Self::Null,
        Self::Boolean,
        Self::Number,
        Self::String,
        Self::Array,
        Self::Object,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Self::Null => "null",
            Self::Boolean => "boolean",
            Self::Number => "number",
            Self::String => "string",
            Self::Array => "array",
            Self::Object => "object",
        }
    }
}

/// A set of instance types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct TypeSet(u8);

impl TypeSet {
    pub const NONE: Self = Self(0);
    pub const ALL: Self = Self(0b11_1111);

    pub const fn of(kind: InstanceType) -> Self {
        Self(1 << kind as u8)
    }

    pub fn contains(self, kind: InstanceType) -> bool {
        self.0 & (1 << kind as u8) != 0
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[must_use]
    pub fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// The types that are not in the set.
    #[must_use]
    pub const fn complement(self) -> Self {
        Self(!self.0 & Self::ALL.0)
    }

    pub fn iter(self) -> impl Iterator<Item = InstanceType> {
        InstanceType::ALL
            .into_iter()
            .filter(move |kind| self.contains(*kind))
    }
}

/// The id of a term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TermId(u32);

/// The id of a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct VarId(u32);

/// The id of a predicate that the engine does not model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct LeafId(u32);

impl VarId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl LeafId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Term {
    True,
    False,
    /// The instance has one of these types.
    TypeIs(TypeSet),
    /// The instance is this boolean.
    BoolConst(bool),
    /// The instance satisfies a predicate that the engine does not model.
    Unknown(LeafId),
    AllOf(Box<[TermId]>),
    AnyOf(Box<[TermId]>),
    /// Exactly one of them holds. It stays one term, because written out with the others it
    /// takes the square of its length.
    OneOf(Box<[TermId]>),
    Not(TermId),
    /// What the variable stands for.
    Ref(VarId),
}

/// A predicate that the engine does not model: a keyword, with what it holds.
///
/// It is never taken for true or false. Two leaves are one only when they must hold for the
/// same instances, which lets a schema subsume itself whatever it contains.
#[derive(Debug)]
pub(crate) struct Leaf {
    /// The types of instance that the predicate says something about. An instance of another
    /// type satisfies it, as a number satisfies `minLength`.
    pub domain: TypeSet,
    /// The keyword and what it holds, which tells the predicate from every other.
    pub key: String,
    /// The schema in which it was first found, and the keyword there. Without a keyword the
    /// leaf is about the schema as a whole.
    pub node: NodeId,
    pub keyword: Option<&'static str>,
}

impl Leaf {
    /// Where the leaf was first found.
    pub fn location(&self, graph: &Graph) -> String {
        match self.keyword {
            Some(keyword) => graph.keyword_location(self.node, keyword),
            None => graph.location(self.node),
        }
    }
}

/// A name for the term of a schema, so that a schema that refers to itself has a term.
#[derive(Debug)]
pub(crate) struct Variable {
    /// The first schema that the variable stands for. Others may say the same.
    pub node: NodeId,
    /// Whether a schema of A and one of B is among them.
    pub sides: [bool; 2],
    pub body: TermId,
}

/// Every term, leaf and variable of a check.
#[derive(Debug, Default)]
pub(crate) struct Terms {
    terms: Vec<Term>,
    ids: HashMap<Term, TermId>,
    leaves: Vec<Leaf>,
    leaf_ids: HashMap<(TypeSet, String), LeafId>,
    variables: Vec<Variable>,
}

impl Terms {
    pub fn term(&self, id: TermId) -> &Term {
        &self.terms[id.0 as usize]
    }

    pub fn leaf(&self, id: LeafId) -> &Leaf {
        &self.leaves[id.index()]
    }

    pub fn variable(&self, id: VarId) -> &Variable {
        &self.variables[id.index()]
    }

    pub fn variables(&self) -> impl Iterator<Item = (VarId, &Variable)> {
        let ids = (0..).map(VarId);
        ids.zip(&self.variables)
    }

    fn intern(&mut self, term: Term) -> TermId {
        if let Some(&id) = self.ids.get(&term) {
            return id;
        }
        let id =
            TermId(u32::try_from(self.terms.len()).expect("a check has fewer than 2^32 terms"));
        self.terms.push(term.clone());
        self.ids.insert(term, id);
        id
    }

    pub fn truth(&mut self) -> TermId {
        self.intern(Term::True)
    }

    pub fn falsity(&mut self) -> TermId {
        self.intern(Term::False)
    }

    pub fn type_is(&mut self, types: TypeSet) -> TermId {
        self.intern(match types {
            TypeSet::ALL => Term::True,
            TypeSet::NONE => Term::False,
            _ => Term::TypeIs(types),
        })
    }

    pub fn bool_const(&mut self, value: bool) -> TermId {
        self.intern(Term::BoolConst(value))
    }

    /// The term of a predicate that the engine does not model. `key` tells it from every
    /// other predicate over the same types; `node` and `keyword` say where it stands.
    pub fn unknown(
        &mut self,
        domain: TypeSet,
        key: String,
        node: NodeId,
        keyword: &'static str,
    ) -> TermId {
        let leaf = self.leaf_of(domain, key, node, Some(keyword));
        self.intern(Term::Unknown(leaf))
    }

    /// The leaf with this key over these types, which is a new one if there is none yet.
    fn leaf_of(
        &mut self,
        domain: TypeSet,
        key: String,
        node: NodeId,
        keyword: Option<&'static str>,
    ) -> LeafId {
        let next = LeafId(u32::try_from(self.leaves.len()).expect("fewer than 2^32 leaves"));
        let id = *self.leaf_ids.entry((domain, key.clone())).or_insert(next);
        if id == next {
            self.leaves.push(Leaf {
                domain,
                key,
                node,
                keyword,
            });
        }
        id
    }

    /// The conjunction, without what says nothing in it.
    pub fn all_of(&mut self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        let (mut kept, mut seen) = (Vec::new(), HashSet::new());
        for id in terms {
            let flat = match self.term(id) {
                Term::True => continue,
                Term::False => return id,
                Term::AllOf(inner) => inner.to_vec(),
                _ => vec![id],
            };
            kept.extend(flat.into_iter().filter(|id| seen.insert(*id)));
        }
        match kept.as_slice() {
            [] => self.truth(),
            [only] => *only,
            _ => self.intern(Term::AllOf(kept.into())),
        }
    }

    /// The disjunction, without what says nothing in it.
    pub fn any_of(&mut self, terms: impl IntoIterator<Item = TermId>) -> TermId {
        let (mut kept, mut seen) = (Vec::new(), HashSet::new());
        for id in terms {
            let flat = match self.term(id) {
                Term::False => continue,
                Term::True => return id,
                Term::AnyOf(inner) => inner.to_vec(),
                _ => vec![id],
            };
            kept.extend(flat.into_iter().filter(|id| seen.insert(*id)));
        }
        match kept.as_slice() {
            [] => self.falsity(),
            [only] => *only,
            _ => self.intern(Term::AnyOf(kept.into())),
        }
    }

    pub fn one_of(&mut self, terms: Vec<TermId>) -> TermId {
        match terms.as_slice() {
            [] => self.falsity(),
            [only] => *only,
            _ => self.intern(Term::OneOf(terms.into())),
        }
    }

    pub fn not(&mut self, term: TermId) -> TermId {
        let negated = match self.term(term) {
            Term::True => Term::False,
            Term::False => Term::True,
            Term::TypeIs(types) => Term::TypeIs(types.complement()),
            Term::Not(inner) => return *inner,
            _ => Term::Not(term),
        };
        self.intern(negated)
    }

    pub fn reference(&mut self, variable: VarId) -> TermId {
        self.intern(Term::Ref(variable))
    }

    /// The leaf for a schema that refers to itself in a way that the engine does not model.
    /// It is about every instance. `node` is the schema in which the cycle closes: the one
    /// that leads back to the variable. Which of its keywords does is not kept.
    pub fn recursion(&mut self, variable: VarId, node: NodeId) -> LeafId {
        let key = format!("recursion x{} @{}", variable.0, node.index());
        self.leaf_of(TypeSet::ALL, key, node, None)
    }

    /// A new variable for a schema. Its term is given later, because the term may refer to
    /// the variable.
    pub fn new_variable(&mut self, node: NodeId) -> VarId {
        let id = VarId(u32::try_from(self.variables.len()).expect("fewer than 2^32 variables"));
        let body = self.truth();
        self.variables.push(Variable {
            node,
            sides: [false; 2],
            body,
        });
        id
    }

    pub fn variable_mut(&mut self, id: VarId) -> &mut Variable {
        &mut self.variables[id.index()]
    }

    /// A term as text, for tests and for the viewer.
    pub fn show(&self, id: TermId) -> String {
        let mut text = String::new();
        self.write(id, &mut text);
        text
    }

    fn write(&self, id: TermId, text: &mut String) {
        // The work left: a term to write, or text that follows what was written.
        enum Step {
            Term(TermId),
            Text(&'static str),
        }
        let mut steps = vec![Step::Term(id)];
        while let Some(step) = steps.pop() {
            let id = match step {
                Step::Term(id) => id,
                Step::Text(follows) => {
                    text.push_str(follows);
                    continue;
                }
            };
            let listed = |name: &'static str, terms: &[TermId], steps: &mut Vec<Step>| {
                steps.push(Step::Text(")"));
                for (position, term) in terms.iter().enumerate().rev() {
                    steps.push(Step::Term(*term));
                    if position > 0 {
                        steps.push(Step::Text(", "));
                    }
                }
                name
            };
            match self.term(id) {
                Term::True => text.push_str("true"),
                Term::False => text.push_str("false"),
                Term::TypeIs(types) => {
                    let names: Vec<&str> = types.iter().map(InstanceType::name).collect();
                    write!(text, "type({})", names.join(" | ")).expect("a string takes any text");
                }
                Term::BoolConst(value) => {
                    write!(text, "is({value})").expect("a string takes any text");
                }
                Term::Unknown(leaf) => {
                    write!(text, "?[{}]", self.leaf(*leaf).key).expect("a string takes any text");
                }
                Term::AllOf(terms) => text.push_str(listed("all(", terms, &mut steps)),
                Term::AnyOf(terms) => text.push_str(listed("any(", terms, &mut steps)),
                Term::OneOf(terms) => text.push_str(listed("one(", terms, &mut steps)),
                Term::Not(inner) => {
                    text.push_str("not ");
                    steps.push(Step::Term(*inner));
                }
                Term::Ref(variable) => {
                    write!(text, "x{}", variable.0).expect("a string takes any text");
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(terms: &mut Terms, key: &str) -> TermId {
        let string = TypeSet::of(InstanceType::String);
        terms.unknown(string, key.to_owned(), NodeId::new(0), "pattern")
    }

    #[test]
    fn a_set_of_types_is_a_set() {
        let string = TypeSet::of(InstanceType::String);
        let null = TypeSet::of(InstanceType::Null);
        let both = string.union(null);
        assert!(both.contains(InstanceType::String) && both.contains(InstanceType::Null));
        assert!(!both.contains(InstanceType::Number));
        assert_eq!(both.intersection(string), string);
        assert!(string.intersection(null).is_empty());
        assert_eq!(both.complement().iter().count(), 4);
        assert_eq!(both.complement().union(both), TypeSet::ALL);
        assert_eq!(TypeSet::NONE.complement(), TypeSet::ALL);
    }

    #[test]
    fn terms_that_are_written_alike_are_one() {
        let mut terms = Terms::default();
        let a = leaf(&mut terms, "pattern \"a\"");
        let again = leaf(&mut terms, "pattern \"a\"");
        let b = leaf(&mut terms, "pattern \"b\"");
        assert_eq!(a, again);
        assert_ne!(a, b);
        assert_eq!(terms.all_of([a, b]), terms.all_of([a, b]));
        assert_ne!(terms.all_of([a, b]), terms.any_of([a, b]));
        // A predicate over other types is another predicate.
        let number = TypeSet::of(InstanceType::Number);
        let other = terms.unknown(number, "pattern \"a\"".to_owned(), NodeId::new(0), "x");
        assert_ne!(a, other);
    }

    #[test]
    fn a_connective_drops_what_says_nothing() {
        let mut terms = Terms::default();
        let (yes, no) = (terms.truth(), terms.falsity());
        let (a, b) = (leaf(&mut terms, "a"), leaf(&mut terms, "b"));
        assert_eq!(terms.all_of([]), yes);
        assert_eq!(terms.any_of([]), no);
        assert_eq!(terms.all_of([yes, a, yes]), a);
        assert_eq!(terms.any_of([no, a]), a);
        assert_eq!(terms.all_of([a, no, b]), no);
        assert_eq!(terms.any_of([a, yes]), yes);
        assert_eq!(terms.all_of([a, a, b]), terms.all_of([a, b]));
        // A conjunction in a conjunction is part of it.
        let both = terms.all_of([a, b]);
        let c = leaf(&mut terms, "c");
        let nested = terms.all_of([both, c]);
        assert_eq!(terms.show(nested), "all(?[a], ?[b], ?[c])");
        let either = terms.any_of([a, b]);
        let nested = terms.any_of([c, either]);
        assert_eq!(terms.show(nested), "any(?[c], ?[a], ?[b])");
        assert_eq!(terms.one_of(vec![]), no);
        assert_eq!(terms.one_of(vec![a]), a);
        assert_eq!(terms.type_is(TypeSet::ALL), yes);
        assert_eq!(terms.type_is(TypeSet::NONE), no);
    }

    #[test]
    fn a_negation_is_undone_where_that_is_plain() {
        let mut terms = Terms::default();
        let (yes, no) = (terms.truth(), terms.falsity());
        let a = leaf(&mut terms, "a");
        let not_a = terms.not(a);
        assert_eq!(terms.not(yes), no);
        assert_eq!(terms.not(no), yes);
        assert_eq!(terms.not(not_a), a);
        let string = terms.type_is(TypeSet::of(InstanceType::String));
        let other = terms.not(string);
        assert_eq!(
            terms.show(other),
            "type(null | boolean | number | array | object)"
        );
        // Further in, it stays where it is until the engine gets there.
        let both = terms.all_of([a, string]);
        let negated = terms.not(both);
        assert_eq!(terms.show(negated), "not all(?[a], type(string))");
    }

    #[test]
    fn a_deep_term_is_written_without_recursion() {
        let mut terms = Terms::default();
        let mut term = leaf(&mut terms, "a");
        let other = leaf(&mut terms, "b");
        for _ in 0..100_000 {
            let negated = terms.not(term);
            term = terms.any_of([negated, other]);
        }
        assert!(terms.show(term).starts_with("any(not any(not any("));
    }
}
