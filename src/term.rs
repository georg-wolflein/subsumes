//! Terms: what the engine works on in place of keywords.
//!
//! A term says which instances it accepts. Terms are kept once each: two that are written
//! alike have one id, so equal ids mean equal terms.

use std::collections::HashMap;
use std::fmt::Write;

use crate::hash::{IdMap, IdSet};
use crate::language::{LanguageId, Languages};
use crate::rational::{Rational, shown};
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

/// A variable as it stands, or with `true` its negation.
pub(crate) type Literal = (VarId, bool);

/// The id of a c-reference: a set of variables, each as it stands or negated, that says what
/// all of them say together. It is what the value of a property has to satisfy, so that
/// schemas which meet in one property are named and never written out.
///
/// Two equal ids are one set. Two that differ may still accept the same instances.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct CRefId(u32);

impl CRefId {
    /// The ids from the least to the greatest, for a look at a range of them.
    pub const FIRST: Self = Self(0);
    pub const LAST: Self = Self(u32::MAX);
}

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
    /// The instance is this number.
    NumConst(Rational),
    /// The instance is no number, or a number that is at least this.
    Min(Rational),
    /// The instance is no number, or a number that is more than this.
    ExMin(Rational),
    /// The instance is no number, or a number that is at most this.
    Max(Rational),
    /// The instance is no number, or a number that is less than this.
    ExMax(Rational),
    /// The instance is no number, or a multiple of this, which is more than zero.
    Mof(Rational),
    /// The instance is this string.
    StrConst(Box<str>),
    /// The instance is no string, or a string of this language.
    Patt(LanguageId),
    /// The instance is no string, or a string of at least so many characters, which is
    /// more than none.
    MinLen(u64),
    /// The instance is no string, or a string of at most so many characters.
    MaxLen(u64),
    /// The instance is no object, or an object in which every property with a name of this
    /// language has a value that the schema of the variable accepts.
    PProp(LanguageId, VarId),
    /// The instance is no object, or an object with a property whose name is of this
    /// language.
    PReq(LanguageId),
    /// The instance is no object, or an object in which the name of every property is a
    /// string that the schema of the variable accepts.
    PNames(VarId),
    /// The instance is no object, or an object of at least so many properties, which is
    /// more than none.
    MinProps(u64),
    /// The instance is no object, or an object of at most so many properties.
    MaxProps(u64),
    /// The instance is no array, or an array whose item at this position, if it has one, is
    /// a value that the schema of the variable accepts. The first position is 0.
    Item(u64, VarId),
    /// The instance is no array, or an array in which every item from this position on is
    /// a value that the schema of the variable accepts.
    AddIts(u64, VarId),
    /// The instance is no array, or an array with an item that the schema of the variable
    /// accepts.
    Contains(VarId),
    /// The instance is no array, or an array of at least so many items, which is more than
    /// none.
    MinIts(u64),
    /// The instance is no array, or an array of at most so many items.
    MaxIts(u64),
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
    /// The c-references of more than no variable, the first of them with the id 2.
    references: Vec<Box<[Literal]>>,
    reference_ids: IdMap<Box<[Literal]>, CRefId>,
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

    pub fn num_const(&mut self, number: Rational) -> TermId {
        self.intern(Term::NumConst(number))
    }

    pub fn min(&mut self, at: Rational) -> TermId {
        self.intern(Term::Min(at))
    }

    pub fn ex_min(&mut self, at: Rational) -> TermId {
        self.intern(Term::ExMin(at))
    }

    pub fn max(&mut self, at: Rational) -> TermId {
        self.intern(Term::Max(at))
    }

    pub fn ex_max(&mut self, at: Rational) -> TermId {
        self.intern(Term::ExMax(at))
    }

    /// The term for "no number, or a multiple of `step`", which is more than zero.
    pub fn mof(&mut self, step: Rational) -> TermId {
        self.intern(Term::Mof(step))
    }

    pub fn str_const(&mut self, word: &str) -> TermId {
        self.intern(Term::StrConst(word.into()))
    }

    /// The term for "no string, or a string of this language".
    pub fn patt(&mut self, language: LanguageId) -> TermId {
        self.intern(match language {
            Languages::EVERYTHING => Term::True,
            _ => Term::Patt(language),
        })
    }

    /// The term for "no string, or a string of at least so many characters".
    pub fn min_len(&mut self, least: u64) -> TermId {
        self.intern(match least {
            0 => Term::True,
            _ => Term::MinLen(least),
        })
    }

    /// The term for "no string, or a string of at most so many characters".
    pub fn max_len(&mut self, most: u64) -> TermId {
        self.intern(Term::MaxLen(most))
    }

    /// The term for "no object, or every property with a name of this language satisfies
    /// the schema of the variable".
    pub fn p_prop(&mut self, names: LanguageId, variable: VarId) -> TermId {
        self.intern(match names {
            Languages::NOTHING => Term::True,
            _ => Term::PProp(names, variable),
        })
    }

    /// The term for "no object, or an object with a property whose name is of this
    /// language".
    pub fn p_req(&mut self, names: LanguageId) -> TermId {
        self.intern(Term::PReq(names))
    }

    /// The term for "no object, or the name of every property satisfies the schema of the
    /// variable".
    pub fn p_names(&mut self, variable: VarId) -> TermId {
        self.intern(Term::PNames(variable))
    }

    /// The term for "no object, or an object of at least so many properties".
    pub fn min_props(&mut self, least: u64) -> TermId {
        self.intern(match least {
            0 => Term::True,
            _ => Term::MinProps(least),
        })
    }

    /// The term for "no object, or an object of at most so many properties".
    pub fn max_props(&mut self, most: u64) -> TermId {
        self.intern(Term::MaxProps(most))
    }

    /// The term for "no array, or the item at this position, if there is one, satisfies the
    /// schema of the variable".
    pub fn item(&mut self, position: u64, variable: VarId) -> TermId {
        self.intern(Term::Item(position, variable))
    }

    /// The term for "no array, or every item from this position on satisfies the schema of
    /// the variable".
    pub fn add_its(&mut self, from: u64, variable: VarId) -> TermId {
        self.intern(Term::AddIts(from, variable))
    }

    /// The term for "no array, or an array with an item that satisfies the schema of the
    /// variable".
    pub fn contains(&mut self, variable: VarId) -> TermId {
        self.intern(Term::Contains(variable))
    }

    /// The term for "no array, or an array of at least so many items".
    pub fn min_its(&mut self, least: u64) -> TermId {
        self.intern(match least {
            0 => Term::True,
            _ => Term::MinIts(least),
        })
    }

    /// The term for "no array, or an array of at most so many items".
    pub fn max_its(&mut self, most: u64) -> TermId {
        self.intern(Term::MaxIts(most))
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
        let (mut kept, mut seen) = (Vec::new(), IdSet::default());
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
        let (mut kept, mut seen) = (Vec::new(), IdSet::default());
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

    /// The leaf for a `propertyNames` whose schema accepts strings that no language says,
    /// because it holds a leaf about strings itself. It is about objects, and stands where
    /// the schema of the variable does.
    pub fn names(&mut self, variable: VarId) -> LeafId {
        let object = TypeSet::of(InstanceType::Object);
        let node = self.variable(variable).node;
        self.leaf_of(object, format!("propertyNames x{}", variable.0), node, None)
    }

    /// The c-reference that accepts every instance.
    pub const ANYTHING: CRefId = CRefId(0);
    /// The c-reference that accepts no instance.
    pub const NOTHING: CRefId = CRefId(1);

    /// The c-reference of one variable, as it stands or negated. A variable whose schema
    /// is `true` or `false` is not named: the c-reference is what it says.
    ///
    /// Nor is a variable whose schema is another one, as that of `{"$ref": "#"}` is: the
    /// c-reference names that other one. So a schema that holds itself in a property asks
    /// of the value what was asked of the instance, by the same name.
    pub fn literal(&mut self, variable: VarId, negated: bool) -> CRefId {
        /// How many times a variable is put in the place of another. Variables that are
        /// each other's schema all the way round have no end of that.
        const FAR: usize = 16;
        let (mut variable, mut negated) = (variable, negated);
        for _ in 0..FAR {
            match self.term(self.variable(variable).body) {
                Term::True if negated => return Self::NOTHING,
                Term::True => return Self::ANYTHING,
                Term::False if negated => return Self::ANYTHING,
                Term::False => return Self::NOTHING,
                Term::Ref(other) => variable = *other,
                Term::Not(inner) => match self.term(*inner) {
                    Term::Ref(other) => (variable, negated) = (*other, !negated),
                    _ => break,
                },
                _ => break,
            }
        }
        self.reference_of(vec![(variable, negated)])
    }

    /// The variables of a c-reference, in order. The two that are of no variable have none.
    pub fn literals(&self, reference: CRefId) -> &[Literal] {
        match reference.0.checked_sub(2) {
            Some(index) => &self.references[index as usize],
            None => &[],
        }
    }

    /// The c-reference that says what two say together. A variable and its negation
    /// together accept nothing.
    pub fn both(&mut self, a: CRefId, b: CRefId) -> CRefId {
        if a == b || b == Self::ANYTHING || a == Self::NOTHING {
            return a;
        }
        if a == Self::ANYTHING || b == Self::NOTHING {
            return b;
        }
        let (of_a, of_b) = (self.literals(a), self.literals(b));
        let mut all = Vec::with_capacity(of_a.len() + of_b.len());
        let (mut at_a, mut at_b) = (0, 0);
        while at_a < of_a.len() || at_b < of_b.len() {
            let next = match (of_a.get(at_a), of_b.get(at_b)) {
                (Some(first), Some(second)) => *first.min(second),
                (Some(only), None) | (None, Some(only)) => *only,
                (None, None) => unreachable!("one of the two has a variable left"),
            };
            at_a += usize::from(of_a.get(at_a) == Some(&next));
            at_b += usize::from(of_b.get(at_b) == Some(&next));
            // A variable comes right before its negation.
            if all.last() == Some(&(next.0, !next.1)) {
                return Self::NOTHING;
            }
            all.push(next);
        }
        self.reference_of(all)
    }

    fn reference_of(&mut self, literals: Vec<Literal>) -> CRefId {
        if let Some(known) = self.reference_ids.get(literals.as_slice()) {
            return *known;
        }
        let literals: Box<[Literal]> = literals.into();
        let id = u32::try_from(self.references.len() + 2).expect("fewer than 2^32 c-references");
        self.references.push(literals.clone());
        self.reference_ids.insert(literals, CRefId(id));
        CRefId(id)
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

    /// A term as text, for tests. A language is named by its id, as in `patt(l2)`.
    #[cfg(test)]
    pub fn show(&self, id: TermId) -> String {
        let mut text = String::new();
        self.write(id, &mut text, &|language| format!("l{}", language.index()));
        text
    }

    /// A term as text for the viewer, with each language as the store of the check shows
    /// it: the pattern, or the name of the format.
    pub fn show_with(&self, id: TermId, languages: &Languages) -> String {
        let mut text = String::new();
        self.write(id, &mut text, &|language| languages.show(language));
        text
    }

    fn write(&self, id: TermId, text: &mut String, named: &dyn Fn(LanguageId) -> String) {
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
                Term::NumConst(number) => write_number(text, "is", number),
                Term::Min(at) => write_number(text, "min", at),
                Term::ExMin(at) => write_number(text, "exmin", at),
                Term::Max(at) => write_number(text, "max", at),
                Term::ExMax(at) => write_number(text, "exmax", at),
                Term::Mof(step) => write_number(text, "mof", step),
                Term::StrConst(word) => {
                    write!(text, "is({word:?})").expect("a string takes any text");
                }
                Term::Patt(language) => {
                    write!(text, "patt({})", named(*language)).expect("a string takes any text");
                }
                Term::MinLen(least) => {
                    write!(text, "minlen({least})").expect("a string takes any text");
                }
                Term::MaxLen(most) => {
                    write!(text, "maxlen({most})").expect("a string takes any text");
                }
                Term::PProp(names, variable) => {
                    write!(text, "pprop({}: x{})", named(*names), variable.0)
                        .expect("a string takes any text");
                }
                Term::PReq(names) => {
                    write!(text, "preq({})", named(*names)).expect("a string takes any text");
                }
                Term::PNames(variable) => {
                    write!(text, "pnames(x{})", variable.0).expect("a string takes any text");
                }
                Term::MinProps(least) => {
                    write!(text, "minprops({least})").expect("a string takes any text");
                }
                Term::MaxProps(most) => {
                    write!(text, "maxprops({most})").expect("a string takes any text");
                }
                Term::Item(position, variable) => {
                    write!(text, "item({position}: x{})", variable.0)
                        .expect("a string takes any text");
                }
                Term::AddIts(from, variable) => {
                    write!(text, "addits({from}: x{})", variable.0)
                        .expect("a string takes any text");
                }
                Term::Contains(variable) => {
                    write!(text, "contains(x{})", variable.0).expect("a string takes any text");
                }
                Term::MinIts(least) => {
                    write!(text, "minits({least})").expect("a string takes any text");
                }
                Term::MaxIts(most) => {
                    write!(text, "maxits({most})").expect("a string takes any text");
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

/// Writes a term about numbers, such as `min(0.5)`.
fn write_number(text: &mut String, name: &str, number: &Rational) {
    write!(text, "{name}({})", shown(number)).expect("a string takes any text");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rational::testing::number;

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
    fn a_term_about_numbers_holds_the_number_itself() {
        let mut terms = Terms::default();
        // However the number was written.
        assert_eq!(terms.min(number("1")), terms.min(number("1.0")));
        assert_eq!(terms.mof(number("0.5")), terms.mof(number("5e-1")));
        assert_ne!(terms.min(number("1")), terms.ex_min(number("1")));
        assert_ne!(terms.min(number("1")), terms.max(number("1")));
        assert_eq!(terms.num_const(number("1e0")), terms.num_const(number("1")));
        let all = [
            terms.num_const(number("2")),
            terms.min(number("0.5")),
            terms.ex_min(number("-1")),
            terms.max(number("1e30")),
            terms.ex_max(number("3")),
            terms.mof(number("0.01")),
        ];
        let all = terms.all_of(all);
        assert_eq!(
            terms.show(all),
            "all(is(2), min(0.5), exmin(-1), max(1e+30), exmax(3), mof(0.01))"
        );
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
    fn a_c_reference_is_a_set_of_variables_as_they_stand_or_negated() {
        let mut terms = Terms::default();
        let variables: Vec<VarId> = (0..3)
            .map(|index| {
                let variable = terms.new_variable(NodeId::new(0));
                terms.variable_mut(variable).body = leaf(&mut terms, &format!("{index}"));
                variable
            })
            .collect();
        let [x, y, z] = [0, 1, 2].map(|index| terms.literal(variables[index], false));
        let not_x = terms.literal(variables[0], true);
        assert_ne!(x, not_x);
        assert_eq!(terms.literals(x), [(variables[0], false)]);
        // Two sets together are one set, in whichever order they come.
        let (xy, yz) = (terms.both(x, y), terms.both(y, z));
        assert_eq!(terms.both(xy, yz), terms.both(z, xy));
        assert_eq!(terms.both(xy, x), xy);
        let all = terms.both(yz, x);
        assert_eq!(
            terms.literals(all),
            [0, 1, 2].map(|index| (variables[index], false))
        );
        // A variable and its negation accept nothing together.
        assert_eq!(terms.both(x, not_x), Terms::NOTHING);
        assert_eq!(terms.both(not_x, xy), Terms::NOTHING);
        assert_eq!(terms.both(Terms::ANYTHING, xy), xy);
        assert_eq!(terms.both(xy, Terms::ANYTHING), xy);
        assert_eq!(terms.both(xy, Terms::NOTHING), Terms::NOTHING);
        assert_eq!(terms.both(Terms::NOTHING, xy), Terms::NOTHING);
        assert!(terms.literals(Terms::ANYTHING).is_empty());
    }

    #[test]
    fn a_c_reference_names_no_variable_that_says_nothing_of_its_own() {
        let mut terms = Terms::default();
        let variable = |terms: &mut Terms, body: TermId| {
            let variable = terms.new_variable(NodeId::new(0));
            terms.variable_mut(variable).body = body;
            variable
        };
        let (yes, no) = (terms.truth(), terms.falsity());
        let (anything, nothing) = (variable(&mut terms, yes), variable(&mut terms, no));
        assert_eq!(terms.literal(anything, false), Terms::ANYTHING);
        assert_eq!(terms.literal(anything, true), Terms::NOTHING);
        assert_eq!(terms.literal(nothing, false), Terms::NOTHING);
        assert_eq!(terms.literal(nothing, true), Terms::ANYTHING);
        // A variable whose schema is another one, or the negation of another one.
        let body = leaf(&mut terms, "a");
        let said = variable(&mut terms, body);
        let reference = terms.reference(said);
        let same = variable(&mut terms, reference);
        let negation = terms.not(reference);
        let other = variable(&mut terms, negation);
        let reference = terms.reference(other);
        let again = variable(&mut terms, reference);
        assert_eq!(terms.literal(same, false), terms.literal(said, false));
        assert_eq!(terms.literal(same, true), terms.literal(said, true));
        assert_eq!(terms.literal(other, false), terms.literal(said, true));
        assert_eq!(terms.literal(again, true), terms.literal(said, false));
        // One that is its own schema stays as it is.
        let endless = terms.new_variable(NodeId::new(0));
        terms.variable_mut(endless).body = terms.reference(endless);
        let negated = terms.literal(endless, true);
        assert_eq!(terms.literals(negated), [(endless, true)]);
    }

    #[test]
    fn a_term_about_objects_is_written_with_its_names() {
        let mut terms = Terms::default();
        let mut languages = Languages::default();
        let variable = terms.new_variable(NodeId::new(0));
        let named = languages.words(["a"]);
        let all = [
            terms.p_prop(named, variable),
            terms.p_req(named),
            terms.p_names(variable),
            terms.min_props(2),
            terms.max_props(3),
        ];
        let all = terms.all_of(all);
        assert_eq!(
            terms.show_with(all, &languages),
            r#"all(pprop(one of ["a"]: x0), preq(one of ["a"]), pnames(x0), minprops(2), maxprops(3))"#
        );
        // What is asked of no name, and at least no property, is asked of nothing.
        assert_eq!(terms.p_prop(Languages::NOTHING, variable), terms.truth());
        assert_eq!(terms.min_props(0), terms.truth());
    }

    #[test]
    fn a_term_about_arrays_is_written_with_its_position() {
        let mut terms = Terms::default();
        let variable = terms.new_variable(NodeId::new(0));
        let all = [
            terms.item(1, variable),
            terms.add_its(2, variable),
            terms.contains(variable),
            terms.min_its(2),
            terms.max_its(3),
        ];
        let all = terms.all_of(all);
        assert_eq!(
            terms.show(all),
            "all(item(1: x0), addits(2: x0), contains(x0), minits(2), maxits(3))"
        );
        // At least no item is asked of nothing.
        assert_eq!(terms.min_its(0), terms.truth());
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
