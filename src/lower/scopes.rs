//! The dynamic scope that each schema is reached in.
//!
//! What a `$dynamicRef` leads to depends on the way that led to it. Of the resources on the
//! way from the root, the outermost one that has a dynamic anchor of the name is the one
//! whose anchor is meant. That way is a way through the schemas, and no instance has a part
//! in it. So it is followed here, before there are terms, and to the terms a `$dynamicRef`
//! is a reference like any other.
//!
//! All that matters of a way is, for each name, the first resource on it that has a dynamic
//! anchor of that name. That is the dynamic scope here: a name is bound when a resource with
//! such an anchor is entered, and stays bound from there on. A schema is reached once for
//! each scope that a way to it ends in, and it may say one thing in one of them and another
//! in the next.
//!
//! Only the names that some `$dynamicRef` looks for are bound. So for schemas without one
//! there is one scope, which binds nothing, and every schema is reached in it once.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::context::{Budget, Exhausted};
use crate::schema::{DynamicReference, Graph, Keywords, NodeId, Schema};

/// The id of a dynamic scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct ScopeId(u32);

impl ScopeId {
    /// The scope that binds no name: the one before the root is entered.
    pub const NOTHING: Self = Self(0);

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// A schema as it is reached: the node, and the dynamic scope with its resource entered.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Reached {
    pub node: NodeId,
    pub scope: ScopeId,
}

/// What a scope binds: for each name, the node with the dynamic anchor that it means.
type Bound<'g> = BTreeMap<&'g str, NodeId>;

/// Every schema that A and B lead to, once for each dynamic scope that it is reached in.
#[derive(Debug)]
pub(super) struct Scopes<'g> {
    graph: &'g Graph<'g>,
    /// The dynamic anchors of each resource that a `$dynamicRef` looks for, by the node
    /// that begins the resource: the name, and the node that has the anchor.
    anchors: HashMap<NodeId, Vec<(&'g str, NodeId)>>,
    bound: Vec<Bound<'g>>,
    scope_ids: HashMap<Bound<'g>, ScopeId>,
    reached: Vec<Reached>,
    places: HashMap<Reached, usize>,
    /// For each schema as it is reached, the schemas that it leads to, as they are reached
    /// from it: those of its keywords, the target of its `$ref`, and what its `$dynamicRef`
    /// leads to in its scope.
    leads_to: Vec<Vec<usize>>,
}

fn keywords<'g>(graph: &'g Graph<'g>, id: NodeId) -> Option<&'g Keywords<'g>> {
    match &graph.node(id).schema {
        Schema::Bool(_) => None,
        Schema::Object(keywords) => Some(keywords),
    }
}

impl<'g> Scopes<'g> {
    /// Follows every way from A and from B.
    ///
    /// # Errors
    ///
    /// When there are more schemas and scopes than the budget covers. A schema that is
    /// reached in a second scope costs a step, so without a `$dynamicRef` the work costs
    /// nothing.
    pub fn of(graph: &'g Graph<'g>, budget: &mut Budget) -> Result<Self, Exhausted> {
        let nodes = || (0..graph.len()).map(NodeId::new);
        let looked_for: HashSet<&str> = nodes()
            .filter_map(|id| keywords(graph, id)?.dynamic_reference?.anchor)
            .collect();
        let mut anchors: HashMap<NodeId, Vec<(&str, NodeId)>> = HashMap::new();
        for id in nodes() {
            let name = keywords(graph, id).and_then(|keywords| keywords.dynamic_anchor);
            if let Some(name) = name.filter(|name| looked_for.contains(name)) {
                let resource = graph.node(id).resource;
                anchors.entry(resource).or_default().push((name, id));
            }
        }
        let mut scopes = Self {
            graph,
            anchors,
            bound: vec![Bound::new()],
            scope_ids: HashMap::from([(Bound::new(), ScopeId::NOTHING)]),
            reached: Vec::new(),
            places: HashMap::new(),
            leads_to: Vec::new(),
        };
        // Where no name is looked for, every schema is in the one scope whichever way leads
        // to it, and they are taken in the order of the nodes, reached or not. Otherwise
        // only what A and B lead to is.
        let begin: Vec<NodeId> = if looked_for.is_empty() {
            nodes().collect()
        } else {
            vec![graph.a, graph.b]
        };
        for root in begin {
            scopes.enter(root, ScopeId::NOTHING);
        }
        let mut next = 0;
        while let Some(&Reached { node, scope }) = scopes.reached.get(next) {
            next += 1;
            let mut leads_to = Vec::new();
            for to in scopes.applied(node, scope) {
                let known = scopes.reached.len();
                leads_to.push(scopes.enter(to, scope));
                if scopes.reached.len() > known {
                    budget.charge(1)?;
                }
            }
            scopes.leads_to.push(leads_to);
        }
        Ok(scopes)
    }

    /// How many schemas there are, counting one once for each scope that it is reached in.
    pub fn len(&self) -> usize {
        self.reached.len()
    }

    pub fn at(&self, index: usize) -> Reached {
        self.reached[index]
    }

    /// What each schema leads to, in the order in which [`applied`](Self::applied) names
    /// it.
    pub fn leads_to(&self) -> &[Vec<usize>] {
        &self.leads_to
    }

    /// A node as it is reached from a schema in this scope. The way to it has been
    /// followed: it is one that [`applied`](Self::applied) names for that schema.
    pub fn from(&self, node: NodeId, scope: ScopeId) -> usize {
        let scope = match self.entering(node, scope) {
            Some(bound) => self.scope_ids[&bound],
            None => scope,
        };
        self.places[&Reached { node, scope }]
    }

    /// What a `$dynamicRef` leads to in a scope: the anchor that the scope binds its name
    /// to, or its first target where it looks for no anchor or the scope binds none.
    pub fn resolved(&self, dynamic: DynamicReference, scope: ScopeId) -> NodeId {
        let bound = &self.bound[scope.index()];
        let anchor = dynamic.anchor.and_then(|name| bound.get(name));
        anchor.copied().unwrap_or(dynamic.target)
    }

    /// The nodes that a schema leads to in a scope: the subschemas of its keywords, the
    /// target of its `$ref`, and what its `$dynamicRef` leads to.
    fn applied(&self, node: NodeId, scope: ScopeId) -> Vec<NodeId> {
        let Some(keywords) = keywords(self.graph, node) else {
            return Vec::new();
        };
        let dynamic = keywords.dynamic_reference;
        let dynamic = dynamic.map(|dynamic| self.resolved(dynamic, scope));
        let subschemas = keywords.subschemas().into_iter().map(|(_, _, to)| to);
        subschemas
            .chain(keywords.reference)
            .chain(dynamic)
            .collect()
    }

    /// What is bound once the resource of a node is entered from a scope, or `None` if the
    /// resource has no anchor to bind. A name that is bound stays as it is.
    fn entering(&self, node: NodeId, from: ScopeId) -> Option<Bound<'g>> {
        let anchors = self.anchors.get(&self.graph.node(node).resource)?;
        let mut bound = self.bound[from.index()].clone();
        for (name, anchor) in anchors {
            bound.entry(name).or_insert(*anchor);
        }
        Some(bound)
    }

    /// Reaches a node from a schema in a scope, and says which of the reached schemas it
    /// is.
    fn enter(&mut self, node: NodeId, from: ScopeId) -> usize {
        let scope = match self.entering(node, from) {
            None => from,
            Some(bound) => {
                let next = u32::try_from(self.bound.len()).expect("fewer than 2^32 scopes");
                let scope = *self.scope_ids.entry(bound.clone()).or_insert(ScopeId(next));
                if scope.index() == self.bound.len() {
                    self.bound.push(bound);
                }
                scope
            }
        };
        let reached = Reached { node, scope };
        let next = self.reached.len();
        let place = *self.places.entry(reached).or_insert(next);
        if place == next {
            self.reached.push(reached);
        }
        place
    }
}
