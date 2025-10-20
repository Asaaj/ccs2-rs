use std::{
    borrow::Borrow,
    cell::{Cell, Ref, RefCell},
    collections::{BTreeSet, BinaryHeap, HashSet},
    hash::Hash,
    ops::{Deref, DerefMut},
    rc::Rc,
};

use indexmap::{IndexMap, IndexSet};

use crate::ast::{
    Clause, Constraint, Expr, Formula, FormulaExpr, Key, Op, PropDef, RuleTreeNode, Specificity,
};

#[derive(thiserror::Error, Debug)]
pub enum DagError {}

pub struct Dag {
    children: IndexMap<String, LiteralMatcher>,
    prop_node: Node,
    next_node_id: usize,
    node_data: IndexMap<Node, NodeData>,
}
impl Default for Dag {
    fn default() -> Self {
        let mut dag = Self {
            children: IndexMap::default(),
            prop_node: Node(0),
            next_node_id: 0, // Temporary
            node_data: IndexMap::default(),
        };

        dag.prop_node = Node::or(&mut dag);
        dag
    }
}
impl Dag {
    pub fn stats(&self) -> Stats {
        todo!()
    }

    fn new_node(&mut self, data: NodeData) -> Node {
        let node = Node(self.next_id());
        debug_assert!(!self.node_data.contains_key(&node));
        self.node_data.insert(node, data);
        node
    }

    fn next_id(&mut self) -> usize {
        let id = self.next_node_id;
        self.next_node_id += 1;
        id
    }

    fn get_data(&self, node: Node) -> &NodeData {
        &self.node_data[&node]
    }

    fn get_data_mut(&mut self, node: Node) -> &mut NodeData {
        &mut self.node_data[&node]
    }

    pub fn build(mut rule_tree_nodes: Vec<RuleTreeNode>) -> Self {
        let mut dag = Self::default();
        let mut lit_nodes = IndexMap::<Key, Node>::default();

        // obviously there are better ways of gathering the unique literals and unique clauses,
        // if performance needs to be improved...
        rule_tree_nodes.sort_by(|lhs, rhs| lhs.formula.cmp(&rhs.formula));
        let mut all_clauses: Vec<_> = rule_tree_nodes
            .iter()
            .flat_map(|f| f.formula.elements().union(f.formula.shared()))
            .collect();

        for lit in all_clauses.iter().flat_map(|c| c.elements()) {
            lit_nodes.insert(lit.clone().into(), dag.add_literal(lit));
        }
        let mut clause_nodes = IndexMap::<Clause, Node>::default();
        all_clauses.sort();
        for clause in all_clauses.into_iter() {
            if !clause.is_empty() {
                let specificity = clause.specificity();
                clause_nodes[clause] = dag.build_expr(
                    clause.clone(),
                    || NodeData::and(specificity),
                    &mut lit_nodes,
                    &mut clause_nodes,
                )
            }
        }

        let mut form_nodes = IndexMap::<Formula, Node>::default();
        for rule in rule_tree_nodes {
            let node = if rule.formula.is_empty() {
                dag.prop_node
            } else {
                let node = dag.build_expr(
                    rule.formula.clone(),
                    || NodeData::or(),
                    &mut clause_nodes,
                    &mut form_nodes,
                );
                form_nodes.insert(rule.formula, node);
                node
            };
            let data = dag.get_data_mut(node);
            data.props.extend(rule.props.iter().cloned());
            data.constraints
                .extend(rule.constraints.iter().cloned().map(Into::into));
        }

        dag
    }

    fn add_literal(&mut self, lit: &Key) -> Node {
        let mut node_data = NodeData::and(lit.specificity);
        node_data.add_link();
        let node = self.new_node(node_data);
        self.children
            .entry(lit.name.clone())
            .or_default()
            .add_values(lit.values.clone(), node);
        node
    }

    fn build_expr<E: NodeCreatorCollection>(
        &mut self,
        expr: E,
        constructor: impl Fn() -> NodeData,
        base_nodes: &mut IndexMap<E::Item, Node>, // Existing graph state
        these_nodes: &mut IndexMap<E, Node>,      // Accumulator for current "layer"
    ) -> Node {
        assert!(!expr.is_empty());

        if expr.len() == 1 {
            return these_nodes[&expr].clone();
        } else if expr.len() == 2 {
            let mut node_data = constructor();
            node_data.add_links(expr.len());
            let node: Node = self.new_node(node_data);

            for el in expr.elements().iter().cloned() {
                self.get_data_mut(base_nodes[&el]).children.push(node);
            }
        }

        let mut item_collection_indices = IndexMap::<E::Item, Vec<usize>>::default();
        for (i, c) in these_nodes.keys().enumerate() {
            if c.is_subset(&expr) {
                assert!(
                    c.len() < expr.len(),
                    "Exact equality should be handled above"
                );
                for el in c.elements() {
                    item_collection_indices[el].push(i);
                }
            }
        }

        let mut covered = BTreeSet::new();
        let node: Node = self.new_node(constructor());
        let mut collections: Vec<_> = these_nodes.keys().cloned().collect();
        collections.sort_by(|l, r| r.cmp(l)); // TODO: Confusing and maybe inefficient?

        // TODO: this constant re-ranking is not very nice, but it should be roughly the same
        // algorithmic complexity as the Python implementation, which re-heapifies the ranking list
        // on every iteration. Still, this should be rethought
        let biggest_collection = |covered_elements: &BTreeSet<E::Item>| {
            let collection_rank = |c: &E| {
                c.elements()
                    .iter()
                    .filter(|e| !covered_elements.contains(*e))
                    .count()
            };
            collections
                .iter()
                .map(|collection| (collection_rank(collection), collection))
                .filter(|(rank, _)| *rank != 0)
                .max_by_key(|(rank, _)| *rank)
                .map(|(_, collection)| collection)
        };

        while let Some(best) = biggest_collection(&covered) {
            eprintln!("BEST: {best:?}");
            self.get_data_mut(these_nodes[best]).children.push(node);
            self.get_data_mut(node).add_link();
            for el in best.elements() {
                if !covered.contains(el) {
                    covered.insert(el.clone());
                }
            }
        }

        let remaining = expr.elements() - &covered;
        self.get_data_mut(node).add_links(remaining.len());
        for el in remaining {
            self.get_data_mut(base_nodes[&el]).children.push(node);
        }

        node
    }
}

trait NodeCreator: Hash + Eq + Ord + Clone + std::fmt::Debug {}
impl NodeCreator for Key {}
impl NodeCreator for Clause {}
impl NodeCreator for Formula {}

trait NodeCreatorCollection: NodeCreator {
    type Item: NodeCreator;

    fn len(&self) -> usize;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn elements(&self) -> &BTreeSet<Self::Item>;
    // fn elements(&self) -> impl Iterator<Item = &Self::Item>;
    fn first(&self) -> Option<Self::Item> {
        self.elements().iter().next().cloned()
    }
    fn is_subset(&self, other: &Self) -> bool;
}
impl NodeCreatorCollection for Clause {
    type Item = Key;
    fn len(&self) -> usize {
        self.len()
    }
    fn elements(&self) -> &BTreeSet<Self::Item> {
        self.elements()
    }
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}
impl NodeCreatorCollection for Formula {
    type Item = Clause;
    fn len(&self) -> usize {
        self.len()
    }
    fn elements(&self) -> &BTreeSet<Self::Item> {
        self.elements()
    }
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

// #[derive(Clone, PartialEq, Eq)]
// struct Rank<E: NodeCreator> {
//     weight: usize,
//     elem: Rc<E>,
// }
// impl<E: NodeCreatorCollection> Rank<E> {
//     fn new(elem: Rc<E>) -> Self {
//         Self {
//             weight: elem.len(),
//             elem,
//         }
//     }
// }
// impl<E: NodeCreator> PartialOrd for Rank<E> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         Some(self.cmp(other))
//     }
// }
// impl<E: NodeCreator> Ord for Rank<E> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         self.weight
//             .cmp(&other.weight)
//             .then_with(|| self.elem.cmp(&other.elem))
//     }
// }

#[derive(Default, Debug)]
struct Stats {
    tally_max: usize,
    tally_total: usize,
}

#[derive(Debug, Default)]
struct LiteralMatcher {
    wildcard: Option<Node>,
    positive_values: IndexMap<String, Vec<Node>>,
    negative_values: Option<()>, // TODO: support this
}
impl LiteralMatcher {
    fn add_values(&mut self, values: Vec<String>, node: Node) {
        // because we find the set of unique literals prior to creating these matchers, we
        // don't currently need to worry about the added node representing being redundant.
        // each node will definitely represent a unique set of values for this name. in the
        // event that the node doesn't end up with any local property settings, building a
        // separate node for every combination is overkill. it might be nice to detect this
        // case and elide the subset node, replacing it with individual nodes for each member.
        // on the other hand, whether this is an improvement depends on whether or not those
        // individual nodes will actually end up existing either way, or alternatively on the
        // number of different sets those values appear in. this isn't a tradeoff with an
        // easy obvious answer.
        if values.len() == 0 {
            if self.wildcard.is_some() {
                assert!(self.wildcard.is_none());
                self.wildcard = Some(node.clone());
            }

            for value in values {
                self.positive_values
                    .entry(value)
                    .or_default()
                    .push(node.clone());
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Node(usize);

impl Node {
    fn and(dag: &mut Dag, specificity: Specificity) -> Self {
        dag.new_node(NodeData::and(specificity))
    }

    fn or(dag: &mut Dag) -> Self {
        dag.new_node(NodeData::or())
    }
}

#[derive(Debug, Clone)]
enum NodeType {
    Or,
    And(Specificity),
}
impl From<&NodeType> for Op {
    fn from(value: &NodeType) -> Self {
        match value {
            NodeType::Or => Op::Or,
            NodeType::And(..) => Op::And,
        }
    }
}

#[derive(Debug, Clone)]
struct NodeData {
    children: Vec<Node>,
    props: Vec<PropDef>,
    constraints: Vec<Constraint>,
    /// Used for poisoning in case of OrNode
    tally_count: usize,
    op: NodeType,
}
impl NodeData {
    fn and(specificity: Specificity) -> Self {
        Self::with_op(NodeType::And(specificity))
    }

    fn or() -> Self {
        Self::with_op(NodeType::Or)
    }

    fn with_op(op: NodeType) -> Self {
        Self {
            children: Default::default(),
            props: Default::default(),
            constraints: Default::default(),
            tally_count: 0,
            op,
        }
    }

    fn add_link(&mut self) {
        self.add_links(1)
    }

    fn add_links(&mut self, num: usize) {
        self.tally_count += num
    }

    fn accumulate_subclass_stats(&self, stats: &mut Stats) {
        if matches!(self.op, NodeType::And(..)) {
            stats.tally_max = stats.tally_max.max(self.tally_count);
            stats.tally_total += self.tally_count;
        }
    }

    fn accumulate_stats(&self, stats: &mut Stats, visited: &mut IndexSet<Node>) {
        todo!()
    }
}
