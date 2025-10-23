use std::{collections::BTreeSet, fmt::Display, hash::Hash};

use indexmap::{IndexMap, IndexSet};

use crate::ast::{
    Clause, Constraint, Formula, Key, Op, PersistentStr, Property, RuleTreeNode, Specificity,
};

#[derive(thiserror::Error, Debug)]
pub enum DagError {}

#[derive(Debug)]
pub struct Dag {
    pub children: IndexMap<PersistentStr, LiteralMatcher>,
    pub prop_node: Node,
    pub next_node_id: usize,
    pub node_data: IndexMap<Node, NodeData>,
}
impl Default for Dag {
    fn default() -> Self {
        let mut dag = Self {
            children: IndexMap::default(),
            prop_node: Node(0),
            next_node_id: 0, // Temporary
            node_data: IndexMap::default(),
        };

        dag.prop_node = dag.new_node(NodeData::or());
        dag
    }
}
impl Dag {
    pub fn stats(&self) -> Stats {
        let mut stats = Stats::default();
        let mut visited = Default::default();

        self.prop_node
            .accumulate_stats(self, &mut stats, &mut visited);

        for (_, matcher) in &self.children {
            stats.literals += 1;
            if let Some(wildcard) = matcher.wildcard {
                wildcard.accumulate_stats(self, &mut stats, &mut visited);
            }
            for (_, nodes) in &matcher.positive_values {
                for node in nodes {
                    node.accumulate_stats(self, &mut stats, &mut visited);
                }
            }
            // TODO: handle negatives as well
        }
        stats
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

    pub fn get_data(&self, node: Node) -> &NodeData {
        &self.node_data[&node]
    }

    fn get_data_mut(&mut self, node: Node) -> &mut NodeData {
        &mut self.node_data[&node]
    }

    pub fn build(rule_tree_node: RuleTreeNode) -> Self {
        let mut dag = Self::default();
        let mut lit_nodes = IndexMap::<Key, Node>::default();

        // obviously there are better ways of gathering the unique literals and unique clauses,
        // if performance needs to be improved...
        let mut sorted_formulae: Vec<_> = rule_tree_node.iter().cloned().collect();
        sorted_formulae.sort_by(|lhs, rhs| lhs.formula.cmp(&rhs.formula));

        let mut all_clauses: Vec<_> = sorted_formulae
            .iter()
            .flat_map(|f| f.formula.elements().union(f.formula.shared()))
            .collect();

        all_clauses.sort();

        let all_elements = all_clauses.iter().flat_map(|c| c.elements()).cloned();
        // This dedup is very important
        for lit in IndexSet::<Key>::from_iter(all_elements) {
            lit_nodes.insert(lit.clone(), dag.add_literal(&lit));
        }

        let mut clause_nodes = IndexMap::<Clause, Node>::default();
        for clause in all_clauses.into_iter() {
            if !clause.is_empty() {
                let specificity = clause.specificity();
                let expr = dag.build_expr(
                    clause.clone(),
                    || NodeData::and(specificity),
                    &mut lit_nodes,
                    &mut clause_nodes,
                );
                clause_nodes.insert(clause.clone(), expr);
            }
        }

        let mut form_nodes = IndexMap::<Formula, Node>::default();
        for rule in sorted_formulae {
            let node = if rule.formula.is_empty() {
                dag.prop_node
            } else {
                let node = dag.build_expr(
                    rule.formula.clone(),
                    NodeData::or,
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
            return base_nodes[&expr.first().unwrap()];
        } else if let Some(existing) = these_nodes.get(&expr) {
            return *existing;
        } else if expr.len() == 2 {
            let mut node_data = constructor();
            node_data.add_links(expr.len());
            let node: Node = self.new_node(node_data);

            for el in expr.elements().iter() {
                self.get_data_mut(base_nodes[el]).children.push(node);
            }
            return node;
        }

        let mut item_collection_indices = IndexMap::<E::Item, Vec<usize>>::default();
        for (i, c) in these_nodes.keys().enumerate() {
            if c.is_subset(&expr) {
                assert!(
                    c.len() < expr.len(),
                    "Exact equality should be handled above"
                );
                for el in c.elements() {
                    item_collection_indices
                        .entry(el.clone())
                        .or_default()
                        .push(i);
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
            let collection_rank = |collection: &E| {
                collection
                    .elements()
                    .iter()
                    .filter(|e| !covered_elements.contains(*e))
                    .count()
            };
            collections
                .iter()
                .filter(|collection| collection.is_subset(&expr))
                .map(|collection| (collection_rank(collection), collection))
                .filter(|(rank, _)| *rank != 0)
                .max_by_key(|(rank, _)| *rank) // TODO: Tie?
                .map(|(_, collection)| collection)
        };

        while let Some(best) = biggest_collection(&covered) {
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

trait NodeCreator: Hash + Eq + Ord + Clone + std::fmt::Debug + std::fmt::Display {}
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

macro_rules! write_stat {
    ($f:expr, $self:ident. $stat:ident) => {
        write!($f, "{}: {}", stringify!($stat), $self.$stat)
    };
}

#[derive(Default, Debug)]
pub struct Stats {
    literals: usize,
    nodes: usize,
    props: usize,
    edges: usize,
    tally_max: usize,
    fanout_max: usize,
    tally_total: usize,
    fanout_total: usize,
    nodes_with_fanout: usize,
}
impl Display for Stats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write_stat!(f, self.literals)?;
        write_stat!(f, self.nodes)?;
        write_stat!(f, self.props)?;
        write_stat!(f, self.edges)?;
        write_stat!(f, self.tally_max)?;
        write_stat!(f, self.fanout_max)?;
        write_stat!(f, self.tally_total)?;
        write_stat!(f, self.fanout_total)?;
        write_stat!(f, self.nodes_with_fanout)?;

        let tally_avg = self.tally_total as f64 / self.nodes as f64;
        let fanout_avg = self.fanout_total as f64 / self.nodes as f64;
        write!(f, "tally_avg: {tally_avg:.2}")?;
        write!(f, "fanout_avg: {fanout_avg:.2}")?;

        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct LiteralMatcher {
    pub wildcard: Option<Node>,
    pub positive_values: IndexMap<PersistentStr, Vec<Node>>,
    pub negative_values: Option<()>, // TODO: support this
}
impl LiteralMatcher {
    fn add_values(&mut self, values: Vec<PersistentStr>, node: Node) {
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
        if values.is_empty() {
            assert!(self.wildcard.is_none());
            self.wildcard = Some(node);
        }

        for value in values {
            self.positive_values.entry(value).or_default().push(node);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Node(usize);
impl Node {
    fn accumulate_stats(self, dag: &Dag, stats: &mut Stats, visited: &mut IndexSet<Node>) {
        if !visited.contains(&self) {
            visited.insert(self);
            dag.get_data(self).accumulate_stats(dag, stats, visited);
        }
    }
}

#[derive(Debug, Clone)]
pub enum NodeType {
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
pub struct NodeData {
    pub children: Vec<Node>,
    pub props: Vec<Property>,
    pub constraints: Vec<Constraint>,
    /// Used for poisoning in case of OrNode
    pub tally_count: usize,
    pub op: NodeType,
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

    fn accumulate_stats(&self, dag: &Dag, stats: &mut Stats, visited: &mut IndexSet<Node>) {
        stats.nodes += 1;
        stats.props += self.props.len();
        stats.edges += self.children.len();
        stats.fanout_max = stats.fanout_max.max(self.children.len());
        stats.fanout_total += self.children.len();
        self.accumulate_subclass_stats(stats);
        if !self.children.is_empty() {
            stats.nodes_with_fanout += 1;
        }
        for node in &self.children {
            node.accumulate_stats(dag, stats, visited);
        }
    }
}

#[cfg(feature = "dot")]
pub mod dot {
    use std::{fmt::Display, ops::AddAssign};

    use crate::{ast::JoinedBy, search};

    use super::*;
    use petgraph::{
        dot::{Config, Dot},
        graph::NodeIndex,
    };

    pub type DiGraph = petgraph::graph::DiGraph<StyledNode, ()>;

    #[allow(dead_code)]
    pub struct StyledNode {
        id: Node, // Unique identity in the dag
        label: String,
        fillcolor: String,
        style: String,
        shape: String,
    }
    impl StyledNode {
        pub fn new(id: Node, name: impl ToString) -> Self {
            Self::styled(id, name, "", "", "")
        }

        pub fn styled(
            id: Node,
            name: impl ToString,
            fillcolor: impl ToString,
            style: impl ToString,
            shape: impl ToString,
        ) -> Self {
            Self {
                id,
                label: name.to_string(),
                fillcolor: fillcolor.to_string(),
                style: style.to_string(),
                shape: shape.to_string(),
            }
        }

        pub fn to_dot(&self) -> String {
            [
                Self::attribute("label", &self.label),
                Self::attribute("fillcolor", &self.fillcolor),
                Self::attribute("style", &self.style),
                Self::attribute("shape", &self.shape),
            ]
            .into_iter()
            .joined_by(" ")
        }

        fn attribute(name: &str, value: &str) -> String {
            if !value.is_empty() {
                format!("{name}=\"{value}\"")
            } else {
                "".to_string()
            }
        }
    }
    impl Display for StyledNode {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.label)
        }
    }
    impl std::fmt::Debug for StyledNode {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            Display::fmt(self, f)
        }
    }

    impl From<&RuleTreeNode> for DiGraph {
        fn from(value: &RuleTreeNode) -> Self {
            let mut g = Self::new();

            let mut uid = 0;
            fn add_node(g: &mut DiGraph, n: &RuleTreeNode, uid: &mut usize) -> NodeIndex {
                let nodeid = g.add_node(StyledNode::styled(
                    Node(*uid),
                    n.label(),
                    n.color(),
                    "filled",
                    "box",
                ));
                uid.add_assign(1);
                for c in &n.children {
                    let child = add_node(g, c, uid);
                    g.add_edge(nodeid, child, ());
                }

                nodeid
            }
            add_node(&mut g, value, &mut uid);

            g
        }
    }

    pub fn dag_to_digraph(dag: &Dag, tallies: &search::Tallies) -> DiGraph {
        let mut g = DiGraph::new();

        let mut node_mapping = IndexMap::default();
        fn add_nodes(
            dag: &Dag,
            g: &mut DiGraph,
            node_mapping: &mut IndexMap<Node, NodeIndex>,
            t: &search::Tallies,
            p: NodeIndex,
            nodes: &[Node],
        ) {
            // TODO: active_only?
            for n in nodes {
                let n_data = dag.get_data(*n);
                let (mut label, color) = if matches!(n_data.op, NodeType::Or) {
                    let label = "V".to_string();
                    if t.contains_key(n) {
                        (label, "palegreen")
                    } else {
                        (label, "lightblue")
                    }
                } else {
                    let count = *t.get(n).unwrap_or(&n_data.tally_count);
                    let mut label = format!("{}", n_data.tally_count);
                    let color = if count == 0 {
                        "palegreen"
                    } else if count != n_data.tally_count {
                        label = format!("{} / {}", n_data.tally_count - count, label);
                        "mistyrose"
                    } else {
                        "pink2"
                    };
                    (label, color)
                };
                let mut style = "filled".to_string();
                if !n_data.props.is_empty() {
                    label += &format!(" [{}]", n_data.props.iter().joined_by(","));
                    style += ", bold";
                }
                let node_id = if let Some(existing) = node_mapping.get(n) {
                    *existing
                } else {
                    let node_id = g.add_node(StyledNode::styled(*n, label, color, style, ""));
                    node_mapping.insert(*n, node_id);
                    node_id
                };

                if !g.contains_edge(p, node_id) {
                    g.add_edge(p, node_id, ());
                }
                add_nodes(dag, g, node_mapping, t, node_id, &n_data.children);
            }
        }

        // These aren't real nodes in the Dag, but we want to draw them anyway
        let mut lit_id = 1000000;

        for (l, matcher) in &dag.children {
            let lit_node = Node(lit_id);
            lit_id += 1;
            let node_id = g.add_node(StyledNode::new(lit_node, l));
            node_mapping.insert(lit_node, node_id);
            if let Some(wildcard) = matcher.wildcard {
                add_nodes(
                    dag,
                    &mut g,
                    &mut node_mapping,
                    tallies,
                    node_id,
                    &[wildcard],
                );
            }
            for (v, nodes) in &matcher.positive_values {
                let lit_node = Node(lit_id);
                lit_id += 1;
                let node_id_2 = g.add_node(StyledNode::styled(
                    lit_node,
                    v,
                    "lightyellow",
                    "filled",
                    "box",
                ));
                node_mapping.insert(lit_node, node_id_2);

                if !g.contains_edge(node_id, node_id_2) {
                    g.add_edge(node_id, node_id_2, ());
                }
                add_nodes(dag, &mut g, &mut node_mapping, tallies, node_id_2, nodes);
            }
        }

        g
    }

    impl From<&Dag> for DiGraph {
        fn from(value: &Dag) -> Self {
            dag_to_digraph(value, &Default::default())
        }
    }

    pub fn to_dot<'a>(graph: &'a DiGraph) -> Dot<'a, &'a DiGraph> {
        Dot::with_attr_getters(
            graph,
            &[Config::EdgeNoLabel, Config::NodeNoLabel],
            &|_, _| "".to_string(),
            &|_, (_, style)| style.to_dot(),
        )
    }

    pub fn to_dot_str<G: Into<DiGraph>>(graph: G) -> String {
        format!("{:?}", to_dot(&graph.into()))
    }
}

#[cfg(test)]
#[cfg(feature = "dot")]
mod dot_tests {
    use crate::{
        ast::RuleTreeNode,
        dag::{Dag, dot::to_dot_str},
    };

    const MULTILEVEL_EXAMPLE: &str = r#"
        a, f b e, c {
            c d {
                x = y
            }
            e f {
                foobar = abc
            }
        }
        a, c, b e f : baz = quux
    "#;

    #[test]
    fn tree_to_dot_1() {
        let n = crate::ast::parse(MULTILEVEL_EXAMPLE).unwrap();

        let mut tree = RuleTreeNode::default();
        n.add_to(&mut tree);
        println!("{}", to_dot_str(&tree));

        let dag = Dag::build(tree);
        println!("{}", to_dot_str(&dag));
    }

    #[test]
    fn tree_to_dot_2() {
        let n = crate::ast::parse(
            r#"
                a b c d e (f, g, h, i, j) {
                    x = y
                }
            "#,
        )
        .unwrap();

        let mut tree = RuleTreeNode::default();
        n.add_to(&mut tree);
        println!("{}", to_dot_str(&tree));

        let dag = Dag::build(tree);
        println!("{}", to_dot_str(&dag));
    }
}
