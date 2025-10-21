use std::fmt::Display;

use crate::ast::{
    JoinedBy, Key, Origin, PropDef, Selector,
    dnf::{expand, to_dnf},
    flatten,
    formula::Formula,
};

#[derive(Clone, Debug)]
pub struct RuleTreeNode {
    expand_limit: u32,
    pub formula: Formula,
    pub children: Vec<RuleTreeNode>,
    pub props: Vec<PropDef>,
    pub constraints: Vec<Key>,
}
impl Default for RuleTreeNode {
    fn default() -> Self {
        Self::new(Formula::default())
    }
}
impl RuleTreeNode {
    pub fn new(formula: Formula) -> Self {
        Self::with_expand_limit(formula, 100)
    }

    pub fn with_expand_limit(formula: Formula, expand_limit: u32) -> Self {
        Self {
            expand_limit,
            formula,
            children: Default::default(),
            props: Default::default(),
            constraints: Default::default(),
        }
    }

    pub fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a RuleTreeNode> + 'a> {
        Box::new(std::iter::once(self).chain(self.children.iter().map(|c| c.iter()).flatten()))
    }

    pub fn traverse(&mut self, selector: Selector) -> &mut RuleTreeNode {
        let dnf = to_dnf(flatten(selector), self.expand_limit as usize);
        let formula = expand(
            [self.formula.clone(), dnf].into_iter(),
            self.expand_limit as usize,
        );
        self.children
            .push(RuleTreeNode::with_expand_limit(formula, self.expand_limit));

        self.children.iter_mut().last().unwrap()
    }

    pub fn add_property(
        &mut self,
        name: impl ToString,
        value: impl ToString,
        origin: Origin,
        should_override: bool,
    ) {
        self.props.push(PropDef {
            name: name.to_string(),
            value: value.to_string(),
            origin,
            should_override,
        })
    }

    pub fn add_constraint(&mut self, key: Key) {
        self.constraints.push(key);
    }

    fn accumulate_stats(self, mut stats: Stats) -> Stats {
        stats.nodes += 1;
        stats.props += self.props.len();
        stats.constraints += self.constraints.len();
        stats.edges += self.children.len();
        for node in self.children {
            stats = node.accumulate_stats(stats);
        }
        stats
    }

    pub fn label(&self) -> String {
        self.formula.to_string()
    }

    pub fn color(&self) -> String {
        if !self.props.is_empty() || !self.constraints.is_empty() {
            "lightblue"
        } else {
            "transparent"
        }
        .to_string()
    }
}
impl Display for RuleTreeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "RuleTreeNode{{formula='{}', constraints=[{}], children=[{}]}}",
            self.formula,
            self.constraints.iter().joined_by(", "),
            self.children.iter().joined_by(", "),
        )
    }
}

pub struct Stats {
    nodes: usize,
    props: usize,
    constraints: usize,
    edges: usize,
}
