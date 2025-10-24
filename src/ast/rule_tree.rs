use std::fmt::Display;

use crate::ast::{
    JoinedBy, Key, Origin, PropDef, Property, Selector,
    dnf::{expand, to_dnf},
    flatten,
    formula::Formula,
};

#[derive(Clone, Debug, PartialEq)]
pub struct RuleTreeNode {
    expand_limit: u32,
    pub formula: Formula,
    pub children: Vec<RuleTreeNode>,
    pub props: Vec<Property>,
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
        Box::new(std::iter::once(self).chain(self.children.iter().flat_map(|c| c.iter())))
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
        self.props.push(
            PropDef {
                name: name.to_string(),
                value: value.to_string(),
                origin,
                should_override,
            }
            .into(),
        )
    }

    pub fn add_constraint(&mut self, key: Key) {
        self.constraints.push(key);
    }

    pub fn stats(&self) -> Stats {
        let mut stats = Stats::default();
        self.accumulate_stats(&mut stats);
        stats
    }

    fn accumulate_stats(&self, stats: &mut Stats) {
        stats.nodes += 1;
        stats.props += self.props.len();
        stats.constraints += self.constraints.len();
        stats.edges += self.children.len();
        for node in &self.children {
            node.accumulate_stats(stats);
        }
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

#[derive(Default, Debug)]
pub struct Stats {
    nodes: usize,
    props: usize,
    constraints: usize,
    edges: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{NullResolver, macros::*, parse};
    use pretty_assertions::assert_eq;

    fn formula(selector: Selector) -> Formula {
        to_dnf(selector, 100)
    }

    macro_rules! prop {
        ($name:literal, $value:literal, $line:literal) => {
            Property::new(
                $name,
                $value,
                Origin {
                    filename: "".into(),
                    line_number: $line as u32,
                },
                false,
            )
        };
    }

    #[test]
    fn multilevel_tree() {
        let ccs = r#"
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
        let n = parse(ccs, NullResolver()).unwrap();
        let mut tree = RuleTreeNode::default();
        n.add_to(&mut tree);

        let expected = RuleTreeNode {
            children: vec![
                RuleTreeNode {
                    formula: formula(OR!("a", "c", AND!("b", "e", "f"))),
                    children: vec![
                        RuleTreeNode {
                            formula: formula(AND!("c", "d")),
                            props: vec![prop!("x", "y", 4)],
                            ..Default::default()
                        },
                        RuleTreeNode {
                            formula: formula(OR!(
                                AND!("a", "e", "f"),
                                AND!("b", "e", "f"),
                                AND!("c", "e", "f")
                            )),
                            props: vec![prop!("foobar", "abc", 7)],
                            ..Default::default()
                        },
                    ],
                    ..Default::default()
                },
                RuleTreeNode {
                    formula: formula(OR!("a", "c", AND!("b", "e", "f"))),
                    props: vec![prop!("baz", "quux", 10)],
                    ..Default::default()
                },
            ],
            ..Default::default()
        };

        assert_eq!(tree, expected);
    }
}
