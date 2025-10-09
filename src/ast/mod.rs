use std::{
    collections::HashMap,
    fmt::Display,
    hash::Hash,
    ops::Add,
    path::{Path, PathBuf},
    rc::Rc,
};

use crate::ast::rule_tree::RuleTreeNode;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

mod dnf;
mod formula;
mod parser;
mod property;
mod rule_tree;

#[derive(thiserror::Error, Debug)]
pub enum CcsError {
    #[error(transparent)]
    ParseError(#[from] parser::ParseError),
    #[error("Circular import detected from file {0}")]
    CircularImport(PathBuf),
    #[error("Failed to resolve import {0}")]
    ImportFailed(PathBuf),
}
pub type CcsResult<T> = Result<T, CcsError>;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Specificity {
    should_override: u32,
    positive: u32,
    negative: u32,
    wildcard: u32,
}
impl Specificity {
    pub const fn zero() -> Self {
        Self::new(0, 0, 0, 0)
    }

    pub const fn positive_lit() -> Self {
        Self::new(0, 1, 0, 0)
    }

    pub const fn wildcard() -> Self {
        Self::new(0, 0, 0, 1)
    }

    pub const fn new(should_override: u32, positive: u32, negative: u32, wildcard: u32) -> Self {
        Self {
            should_override,
            positive,
            negative,
            wildcard,
        }
    }
}
impl Add for Specificity {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            should_override: self.should_override + rhs.should_override,
            positive: self.positive + rhs.positive,
            negative: self.negative + rhs.negative,
            wildcard: self.wildcard + rhs.wildcard,
        }
    }
}

#[derive(Debug, Clone, Hash, Eq)]
pub struct Key {
    name: String,
    values: Vec<String>,
    specificity: Specificity,
}
impl Key {
    pub fn new(name: impl ToString, values: impl IntoIterator<Item = String>) -> Self {
        let mut values: Vec<_> = values.into_iter().collect();
        values.sort_unstable(); // Important: values are always sorted!
        Self {
            name: name.to_string(),
            specificity: if !values.is_empty() {
                Specificity::positive_lit()
            } else {
                Specificity::wildcard()
            },
            values,
        }
    }
    /// Key-value parsing shouldn't be done here, really. It's done by the actual parser
    /// implementation. However, this is handy for expressivity in tests, so we'll just allow it for
    /// that.
    #[cfg(test)]
    pub fn parse(input: impl ToString) -> Self {
        let input = input.to_string();
        let inputs: Vec<&str> = input.split(".").collect();
        assert!(!inputs.is_empty());
        let (key, values) = &inputs.split_at(1);
        let values: Vec<_> = values.iter().map(ToString::to_string).collect();
        Self::new(key[0], values)
    }
}
impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.values == other.values
    }
}
impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Key {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        debug_assert!(self.values.is_sorted());
        debug_assert!(other.values.is_sorted());

        self.name
            .cmp(&other.name)
            .then_with(|| self.values.cmp(&other.values))
    }
}
impl Display for Key {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // # TODO java code notices if key/val are actually not idents and quotes them
        if self.values.len() > 1 {
            let vals_str = self
                .values
                .iter()
                .map(|val| format!("{}.{val}", self.name))
                .joined_by(", ");
            write!(f, "({})", vals_str)
        } else if let Some(first) = self.values.first()
            && first != ""
        {
            write!(f, "{}.{first}", self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

type Env = HashMap<String, String>;

/// The original source location from which a rule/property was parsed
#[derive(Debug, Clone)]
pub struct Origin {
    pub filename: PathBuf,
    pub line_number: u32,
}
impl Display for Origin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}",
            self.filename.to_str().unwrap(),
            self.line_number,
        )
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    And,
    Or,
}
impl Display for Op {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::And => write!(f, "AND"),
            Op::Or => write!(f, "OR"),
        }
    }
}

/// AST nodes representing selector expressions
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Selector {
    /// A conjunction or disjunction selector expression
    Expr(Expr),
    /// A single-step primitive selector expression
    Step(Key),
}
impl Display for Selector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Selector::Expr(expr) => write!(f, "{expr}"),
            Selector::Step(key) => write!(f, "{key}"),
        }
    }
}

/// Provides a binding to paths which are used for resolving `@import` expressions
pub trait ImportResolver {
    fn resolve(&self, location: &PathBuf) -> CcsResult<String>;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Expr {
    pub op: Op,
    pub children: Vec<Selector>,
}
impl Expr {
    pub fn new(op: Op, children: impl IntoIterator<Item = Selector>) -> Self {
        Self {
            op,
            children: children.into_iter().collect(),
        }
    }
}
impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let children_str = self.children.iter().joined_by(" ");
        write!(f, "({} {children_str})", self.op)
    }
}

pub fn conj(terms: Vec<Selector>) -> Expr {
    Expr {
        op: Op::And,
        children: terms,
    }
}
pub fn disj(terms: Vec<Selector>) -> Expr {
    Expr {
        op: Op::Or,
        children: terms,
    }
}

#[derive(Debug)]
pub struct Step {
    pub key: Key,
}

/// AST nodes representing rules
#[derive(Debug)]
pub enum AstNode {
    /// AST node for @import
    Import(Import),
    /// AST node for a property setting
    PropDef(PropDef),
    /// AST node for @constrain
    Constraint(Key),
    /// AST node for a nested ruleset (single or multiple rules)
    Nested(Nested),
}
impl AstNode {
    pub fn add_to(&mut self, build_context: &mut RuleTreeNode) {
        use AstNode::*;
        match self {
            Import(import) => {
                if let Some(ast) = import.ast.as_mut() {
                    ast.add_to(build_context)
                } else {
                    panic!("Attempted to add Import node without a resolved AST context");
                }
            }
            PropDef(prop_def) => build_context.add_property(
                &prop_def.name,
                &prop_def.value,
                prop_def.origin.clone(),
                prop_def.should_override,
            ),
            Constraint(key) => {
                build_context.add_constraint(key.clone());
            }
            Nested(nested) => {
                if let Some(selector) = nested.selector.as_ref() {
                    *build_context = build_context.traverse(selector.clone()).clone();
                } else {
                    for rule in nested.rules.iter_mut() {
                        rule.add_to(build_context);
                    }
                }
            }
        }
    }

    pub fn resolve_imports(
        &mut self,
        resolver: Rc<dyn ImportResolver>,
        in_progress: &mut Vec<PathBuf>,
    ) -> CcsResult<()> {
        use AstNode::*;
        match self {
            Import(import) => {
                if in_progress.contains(&import.location) {
                    Err(CcsError::CircularImport(import.location.clone()))
                } else {
                    in_progress.push(import.location.clone());
                    let nested = parser::parse(resolver.resolve(&import.location)?)?;
                    import.ast = Some(Box::new(AstNode::Nested(nested)));
                    Ok(())
                }
            }
            Nested(nested) => {
                for rule in nested.rules.iter_mut() {
                    if let Err(err) = rule.resolve_imports(resolver.clone(), in_progress) {
                        return Err(err);
                    }
                }
                Ok(())
            }
            PropDef(..) | Constraint(..) => Ok(()),
        }
    }
}

#[derive(Debug)]
pub struct Import {
    location: PathBuf,
    ast: Option<Box<AstNode>>,
}
impl Import {
    pub fn new(location: impl AsRef<Path>) -> Self {
        Self {
            location: location.as_ref().to_path_buf(),
            ast: None,
        }
    }
}

#[derive(Debug)]
pub struct PropDef {
    pub name: String,
    pub value: String,
    pub origin: Origin,
    pub should_override: bool,
}

#[derive(Debug)]
pub struct Constraint {
    pub key: Key,
}

#[derive(Default, Debug)]
pub struct Nested {
    selector: Option<Selector>,
    rules: Vec<AstNode>,
}
impl Nested {
    pub fn set_selector(&mut self, selector: Selector) {
        assert!(self.selector.is_none());
        self.selector = Some(selector)
    }

    pub fn append(&mut self, rule: AstNode) {
        self.rules.push(rule)
    }
}

/// Flatten a selector expression.
///
/// A selector is flattened when we've inlined trivially nested expressions. In other
/// words, a flat selector consists of strictly alternating levels of AND and OR.
pub fn flatten(expr: Selector) -> Selector {
    match expr {
        Selector::Step(k) => Selector::Step(k),
        Selector::Expr(expr) => {
            let mut lit_children = IndexMap::<Selector, IndexSet<String>>::default();
            let mut new_children = Vec::<Selector>::default();

            let mut add_child = |e: Selector| {
                match (e, expr.op) {
                    (Selector::Step(key), Op::Or) => {
                        // in this case, we can group matching literals by key to avoid unnecessary dnf expansion.
                        // it's not totally clear whether it's better to do this here or in to_dnf() (or possibly even in
                        // normalize()??, so this is a bit of an arbitrary choice...
                        // TODO negative matches will need to be handled here, probably adding as separate clusters,
                        // depending on specificity rules?
                        // TODO wildcard matches also need to be handled specially here, either as a flag on the key or
                        // a special entry in values...
                        // TODO if this is done prior to normalize(), that function needs to be changed to understand
                        // set-valued pos/neg literals... and might need to be changed for negative literals either way?
                        let key_without_values = Key::new(key.name, []);
                        lit_children
                            .entry(Selector::Step(key_without_values))
                            .or_default()
                            .extend(key.values.iter().cloned());
                    }
                    (e, _) => {
                        new_children.push(e);
                    }
                }
            };

            for e in expr.children.into_iter().map(flatten) {
                match e {
                    Selector::Expr(e) => {
                        if e.op == expr.op {
                            for c in e.children {
                                add_child(c)
                            }
                        } else {
                            add_child(Selector::Expr(e))
                        }
                    }
                    Selector::Step(..) => add_child(e),
                }
            }

            for (child, values) in lit_children {
                match child {
                    Selector::Step(key) => {
                        new_children.push(Selector::Step(Key::new(key.name, values)))
                    }
                    Selector::Expr(..) => panic!("Attempted to add literal expr!"),
                }
            }
            if new_children.len() == 1 {
                new_children.into_iter().next().unwrap()
            } else {
                Selector::Expr(Expr::new(expr.op, new_children))
            }
        }
    }
}

pub trait JoinedBy {
    fn joined_by(self, joiner: impl AsRef<str>) -> String;
}
impl<S: ToString, T: Iterator<Item = S>> JoinedBy for T {
    fn joined_by(self, joiner: impl AsRef<str>) -> String {
        Itertools::intersperse(self.map(|s| s.to_string()), joiner.as_ref().to_string()).collect()
    }
}

pub mod macros {
    #![allow(unused)] // Mostly just used by tests, but kind handy for expressivity

    macro_rules! selector {
        ($item:literal) => {
            crate::ast::Selector::Step(crate::ast::Key::parse($item))
        };
        ($item:expr) => {
            $item
        };
    }

    macro_rules! key {
        ($item:literal $(: ($($val:literal)+))?) => {
            crate::ast::Key::new($item, [$($($val.to_string(),)+)?])
        };
    }

    macro_rules! kv_selector {
        ($item:literal $(: ($($val:literal)+))?) => {
            crate::ast::Selector::Step(crate::ast::Key::new($item, [$($($val.to_string(),)+)?]))
        };
    }

    macro_rules! expr {
        ($operator:ident, $op1:expr $(, $ops:expr)*) => {
            crate::ast::Selector::Expr(
                crate::ast::Expr::new(
                    crate::ast::Op::$operator, [selector!($op1) $(, selector!($ops))*]
                )
            )
        }
    }

    macro_rules! AND {
        ($op1:expr $(, $ops:expr)*) => {
            expr!(And, $op1 $(, $ops)*)
        }
    }

    macro_rules! OR {
        ($op1:expr $(, $ops:expr)*) => {
            expr!(Or, $op1 $(, $ops)*)
        }
    }

    pub(crate) use AND;
    pub(crate) use OR;
    pub(crate) use expr;
    pub(crate) use key;
    pub(crate) use kv_selector;
    pub(crate) use selector;
}

#[cfg(test)]
mod tests {
    use super::{macros::*, *};
    use pretty_assertions::assert_eq;

    #[test]
    fn flatten_already_flattened() {
        let selector = AND!("a", "b", "c", "d");

        assert_eq!(flatten(selector.clone()), selector);
    }

    #[test]
    fn flatten_and() {
        let selector = AND!(AND!("a", "b"), AND!("c", "d"));
        let expected = AND!("a", "b", "c", "d");

        let flattened = flatten(selector);
        assert_eq!(flattened, expected);
        assert_eq!(flattened.to_string(), "(AND a b c d)");
    }

    #[test]
    fn flatten_or() {
        let selector = OR!(OR!("a", "b"), OR!("c", "d"));
        let expected = OR!("a", "b", "c", "d");

        let flattened = flatten(selector);
        assert_eq!(flattened, expected);
        assert_eq!(flattened.to_string(), "(OR a b c d)");
    }

    #[test]
    fn flatten_mixed() {
        #[rustfmt::skip]
        let selector = AND!(OR!("a", "b", "c"), AND!("c", "d"), OR!("d", OR!("e", AND!("f", "g"))));
        let expected = AND!(OR!("a", "b", "c"), "c", "d", OR!(AND!("f", "g"), "d", "e"));

        let flattened = flatten(selector);
        assert_eq!(flattened, expected);
        assert_eq!(
            flattened.to_string(),
            "(AND (OR a b c) c d (OR (AND f g) d e))"
        );
    }

    #[test]
    fn flatten_single_key_leaf_disjunctions() {
        let selector = AND!(OR!("a.x", "a.y", "a.z"), "b");
        let expected = AND!(kv_selector!("a": ("x" "y" "z")), "b");

        let flattened = flatten(selector);
        assert_eq!(flattened, expected);
        assert_eq!(flattened.to_string(), "(AND (a.x, a.y, a.z) b)");
    }
}
