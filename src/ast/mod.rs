use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    io::Read,
    ops::{Add, Range},
    path::{Path, PathBuf},
    rc::Rc,
};

use indexmap::IndexMap;

use crate::ast::rule_tree::RuleTreeNode;

mod dnf;
mod formula;
mod parser;
mod property;
mod rule_tree;

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

type Env = HashMap<String, String>;

/// The original source location from which a rule/property was parsed
#[derive(Debug, Clone)]
pub struct Origin {
    filename: PathBuf,
    line_number: u32,
    char_slice: Range<u32>,
}
impl Display for Origin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}-{}",
            self.filename.to_str().unwrap(),
            self.line_number,
            self.char_slice.start,
            self.char_slice.end
        )
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    And,
    Or,
}

/// AST nodes representing selector expressions
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Selector {
    /// A conjunction or disjunction selector expression
    Expr(Expr),
    /// A single-step primitive selector expression
    Step(Key),
}
// impl Display for Selector {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         todo!()
//     }
// }

/// Provides a binding to paths which are used for resolving `@import` expressions
pub trait ImportResolver {
    fn resolve(&self, location: &PathBuf) -> String;
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
        in_progress: &mut HashSet<PathBuf>,
    ) -> bool {
        use AstNode::*;
        match self {
            Import(import) => todo!(),
            Nested(nested) => {
                for rule in nested.rules.iter_mut() {
                    if !rule.resolve_imports(resolver.clone(), in_progress) {
                        return false;
                    }
                }
                true
            }
            PropDef(..) | Constraint(..) => true,
        }
    }
}

#[derive(Debug)]
pub struct Import {
    location: PathBuf,
    env: Env,
    ast: Option<Box<AstNode>>, // TODO: Rc?
}
impl Import {
    pub fn new(location: impl AsRef<Path>, env: Env) -> Self {
        Self {
            location: location.as_ref().to_path_buf(),
            env,
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

#[derive(Debug)]
pub struct Nested {
    selector: Option<Selector>,
    rules: Vec<AstNode>,
}
impl Nested {
    pub fn set_selector(&mut self, selector: Selector) {
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
        Selector::Step(..) => {
            eprintln!("Step: {expr:?}");
            expr
        }
        Selector::Expr(expr) => {
            let mut lit_children = IndexMap::<Selector, HashSet<String>>::default();
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
                        eprintln!("Add {key:?} to lit_children");
                        lit_children
                            .entry(Selector::Step(key.clone()))
                            .or_default()
                            .extend(key.values.iter().cloned());
                    }
                    (e, _) => {
                        new_children.push(e);
                    }
                }
            };

            for e in expr.children.into_iter().map(flatten) {
                println!("Checking child {e:?}");
                match e {
                    Selector::Expr(e) => {
                        if e.op == expr.op {
                            for c in e.children {
                                add_child(c)
                            }
                        }
                    }
                    Selector::Step(..) => add_child(e),
                }
            }

            for (child, values) in lit_children {
                eprintln!("ADDING: {child:?}");
                match child {
                    Selector::Step(key) => new_children.push(Selector::Step(Key::new(key.name, values))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    macro_rules! selector {
        ($item:literal) => {
            Selector::Step(Key::new($item, []))
        };
        ($item:expr) => {
            $item
        };
    }

    macro_rules! expr {
        ($operator:ident, $op1:expr $(, $ops:expr)*) => {
            Selector::Expr(Expr::new(Op::$operator, [selector!($op1) $(, selector!($ops))*]))
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

    #[test]
    fn flatten_already_flattened() {
        let selector = AND!("a", "b", "c", "d");

        assert_eq!(flatten(selector.clone()), selector);
    }

    #[test]
    fn flatten_and() {
        let selector = AND!(AND!("a", "b"), AND!("c", "d"));
        let expected = AND!("a", "b", "c", "d");

        assert_eq!(flatten(selector), expected);
    }

    #[test]
    fn flatten_or() {
        let selector = OR!(OR!("a", "b"), OR!("c", "d"));
        let expected = OR!("a", "b", "c", "d");

        assert_eq!(flatten(selector), expected);
    }

    #[test]
    fn flatten_mixed() {
        let selector = AND!(OR!("a", "b", "c"), AND!("c", "d"), OR!("d", OR!("e", AND!("f", "g"))));
        let expected = AND!(OR!("a", "b", "c"), "c", "d", OR!(AND!("f", "g"), "d", "e"));

        assert_eq!(flatten(selector), expected);
    }
}
