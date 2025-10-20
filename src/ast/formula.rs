use crate::ast::{JoinedBy, Key, Specificity};
use std::{collections::BTreeSet, fmt::Display, ops::Add};

// #[derive(Debug, Clone, Hash, PartialEq, Eq)]
// TODO: Name
// pub enum FormulaExpr {
//     Formula(Formula),
//     Clause(Clause),
// }
// impl FormulaExpr {
//     pub fn is_empty(&self) -> bool {
//         match self {
//             FormulaExpr::Formula(formula) => formula.is_empty(),
//             FormulaExpr::Clause(clause) => clause.is_empty(),
//         }
//     }
//
//     pub fn len(&self) -> usize {
//         match self {
//             FormulaExpr::Formula(formula) => formula.len(),
//             FormulaExpr::Clause(clause) => clause.len(),
//         }
//     }
//
//     pub fn first(&self) -> usize {
//         match self {
//             FormulaExpr::Formula(formula) => formula.first(),
//             FormulaExpr::Clause(clause) => clause.first(),
//         }
//     }
// }

pub trait FormulaExpr {
    type Component: Clone + Into<Clause>;
    fn is_empty(&self) -> bool;
    fn len(&self) -> usize;
    fn first(&self) -> Option<Self::Component>;
    fn elements(&self) -> impl Iterator<Item = &Self::Component>;
}

/// A conjunction of literal matchers
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Clause {
    literals: BTreeSet<Key>,
}
impl Clause {
    pub fn with_literal(key: Key) -> Self {
        Self {
            literals: BTreeSet::from([key]),
        }
    }

    pub fn with_literals(keys: impl IntoIterator<Item = Key>) -> Self {
        Self {
            literals: BTreeSet::from_iter(keys),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn first(&self) -> Option<Key> {
        self.literals.iter().next().cloned()
    }

    pub fn is_subset(&self, other: &Clause) -> bool {
        self.literals.is_subset(&other.literals)
    }

    pub fn is_strict_subset(&self, other: &Clause) -> bool {
        self.is_subset(other) && self.literals.len() < other.literals.len()
    }

    pub fn elements(&self) -> &BTreeSet<Key> {
        &self.literals
    }

    pub fn union(&self, other: &Clause) -> Clause {
        Clause {
            literals: self.literals.union(&other.literals).cloned().collect(),
        }
    }

    pub fn specificity(&self) -> Specificity {
        self.literals
            .iter()
            .map(|lit| lit.specificity)
            .reduce(Add::add)
            .unwrap_or(Specificity::zero())
    }

    pub fn len(&self) -> usize {
        self.literals.len()
    }
}
impl PartialOrd for Clause {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
/// note: we rely on this ordering when building the dag
impl Ord for Clause {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.literals
            .len()
            .cmp(&other.literals.len())
            .then_with(|| self.literals.cmp(&other.literals))
    }
}
impl Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let literals: String = self.literals.iter().joined_by(" ");
        write!(f, "{literals}")
    }
}
impl From<Key> for Clause {
    fn from(value: Key) -> Self {
        Self::with_literal(value)
    }
}

#[derive(Clone, Debug, Eq, Hash)]
pub struct Formula {
    clauses: BTreeSet<Clause>,
    shared: BTreeSet<Clause>,
}
impl Default for Formula {
    fn default() -> Self {
        Self::with_clause(Clause::default())
    }
}

impl Formula {
    pub fn new(clauses: BTreeSet<Clause>, shared: BTreeSet<Clause>) -> Self {
        Self { clauses, shared }
    }

    pub fn with_clause(clause: Clause) -> Self {
        Self::new(BTreeSet::from([clause]), Default::default())
    }

    pub fn with_clauses(clauses: impl IntoIterator<Item = Clause>) -> Self {
        Self::new(BTreeSet::from_iter(clauses), Default::default())
    }

    pub fn is_empty(&self) -> bool {
        self.first().is_empty()
    }

    pub fn first(&self) -> &Clause {
        self.clauses
            .first()
            .expect("Empty formula should be impossible!")
    }

    pub fn is_subset(&self, other: &Formula) -> bool {
        self.clauses.is_subset(&other.clauses)
    }

    pub fn into_inner(self) -> (BTreeSet<Clause>, BTreeSet<Clause>) {
        (self.clauses, self.shared)
    }

    pub fn elements(&self) -> &BTreeSet<Clause> {
        &self.clauses
    }

    pub fn shared(&self) -> &BTreeSet<Clause> {
        &self.shared
    }

    pub fn merge(self, other: Formula) -> Self {
        let merged = Self::new(
            self.clauses.into_union(other.clauses),
            self.shared.into_union(other.shared),
        );
        merged.normalize()
    }

    pub fn len(&self) -> usize {
        self.clauses.len()
    }

    ///Normalize a formula.
    ///
    /// For any formula, we define a normal form which exists, is unique, and is equivalent
    /// to the original formula under the usual interpretation of boolean logic.
    ///
    /// Clauses are always normal, since all literals are positive. Formulae are normalized
    /// by removing any clause subsumed by any other. A clause c is subsumed by a clause s
    /// if s <= c. This is the obvious O(mn) algorithm. Our formulae are usually of size 1,
    /// so this is just fine.
    pub fn normalize(self) -> Self {
        let mut minimized = BTreeSet::<Clause>::default();
        for c in self.clauses.into_iter() {
            minimized = minimized.into_iter().filter(|s| !subsumes(&c, s)).collect();
            if !minimized.iter().any(|s| subsumes(s, &c)) {
                minimized.insert(c);
            }
        }
        // note *strict* subset check here...
        let shared: BTreeSet<_> = self
            .shared
            .into_iter()
            .filter(|s| minimized.iter().any(|c| s.is_strict_subset(c)))
            .collect();

        Self {
            clauses: minimized,
            shared,
        }
    }
}
impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        self.clauses == other.clauses
    }
}
impl PartialOrd for Formula {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
/// note: we rely on this ordering when building the dag
impl Ord for Formula {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.clauses
            .len()
            .cmp(&other.clauses.len())
            .then_with(|| self.clauses.cmp(&other.clauses))
    }
}
impl Display for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let clauses: String = self.clauses.iter().joined_by(", ");
        write!(f, "{clauses}")
    }
}

/// A clause c "subsumes" a clause d when d is a subset of c
/// BUG: The comment seems to describe the opposite of the implementation
fn subsumes(c: &Clause, d: &Clause) -> bool {
    c.is_subset(d)
}

pub trait IntoUnion {
    fn into_union(self, other: Self) -> Self;
}
impl IntoUnion for Clause {
    fn into_union(self, other: Self) -> Self {
        Clause {
            literals: self.literals.into_union(other.literals),
        }
    }
}
impl<T: Clone + Ord> IntoUnion for BTreeSet<T> {
    fn into_union(self, other: Self) -> Self {
        self.union(&other).cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::macros::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn normalize() {
        let form = Formula::with_clauses([
            Clause::with_literals([key!("a"), key!("b")]),
            Clause::with_literals([key!("b")]),
            Clause::with_literals([key!("a")]),
            Clause::with_literals([key!("c"), key!("d")]),
            Clause::with_literals([key!("a"), key!("c"), key!("d")]),
            Clause::with_literals([key!("c"), key!("d")]),
        ]);
        assert_eq!(form.to_string(), "a, b, a b, c d, a c d");
        assert_eq!(form.normalize().to_string(), "a, b, c d");
    }
}
