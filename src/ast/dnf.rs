//! DNF-conversion
//!
//! These functions convert from AST selector types, ideally flattened, to DNF formulae.
use std::collections::BTreeSet;

use crate::ast::{
    JoinedBy, Selector,
    formula::{Clause, Formula, IntoUnion},
};

pub fn to_dnf(expr: Selector, limit: usize) -> Formula {
    match expr {
        Selector::Step(key) => Formula::with_clause(Clause::with_literal(key)),
        Selector::Expr(expr) => match expr.op {
            super::Op::Or => merge(expr.children.into_iter().map(|e| to_dnf(e, limit))),
            super::Op::And => expand(expr.children.into_iter().map(|e| to_dnf(e, limit)), limit),
        },
    }
}

/// Merge a sequence of formulae into one, preserving shared subclauses
pub fn merge(forms: impl Iterator<Item = Formula>) -> Formula {
    forms
        .into_iter()
        .reduce(|acc, f| acc.merge(f))
        .unwrap_or(Formula::default())
}

/// Exponentially expand a conjunction of formulae to DNF.
///
/// We also detect and accumulate subclauses which end up shared due to the duplication
/// of clauses during expansion.
pub fn expand(forms: impl Iterator<Item = Formula>, limit: usize) -> Formula {
    let forms: Vec<_> = forms.into_iter().collect();

    // first, build the subclause which is guaranteed to be common
    // to all clauses produced in this expansion. keep count of
    // the non-trivial forms and the size of the result as we go...
    let mut nontrivial = 0u32;
    let mut common = Clause::default();
    let mut result_size = 1;
    for f in forms.iter() {
        result_size *= f.len();
        if f.len() == 1 {
            common = common.union(f.first())
        } else {
            nontrivial += 1;
        }
    }

    if result_size > limit {
        panic!(
            "Expanded form would have {result_size} clauses, which is more than the limit of \
             {limit}. Consider increasing the limit or stratifying this rule."
        );
    }

    // next, perform the expansion...
    fn exprec(forms: &[Formula]) -> Formula {
        if forms.len() == 0 {
            return Formula::default();
        }
        let first = forms.first().unwrap();
        let rest = exprec(&forms[1..]);
        let cs = first
            .elements()
            .iter()
            .map(|c1| rest.elements().iter().map(|c2| c1.union(c2)))
            .flatten()
            .collect();
        Formula::new(cs, first.shared().union(rest.shared()).cloned().collect())
    }

    let res = exprec(&forms);

    // finally, gather shared subclauses and normalize...
    let mut all_shared = BTreeSet::<Clause>::default();
    if nontrivial > 0 && common.len() > 1 {
        all_shared.insert(common);
    }
    if nontrivial > 1 {
        for f in forms {
            if f.len() > 1 {
                all_shared.extend(f.elements().iter().filter(|c| c.len() > 1).cloned())
            }
        }
    }
    let res = Formula::new(
        res.elements().clone(),
        res.shared().union(&all_shared).cloned().collect(),
    )
    .normalize();

    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{flatten, macros::*};

    #[test]
    fn dnf() {
        let selector = OR!(AND!("a", "b"), AND!("c", "d"));
        let expected_str = "a b, c d";

        assert_eq!(to_dnf(flatten(selector), 100).to_string(), expected_str);
    }

    #[test]
    fn cnf() {
        let selector = AND!(OR!("a", "b"), OR!("c", "d"));
        let expected_str = "a c, a d, b c, b d";

        assert_eq!(to_dnf(flatten(selector), 100).to_string(), expected_str);
    }

    #[test]
    fn nested_and() {
        let selector = AND!(AND!("a", "b"), AND!("c", "d"));
        let expected_str = "a b c d";

        assert_eq!(to_dnf(flatten(selector), 100).to_string(), expected_str);
    }

    #[test]
    fn sharing() {
        let selector = AND!(AND!("a", "f", OR!("b", "e")), AND!("c", "d"));
        let expected_str = "a b c d f, a c d e f";

        assert_eq!(to_dnf(flatten(selector), 100).to_string(), expected_str);
    }

    #[test]
    fn flatten_single_key_leaf_disjunctions() {
        let selector = AND!(OR!("a.x", "a.y", "a.z"), "b");
        let expected_str = "(a.x, a.y, a.z) b";

        assert_eq!(to_dnf(flatten(selector), 100).to_string(), expected_str);
    }
}
