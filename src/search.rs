use std::{collections::VecDeque, fmt::Display, path::Path};

use crate::{
    ast::{
        self, Constraint, ImportResolver, JoinedBy, Key, PersistentStr, Property, PropertyValue,
        Specificity,
    },
    dag::{self, Node, NodeType},
    load_helper,
    tracer::PropertyTracer,
};

// TODO: Make thread-safety opt-in? These should be the only changes...
// rpds docs say Rc -> Arc doubles runtime of some operations.
type PersistentQueue<T> = rpds::QueueSync<T>;
type PersistentSet<T> = rpds::HashTrieSetSync<T>;
type PersistentMap<K, V> = rpds::HashTrieMapSync<K, V>;
type Dag = std::sync::Arc<crate::dag::Dag>;

/// Represents a problem finding a property in the current context
///
/// See [`SearchResult`]
#[derive(thiserror::Error, Debug)]
pub enum SearchError {
    #[error("Failed to find property '{0}' {1}")]
    MissingPropertyError(String, DisplayContext),
    #[error("Property '{0}' has no values {1}")]
    EmptyPropertyError(String, DisplayContext),
    #[error("Found {0} properties matching '{1}' {2}")]
    AmbiguousPropertyError(usize, String, DisplayContext),
}

pub type SearchResult<T> = std::result::Result<T, SearchError>;

/// A public-facing [`Key`] converter, which allows creating a valid `Key` for constraints
///
/// Currently we only support standalone `Key`s, or key-value pairs (via 2-tuples).
pub trait AsKey {
    fn as_key(&self) -> Key;
}

impl AsKey for &str {
    fn as_key(&self) -> Key {
        Key::new_lit(self, [])
    }
}

impl<T: AsRef<str>, U: AsRef<str>> AsKey for (T, U) {
    fn as_key(&self) -> Key {
        Key::new_lit(self.0.as_ref(), [self.1.as_ref().into()])
    }
}

#[derive(Clone)]
pub struct Context<Acc: Accumulator, Tracer: PropertyTracer> {
    dag: Dag,
    tracer: Tracer,
    state: ContextState<Acc>,
}
impl<Acc: Accumulator, Tracer: PropertyTracer> Context<Acc, Tracer> {
    pub fn load(
        path: impl AsRef<Path>,
        resolver: impl ImportResolver,
        tracer: Tracer,
    ) -> crate::CcsResult<Self> {
        let content = load_helper::load(path)?;
        Ok(Self::from_ccs_with(&content, resolver, tracer)?)
    }

    pub fn from_ccs_with(
        ccs: impl AsRef<str>,
        resolver: impl ImportResolver,
        tracer: Tracer,
    ) -> crate::AstResult<Self> {
        let rules = ast::parse(ccs, resolver)?;
        let mut tree = ast::RuleTreeNode::default();
        rules.add_to(&mut tree);
        let dag = std::sync::Arc::new(dag::Dag::build(tree));

        Ok(Self {
            dag,
            tracer,
            state: Default::default(),
        }
        .augment_all([], true))
    }

    pub fn augment(&self, key: impl AsKey) -> Self {
        let key = key.as_key();
        self.augment_all([key.clone()], false)
    }

    pub fn get_single_property(&self, prop: impl AsRef<str>) -> SearchResult<PropertyValue> {
        let prop = prop.as_ref().to_string();

        let contenders = self.state.props.get(prop.as_str());
        let mut properties = match contenders {
            Some(contenders) => contenders.values(),
            None => {
                return Err(SearchError::MissingPropertyError(
                    prop,
                    self.state.display_context(),
                ));
            }
        };
        if properties.len() == 0 {
            Err(SearchError::EmptyPropertyError(
                prop,
                self.state.display_context(),
            ))
        } else if properties.len() > 1 {
            Err(SearchError::AmbiguousPropertyError(
                properties.len(),
                prop,
                self.state.display_context(),
            ))
        } else {
            let matching = properties.next().unwrap();
            self.tracer
                .trace(&prop, matching, self.state.display_context());
            Ok(matching.clone())
        }
    }

    pub fn get_single_value(&self, prop: impl AsRef<str>) -> SearchResult<PersistentStr> {
        Ok(self.get_single_property(prop)?.value.clone())
    }

    fn with_new_state(&self, state: ContextState<Acc>) -> Self {
        Self {
            dag: self.dag.clone(),
            tracer: self.tracer.clone(),
            state,
        }
    }

    fn augment_all(
        &self,
        keys: impl IntoIterator<Item = Key>, // TODO: this causes an unnecessary Arc alloc
        activate_root: bool,
    ) -> Self {
        let mut state = self.state.clone();

        let mut keys = CurrentConstraints::from_iter(keys.into_iter().map(Into::into));
        // Only add the initial keys to this context; don't want to track activations
        for key in keys.iter().cloned() {
            state.debug_context = state.debug_context.enqueue(key);
        }

        if activate_root {
            let prop_node = self.dag.get_data(self.dag.prop_node);
            let root_constraints = VecDeque::from_iter(prop_node.constraints.iter().cloned());
            // TODO: This is messy and creates duplicate work
            keys = root_constraints.into_iter().chain(keys).collect();
            state = state.activate(&mut keys, &self.dag, self.dag.prop_node, None);
        }
        while let Some(constraint) = keys.pop_front() {
            assert!(constraint.key.values.len() < 2);
            let value = constraint.key.values.first().cloned();
            state = state.match_step(&mut keys, &self.dag, &constraint.key.name, value.as_deref());
        }
        self.with_new_state(state)
    }

    pub fn get_debug_context(&self) -> DisplayContext {
        self.state.display_context()
    }

    pub fn get_dag_stats(&self) -> dag::Stats {
        self.dag.stats()
    }

    #[cfg(feature = "dot")]
    pub fn dag_to_dot_str(&self) -> String {
        use crate::dag::dot::*;
        let digraph = dag_to_digraph(&self.dag, &self.state.tallies);
        format!("{:?}", to_dot(&digraph))
    }
}

pub trait Accumulator: Default + Clone + std::fmt::Debug {
    fn accum(self, prop: PropertyValue, specificity: Specificity) -> Self;
    fn values(&self) -> impl ExactSizeIterator<Item = &PropertyValue>;
}

// TODO really this should probably be a map from value to specificity, where only the highest specificity
// for a given specific value/origin is retained
#[allow(dead_code)] // Temporarily keeping this around, but don't really need it
#[derive(Clone, Debug, Default)]
struct SetAccumulator {
    values: PersistentSet<(PropertyValue, Specificity)>,
}
impl Accumulator for SetAccumulator {
    fn accum(self, prop: PropertyValue, specificity: Specificity) -> Self {
        SetAccumulator {
            values: self.values.insert((prop, specificity)),
        }
    }
    fn values(&self) -> impl ExactSizeIterator<Item = &PropertyValue> {
        self.values.iter().map(|(v, _)| v)
    }
}

#[derive(Clone, Debug)]
pub struct MaxAccumulator {
    specificity: Specificity,
    values: PersistentSet<PropertyValue>,
}
impl Accumulator for MaxAccumulator {
    fn accum(self, prop: PropertyValue, specificity: Specificity) -> Self {
        if specificity > self.specificity {
            MaxAccumulator {
                specificity,
                values: PersistentSet::from_iter([prop]),
            }
        } else if specificity == self.specificity {
            MaxAccumulator {
                specificity: self.specificity,
                values: self.values.insert(prop),
            }
        } else {
            self
        }
    }
    fn values(&self) -> impl ExactSizeIterator<Item = &PropertyValue> {
        self.values.iter()
    }
}
impl Default for MaxAccumulator {
    fn default() -> Self {
        Self {
            specificity: Specificity::zero(),
            values: Default::default(),
        }
    }
}

pub type Tallies = PersistentMap<Node, usize>;
type CurrentConstraints = VecDeque<Constraint>;

#[derive(Default, Clone, Debug)]
struct ContextState<Acc: Accumulator> {
    tallies: Tallies,
    or_specificities: PersistentMap<Node, Specificity>,
    props: PersistentMap<PersistentStr, Acc>,
    poisoned: PersistentSet<Node>,
    debug_context: PersistentQueue<Constraint>,
}
impl<Acc: Accumulator> ContextState<Acc> {
    fn insert_or_specificity(&self, n: Node, specificity: Specificity) -> Self {
        let mut new_state = self.clone();
        new_state.or_specificities = new_state.or_specificities.insert(n, specificity);
        new_state
    }

    // TODO: Replacement functions are very error-prone. Easy to forget to update the state
    #[must_use]
    fn with_tallies(&self, tallies: Tallies) -> Self {
        let mut new_state = self.clone();
        new_state.tallies = tallies;
        new_state
    }

    #[must_use]
    fn accum_tally(&self, g: &Dag, n: Node) -> (Self, bool) {
        let mut count = *self.tallies.get(&n).unwrap_or(&g.get_data(n).tally_count);
        if count > 0 {
            count -= 1;
            let tallies = self.tallies.insert(n, count);
            let activated = count == 0;
            return (self.with_tallies(tallies), activated);
        }
        (self.clone(), false)
    }

    #[must_use]
    fn activate_and(
        mut self,
        g: &Dag,
        n: Node,
        _propagated_specificity: Option<Specificity>,
    ) -> (Self, Option<Specificity>) {
        let (state, zeroed) = self.accum_tally(g, n);
        self = state;
        if zeroed {
            let n_data = g.get_data(n);
            if let NodeType::And(specificity) = n_data.op {
                (self, Some(specificity))
            } else {
                panic!("Attempted activate_and with an OR node: {n:?}, {n_data:?}");
            }
        } else {
            (self, None)
        }
    }

    #[must_use]
    fn activate_or(
        self,
        _g: &Dag,
        n: Node,
        propagated_specificity: Option<Specificity>,
    ) -> (Self, Option<Specificity>) {
        let prev_spec = *self
            .or_specificities
            .get(&n)
            .unwrap_or(&Specificity::zero());
        if let Some(propagated_specificity) = propagated_specificity {
            if propagated_specificity > prev_spec {
                (
                    self.insert_or_specificity(n, propagated_specificity),
                    Some(propagated_specificity),
                )
            } else {
                (self, None)
            }
        } else {
            (self, Some(prev_spec))
        }
    }

    #[must_use]
    fn update_props(
        mut self,
        new_props: impl IntoIterator<Item = Property>,
        activation_specificity: Specificity,
    ) -> Self {
        for Property(name, prop_val) in new_props {
            let prop_vals = self.props.get(&name).unwrap_or(&Acc::default()).clone();
            let prop_specificity =
                Specificity::new(prop_val.override_level, 0, 0, 0) + activation_specificity;
            self.props = self
                .props
                .insert(name, prop_vals.accum(prop_val, prop_specificity));
        }
        self
    }

    #[must_use]
    fn activate(
        mut self,
        active_constraints: &mut CurrentConstraints,
        g: &Dag,
        n: Node,
        propagated_specificity: Option<Specificity>,
    ) -> Self {
        let activator = if matches!(g.get_data(n).op, NodeType::And(..)) {
            Self::activate_and
        } else {
            Self::activate_or
        };
        let (new_state, activation_specificity) = activator(self, g, n, propagated_specificity);
        self = new_state;
        if let Some(activation_specificity) = activation_specificity {
            let n_data = g.get_data(n);
            for constraint in &n_data.constraints {
                active_constraints.push_back(constraint.clone());
            }

            self = self.update_props(n_data.props.clone(), activation_specificity);
            for n in &n_data.children {
                self = Self::activate(
                    self,
                    active_constraints,
                    g,
                    *n,
                    Some(activation_specificity),
                )
            }
            self
        } else {
            self
        }
    }

    #[must_use]
    fn poison(mut self, g: &Dag, n: Node) -> Self {
        let mut fully_poisoned = false;
        if matches!(g.get_data(n).op, NodeType::And(..)) {
            // a bit of care is required here, since we build tally-one
            // conjunction nodes for literals, even when they represent
            // disjunctions of multiple values.
            // TODO this is starting to feel a bit too cute and tricky,
            // might be time to build those in a more obvious way and use
            // a more explicit technique to ensure uniqueness of literal
            // values in context.
            // but anyway, because of that, and because we always activate
            // prior to poisoning, we can avoid incorrectly poisoning a
            // literal node just by checking to see whether it's already
            // been fully activated. that's the only scenario in which this
            // can happen, so it's sufficient to detect it.
            if self.tallies.get(&n).is_some_and(|t| *t != 0) && !self.poisoned.contains(&n) {
                fully_poisoned = true;
            }
        } else {
            (self, fully_poisoned) = self.accum_tally(g, n);
        }

        if fully_poisoned {
            self.poisoned = self.poisoned.insert(n);
            for n in &g.get_data(n).children {
                self = self.poison(g, *n);
            }
        }
        self
    }

    #[must_use]
    fn match_step(
        mut self,
        active_constraints: &mut CurrentConstraints,
        g: &Dag,
        key: &str,
        value: Option<&str>,
    ) -> Self {
        if let Some(matcher) = g.children.get(key) {
            if let Some(wildcard) = matcher.wildcard {
                self = self.activate(active_constraints, g, wildcard, None);
            }
            if let Some(value) = value
                && let Some(positive_values) = matcher.positive_values.get(value)
            {
                for node in positive_values {
                    self = self.activate(active_constraints, g, *node, None);
                }
            }
            // TODO negative matches here too
            if !self.poisoned.is_empty() {
                for (v2, nodes) in &matcher.positive_values {
                    // TODO here, there's a question... if value is None, do
                    // we insist that no value ever be asserted for key and
                    // poison everything? or do we remain agnostic, with the
                    // idea that key.value is still a monotonic refinement of
                    // just key? for now we assume the former.
                    if value != Some(v2) {
                        for node in nodes {
                            self = self.poison(g, *node);
                        }
                    }
                }
            }
        }

        self
    }

    fn display_context(&self) -> DisplayContext {
        DisplayContext(self.debug_context.clone())
    }
}

/// Contains the constraints which have been applied to the current context. Formats nicely for
/// debugging and logging.
pub struct DisplayContext(pub PersistentQueue<Constraint>);
impl Display for DisplayContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "in context: [ {} ]", self.0.iter().joined_by(" > "))
    }
}
impl std::fmt::Debug for DisplayContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Context[{}]", self.0.iter().joined_by(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::NullResolver, tracer::NullTracer};

    impl Context<MaxAccumulator, NullTracer> {
        pub fn from_ccs(ccs: impl AsRef<str>) -> crate::AstResult<Self> {
            Self::from_ccs_with(ccs, NullResolver(), NullTracer {})
        }
    }

    #[test]
    fn get_single_value() {
        let ctx = Context::from_ccs(
            r#"
                a = 1
                a = 2

                c = 4.3
                d = "cannotcast"
            "#,
        )
        .unwrap();

        assert!(matches!(
            ctx.get_single_value("a"),
            Err(SearchError::AmbiguousPropertyError(2, ..))
        ));

        assert!(matches!(
            ctx.get_single_value("b"),
            Err(SearchError::MissingPropertyError(..))
        ));

        assert_eq!(&*ctx.get_single_value("c").unwrap(), "4.3");
    }

    #[test]
    fn with_root_node() {
        let context = Context::from_ccs(
            r#"
                a, f b e, c {
                    c d {
                        x = y
                    }
                    e f {
                        foobar = abc
                    }
                }
                a, c, b e f : baz = quux

                x = outerx
                baz = outerbaz
                foobar = outerfoobar
                noothers = val
                
                multi {
                    x = failure
                    level {
                        x = success
                    }
                }

                z.underconstraint {
                    c = success
                }
                @constrain z.underconstraint
                c = failure
            "#,
        )
        .unwrap();

        assert_eq!(&*context.get_single_value("baz").unwrap(), "outerbaz");

        let in_a = context.augment("a");
        assert_eq!(&*in_a.get_single_value("baz").unwrap(), "quux");
        assert_eq!(&*context.get_single_value("x").unwrap(), "outerx");

        let in_c = context.augment("c");
        assert_eq!(&*in_c.get_single_value("x").unwrap(), "outerx");

        let in_cd = in_c.augment("d");
        assert_eq!(&*in_cd.get_single_value("x").unwrap(), "y");

        assert_eq!(&*in_cd.get_single_value("noothers").unwrap(), "val");

        assert_eq!(&*context.get_single_value("c").unwrap(), "success");

        let lvl1 = context.augment("multi");
        let lvl2 = lvl1.augment("level");

        assert_eq!(&*lvl2.get_single_value("x").unwrap(), "success");
    }
}

#[cfg(all(test, feature = "dot"))]
mod dot_examples {
    use super::*;
    use crate::ast::macros::*;

    #[test]
    fn activations_to_dot_1() {
        let ccs = r#"
                a b c {
                    x = 1
                }
                a b {
                    y = 2
                }
                b c (e, f, g) {
                    z = 3
                }
                b d (e, f) {
                    w = 4
                }
                b {
                    s = 5
                }
            "#;
        let context = Context::from_ccs(ccs).unwrap();
        let context = context.augment_all([key!("b"), key!("d")], false);
        println!("{}", context.dag_to_dot_str());
    }
}
