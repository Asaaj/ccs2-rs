use std::{marker::PhantomData, ops::Deref};

use crate::{
    ast::{Constraint, Key, PersistentStr, PropDef, Property, PropertyValue, Specificity},
    dag::{Node, NodeType},
};

// TODO: Make thread-safety opt-in? These should be the only changes...
// rpds docs say Rc -> Arc doubles runtime of some operations.
type PersistentQueue<T> = rpds::QueueSync<T>;
type PersistentSet<T> = rpds::HashTrieSetSync<T>;
type PersistentMap<K, V> = rpds::HashTrieMapSync<K, V>;
type Dag = std::sync::Arc<crate::dag::Dag>;

trait Accumulator: Default + Clone {
    fn accum(self, prop: PropertyValue, specificity: Specificity) -> Self;
}

// TODO really this should probably be a map from value to specificity, where only the highest specificity
// for a given specific value/origin is retained
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
}

#[derive(Clone, Debug)]
struct MaxAccumulator {
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
}
impl Default for MaxAccumulator {
    fn default() -> Self {
        Self {
            specificity: Specificity::zero(),
            values: Default::default(),
        }
    }
}

pub trait PropertyTracer {
    fn trace(&mut self); // TODO!
}
pub struct NullTracer();
impl PropertyTracer for NullTracer {
    fn trace(&mut self) {}
}

type Tallies = PersistentMap<Node, usize>;

#[derive(Default, Clone)]
struct ContextState<Acc: Accumulator> {
    keys: PersistentQueue<Constraint>, // TODO: name is just for consistency with Python
    tallies: Tallies,
    or_specificities: PersistentMap<Node, Specificity>,
    props: PersistentMap<PersistentStr, Acc>,
    poisoned: PersistentSet<Node>,
    debug_context: Option<String>, // TODO: Persistent
}
impl<Acc: Accumulator> ContextState<Acc> {
    fn insert_or_specificity(&self, n: Node, specificity: Specificity) -> Self {
        let mut new_state = self.clone();
        new_state.or_specificities = new_state.or_specificities.insert(n, specificity);
        new_state
    }

    fn append_constraint(&self, constraint: Constraint) -> Self {
        let mut new_state = self.clone();
        new_state.keys = new_state.keys.enqueue(constraint);
        new_state
    }

    // TODO: Replacement functions are very error-prone. Easy to forget to update the state
    fn with_tallies(&self, tallies: Tallies) -> Self {
        let mut new_state = self.clone();
        new_state.tallies = tallies;
        new_state
    }
    fn accum_tally(&self, g: &Dag, n: Node) -> (Self, bool) {
        let mut count = *self.tallies.get(&n).unwrap_or(&g.get_data(n).tally_count);
        if count > 0 {
            count -= 1;
            let tallies = self.tallies.insert(n, count);
            if count == 0 {
                return (self.with_tallies(tallies), true);
            }
        }
        (self.clone(), false)
    }

    fn activate_and(
        &self,
        g: &Dag,
        n: Node,
        _propagated_specificity: Option<Specificity>,
    ) -> (Self, Option<Specificity>) {
        let (state, zeroed) = self.accum_tally(g, n);
        if zeroed {
            let n_data = g.get_data(n);
            if let NodeType::And(specificity) = n_data.op {
                (state, Some(specificity))
            } else {
                panic!("Attempted activate_and with an OR node: {n:?}, {n_data:?}");
            }
        } else {
            (state, None)
        }
    }

    fn activate_or(
        &self,
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
                (self.clone(), None)
            }
        } else {
            (self.clone(), Some(prev_spec))
        }
    }

    fn update_props(
        &self,
        new_props: impl IntoIterator<Item = Property>,
        activation_specificity: Specificity,
    ) -> Self {
        let mut state = self.clone();
        for Property(name, prop_val) in new_props {
            let prop_vals = state.props.get(&name).unwrap_or(&Acc::default()).clone();
            let prop_specificity =
                Specificity::new(prop_val.override_level, 0, 0, 0) + activation_specificity;
            state.props = state
                .props
                .insert(name, prop_vals.accum(prop_val, prop_specificity));
        }
        state
    }

    fn activate(&self, g: &Dag, n: Node, propagated_specificity: Option<Specificity>) -> Self {
        let activator = if matches!(g.get_data(n).op, NodeType::And(..)) {
            Self::activate_and
        } else {
            Self::activate_or
        };
        let (mut state, activation_specificity) = activator(self, g, n, propagated_specificity);
        if let Some(activation_specificity) = activation_specificity {
            let n_data = g.get_data(n);
            for constraint in &n_data.constraints {
                state = state.append_constraint(constraint.clone());
            }

            state = state.update_props(n_data.props.clone(), activation_specificity);
            for n in &n_data.children {
                state = state.activate(g, *n, Some(activation_specificity))
            }
            state
        } else {
            self.clone()
        }
    }

    fn poison(&self, g: &Dag, n: Node) -> Self {
        let mut fully_poisoned = false;
        let mut state = self.clone();
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
            (state, fully_poisoned) = self.accum_tally(g, n);
        }

        if fully_poisoned {
            state.poisoned = state.poisoned.insert(n);
            for n in &g.get_data(n).children {
                state = state.poison(g, *n);
            }
        }
        state
    }

    fn match_step(&self, g: &Dag, key: &str, value: Option<&str>) -> Self {
        let mut state = self.clone();
        if let Some(matcher) = g.children.get(key) {
            if let Some(wildcard) = matcher.wildcard {
                state = state.activate(g, wildcard, None);
            }
            if let Some(value) = value
                && let Some(positive_values) = matcher.positive_values.get(value)
            {
                for node in positive_values {
                    state = state.activate(g, *node, None);
                }
            }
            // TODO negative matches here too
            if !state.poisoned.is_empty() {
                for (v2, nodes) in &matcher.positive_values {
                    // TODO here, there's a question... if value is None, do
                    // we insist that no value ever be asserted for key and
                    // poison everything? or do we remain agnostic, with the
                    // idea that key.value is still a monotonic refinement of
                    // just key? for now we assume the former.
                    if value != Some(&*v2) {
                        for node in nodes {
                            state = state.poison(g, *node);
                        }
                    }
                }
            }
        }

        state
    }
}

pub struct Context<Acc: Accumulator, Tracer: PropertyTracer> {
    dag: Dag,
    tracer: Tracer,
    state: ContextState<Acc>,
}
impl<Acc: Accumulator, Tracer: PropertyTracer> Context<Acc, Tracer> {
    pub fn with_tracer(dag: Dag, tracer: Tracer) -> Self {
        Self {
            dag,
            tracer,
            state: Default::default(),
        }
    }

    fn new(dag: Dag, state: ContextState<Acc>, tracer: Tracer) -> Self {
        Self { dag, tracer, state }
    }

    fn augment_all(
        &self,
        keys: impl IntoIterator<Item = Key>,
        activate_root: bool,
    ) -> ContextState<Acc> {
        let mut state = self.state.clone();
        if activate_root {
            let prop_node = self.dag.get_data(self.dag.prop_node);
            // TODO: Would probably be nicer to use a List, especially for this case
            state.keys = PersistentQueue::from_iter(
                prop_node
                    .constraints
                    .iter()
                    .cloned()
                    .chain(state.keys.iter().cloned()),
            );
            state = state.activate(&self.dag, self.dag.prop_node, None);
        }
        for key in keys.into_iter() {
            assert!(key.values.len() < 2);
            let value = key.values.first().cloned();
            state = state.match_step(&self.dag, &*key.name, value.as_deref());
        }
        state
    }
}
