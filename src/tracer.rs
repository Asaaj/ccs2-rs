use crate::{ast::PropertyValue, search::DisplayContext};

/// A callback which is called by the [`Context`] when a property is found
///
/// Provides debug information about the current context's constraints under which the property was
/// found.
///
/// [`Context`]: crate::Context
pub trait PropertyTracer: Clone {
    fn trace(&self, name: &str, value: &PropertyValue, context: DisplayContext);
}

/// A [`PropertyTracer`] that does nothing
#[derive(Clone)]
pub struct NullTracer();
impl PropertyTracer for NullTracer {
    fn trace(&self, _name: &str, _value: &PropertyValue, _context: DisplayContext) {}
}

#[cfg(feature = "log")]
pub(crate) mod log_tracer {
    use super::*;

    /// A [`PropertyTracer`] that logs when and where properties are found
    ///
    /// Requires the `log` feature
    #[derive(Clone)]
    pub struct LogTracer(pub log::Level);

    impl PropertyTracer for LogTracer {
        fn trace(&self, name: &str, value: &PropertyValue, context: DisplayContext) {
            log::log!(
                self.0,
                "Found property: {name} = {}\n\t{context}\n\torigin: {}",
                value.value,
                value.origin
            );
        }
    }
}
