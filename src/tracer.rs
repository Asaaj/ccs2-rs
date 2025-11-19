use std::{ops::Deref, sync::Arc};

use crate::{SearchError, ast::PropertyValue, search::DisplayContext};

/// A callback which is called by the [`Context`] when a property is found
///
/// Provides debug information about the current context's constraints under which the property was
/// found.
///
/// [`Context`]: crate::Context
pub trait PropertyTracer: Send + Sync {
    fn on_found(&self, name: &str, value: &PropertyValue, context: DisplayContext);
    fn on_error(&self, error: SearchError);
}

pub trait ClonablePropertyTracer: PropertyTracer + Clone {}
impl<T: PropertyTracer + Clone> ClonablePropertyTracer for T {}

impl<T: ?Sized + PropertyTracer> PropertyTracer for Arc<T> {
    fn on_found(&self, name: &str, value: &PropertyValue, context: DisplayContext) {
        self.deref().on_found(name, value, context)
    }

    fn on_error(&self, error: SearchError) {
        self.deref().on_error(error);
    }
}
// impl<T: PropertyTracerImpl + Clone> PropertyTracer for Arc<T> {}

/// A [`PropertyTracer`] that does nothing
#[derive(Clone)]
pub struct NullTracer();
impl PropertyTracer for NullTracer {
    fn on_found(&self, _name: &str, _value: &PropertyValue, _context: DisplayContext) {}
    fn on_error(&self, _error: SearchError) {}
}

#[cfg(feature = "log")]
pub(crate) mod log {
    use super::*;

    /// A [`PropertyTracer`] that logs when and where properties are found
    ///
    /// Requires the `log` feature
    #[derive(Clone)]
    pub struct LogTracer {
        pub success_level: ::log::Level,
        pub error_level: ::log::Level,
    }
    impl LogTracer {
        pub fn single_level(level: ::log::Level) -> Self {
            LogTracer {
                success_level: level,
                error_level: level,
            }
        }
    }

    impl PropertyTracer for LogTracer {
        fn on_found(&self, name: &str, value: &PropertyValue, context: DisplayContext) {
            ::log::log!(
                self.success_level,
                "Found property: {name} = {}\n\t{context}\n\torigin: {}",
                value.value,
                value.origin
            );
        }

        fn on_error(&self, error: SearchError) {
            match error {
                SearchError::MissingPropertyError { name, context } => {
                    ::log::log!(self.error_level, "Property not found: {name}\n\t{context}");
                }
                SearchError::EmptyPropertyError { name, context } => {
                    ::log::log!(
                        self.error_level,
                        "Empty property found: {name}\n\t{context}"
                    );
                }
                SearchError::AmbiguousPropertyError {
                    count,
                    name,
                    context,
                } => {
                    ::log::log!(
                        self.error_level,
                        "Ambiguous property found ({count} values): {name}\n\t{context}"
                    );
                }
            }
        }
    }
}
