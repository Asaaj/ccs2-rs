//! # Welcome to CCS2!
//!
//! Let's get started with an example to show some of the common use-cases. Given a file called
//! `doc.ccs` with the following contents:
//!
//! ```text
//! a, f b e, c {
//!   c d {
//!     x = y
//!   }
//!   e f {
//!     foobar = abc
//!   }
//! }
//!
//! x = 42
//! ```
//! ... you may want to do something like this:
//!
//! ```
//! use ccs2::{Context, ToType};
//!
//! let context = Context::logging("examples/configs/doc.ccs", log::Level::Info)?;
//!
//! let constrained = context.constrain("a").constrain("c").constrain("d");
//! assert_eq!(&constrained.get_type::<String>("x")?, "y");
//! assert!(constrained.get("foobar").is_err());
//!
//! // Original context is untouched:
//! assert_eq!(context.get("x")?.to_type::<i32>()?, 42);
//! # Ok::<(), ccs2::CcsError>(())
//! ```
//!
//! Example output (if logger is configured). Note that the actual origin will typically be absolute:
//!
//! ```text
//! [2025-10-27T15:22:32Z INFO  ccs2::tracer::log] Found property: x = y
//!         in context: [ a > c > d ]
//!         origin: examples/configs/doc.ccs:3
//! [2025-10-27T15:22:32Z INFO  ccs2::tracer::log] Property not found: foobar
//!         in context: [ a > c > d ]
//! [2025-10-27T15:22:32Z INFO  ccs2::tracer::log] Found property: x = 42
//!         in context: [  ]
//!         origin: examples/configs/doc.ccs:10
//! ```
//!
//! Most of the public API is in [`Context`], so check there for a resonable starting point.
//!
//! # Incomplete Requirements
//!
//! The following requirements are not yet complete:
//! - [x] `@import` does not work; I still need to add support for import resolvers and filename
//!       tracking.
//! - [x] The parser doesn't track files right now, which isn't great.
//! - [x] Log when a property could not be found, and when it's ambiguous.
//! - [x] Support search with default value, which doesn't return a `Result`.
//! - [ ] String interpolation from environment variables (or whatever injected mapping)
//! - [ ] `ContextState::debug_context` probably doesn't correctly communicate `@constrain` or
//!       `@context` statements... Instead of a separate queue, we may want to compute it directly
//!       from the dag.
//! - [ ] `stable` channel support: I'm currently on `nightly` for some odd `thiserror` reasons, but I
//!       don't think I should require that. I'll need to figure that out.
//! - [ ] Opt-in Arc vs Rc context?
//! - [ ] Much better error information for CCS syntax issues.
//!
//! - ... Probably a bunch of other stuff, I'll add to this as I think of things.
//!
//! # Features
//!
//! The crate provides the following features:
//! - `log` (default): Adds the [`LogTracer`] for logging when properties are found. Adds a
//!   dependency on [`log`].
//! - `extra_conversions` (default): Adds a parsers for getting [`std::time::Duration`] and
//!   [`std::time::SystemTime`] from CCS property strings. Adds a dependency on [`chrono`] and
//!   [`humantime`].
//! - `dot`: Adds tools for exporting the underlying DAG to `dot` syntax, which allows for
//!   visualizing the context's state. Adds a dependency on [`petgraph`].

// Used for thiserror backtrace:
#![feature(error_generic_member_access)]

pub mod ast;
pub mod dag;

mod load_helper;
mod property_helper;
mod search;
mod tracer;

use std::{path::Path, sync::Arc};

#[cfg(feature = "log")]
pub use crate::tracer::log::LogTracer;
pub use crate::{
    ast::{AstError, AstResult, ImportResolver, PersistentStr, PropertyValue},
    dag::Stats as DagStats,
    load_helper::{IoError, IoResult, RelativePathResolver},
    property_helper::{
        CommaSeparatedList, ConversionFailed, ConversionResult, ToType, TypedProperty,
    },
    search::{AsKey, DisplayContext, SearchError, SearchResult},
    tracer::{ClonablePropertyTracer, NullTracer, PropertyTracer},
};

/// A common error type for code that tries to find and then convert a property
///
/// See [`ContextResult`]
#[derive(thiserror::Error, Debug)]
pub enum ContextError {
    #[error(transparent)]
    SearchError(#[from] SearchError),

    #[error(transparent)]
    ConversionError(#[from] ConversionFailed),
}
pub type ContextResult<T> = Result<T, ContextError>;

/// Slightly more flexible than `ContextError`, as it also handles issues in parsing/interpreting
///
/// This is the catch-all type for anything that can go wrong
///
/// See [`CcsResult`]
#[derive(thiserror::Error, Debug)]
pub enum CcsError {
    #[error(transparent)]
    IoError(#[from] IoError),

    #[error(transparent)]
    AstError(#[from] AstError),

    #[error(transparent)]
    SearchError(#[from] SearchError),

    #[error(transparent)]
    ConversionError(#[from] ConversionFailed),

    #[error(transparent)]
    ContextError(#[from] ContextError),
}
pub type CcsResult<T> = Result<T, CcsError>;

/// The primary representation of a CCS search state
///
/// Typically you'll want the [`Context::logging`] constructor, or (if not using the `log` feature),
/// the [`Context::load_with_tracer`]. See [`PropertyTracer`] for more information.
///
/// In tests, you may want [`Context::from_str`] with test implementations of resolvers and tracers.
#[derive(Clone)]
pub struct Context {
    context: search::Context<search::MaxAccumulator, Arc<dyn PropertyTracer>>,
}

#[cfg(feature = "log")]
impl Context {
    /// Loads a CCS file, and creates a context that logs when and where properties are found
    ///
    /// Uses the [`RelativePathResolver`]
    ///
    /// See [`PropertyTracer`] and [`LogTracer`] for more.
    pub fn logging(path: impl AsRef<Path>, level: log::Level) -> CcsResult<Self> {
        let path = path.as_ref();
        Self::load(
            path,
            Self::default_resolver(&path)?,
            LogTracer::single_level(level),
        )
    }
}

impl Context {
    /// Creates a context that does not trace when or where properties are found
    ///
    /// Will use an empty [`ImportResolver`], that just skips over import statements. To provide a
    /// different `ImportResolver`, use [`Context::from_str`]
    ///
    /// Generally this is most useful in tests.
    pub fn from_str_without_tracing(ccs: impl AsRef<str>) -> AstResult<Self> {
        Self::from_str(ccs, ast::NullResolver(), NullTracer {})
    }
}

impl Context {
    fn default_resolver(path: impl AsRef<Path>) -> CcsResult<impl ImportResolver> {
        Ok(RelativePathResolver::siblings_with(path)?)
    }

    /// Loads a CCS file, and creates a context with the provided tracer
    ///
    /// Uses the [`RelativePathResolver`]
    ///
    /// See [`PropertyTracer`] for more.
    pub fn load_with_tracer(
        path: impl AsRef<Path>,
        tracer: impl PropertyTracer + 'static,
    ) -> CcsResult<Self> {
        let path = path.as_ref();
        Self::load(path, Self::default_resolver(&path)?, tracer)
    }

    /// Loads a CCS file, and creates a context with the provided import resolver and tracer
    ///
    /// See [`ImportResolver`] [`PropertyTracer`] for more.
    pub fn load(
        path: impl AsRef<Path>,
        resolver: impl ImportResolver,
        tracer: impl PropertyTracer + 'static,
    ) -> CcsResult<Self> {
        let tracer: Arc<dyn PropertyTracer> = Arc::new(tracer);
        Ok(Self {
            context: search::Context::load(path, resolver, tracer)?,
        })
    }

    /// Creates a context from a provided CCS string, using the provided import resolver and tracer
    ///
    /// See [`ImportResolver`] [`PropertyTracer`] for more.
    ///
    /// Mostly useful for tests.
    pub fn from_str(
        ccs: impl AsRef<str>,
        resolver: impl ImportResolver,
        tracer: impl PropertyTracer + 'static,
    ) -> AstResult<Self> {
        let tracer: Arc<dyn PropertyTracer> = Arc::new(tracer);
        Ok(Self {
            context: search::Context::from_ccs_with(ccs, resolver, tracer)?,
        })
    }

    /// Create a new context augmented with the given constraint
    ///
    /// # Example: Key-only constraint
    /// Given the following CCS:
    /// ```text
    /// module : a = z
    /// ```
    /// the property `a` can be retrieved through constraining with `"module"`:
    ///
    /// ```
    /// # let context = ccs2::Context::logging("examples/configs/doc.ccs", log::Level::Info).unwrap();
    /// assert!(context.get_value("a").is_err());
    ///
    /// let x: &str = &context.constrain("module").get_value("a")?;
    /// assert_eq!(x, "z");
    /// # Ok::<(), ccs2::SearchError>(())
    /// ```
    ///
    /// # Example: Key-value constraint
    /// Given the following CCS;
    /// ```text
    /// env.prod : a = z
    /// ```
    /// the property `a` can be retrieved through constraining with `("env", "prod")`:
    ///
    /// ```
    /// # let context = ccs2::Context::logging("examples/configs/doc.ccs", log::Level::Info).unwrap();
    /// assert!(context.constrain("env").get_value("a").is_err());
    ///
    /// let x: &str = &context.constrain(("env", "prod")).get_value("a")?;
    /// assert_eq!(x, "z");
    /// # Ok::<(), ccs2::SearchError>(())
    /// ```
    pub fn constrain(&self, constraint: impl AsKey) -> Self {
        Self {
            context: self.context.augment(constraint),
        }
    }

    /// Retrieves the value of a property from the current context, if possible
    pub fn get(&self, prop: impl AsRef<str>) -> SearchResult<PropertyValue> {
        self.context.get_single_property(prop)
    }

    /// Helper function for [`Context::get`] to get [`PropertyValue::value`]
    pub fn get_value(&self, prop: impl AsRef<str>) -> SearchResult<PersistentStr> {
        self.context.get_single_value(prop)
    }

    /// Helper for the ever-common "get and convert" pattern
    ///
    /// `context.get_type::<T>(prop)` is basically equivalent to `context.get(prop)?.to_type::<T>()`
    ///
    /// ```
    /// # let context = ccs2::Context::logging("examples/configs/doc.ccs", log::Level::Info).unwrap();
    /// assert_eq!(context.get_type::<i32>("x")?, 42);
    /// # Ok::<(), ccs2::ContextError>(())
    /// ```
    pub fn get_type<T: TypedProperty>(&self, prop: impl AsRef<str>) -> ContextResult<T> {
        Ok(self.get(prop)?.to_type::<T>()?)
    }

    /// Get a typed value, or provide the default if it cannot be found
    ///
    /// ```
    /// # let context = ccs2::Context::logging("examples/configs/doc.ccs", log::Level::Info).unwrap();
    /// assert_eq!(&context.get_or("undefined", "default_val".to_string()), "default_val");
    /// ```
    pub fn get_or<T: TypedProperty>(&self, prop: impl AsRef<str>, default: T) -> T {
        self.get_type::<T>(prop).unwrap_or(default)
    }

    /// Get a typed value, or return the type's [`Default`] value
    ///
    /// ```
    /// # let context = ccs2::Context::logging("examples/configs/doc.ccs", log::Level::Info).unwrap();
    /// assert_eq!(&context.get_or_default::<String>("undefined"), "");
    /// ```
    pub fn get_or_default<T: TypedProperty + Default>(&self, prop: impl AsRef<str>) -> T {
        self.get_type::<T>(prop).unwrap_or_default()
    }

    /// Retrieves the current context's queue of applied constraints, in the order they were applied
    pub fn get_current_context(&self) -> DisplayContext {
        self.context.get_debug_context()
    }

    /// Retrieves information about the DAG that underpins the activation algorithm
    pub fn get_dag_stats(&self) -> DagStats {
        self.context.get_dag_stats()
    }

    /// Turns the underlying DAG into a DOT string, which can be used for visualization.
    ///
    /// Requires the `dot` feature
    #[cfg(feature = "dot")]
    pub fn dag_as_dot_str(&self) -> String {
        self.context.dag_to_dot_str()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::NullResolver;

    #[test]
    fn context_is_send() {
        fn needs_send(_: impl Send) {}
        needs_send(Context::from_str("", NullResolver(), NullTracer {}));
    }

    #[test]
    fn context_is_sync() {
        fn needs_sync(_: impl Sync) {}
        needs_sync(Context::from_str("", NullResolver(), NullTracer {}));
    }
}
