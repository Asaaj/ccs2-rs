//! # Welcome to CCS2!
//!
//! Let's get started with an example to show some of the common use-cases:
//!
//! ```
//! use ccs2::{Context, ToType};
//!
//! // Usually from a file
//! let ccs_str = r#"
//! a, f b e, c {
//!     c d {
//!         x = y
//!     }
//!     e f {
//!         foobar = abc
//!     }
//! }
//!
//! x = 42
//! "#;
//!
//! let context = Context::logging(ccs_str, log::Level::Info)?;
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
//! Example output (if logger is configured). Note the file name on `origin` is missing, since we
//! aren't loading a file:
//!
//! ```text
//! [2025-10-23T20:51:27Z INFO  ccs2::tracer::log_tracer] Found property: x = y
//!         in context: [ a > c > d ]
//!         origin: :4
//! [2025-10-23T20:51:27Z INFO  ccs2::tracer::log_tracer] Found property: x = 42
//!         in context: [  ]
//!         origin: :11
//! ```
//!
//! # Imcomplete Requirements
//!
//! The following requirements are not yet complete:
//! - `@import` does not work; I still need to add support for import resolvers and filename
//!   tracking.
//! - `stable` channel support: I'm currently on `nightly` for some odd `thiserror` reasons, but I
//!   don't think I should require that. I'll need to figure that out.
//! - ... Probably a bunch of other stuff, I'll add to this as I think of things.
//!
//! # Features
//!
//! The crate provides the following features:
//! - `log` (default): Adds the [`LogTracer`] for logging when properties are found. Adds a
//!   dependency on [`log`].
//! - `extra_conversions` (default): Adds a parser for getting [`std::time::Duration`] from CCS
//!   property strings. Adds a dependency on [`humantime`].
//! - `dot`: Adds tools for exporting the underlying DAG to `dot` syntax, which allows for
//!   visualizing the context's state. Adds a dependency on [`petgraph`].

// Used for thiserror backtrace:
#![feature(error_generic_member_access)]

pub mod ast;
pub mod dag;

mod property_helper;
mod search;
mod tracer;

#[cfg(feature = "log")]
pub use crate::tracer::log_tracer::LogTracer;
pub use crate::{
    ast::{AstError, AstResult, PersistentStr, PropertyValue},
    dag::Stats as DagStats,
    property_helper::{
        CommaSeparatedList, ConversionFailed, ConversionResult, ToType, TypedProperty,
    },
    search::{AsKey, DisplayContext, SearchError, SearchResult},
    tracer::{NullTracer, PropertyTracer},
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
    /// Temporarily here; need to move this when we do import resolution and better file handling
    #[error("Failed to find file {0:?}")]
    FileNotFound(std::path::PathBuf),
    /// Also probably temporary; some other IO error happened while loading or something
    #[error(transparent)]
    Io(#[from] std::io::Error),

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
#[derive(Clone)]
pub struct Context<Tracer: PropertyTracer> {
    context: search::Context<search::MaxAccumulator, Tracer>,
}

#[cfg(feature = "log")]
impl Context<LogTracer> {
    /// Creates a context that logs when and where properties are found
    ///
    /// See [`PropertyTracer`] and [`LogTracer`] for more.
    pub fn logging(ccs: impl AsRef<str>, level: log::Level) -> Result<Self, AstError> {
        Self::new(ccs, LogTracer(level))
    }
}

impl Context<NullTracer> {
    /// Creates a context that does not trace when or where properties are found
    pub fn without_tracing(ccs: impl AsRef<str>) -> Result<Self, AstError> {
        Self::new(ccs, NullTracer {})
    }
}

impl<Tracer: PropertyTracer> Context<Tracer> {
    /// Creates a context with the provided tracer
    ///
    /// See [`PropertyTracer`] for more.
    pub fn new(ccs: impl AsRef<str>, tracer: Tracer) -> Result<Self, AstError> {
        Ok(Self {
            context: search::Context::from_ccs_with_tracer(ccs, tracer)?,
        })
    }

    /// Create a new context augmented with the given constraint
    ///
    /// # Example: Key-only constraint
    /// Given the following CCS:
    /// ```text
    /// module : x = y
    /// ```
    /// the property `x` can be retrieved through constraining with `"module"`:
    ///
    /// ```
    /// # let context = ccs2::Context::new("module : x = y", ccs2::NullTracer{}).unwrap();
    /// assert!(context.get_value("x").is_err());
    ///
    /// let x: &str = &context.constrain("module").get_value("x")?;
    /// assert_eq!(x, "y");
    /// # Ok::<(), ccs2::SearchError>(())
    /// ```
    ///
    /// # Example: Key-value constraint
    /// Given the following CCS;
    /// ```text
    /// env.prod : x = y
    /// ```
    /// the property `x` can be retrieved through constraining with `("env", "prod")`:
    ///
    /// ```
    /// # let context = ccs2::Context::new("env.prod : x = y", ccs2::NullTracer{}).unwrap();
    /// assert!(context.constrain("env").get_value("x").is_err());
    ///
    /// let x: &str = &context.constrain(("env", "prod")).get_value("x")?;
    /// assert_eq!(x, "y");
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
    pub fn get_type<T: TypedProperty>(&self, prop: impl AsRef<str>) -> ContextResult<T> {
        Ok(self.get(prop)?.to_type::<T>()?)
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
