// Used for thiserror backtrace:
#![feature(error_generic_member_access)]

pub mod ast;
pub mod dag;
pub mod search;

pub use search::Context;

#[derive(thiserror::Error, Debug)]
pub enum CcsError {
    #[error(transparent)]
    AstError(#[from] ast::AstError),
    #[error(transparent)]
    DagError(#[from] dag::DagError),
    #[error(transparent)]
    ContextError(#[from] search::ContextError),
}

pub type CcsResult<T> = Result<T, CcsError>;
