#![feature(error_generic_member_access)]

pub mod ast;
pub mod dag;

#[derive(thiserror::Error, Debug)]
pub enum CcsError {
    #[error(transparent)]
    AstError(#[from] ast::AstError),
    #[error(transparent)]
    DagError(#[from] dag::DagError),
}

pub type CcsResult<T> = Result<T, CcsError>;
