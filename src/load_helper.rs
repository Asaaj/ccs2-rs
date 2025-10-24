use std::path::{Path, PathBuf};

use crate::{AstError, AstResult, ast::ImportResolver};

/// An error that occurs while reading a CCS file, before it gets parsed
///
/// See [`IoResult`]
#[derive(thiserror::Error, Debug)]
pub enum IoError {
    #[error("Failed to find file {0:?}")]
    FileNotFound(std::path::PathBuf),
    #[error(transparent)]
    Other(#[from] std::io::Error),
}
pub type IoResult<T> = Result<T, IoError>;

pub fn load(path: impl AsRef<Path>) -> IoResult<String> {
    use std::io::ErrorKind::*;

    let path = path.as_ref();
    match std::fs::read_to_string(path) {
        Ok(content) => Ok(content),
        Err(e) => match e.kind() {
            NotFound => Err(IoError::FileNotFound(path.into())),
            _ => Err(IoError::Other(e)),
        },
    }
}

/// The default import resolver, which resolves everything relative to one initial path
pub struct RelativePathResolver(PathBuf);
impl RelativePathResolver {
    /// A convenience function for creating based on a specific path, such as the `main.ccs`
    ///
    /// Note that the source should be an absolute path, but this will then allow for resolving
    /// relative to the parent directory of the given file.
    ///
    /// If the source isn't absolute, it will go relative to the current working directory. However,
    /// subsequent resolvers created through [`ImportResolver::new_context`] _will_ be absolute.
    pub fn siblings_with(file: impl AsRef<Path>) -> AstResult<Self> {
        let path: PathBuf = file.as_ref().into();
        if !path.is_file() {
            Err(AstError::ImportFailed(path))
        } else {
            Ok(Self(path))
        }
    }
}
impl ImportResolver for RelativePathResolver {
    fn current_file_name(&self) -> PathBuf {
        self.0.clone()
    }

    fn new_context(&self, location: &Path) -> AstResult<Self> {
        let new_file = self
            .0
            .parent()
            .ok_or(AstError::ImportFailed(location.into()))?
            .join(location);
        Self::siblings_with(new_file)
    }

    fn load(&self) -> AstResult<String> {
        std::fs::read_to_string(&self.0).map_err(|_| AstError::ImportFailed(self.0.clone()))
    }
}
