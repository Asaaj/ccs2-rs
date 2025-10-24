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
    /// Given an absolute directory, this will resolve imports relative to that directory
    pub fn rooted_in(directory: impl AsRef<Path>) -> Self {
        let path = directory.as_ref();
        assert!(
            path.is_dir(),
            "Cannot create SameDirectoryResolver from invalid directory: {path:?}"
        );
        Self(path.into())
    }

    /// A convenience function for creating based on a specific path, such as the `main.ccs`
    ///
    /// Note that the source must be an absolute path, but this will then allow for resolving
    /// relative to the parent directory of the `main.ccs` file (or whatever is provided).
    pub fn from_main_file(file: impl AsRef<Path>) -> Self {
        let path = file.as_ref();
        assert!(
            path.is_file(),
            "Cannot create SameDirectoryResolver from invalid file: {path:?}"
        );
        Self(path.parent().unwrap().into())
    }
}
impl ImportResolver for RelativePathResolver {
    fn resolve(&self, location: &Path) -> AstResult<String> {
        let location = self.0.join(location);
        std::fs::read_to_string(&location).map_err(|_| AstError::ImportFailed(location))
    }
}
