use std::path::PathBuf;

use crate::name::ModulePath;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),

    #[error("Invalid characters in file path: `{0}`")]
    BadFilePath(String),

    #[error("Attempt to compile a directory: `{0}`")]
    InputFileWasDirectory(PathBuf),

    #[error(
        "Multiple modules defined with the same name: `{0}` (files {} and {})",
        .1.as_ref().map(|p| format!("{}", p.display())).unwrap_or_else(|| "<stdin>".to_string()),
        .2.as_ref().map(|p| format!("{}", p.display())).unwrap_or_else(|| "<stdin>".to_string()),
    )]
    MultipleModules(ModulePath, Option<PathBuf>, Option<PathBuf>),
}
