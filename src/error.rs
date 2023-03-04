use crate::{dependencies, file, name, parse, typecheck};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Filesystem error: {0}")]
    File(#[from] file::Error),

    // @Cleanup: move to somewhere else, maybe utils::error?
    #[error("Failed when normalizing Lua output, with lua-format stderr: {0}")]
    NormalizeFailed(String),

    #[error("Parse error: {0}")]
    Parse(#[from] parse::Error),

    #[error("Name resolution error: {0}")]
    NameResolution(#[from] name::Error),

    #[error("Dependency resolution error: {0}")]
    DependencyResolution(#[from] dependencies::Error),

    #[error("Type error: {0}")]
    Type(#[from] typecheck::Error),
}
