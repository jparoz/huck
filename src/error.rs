use std::path::PathBuf;

use crate::{dependencies, name, parse, typecheck};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),

    #[error("Invalid characters in file path: `{0}`")]
    BadFilePath(String),

    #[error("Attempt to compile a directory: `{0}`")]
    InputFileWasDirectory(PathBuf),

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

#[cfg(test)]
mod test {
    use super::Error;

    #[test]
    fn error_file_doesnt_exist() {
        assert!(matches!(
            dbg!(crate::load("file/doesnt/exist.hk")),
            Err(Error::IO(_))
        ))
    }

    #[cfg_attr(not(unix), ignore)]
    #[test]
    fn error_bad_file_path() {
        use std::{ffi::OsString, os::unix::prelude::OsStringExt};

        // \xC3\x28 is invalid UTF-8
        let path = OsString::from_vec(Vec::from(&b"\xC3\x28.hk"[..]));
        assert!(matches!(
            dbg!(crate::load(&path)),
            Err(Error::BadFilePath(_))
        ))
    }
}
