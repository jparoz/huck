use crate::{codegen, parse, resolve, typecheck};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),

    #[error("Invalid characters in file path: `{0}`")]
    BadFilePath(String),

    #[error("Parse error: {0}")]
    Parse(#[from] parse::Error),

    #[error("Resolution error: {0}")]
    Resolve(#[from] resolve::Error),

    #[error("Type error: {0}")]
    Type(#[from] typecheck::Error),

    #[error("Code generation error: {0}")]
    CodeGen(#[from] codegen::Error),
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

        //                              invalid UTF-8     .     h     k
        let path = OsString::from_vec(vec![0xC3, 0x28, 0x2E, 0x68, 0x6B]);
        assert!(matches!(
            dbg!(crate::load(&path)),
            Err(Error::BadFilePath(_))
        ))
    }
}
