use crate::{codegen, parse, resolve, types};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),

    #[error("Multiple modules defined with the same name: {0}")]
    MultipleModules(String),

    #[error("Parse error: {0}")]
    Parse(#[from] parse::Error),

    #[error("Resolution error: {0}")]
    Resolve(#[from] resolve::Error),

    #[error("Type error: {0}")]
    Type(#[from] types::Error),

    #[error("Code generation error: {0}")]
    CodeGen(#[from] codegen::Error),
}
