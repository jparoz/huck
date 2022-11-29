use crate::{codegen, parse, types};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO error: {0}")]
    IO(#[from] std::io::Error),

    #[error("Parse error: {0}")]
    Parse(#[from] parse::Error),

    #[error("Type error: {0}")]
    Type(#[from] types::Error),

    #[error("Code generation error: {0}")]
    CodeGen(#[from] codegen::Error),
}
