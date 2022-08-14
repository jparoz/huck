use crate::{parse, types};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Parse error: {0}")]
    Parse(#[from] parse::Error),
    #[error("Type error: {0}")]
    Type(#[from] types::Error),
}
