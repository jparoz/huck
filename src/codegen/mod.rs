pub mod lua;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Write error: {0}")]
    Write(#[from] std::fmt::Error),

    #[error("Incorrect number of function arguments in definition of function `{0}`")]
    IncorrectArgumentCount(String),
}
