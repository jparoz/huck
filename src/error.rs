use crate::types;

#[derive(Debug)]
pub enum Error {
    // @Cleanup: rename Nom to Parse (?)
    Nom(String),
    Type(types::Error),
}

pub type Result<T> = std::result::Result<T, Error>;
