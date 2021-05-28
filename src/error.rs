#[derive(Debug)]
pub enum Error {
    Nom(String),
}

pub type Result<T> = std::result::Result<T, Error>;
