use std::str::FromStr;

pub enum Ast<'a> {
    Lit(Lit<'a>),
    Var(&'a str),
}
// data Expr'
// = Lit Lit
// | Var Symbol
// | Lam Lambda
// | App Expr' Expr'

pub struct Lit<'a> {
    text: &'a str,
}
// data Lit
// = Number (Either Integer Double)
// | String Text
// | Char Char

impl<'a> FromStr for Ast<'a> {
    type Err = ParseError;
    fn from_str(file: &str) -> Result<Ast<'a>, ParseError> {
        let mut iter = Tokens::new(file);
        while let Some(tok) = iter.next() {
            // @Todo
            println!("{}", tok);
        }
        Err(ParseError { message: "hi" }) // @Todo
    }
}

#[derive(Debug)] // @Todo: proper impl
pub struct ParseError {
    message: &'static str,
}

struct Tokens<'a> {
    file: &'a str,
    cursor: usize,
}

impl<'a> Tokens<'a> {
    fn new<'b>(file: &'b str) -> Tokens<'b> {
        Tokens {
            file: file,
            cursor: 0,
        }
    }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<Self::Item> {
        None // @Todo
    }
}
