use std::str::{FromStr, Chars};
use std::iter::{Enumerate, Peekable};
use std::fmt;

#[derive(Debug)]
pub enum Ast<'a> {
    Lit(Lit<'a>),
    Var(&'a str),
}
// data Expr'
// = Lit Lit
// | Var Symbol
// | Lam Lambda
// | App Expr' Expr'

#[derive(Debug)]
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
            println!("{:?}", tok);
        }
        Ok(Ast::Var("hi")) // @Todo
    }
}

#[derive(Debug)]
pub struct LexError {
    message: &'static str,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Lex error: {}", self.message)
    }
}

#[derive(Debug)]
pub struct ParseError {
    message: &'static str,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Parse error: {}", self.message)
    }
}

#[derive(Debug)]
enum Token<'a> {
    Module,
    Class,
    Data,
    Infix,
    Infixl,
    Infixr,
    Semi,
    Colon,
    Equals,
    Bar,
    Comma,
    Backslash,
    BraceOpen,
    BraceClose,
    BracketOpen,
    BracketClose,
    ParenOpen,
    ParenClose,
    Number(&'a str),
    Ident(&'a str),
    Operator(&'a str),
}

struct Tokens<'a> {
    file: &'a str,
    iter: Peekable<Enumerate<Chars<'a>>>,
}

impl<'a> Tokens<'a> {
    fn new<'b>(file: &'b str) -> Tokens<'b> {
        let iter = file.chars().enumerate().peekable();
        let mut tokens = Tokens {
            file: file,
            iter: iter,
        };

        tokens.skip_whitespace();
        tokens
    }

    fn lex_with<F>(&mut self, mut pred: F) -> Result<usize, LexError>
        where F: FnMut(char) -> bool
    {
        while let Some(&(i, c)) = self.iter.peek() {
            if pred(c) {
                self.iter.next();
            } else {
                return Ok(i);
            }
        }
        Err(LexError { message: "Unexpected EOF" })
    }

    fn skip_whitespace(&mut self) {
        let _ = self.lex_with(|c| c.is_whitespace());
    }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some((start, c)) = self.iter.next() {

            // Check for (line) comments.
            if c == '-' {
                if let Some(&(_, c2)) = self.iter.peek() {
                    if c2 == '-' {
                        let _ = self.lex_with(|c| c != '\n'); // Skip to newline
                        self.skip_whitespace();
                        continue;
                    }
                }
            }

            let res: Result<Token, LexError> = match c {
                ';' => Ok(Token::Semi),
                '\\' => Ok(Token::Backslash),
                ',' => Ok(Token::Comma),
                '{' => Ok(Token::BraceOpen),
                '}' => Ok(Token::BraceClose),
                '[' => Ok(Token::BracketOpen),
                ']' => Ok(Token::BracketClose),
                '(' => Ok(Token::ParenOpen),
                ')' => Ok(Token::ParenClose),
                '0'...'9' => {
                    let res = self.lex_with(|c| c.is_digit(10));
                    res.map(|end| Token::Number(&self.file[start..end]))
                }
                c if is_word_start_char(c) => {
                    let res = self.lex_with(is_word_char);
                    res.map(|end| {
                        let slice = &self.file[start..end];
                        match slice {
                            "module" => Token::Module,
                            "class" => Token::Class,
                            "data" => Token::Data,
                            "infix" => Token::Infix,
                            "infixl" => Token::Infixl,
                            "infixr" => Token::Infixr,
                            ident => Token::Ident(ident),
                        }
                    })
                }
                c if is_operator_char(c) => {
                    let res = self.lex_with(is_operator_char);
                    res.map(|end| {
                        let slice = &self.file[start..end];
                        match slice {
                            ":" => Token::Colon,
                            "=" => Token::Equals,
                            "|" => Token::Bar,
                            op => Token::Operator(op),
                        }
                    })
                }
                c => panic!("Got char {:?}, not handled", c),
            };

            if let Err(err) = res {
                panic!("Lex error: {}", err.message)
            }

            self.skip_whitespace();

            return res.ok();
        }
        // The internal iterator ended, and so also do we!
        None
    }
}

fn is_word_start_char(c: char) -> bool {
    match c {
        'a'...'z' | 'A'...'Z' | '_' => true,
        _ => false,
    }
}

fn is_word_char(c: char) -> bool {
    match c {
        'a'...'z' | 'A'...'Z' | '0'...'9' | '_' | '\'' => true,
        _ => false,
    }
}

fn is_operator_char(c: char) -> bool {
    "!$%^&*-=+|<>./?:~".contains(c)
}
