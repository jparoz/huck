// Lifetimes
// <'compile> is for values that will be erased in the final binary, or after typechecking and so
// forth. Probably will only be used in type-level stuff.
//
// <'run> is for values that may be needed at runtime, i.e. will be included in the final binary, or
// in memory when interpreted.

extern crate num_bigint;
use self::num_bigint::BigInt;

use std::str::{FromStr, Chars};
use std::iter::{Enumerate, Peekable};
use std::fmt;
use std::ops::Range;

#[derive(Debug)]
pub enum Ast<'compile, 'run> {
    Lit(Lit<'run>),
    // TypeLit(Lit<'compile>), // or something like that
    Var(&'compile str),
}
// data Expr'
// = Lit Lit
// | Var Symbol
// | Lam Lambda
// | App Expr' Expr'

#[derive(Debug)]
pub enum Lit<'a> {
    Int(BigInt), // Is BigInt the right move?
    Float(f64), // Is f64 the right move?
    String(&'a str), /* @Fixme: ownership probably needs to be differently defined.
                      * See "Lifetimes" at top of file */
    Char(char),
}

impl<'compile, 'run> FromStr for Ast<'compile, 'run> {
    type Err = ParseError;
    fn from_str(file: &str) -> Result<Ast<'compile, 'run>, ParseError> {
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
    Type,
    Data,
    Precedence,
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
    String(&'a str),
    Number(&'a str),
    Ident(&'a str),
    Operator(&'a str),
}

impl<'a> Token<'a> {
    fn requires_separator(&self) -> bool {
        use self::Token::*;
        match *self {
            Ident(_) | Number(_) | String(_) | Module | Class | Type | Data | Precedence => true,
            _ => false,
        }
    }
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

    fn lex_while<F>(&mut self, start: usize, mut pred: F) -> Result<Range<usize>, LexError>
        where F: FnMut(char) -> bool
    {
        while let Some(&(i, c)) = self.iter.peek() {
            if pred(c) {
                self.iter.next();
            } else {
                return Ok(start..i);
            }
        }
        Err(LexError { message: "Unexpected EOF" })
    }

    /// Returns true if whitespace was skipped, otherwise returns false.
    // @Todo: handle comments here
    fn skip_whitespace(&mut self) -> bool {
        if let Some(&(start, _)) = self.iter.peek() {
            self.lex_while(start, |c| c.is_whitespace())
                .map(|range| range.start < range.end)
                .unwrap_or(false) // @Check: maybe true?
        } else {
            false
        }
    }

    fn peek_with<F, T>(&mut self, mut f: F) -> T
        where F: FnMut(Option<char>) -> T
    {
        let arg = if let Some(&(_, c)) = self.iter.peek() {
            Some(c)
        } else {
            None
        };
        f(arg)
    }

    fn extend_range(&mut self, mut range: Range<usize>) -> Range<usize> {
        self.iter.next();
        range.end += 1;
        range
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
                        let _ = self.lex_while(start, |c| c != '\n'); // Skip to newline
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
                '"' => {
                    // At this stage, we include opening and closing quotes, and we don't do
                    // escaping of any kind; a Token::String includes the whole string literal,
                    // as it is in the source.
                    self.lex_while(start, |c| c != '"' /* @Fixme */).map(|range| {
                        let range = self.extend_range(range);
                        Token::String(&self.file[range])
                    })
                }
                '0'...'9' => {
                    // @Todo
                    self.lex_while(start, |c| c.is_digit(10))
                        .map(|range| Token::Number(&self.file[range]))
                }
                c if is_word_start_char(c) => {
                    self.lex_while(start, is_word_char)
                        .map(|range| {
                            let slice = &self.file[range];
                            match slice {
                                "module" => Token::Module,
                                "class" => Token::Class,
                                "type" => Token::Type,
                                "data" => Token::Data,
                                "prec" => Token::Precedence,
                                ident => Token::Ident(ident),
                            }
                        })
                }
                c if is_operator_char(c) => {
                    self.lex_while(start, is_operator_char)
                        .map(|range| {
                            let slice = &self.file[range];
                            match slice {
                                ":" => Token::Colon,
                                "=" => Token::Equals,
                                "|" => Token::Bar,
                                op => Token::Operator(op),
                            }
                        })
                }
                c => panic!("Char {:?} not yet handled!", c),
            };

            match res {
                Ok(tok) => {
                    let skipped = self.skip_whitespace();
                    let next_is_sep =
                        skipped || self.peek_with(|opt| opt.map(is_separator_char)).unwrap_or(true);
                    if tok.requires_separator() && !next_is_sep {
                        panic!("Lex error: Expected separating character");
                    }
                    return Some(tok);
                }
                Err(err) => panic!("{}", err),
            }
        }
        // We ran out of chars, and therefore out of tokens.
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

fn is_separator_char(c: char) -> bool {
    is_operator_char(c) || c.is_whitespace() || ",;(){}[]".contains(c)
}
