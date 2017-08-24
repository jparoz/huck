// Lifetimes
// <'compile> is for values that will be erased in the final binary, or after typechecking and so
// forth. Probably will only be used in type-level stuff.
//
// <'run> is for values that may be needed at runtime, i.e. will be included in the final binary, or
// in memory when interpreted.

use std::str::Chars;
use std::iter::{Enumerate, Peekable};
use std::ops::Range;

use error::{Error, Location};
use error::ErrorType::*;

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
    Int(bool, u64), // Int(is_negative, value)
    Float(f64), // Is f64 the right move?
    String(&'a str),
    Char(char),
}

pub fn parse<'compile, 'run>(filename: &str,
                             file: &str)
                             -> Result<Ast<'compile, 'run>, Error<'compile>> {
    let mut iter = Tokens::new(filename, file);
    while let Some(tok) = iter.next() {
        // @Todo
        println!("{:?}", tok);
    }
    Ok(Ast::Var("hi")) // @Todo
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
    filename: &'a str,
    file: &'a str,
    iter: Peekable<Enumerate<Chars<'a>>>,
}

impl<'a> Tokens<'a> {
    fn new(filename: &'a str, file: &'a str) -> Tokens<'a> {
        let iter = file.chars().enumerate().peekable();
        let mut tokens = Tokens {
            filename: filename,
            file: file,
            iter: iter,
        };

        tokens.skip_whitespace();
        tokens
    }

    fn lex_while<F>(&mut self, start: usize, mut pred: F) -> Result<Range<usize>, Error<'a>>
        where F: FnMut(char) -> bool
    {
        let mut last = start;
        while let Some(&(i, c)) = self.iter.peek() {
            last = i;
            if pred(c) {
                self.iter.next();
            } else {
                return Ok(start..i);
            }
        }
        Err(Error {
            error_type: Lex,
            message: "Unexpected EOF".to_string(),
            location: self.get_location(start, last),
        })
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

    fn get_location(&mut self, start: usize, end: usize) -> Location<'a> {
        // @Todo
        Location::new(self.filename)
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

            let res: Result<Token, Error> = match c {
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
                    if let Some(&(end, c2)) = self.iter.peek() {
                            match c2 {
                                'x' | 'X' => Err(error!(self, Lex, start, end, "hexadecimal")),
                                'b' | 'B' => Err(error!(self, Lex, start, end, "binary")),
                                _ => {
                                    // @Todo: floats
                                    self.lex_while(start, |c| c.is_digit(10))
                                }
                            }
                        } else {
                            self.lex_while(start, |c| c.is_digit(10))
                        }
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
                c => {
                    Err(error!(self, Lex, start, start, "Char {:?} not yet handled!", c))
                    // Err(Error {
                    //     error_type: Lex,
                    //     message: format!("Char {:?} not yet handled!", c),
                    //     location: self.get_location(start, start),
                    // })
                }
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
