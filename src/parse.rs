use std::str::CharIndices;
use std::iter::Peekable;
use std::ops::RangeInclusive;

use error::{Error, Location, Position};
use error::ErrorType::*;

macro_rules! error {
    ($toks:expr, $et:expr, $range:expr, $str:expr) => {
        Error {error_type: $et, location: $toks.location($range), message: $str.to_string()}
    };
    ($toks:expr, $et:expr, $range:expr, $str:expr, $($arg:tt)*) => {
        Error {error_type: $et, location: $toks.location($range), message: format!($str, $($arg)*)}
    };
}

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
    Float(f64),
    String(&'a str),
    Char(char),
}

pub fn parse<'compile, 'run>(filename: &'compile str,
                             file: &'compile str)
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
    iter: Peekable<CharIndices<'a>>,
}

impl<'a> Tokens<'a> {
    fn new(filename: &'a str, file: &'a str) -> Tokens<'a> {
        let iter = file.char_indices().peekable();
        let mut tokens = Tokens {
            filename: filename,
            file: file,
            iter: iter,
        };

        tokens.skip_whitespace();
        tokens
    }

    fn lex_while<F>(&mut self,
                    start: usize,
                    mut pred: F)
                    -> Result<RangeInclusive<usize>, Error<'a>>
        where F: FnMut(char) -> bool
    {
        let mut last = start;
        while let Some(&(i, c)) = self.iter.peek() {
            if pred(c) {
                self.iter.next();
            } else {
                return Ok(start...last);
            }
            last = i;
        }
        Err(error!(self, Lex, start...last, "Unexpected EOF"))
    }

    fn lex_while_until<F, G>(&mut self,
                             start: usize,
                             pred_while: F,
                             mut pred_until: G)
                             -> Result<RangeInclusive<usize>, Error<'a>>
        where F: FnMut(char) -> bool,
              G: FnMut(char) -> bool
    {
        let lexed = self.lex_while(start, pred_while);
        let success: bool;
        if let Some(&(_, c)) = self.iter.peek() {
            success = pred_until(c);
        } else {
            success = true;
        }

        if success {
            lexed
        } else {
            let end = lexed.unwrap_or(start...start).end;
            if let Some(&(_, c)) = self.iter.peek() {
                Err(error!(self, Lex, start...end, "Unexpected char {:?}", c))
            } else {
                Err(error!(self, Lex, start...end, "Unexpected char"))
            }
        }
    }

    fn lex_decimal(&mut self, start: usize) -> Result<RangeInclusive<usize>, Error<'a>> {
        let integer = self.lex_while(start, is_decimal_char)?;
        if let Some(&(dot_index, dot)) = self.iter.peek() {
            if dot != '.' {
                return Ok(integer);
            }

            self.iter.next();

            let floating = self.lex_while(start, is_decimal_char)?;
            if dot_index >= floating.end {
                return Err(error!(self,
                                  Lex,
                                  floating,
                                  "Missing fractional part of numeric literal"));
            } else {
                return Ok(floating);
            }
        } else {
            Err(error!(self, Lex, start...start, "Unexpected EOF"))
        }
    }

    /// Returns true if whitespace was skipped, otherwise returns false.
    // @Todo: handle comments here
    fn skip_whitespace(&mut self) -> bool {
        let skipped: bool;
        if let Some(&(start, c)) = self.iter.peek() {
            skipped = c.is_whitespace();
            let _ = self.lex_while(start, |c| c.is_whitespace());
        } else {
            skipped = false; // @Check: maybe true?
        }
        skipped
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

    fn extend_range(&mut self, mut range: RangeInclusive<usize>) -> RangeInclusive<usize> {
        self.iter.next();
        range.end += 1;
        range
    }

    fn location(&mut self, range: RangeInclusive<usize>) -> Location<'a> {
        let mut chars = self.file.chars();

        let mut start = Position::default();
        for _ in 0..range.start {
            if let Some(c) = chars.next() {
                if c == '\n' {
                    start.line += 1;
                    start.column = 1;
                } else {
                    start.column += 1;
                }
            }
        }

        let mut end = start;
        for _ in range.start..range.end {
            if let Some(c) = chars.next() {
                if c == '\n' {
                    end.line += 1;
                    end.column = 1;
                } else {
                    end.column += 1;
                }
            }
        }

        Location {
            filename: self.filename,
            start: start,
            end: end,
        }
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

            let res = match c {
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
                    if let Some(&(_, c2)) = self.iter.peek() {
                            match c2 {
                                'x' | 'X' => {
                                    self.iter.next();
                                    self.lex_while_until(start, is_hex_char, is_separator_char)
                                }
                                'b' | 'B' => {
                                    self.iter.next();
                                    self.lex_while_until(start, is_binary_char, is_separator_char)
                                }
                                _ => self.lex_decimal(start),
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
                c => Err(error!(self, Lex, start...start, "Char {:?} not yet handled!", c)),
            };

            match res {
                Ok(tok) => {
                    let skipped = self.skip_whitespace();
                    let next_is_sep =
                        skipped || self.peek_with(|opt| opt.map(is_separator_char)).unwrap_or(true);
                    if tok.requires_separator() && !next_is_sep {
                        panic!("{}",
                               error!(self, Lex, start...start, "Expected separating character"));
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

fn is_decimal_char(c: char) -> bool {
    c.is_digit(10) || c == '_'
}

fn is_hex_char(c: char) -> bool {
    c.is_digit(16) || c == '_'
}

fn is_binary_char(c: char) -> bool {
    c.is_digit(2) || c == '_'
}
