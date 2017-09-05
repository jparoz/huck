use std::str::CharIndices;
use std::iter::Peekable;

use error::{Error, Location, Position};
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
    Char(&'a str),
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
    start: usize,
    end: usize,
    errors: Vec<Error<'a>>,
}

impl<'a> Tokens<'a> {
    fn new(filename: &'a str, file: &'a str) -> Tokens<'a> {
        let iter = file.char_indices().peekable();
        let mut tokens = Tokens {
            filename: filename,
            file: file,
            iter: iter,
            start: 0,
            end: 0,
            errors: Vec::new(),
        };

        if !tokens.skip_whitespace() {
            tokens.start = 0;
        }
        tokens
    }

    fn eat(&mut self) -> Option<char> {
        if let Some((i, c)) = self.iter.next() {
            self.end = i;
            Some(c)
        } else {
            None
        }
    }

    fn peek(&mut self) -> Option<char> {
        if let Some(&(_, c)) = self.iter.peek() {
            Some(c)
        } else {
            None
        }
    }

    fn eat_if_char(&mut self, c: char) -> Option<char> {
        if let Some(actual_c) = self.peek() {
            if c == actual_c {
                return self.eat();
            }
        }
        None
    }

    fn snip(&mut self) -> &'a str {
        let s = &self.file[self.start...self.end];
        self.end += 1;
        self.start = self.end;
        s
    }

    fn lex_while<F>(&mut self, mut pred: F) -> usize
        where F: FnMut(char) -> bool
    {
        let start = self.end;
        while let Some(c) = self.peek() {
            if pred(c) {
                self.eat();
            } else {
                break;
            }
        }
        self.end - start
    }

    fn lex_while_until<F, G>(&mut self, pred_while: F, mut pred_until: G) -> Option<usize>
        where F: FnMut(char) -> bool,
              G: FnMut(char) -> bool
    {
        let lexed_len = self.lex_while(pred_while);
        let success: bool;
        if let Some(c) = self.peek() {
            success = pred_until(c);
        } else {
            success = true; // Maybe false? or ask for default but that sucks
        }

        if success {
            Some(lexed_len)
        } else {
            if let Some(c) = self.peek() {
                self.error(format!("Unexpected char {:?}", c));
            } else {
                self.error("Unexpected char".to_string());
            }
            None
        }
    }

    fn lex_decimal(&mut self) {
        self.lex_while(is_decimal_char);
        if let Some(dot) = self.peek() {
            if dot != '.' {
                return;
            }

            self.eat();

            let lexed = self.lex_while(is_decimal_char);
            if lexed == 0 {
                self.error("Missing fractional part of numeric literal".to_string());
                return;
            }
        }
    }

    /// Returns true if whitespace was skipped, otherwise returns false.
    // @Todo: handle comments here
    fn skip_whitespace(&mut self) -> bool {
        let skipped: bool;
        if let Some(c) = self.peek() {
            skipped = c.is_whitespace();
            let _ = self.lex_while(|c| c.is_whitespace());
        } else {
            skipped = false; // @Check: maybe true?
        }
        self.snip();
        skipped
    }

    fn error(&mut self, msg: String) {
        let mut chars = self.file.chars();

        let mut start = Position::default();
        for _ in 0..self.start {
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
        for _ in self.start..self.end {
            if let Some(c) = chars.next() {
                if c == '\n' {
                    end.line += 1;
                    end.column = 1;
                } else {
                    end.column += 1;
                }
            }
        }

        let loc = Location {
            filename: self.filename,
            start: start,
            end: end,
        };

        let e = Error {
            error_type: Lex,
            location: loc,
            message: msg,
        };

        self.errors.push(e);
    }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(c) = self.eat() {
            // Check for (line) comments.
            if c == '-' {
                if let Some(c2) = self.peek() {
                    if c2 == '-' {
                        let _ = self.lex_while(|c| c != '\n'); // Skip to newline
                        self.skip_whitespace();
                        continue;
                    }
                }
            }

            let tok = match c {
                ';' => Some(Token::Semi),
                '\\' => Some(Token::Backslash),
                ',' => Some(Token::Comma),
                '{' => Some(Token::BraceOpen),
                '}' => Some(Token::BraceClose),
                '[' => Some(Token::BracketOpen),
                ']' => Some(Token::BracketClose),
                '(' => Some(Token::ParenOpen),
                ')' => Some(Token::ParenClose),
                '"' => {
                    while let Some(c) = self.eat() {
                        match c {
                            '"' => break,
                            '\\' => {
                                if let Some(c2) = self.eat() {
                                    if !is_escaped_char('"', c2) {
                                        self.error(format!("Illegal escaped character {:?}", c2));
                                    }
                                } else {
                                    self.error("Unexpected EOF in string literal".to_string());
                                }
                            }
                            _ => (),
                        }
                    }
                    Some(Token::String(self.snip()))
                }
                '\'' => {
                    match self.eat() {
                        Some('\\') => {
                            match self.eat() {
                                Some(c) => {
                                    match c {
                                        c if is_escaped_char('\'', c) => (),
                                        c => {
                                            self.error(format!("Unexpected character {:?} in \
                                                                character literal",
                                                               c))
                                        }
                                    }
                                }
                                None => {
                                    self.error("Unexpected EOF in character literal".to_string())
                                }
                            }
                        }
                        Some(_) => (),
                        None => self.error("Unexpected EOF in character literal".to_string()),
                    }
                    assert_eq!(self.eat(), Some('\''));
                    Some(Token::Char(self.snip()))
                }
                '0'...'9' => {
                    if let Some(c2) = self.peek() {
                        match c2 {
                            'x' | 'X' => {
                                self.eat();
                                self.lex_while_until(is_hex_char, is_separator_char);
                            }
                            'b' | 'B' => {
                                self.eat();
                                self.lex_while_until(is_binary_char, is_separator_char);
                            }
                            _ => self.lex_decimal(),
                        }
                    } else {
                        self.lex_while(|c| c.is_digit(10));
                    }
                    Some(Token::Number(self.snip()))
                }
                c if is_word_start_char(c) => {
                    self.lex_while(is_word_char);
                    match self.snip() {
                        "module" => Some(Token::Module),
                        "class" => Some(Token::Class),
                        "type" => Some(Token::Type),
                        "data" => Some(Token::Data),
                        "prec" => Some(Token::Precedence),
                        ident => Some(Token::Ident(ident)),
                    }
                }
                c if is_operator_char(c) => {
                    self.lex_while(is_operator_char);
                    match self.snip() {
                        ":" => Some(Token::Colon),
                        "=" => Some(Token::Equals),
                        "|" => Some(Token::Bar),
                        op => Some(Token::Operator(op)),
                    }
                }
                c => {
                    self.error(format!("Char {:?} not yet handled!", c));
                    self.eat();
                    self.snip();
                    None
                }
            };

            if let Some(tok) = tok.as_ref() {
                let skipped = self.skip_whitespace();
                let next_is_sep = skipped || self.peek().map(is_separator_char).unwrap_or(true);
                if tok.requires_separator() && !next_is_sep {
                    self.error("Expected separating character".to_string());
                }
            }

            if !self.errors.is_empty() {
                panic!("{}", self.errors[0]);
            }

            return tok;
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

fn is_escaped_char(quote: char, c: char) -> bool {
    "\\nrt".contains(c) || c == quote
}
