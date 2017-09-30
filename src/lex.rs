use std::str::CharIndices;
use std::iter::Peekable;
use std::fmt;

use ast;
use error::{Error, Location, Position};
use error::ErrorType::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Token<'a> {
    pub typ: TokenType,
    pub text: &'a str,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenType {
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
    String,
    Char,
    Int,
    Float,
    Ident,
    Operator,
    Backtick,
    Hash,
}

impl TokenType {
    fn requires_separator(&self) -> bool {
        use self::TokenType::*;
        match *self {
            Ident | Int | Float | String | Char | Hash | Backtick | Module | Class | Type |
            Data | Precedence => true,
            _ => false,
        }
    }

    fn is_literal(&self) -> bool {
        use self::TokenType::*;
        match *self {
            String | Char | Int | Float => true,
            _ => false,
        }
    }

    pub fn is_pattern_start(&self) -> bool {
        use self::TokenType::*;
        match *self {
            String | Char | Int | Float | Ident | ParenOpen => true,
            _ => false,
        }
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TokenType::*;
        let name = match *self {
            Module => "keyword 'module'",
            Class => "keyword 'class'",
            Type => "keyword 'type'",
            Data => "keyword 'data'",
            Precedence => "keyword 'prec'",
            Semi => "';'",
            Colon => "':'",
            Equals => "'='",
            Bar => "'|'",
            Comma => "','",
            Backslash => "'\\'",
            BraceOpen => "'{'",
            BraceClose => "'}'",
            BracketOpen => "'['",
            BracketClose => "']'",
            ParenOpen => "'('",
            ParenClose => "')'",
            String => "string literal",
            Char => "char literal",
            Int => "integer literal",
            Float => "floating literal",
            Ident => "identifier",
            Operator => "operator",
            Backtick => "'`'",
            Hash => "'#ident'",
        };
        f.write_str(name)
    }
}

pub struct Tokens<'a> {
    pub filename: &'a str,
    file: &'a str,
    iter: Peekable<Lexer<'a>>,
    pub errors: Vec<Error<'a>>,
}

impl<'a> Tokens<'a> {
    pub fn new(filename: &'a str, file: &'a str) -> Tokens<'a> {
        Tokens {
            filename: filename,
            file: file,
            iter: Lexer::new(filename, file).peekable(),
            errors: Vec::new(),
        }
    }

    pub fn peek(&mut self) -> Option<Token<'a>> {
        self.iter.peek().map(|x| *x)
    }

    pub fn eat(&mut self) -> Option<Token<'a>> {
        self.iter.next()
    }

    pub fn eat_if(&mut self, typ: TokenType) -> Option<Token<'a>> {
        if let Some(tok) = self.peek() {
            if typ != tok.typ {
                return None;
            }
        } else {
            return None;
        }
        self.eat()
    }

    pub fn parse_expr(&mut self) -> Box<ast::Expr<'a>> {
        // @Todo
        unimplemented!()
    }

    pub fn parse_pattern(&mut self) -> Option<ast::Pattern<'a>> {
        use ast::Pattern::*;
        use lex::TokenType::*;
        if let Some(tok) = self.peek() {
            match tok.typ {
                Ident => {
                    self.next();
                    if tok.text.starts_with(char::is_uppercase) {
                        Some(Match {
                            constructor: tok.text,
                            args: Vec::new(),
                        })
                    } else {
                        Some(Bind(tok.text))
                    }
                }
                ParenOpen => {
                    self.next(); // self.expect(ParenOpen);
                    if let Some(tok) = self.next() {
                        match tok.typ {
                            Ident => {
                                if tok.text.starts_with(char::is_uppercase) {
                                    let cons = tok.text;
                                    let mut args = Vec::new();

                                    while let Some(cur_tok) = self.peek() {
                                        if cur_tok.typ.is_pattern_start() {
                                            if let Some(pat) = self.parse_pattern() {
                                                args.push(pat);
                                            } else {
                                                // @Error: couldn't parse pattern
                                                panic!("@Todo @Error patterns: {:?}", cur_tok);
                                            }
                                        } else {
                                            break;
                                        }
                                    }

                                    self.expect(ParenClose);

                                    Some(Match {
                                        constructor: cons,
                                        args: args,
                                    })
                                } else {
                                    // @Todo: clean up, probably skip until close parens or sommat
                                    None
                                }
                            }
                            _ => None,
                        }
                    } else {
                        // @Error: eof
                        panic!("EOFFF")
                    }
                }
                _ if tok.typ.is_literal() => {
                    let lit = self.parse_literal();
                    if lit.is_none() {
                        // @Error: probably impossible
                        panic!("probably impossible, failed to parse literal we know is a literal");
                    }
                    Some(Lit(lit.unwrap()))
                }
                _ => None,
            }
        } else {
            // @Error: eof
            panic!("EOFFF");
        }
    }

    fn parse_literal(&mut self) -> Option<ast::Literal> {
        use ast::Literal::*;
        use lex::TokenType;
        if let Some(tok) = self.next() {
            match tok.typ {
                TokenType::String => {
                    // @Todo: properly process. for now we just pass through as is, but we want to
                    // expand escapes, and maybe some other stuff that i can't think of right now.
                    let processed = tok.text.to_string();
                    Some(String(processed))
                }
                TokenType::Char => {
                    // @Todo: we probably want to manually process escapes and so forth.
                    // Also, this relies on the single-quotes being included in the tok.text, which
                    // I'm getting more iffy on as time goes by.
                    tok.text.parse().ok().map(Char)
                }
                TokenType::Int => {
                    // @Todo: proper parsing, similar to above
                    tok.text.parse().ok().map(Int)
                }
                TokenType::Float => {
                    // @Todo: proper parsing, similar to above
                    tok.text.parse().ok().map(Float)
                }
                _ => unreachable!(),
            }
        } else {
            // @Error: eof
            panic!("EOFFF");
        }
    }

    pub fn expect(&mut self, typ: TokenType) -> Option<Token<'a>> {
        if let Some(tok) = self.peek() {
            if typ != tok.typ {
                self.error(&tok, &tok, format!("Expected {}, but got {}", typ, tok.typ));
                return None;
            }
        } else {

            // @Hack-y
            let ix = self.file.len();
            let tok = Token {
                typ: TokenType::Ident,
                text: &self.file[ix - 1..ix],
            };

            self.error(&tok, &tok, format!("Expected {}, but got EOF", typ));
            return None;
        }
        self.eat()
    }

    pub fn error<'b>(&mut self, start_tok: &'b Token<'a>, end_tok: &'b Token<'a>, msg: String) {
        let start = pos_from_slice(self.file, start_tok.text);

        let ix = end_tok.text.len();
        // @Hack: see note on pos_from_slice
        let end = pos_from_slice(self.file, &end_tok.text[ix - 1..ix]);

        let loc = Location {
            filename: self.filename,
            start: start,
            end: end,
        };

        let e = Error {
            error_type: Parse,
            message: msg,
            location: loc,
        };

        self.errors.push(e);
    }
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

struct Lexer<'a> {
    filename: &'a str,
    file: &'a str,
    iter: Peekable<CharIndices<'a>>,
    start: usize,
    end: usize,
    errors: Vec<Error<'a>>,
}

impl<'a> Lexer<'a> {
    fn new(filename: &'a str, file: &'a str) -> Lexer<'a> {
        let iter = file.char_indices().peekable();
        let mut tokens = Lexer {
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

    fn reset(&mut self) {
        self.start = self.end + 1;
    }

    fn snip(&mut self, typ: TokenType) -> Token<'a> {
        let tok = Token {
            typ: typ,
            text: &self.file[self.start..self.end + 1],
        };
        self.reset();
        tok
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

    fn lex_while_until<F, G>(&mut self, pred_while: F, pred_until: G) -> Option<usize>
        where F: FnMut(char) -> bool,
              G: FnMut(char) -> bool
    {
        let lexed_len = self.lex_while(pred_while);

        let success = self.peek().map(pred_until).unwrap_or(false);

        if success {
            Some(lexed_len)
        } else {
            if let Some(c) = self.peek() {
                self.error(format!("Unexpected char {:?}", c));
            } else {
                self.error("Unexpected EOF".to_string());
            }
            None
        }
    }

    fn lex_ident(&mut self) -> usize {
        let start = self.end;
        let success = self.peek().map(is_word_start_char).unwrap_or(false);
        if success {
            self.eat();
            self.lex_while(is_word_char);
        }
        self.end - start
    }

    fn lex_decimal(&mut self) -> TokenType {
        let mut typ = TokenType::Int;

        self.lex_while(is_decimal_char);
        if let Some(dot) = self.peek() {
            if dot != '.' {
                return typ;
            }
            typ = TokenType::Float;

            self.eat();

            let lexed = self.lex_while(is_decimal_char);
            if lexed == 0 {
                self.error("Missing fractional part of numeric literal".to_string());
                return TokenType::Float;
            }
        }

        typ
    }

    /// Returns true if whitespace was skipped, otherwise returns false.
    // @Todo: handle comments here
    fn skip_whitespace(&mut self) -> bool {
        let skipped = self.peek().map(|c| c.is_whitespace()).unwrap_or(false);
        self.lex_while(|c| c.is_whitespace());
        self.reset();
        skipped
    }

    fn error(&mut self, msg: String) {
        let mut chars = self.file.chars();

        // @Cleanup: use Position::from_offset()
        // although this is bad for speed... worth?
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

impl<'a> Iterator for Lexer<'a> {
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

            use self::TokenType::*;
            let tok = match c {
                ';' => Some(self.snip(Semi)),
                '\\' => Some(self.snip(Backslash)),
                ',' => Some(self.snip(Comma)),
                '{' => Some(self.snip(BraceOpen)),
                '}' => Some(self.snip(BraceClose)),
                '[' => Some(self.snip(BracketOpen)),
                ']' => Some(self.snip(BracketClose)),
                '(' => Some(self.snip(ParenOpen)),
                ')' => Some(self.snip(ParenClose)),
                '@' => {
                    self.error("Illegal character '@' is currently reserved".to_string());
                    None
                }
                '#' => {
                    let lexed = self.lex_ident();
                    if lexed == 0 {
                        self.error("Missing identifier after hash".to_string());
                        None
                    } else {
                        Some(self.snip(Hash))
                    }
                }
                '"' => {
                    loop {
                        match self.eat() {
                            Some('"') => break,
                            Some('\\') => {
                                if let Some(c2) = self.eat() {
                                    if !is_escaped_char('"', c2) {
                                        self.error(format!("Illegal escaped character {:?}", c2));
                                    }
                                } else {
                                    self.error("Unexpected EOF in string literal".to_string());
                                }
                            }
                            Some(_) => (),
                            None => {
                                self.error("Unexpected EOF in string literal".to_string());
                                break;
                            }
                        }
                    }
                    Some(self.snip(String))
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
                    if let Some(c) = self.eat() {
                        if c == '\'' {
                            Some(self.snip(Char))
                        } else {
                            self.error(format!("Expected '\\'' to end character literal, but \
                                                found {:?}",
                                               c));
                            None
                        }
                    } else {
                        self.error("Unexpected EOF in character literal".to_string());
                        None
                    }
                }
                '`' => {
                    let lexed = self.lex_ident();
                    if lexed == 0 {
                        if let Some(c) = self.peek() {
                            self.error(format!("Expected identifier after backtick, but found \
                                                {:?}",
                                               c));
                        } else {
                            self.error("Expected identifier after backtick, but found EOF"
                                .to_string());
                        }
                        None
                    } else {
                        if let Some(c) = self.eat() {
                            if c == '`' {
                                Some(self.snip(Backtick))
                            } else {
                                self.error(format!("Expected '`' to end infix function \
                                                        call, but found {:?}",
                                                   c));
                                None
                            }
                        } else {
                            self.error("Unexpected EOF in infix function call".to_string());
                            None
                        }
                    }
                }
                '0'...'9' => {
                    let typ = if let Some(c2) = self.peek() {
                        match c2 {
                            'x' | 'X' => {
                                self.eat();
                                self.lex_while_until(is_hex_char, is_separator_char);
                                Int
                            }
                            'b' | 'B' => {
                                self.eat();
                                self.lex_while_until(is_binary_char, is_separator_char);
                                Int
                            }
                            _ => self.lex_decimal(),
                        }
                    } else {
                        Int
                    };
                    Some(self.snip(typ))
                }
                c if is_word_start_char(c) => {
                    self.lex_while(is_word_char);
                    let mut tok = self.snip(Ident);
                    tok.typ = match tok.text {
                        "module" => Module,
                        "class" => Class,
                        "type" => Type,
                        "data" => Data,
                        "prec" => Precedence,
                        _ => Ident,
                    };
                    Some(tok)
                }
                c if is_operator_char(c) => {
                    self.lex_while(is_operator_char);
                    let mut tok = self.snip(Operator);
                    tok.typ = match tok.text {
                        ":" => Colon,
                        "=" => Equals,
                        "|" => Bar,
                        _ => Operator,
                    };
                    Some(tok)
                }
                c if c.is_control() => {
                    self.error(format!("Found illegal control character {:?}", c));
                    self.reset();
                    None
                }
                c => {
                    self.error(format!("Unknown char {:?}", c));
                    self.reset();
                    None
                }
            };

            if let Some(tok) = tok.as_ref() {
                let skipped = self.skip_whitespace();
                let next_is_sep = skipped || self.peek().map(is_separator_char).unwrap_or(true);
                if tok.typ.requires_separator() && !next_is_sep {
                    self.error("Expected separating character".to_string());
                }
            }

            // @Fixme @Cleanup: Really we ought to propogate this up somehow.
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

// This is almost certainly the wrong thing to do. Not UTF8-clean, not neat. We should just store
// the start and end char indicies on Token, like we do in Charles! Silly Jesse.
// Also, it's just plain wrong! We need to give it the end of the second token, and this just gives
// the position of the start of the string. Bloody hell mate.
// But all this said, I'm still about to write the thing, because it'll be fun and whatever. Close
// enough for now.
// @Fixme @Hack
pub fn pos_from_slice(haystack: &str, needle: &str) -> Position {
    let base = haystack.as_ptr() as usize;
    let offset = needle.as_ptr() as usize - base;
    Position::from_offset(haystack, offset)
}
