use lex::{TokenType, Tokens};
use ast::{self, Statement, Lambda, Pattern};
use error::Error;

pub fn parse_module<'a>(filename: &'a str,
                        file: &'a str)
                        -> Result<ast::Module<'a>, Vec<Error<'a>>> {
    use self::TokenType::*;

    let mut module = ast::Module::new();
    let mut tokens = Tokens::new(filename, file);

    if let Some(_) = tokens.eat_if(Module) {
        tokens.expect(Ident).map(|tok| module.name = tok.text);
        tokens.expect(Semi);
    }

    // Start of each statement is here
    while let Some(tok) = tokens.next() {
        match tok.typ {
            Ident => {
                if let Some(next_tok) = tokens.peek() {
                    match next_tok.typ {
                        // Definition
                        Ident | ParenOpen | Equals => {
                            let name = tok.text;
                            let mut args: Vec<Pattern<'a>> = Vec::new();

                            while let Some(cur_tok) = tokens.peek() {
                                if cur_tok.typ.is_pattern_start() {
                                    if let Some(pat) = tokens.parse_pattern() {
                                        args.push(pat);
                                    } else {
                                        // @Error: couldn't parse pattern
                                        panic!("@Todo @Error patterns: {:?}", cur_tok);
                                    }
                                } else {
                                    break;
                                }
                            }

                            tokens.expect(Equals);
                            let rhs = tokens.parse_expr();
                            tokens.expect(Semi);

                            module.statements.push(Statement::Definition {
                                name: name,
                                lam: Lambda {
                                    args: args,
                                    rhs: rhs,
                                },
                            });
                        }

                        // Type signature
                        Comma => {
                            // @Todo
                            unimplemented!("{:?}", next_tok);
                        }
                        Colon => {
                            // @Todo
                            unimplemented!("{:?}", next_tok);
                        }

                        _ => {
                            // @Error unexpected token @Todo
                            panic!("unexpected token {:?}", next_tok);
                        }
                    }
                } else {
                    // @Error eof @Todo
                    panic!("EOFFF");
                }
            }
            _ => unimplemented!("{:?}", tok),
        }
    }

    if tokens.errors.is_empty() {
        Ok(module)
    } else {
        Err(tokens.errors)
    }
}
