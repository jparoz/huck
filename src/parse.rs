use lex::{TokenType, Tokens};
use ast::{self, Statement};
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
                        Ident => {
                            let name = next_tok.text;
                            tokens.next();
                            let mut args: Vec<ast::Expr> = Vec::new();
                            while let Some(cur_tok) = tokens.eat_if(Ident) {
                            }

                            // let value: ast::Expr;

                            // module.statements.push(Statement::Definition {
                            //     name: name,
                            //     args: args,
                            //     value: value,
                            // });
                        }
                        Equals => {
                            // @Todo
                        }

                        // Type signature
                        Comma => {
                            // @Todo
                        }
                        Colon => {
                            // @Todo
                        }

                        _ => {
                            // @Error unexpected token @Todo
                        }
                    }
                } else {
                    // @Error eof @Todo
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
