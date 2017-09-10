use lex::{TokenType, Tokens};
use ast;
use error::Error;

pub fn parse_module<'a>(filename: &'a str,
                        file: &'a str)
                        -> Result<ast::Module<'a>, Vec<Error<'a>>> {
    let mut module = ast::Module::new();
    let mut tokens = Tokens::new(filename, file);

    if tokens.eat_if(TokenType::Module) {
        tokens.expect(TokenType::Ident).map(|tok| module.name = tok.text);
        tokens.expect(TokenType::Semi);
    }

    Ok(module)
}
