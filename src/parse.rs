use lex::{Token, Tokens};
use ast;
use error::Error;

pub fn parse_module<'a>(filename: &'a str, file: &'a str) -> Result<ast::Module<'a>, Error<'a>> {
    let mut module = ast::Module::new();
    let mut tokens = Tokens::new(filename, file);

    if tokens.eat_if(Token::Module) {
        tokens.expect_ident(|s| module.name = s);
        tokens.expect(Token::Semi);
    }

    Ok(module)
}
