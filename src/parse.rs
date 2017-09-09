use lex::{Token, Tokens};
use ast;
use error::Error;

pub fn parse_module<'a>(filename: &'a str, file: &'a str) -> Result<ast::Module<'a>, Error<'a>> {
    let mut module = ast::Module::new();
    let tokens: Vec<Token> = Tokens::new(filename, file).collect();
    let mut cursor = 0;

    if tokens[cursor] == Token::Module {
        cursor += 1;
        if let Token::Ident(s) = tokens[cursor] {
            module.name = s;

            if tokens[cursor] != Token::Semi {
                module.error(format!("Expected semicolon, but found {:?}", tokens[cursor]));
            }
        } else {
            // @Error
        }
    }

    // loop {
    //     match tokens[cursor] {
    //         // @Todo
    //     }
    // }

    // for tok in tokens {
    // }

    println!("tokens[cursor]: {:?}", tokens[cursor]);
    Ok(module)
}
