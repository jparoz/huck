use lex::Tokens;
use ast::Ast;
use error::Error;

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
