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
