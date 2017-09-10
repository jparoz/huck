#[derive(Debug)]
pub struct Module<'a> {
    pub name: &'a str,
    pub statements: Vec<Statement<'a>>,
}

impl<'a> Module<'a> {
    pub fn new() -> Module<'a> {
        Module {
            name: "Main",
            statements: Vec::new(),
        }
    }
}

#[derive(Debug)]
pub enum Statement<'a> {
    TypeSignature { name: &'a str, typ: Type<'a> },
    Definition { name: &'a str, value: Expr<'a> },
}

#[derive(Debug)]
pub enum Expr<'a> {
    Lit(Lit<'a>),
    Var(&'a str),
    Lam(&'a Lambda<'a>),
    App(&'a Expr<'a>, &'a Expr<'a>),
}

#[derive(Debug)]
pub enum Type<'a> {
    Var(&'a str),
    Concrete(&'a str),
    App(&'a Type<'a>, &'a Type<'a>),
}

#[derive(Debug)]
pub enum Lit<'a> {
    Int(bool, u64), // Int(is_negative, value)
    Float(f64),
    String(&'a str),
    Char(char),
}

#[derive(Debug)]
pub struct Lambda<'a> {
    lhs: Pattern<'a>,
    rhs: &'a Expr<'a>,
}

#[derive(Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    Match {
        constructor: &'a str,
        arity: usize,
        args: Vec<&'a str>,
    },
}
