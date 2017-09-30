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
    TypeSignature { names: Vec<&'a str>, typ: Type<'a> },
    Definition { name: &'a str, lam: Lambda<'a> },
}

#[derive(Debug)]
pub enum Expr<'a> {
    Lit(Literal),
    Var(&'a str),
    Lam(Lambda<'a>),
    App(Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Debug)]
pub struct Lambda<'a> {
    pub args: Vec<Pattern<'a>>,
    pub rhs: Box<Expr<'a>>,
}

#[derive(Debug)]
pub enum Type<'a> {
    Var(&'a str),
    Concrete(&'a str),
    App(Box<Type<'a>>, Box<Type<'a>>),
}

#[derive(Debug)]
pub enum Literal {
    Int(u64),
    Float(f64),
    String(String),
    Char(char),
} // @Todo: [1, 2, 3] !!!!

#[derive(Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    Lit(Literal),
    Match {
        constructor: &'a str,
        args: Vec<Pattern<'a>>,
    },
}
