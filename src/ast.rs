use std::collections::HashMap;
use std::fmt::{self, Display};

// @Todo: use these, or something similar
//
// #[derive(PartialEq, Debug)]
// pub struct Spanned<T> {
//     node: T,
//     span: Span,
// }
//
// #[derive(PartialEq, Debug)]
// pub struct Span {
//     // @Checkme: usize necessary? simple for now, but could probably be u32/u16 in some combination
//     start: usize,
//     len: usize,
// }

#[derive(Debug)]
pub struct Chunk<'a> {
    pub assignments: HashMap<Name, Vec<Assignment<'a>>>,
}

impl<'a> Chunk<'a> {
    pub fn new(assignments: HashMap<Name, Vec<Assignment<'a>>>) -> Chunk<'a> {
        Chunk { assignments }
    }
}

pub type Assignment<'a> = (Lhs<'a>, Expr<'a>);

pub type Definition<'file> = Vec<Assignment<'file>>;

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Name {
    Ident(String),
    Binop(String),
}

impl<'a> Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Name::Ident(s) | Name::Binop(s) => write!(f, "{}", s),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Lhs<'a> {
    Func {
        name: Name,
        args: Vec<Pattern<'a>>,
    },
    Binop {
        a: Pattern<'a>,
        op: Name,
        b: Pattern<'a>,
    },
}

impl<'a> Lhs<'a> {
    pub fn name(&self) -> &Name {
        match self {
            Lhs::Func { name, .. } => name,
            Lhs::Binop { op, .. } => op,
        }
    }
}

impl<'a> Display for Lhs<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Func { name, args } => {
                match name {
                    Name::Ident(s) => write!(f, "{}", s)?,
                    Name::Binop(s) => write!(f, "({})", s)?,
                }
                for arg in args.iter() {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            Lhs::Binop { a, op, b } => {
                write!(f, "{} {} {}", a, op, b)
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    List(Vec<Pattern<'a>>),
    Numeral(Numeral<'a>),
    String(&'a str),
    Binop {
        operator: Name,
        lhs: Box<Pattern<'a>>,
        rhs: Box<Pattern<'a>>,
    },
    UnaryConstructor(Name),
    Destructure {
        constructor: Name,
        args: Vec<Pattern<'a>>,
    },
}

impl<'a> Display for Pattern<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Pattern::*;
        match self {
            Bind(n) => write!(f, "{}", n),
            List(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<std::string::String>>()
                    .join(", ")
            ),
            Numeral(n) => write!(f, "{}", n),
            String(s) => write!(f, "{}", s),
            Binop { operator, lhs, rhs } => {
                write!(f, "({} {} {})", lhs, operator, rhs)
            }
            UnaryConstructor(name) => write!(f, "{}", name),
            Destructure { constructor, args } => {
                write!(f, "(")?;
                write!(f, "{}", constructor)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum Expr<'a> {
    Term(Term<'a>),
    App {
        func: Box<Expr<'a>>,
        argument: Box<Expr<'a>>,
    },
    Binop {
        operator: Name,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
    Let {
        definitions: HashMap<Name, Definition<'a>>,
        in_expr: Box<Expr<'a>>,
    },
    Lambda {
        args: Vec<Pattern<'a>>,
        rhs: Box<Expr<'a>>,
    },
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Expr::*;
        match self {
            App { func, argument } => {
                write!(f, "{}({}", DIM, RESET)?;
                write!(f, "{} {}", func, argument)?;
                write!(f, "{}){}", DIM, RESET)
            }
            Binop { operator, lhs, rhs } => {
                write!(f, "{}({}", DIM, RESET)?;
                write!(f, "{} {} {}", lhs, operator, rhs)?;
                write!(f, "{}){}", DIM, RESET)
            }
            Term(t) => write!(f, "{}", t),
            Let {
                definitions: assignments,
                in_expr,
            } => {
                write!(f, "let")?;
                for (_name, defns) in assignments {
                    for (lhs, rhs) in defns {
                        write!(f, " {} = {}", lhs, rhs)?;
                        write!(f, "{};{}", DIM, RESET)?;
                    }
                }
                write!(f, " in {}", in_expr)
            }
            Lambda { args: pats, rhs } => {
                write!(f, "\\")?;
                for pat in pats {
                    write!(f, "{} ", pat)?;
                }
                write!(f, "-> {}", rhs)
            }
        }
        // @Debug: below is nonsense

        // ?;
        // write!(f, "<<M: {:?}>>", self.m)
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum Term<'a> {
    Numeral(Numeral<'a>),
    String(&'a str),
    List(Vec<Expr<'a>>),
    Name(Name),
    Parens(Box<Expr<'a>>),
}

impl<'a> Display for Term<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            Numeral(n) => write!(f, "{}", n),
            String(s) => write!(f, "{}", s),
            List(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<std::string::String>>()
                    .join(", ")
            ),

            Name(n) => {
                write!(f, "{}", n)
            }
            Parens(e) => {
                write!(f, "({})", e)
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Numeral<'a> {
    Int(&'a str),
    Float(&'a str),
}

impl<'a> Display for Numeral<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Numeral::*;
        match self {
            Int(s) | Float(s) => write!(f, "{}", s),
        }
    }
}

// Terminal colour escape codes, used to denote implicit parens
const DIM: &str = "\x1b[34;1m";
const RESET: &str = "\x1b[0m";
