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

pub type Definition<'file> = Vec<Assignment<'file>>;

#[derive(Debug, PartialEq, Eq)]
pub struct Chunk<'file> {
    pub definitions: HashMap<Name, Definition<'file>>,
}

impl<'file> Chunk<'file> {
    pub fn new(definitions: HashMap<Name, Definition<'file>>) -> Chunk<'file> {
        Chunk { definitions }
    }
}

pub type Assignment<'file> = (Lhs<'file>, Expr<'file>);

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Debug)]
pub enum Name {
    Ident(String),
    Binop(String),
    Lambda,
}

impl Name {
    pub fn as_str(&self) -> &str {
        match self {
            Name::Ident(s) | Name::Binop(s) => &s,
            Name::Lambda => unreachable!(),
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Lhs<'file> {
    Func {
        name: Name,
        args: Vec<Pattern<'file>>,
    },
    Binop {
        a: Pattern<'file>,
        op: Name,
        b: Pattern<'file>,
    },
    Lambda {
        args: Vec<Pattern<'file>>,
    },
}

impl<'file> Lhs<'file> {
    pub fn name(&self) -> &Name {
        match self {
            Lhs::Func { name, .. } => name,
            Lhs::Binop { op, .. } => op,
            Lhs::Lambda { .. } => &Name::Lambda,
        }
    }

    pub fn arg_count(&self) -> usize {
        match self {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => args.len(),
            Lhs::Binop { .. } => 2,
        }
    }

    pub fn args(&self) -> Vec<Pattern<'file>> {
        match self {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => args.clone(),
            Lhs::Binop { a, b, .. } => vec![a.clone(), b.clone()],
        }
    }
}

impl<'file> Display for Lhs<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Func { name, args } => {
                match name {
                    Name::Ident(s) => write!(f, "{}", s)?,
                    Name::Binop(s) => write!(f, "({})", s)?,
                    Name::Lambda => unreachable!(),
                }
                for arg in args.iter() {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
            Lhs::Binop { a, op, b } => {
                write!(f, "{} {} {}", a, op, b)
            }
            Lhs::Lambda { args } => {
                for arg in args.iter() {
                    write!(f, " {}", arg)?;
                }
                Ok(())
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Pattern<'file> {
    Bind(&'file str),
    List(Vec<Pattern<'file>>),
    Numeral(Numeral<'file>),
    String(&'file str),
    Binop {
        operator: Name,
        lhs: Box<Pattern<'file>>,
        rhs: Box<Pattern<'file>>,
    },
    UnaryConstructor(Name),
    Destructure {
        constructor: Name,
        args: Vec<Pattern<'file>>,
    },
}

impl<'file> Display for Pattern<'file> {
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Expr<'file> {
    Term(Term<'file>),
    App {
        func: Box<Expr<'file>>,
        argument: Box<Expr<'file>>,
    },
    Binop {
        operator: Name,
        lhs: Box<Expr<'file>>,
        rhs: Box<Expr<'file>>,
    },
    Let {
        definitions: HashMap<Name, Definition<'file>>,
        in_expr: Box<Expr<'file>>,
    },
    Lambda {
        lhs: Lhs<'file>,
        rhs: Box<Expr<'file>>,
    },
}

impl<'file> Display for Expr<'file> {
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
            Lambda { lhs, rhs } => {
                write!(f, "\\")?;
                for pat in lhs.args() {
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Term<'file> {
    Numeral(Numeral<'file>),
    String(&'file str),
    List(Vec<Expr<'file>>),
    Name(Name),
    Parens(Box<Expr<'file>>),
    Unit,
}

impl<'file> Display for Term<'file> {
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
            Unit => write!(f, "()"),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Numeral<'file> {
    Int(&'file str),
    Float(&'file str),
}

impl<'file> Display for Numeral<'file> {
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
