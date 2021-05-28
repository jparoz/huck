use std::collections::HashMap;
use std::fmt::{self, Display};

// @Todo: use these
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
    assignments: HashMap<Name<'a>, Expr<'a>>,
}

impl<'a> Chunk<'a> {
    pub fn new(assignments: HashMap<Name<'a>, Expr<'a>>) -> Chunk<'a> {
        Chunk { assignments }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Name<'a> {
    pub name: &'a str,
    // @Todo: path/scope i.e. `Foo::foo 123` instead of just `foo 123`
    // pub path: Vec<&'a str>,
}

impl<'a> Display for Name<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Debug)]
pub enum Expr<'a> {
    Term(Term<'a>),
    App {
        func: Box<Expr<'a>>,
        argument: Box<Expr<'a>>,
    },
    Unop {
        operator: &'a str,
        operand: Box<Expr<'a>>,
    },
    Binop {
        operator: &'a str,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Debug)]
pub enum Term<'a> {
    Numeral(&'a str),
    String(&'a str),
    Name(Name<'a>),
    Parens(Box<Expr<'a>>),
}

impl<'a> Display for Term<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Debug)]
pub struct LineEnd(pub usize);
