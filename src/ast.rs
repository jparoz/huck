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
    assignments: HashMap<Lhs<'a>, Expr<'a>>,
}

impl<'a> Chunk<'a> {
    pub fn new(assignments: HashMap<Lhs<'a>, Expr<'a>>) -> Chunk<'a> {
        Chunk { assignments }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
// @Todo: path/scope i.e. `Foo::foo 123` instead of just `foo 123`
pub struct Name<'a>(pub &'a str);

impl<'a> Display for Name<'a> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Lhs<'a> {
    pub name: Name<'a>,
    pub args: Vec<Pattern<'a>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Pattern<'a> {
    Name(Name<'a>),
    Match {
        constructor: Name<'a>,
        args: Vec<Pattern<'a>>,
    },
}

#[derive(PartialEq, Clone, Debug)]
pub enum Expr<'a> {
    Term(Term<'a>),
    App {
        func: Box<Expr<'a>>,
        argument: Box<Expr<'a>>,
    },
    Binop {
        operator: Name<'a>,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum Term<'a> {
    Numeral(&'a str),
    String(&'a str),
    List(Vec<Expr<'a>>),
    Name(Name<'a>),
    Parens(Box<Expr<'a>>),
}

impl<'a> Display for Term<'a> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}
