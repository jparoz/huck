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
    pub assignments: HashMap<Name<'a>, Vec<Assignment<'a>>>,
}

impl<'a> Chunk<'a> {
    pub fn new(assignments: HashMap<Name<'a>, Vec<Assignment<'a>>>) -> Chunk<'a> {
        Chunk { assignments }
    }

    pub fn apply_precs(&mut self, precs: &HashMap<Name<'a>, Precedence>) {
        // @Note: These defaults should one day be replaced with source code.

        let mut defaults = HashMap::with_capacity(4);
        defaults.insert(Name::binop("*"), Precedence(Associativity::Left, 7));
        defaults.insert(Name::binop("/"), Precedence(Associativity::Left, 7));
        defaults.insert(Name::binop("+"), Precedence(Associativity::Left, 6));
        defaults.insert(Name::binop("-"), Precedence(Associativity::Left, 6));

        defaults.extend(precs);

        for (_name, defns) in &mut self.assignments {
            for (_lhs, rhs) in defns.iter_mut() {
                rhs.apply_precs(&defaults);
            }
        }
    }
}

type Assignment<'a> = (Lhs<'a>, Expr<'a>);

#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
// @Todo: path/scope i.e. `Foo::foo 123` instead of just `foo 123`
pub struct Name<'a> {
    pub name: &'a str,
    pub is_binop: bool,
    // pub path: &'a str,
}

impl<'a> Name<'a> {
    pub fn new(s: &str) -> Name {
        Name {
            name: s,
            is_binop: false,
        }
    }

    pub fn binop(s: &str) -> Name {
        Name {
            name: s,
            is_binop: true,
        }
    }
}

impl<'a> Display for Name<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct Lhs<'a> {
    pub name: Name<'a>,
    pub args: Vec<Pattern<'a>>,
}

impl<'a> Display for Lhs<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?;
        for arg in self.args.iter() {
            write!(f, " {}", arg)?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Pattern<'a> {
    Bind(&'a str),
    List(Vec<Pattern<'a>>),
    Tuple(Box<Pattern<'a>>, Box<Pattern<'a>>),
    String(&'a str),
    Destructure {
        constructor: Name<'a>,
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
            Tuple(a, b) => write!(f, "({}, {})", a, b),
            String(s) => write!(f, "{}", s),
            Destructure { constructor, args } => {
                if constructor.is_binop {
                    assert!(args.len() == 2);
                    write!(f, "({} {} {})", args[0], constructor, args[1])
                } else {
                    write!(f, "({}", constructor)?;
                    for arg in args {
                        write!(f, " {}", arg)?;
                    }
                    write!(f, ")")
                }
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
        operator: Name<'a>,
        lhs: Box<Expr<'a>>,
        rhs: Box<Expr<'a>>,
    },
}

impl<'a> Expr<'a> {
    pub fn apply_precs(&mut self, precs: &HashMap<Name<'a>, Precedence>) {
        match self {
            Expr::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                a.apply_precs(precs);
                rhs.apply_precs(precs);
                if let Expr::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply_precs(precs);
                    c.apply_precs(precs);

                    // @Note: this default is borrowed from Haskell; think about the right value
                    let Precedence(l_assoc, l_pri) = precs
                        .get(&l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(_r_assoc, r_pri) = precs
                        .get(&r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri >= r_pri && *l_assoc == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
            }
            Expr::App { func, argument } => {
                func.apply_precs(precs);
                argument.apply_precs(precs);
            }
            Expr::Term(t) => match t {
                Term::List(v) => {
                    for e in v {
                        e.apply_precs(precs);
                    }
                }
                Term::Tuple(a, b) => {
                    a.apply_precs(precs);
                    b.apply_precs(precs);
                }
                Term::Parens(e) => e.apply_precs(precs),
                _ => (),
            },
        }
    }
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
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum Term<'a> {
    Numeral(&'a str),
    String(&'a str),
    List(Vec<Expr<'a>>),
    Tuple(Box<Expr<'a>>, Box<Expr<'a>>),
    Name(Name<'a>),
    Parens(Box<Expr<'a>>),
}

impl<'a> Display for Term<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            Numeral(n) => {
                write!(f, "{}", n)
            }
            String(s) => {
                write!(f, "{}", s)
            }
            List(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<std::string::String>>()
                    .join(", ")
            ),

            Tuple(a, b) => {
                write!(f, "({}, {})", a, b)
            }
            Name(n) => {
                write!(f, "{}", n)
            }
            Parens(e) => {
                write!(f, "({})", e)
            }
        }
    }
}

#[derive(PartialEq, Clone, Copy, Debug)]
pub struct Precedence(pub Associativity, pub u8);

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Associativity {
    Left,
    Right,
    None,
}

// Terminal colour escape codes, used to denote implicit parens
const DIM: &str = "\x1b[34;1m";
const RESET: &str = "\x1b[0m";
