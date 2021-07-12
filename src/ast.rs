use std::collections::HashMap;
use std::fmt::{self, Display};

use crate::types::Type;

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

    pub fn apply_precs(&mut self, precs: &HashMap<Name, Precedence>) {
        // @Note: These defaults should one day be replaced with source code.

        let mut defaults: HashMap<Name, Precedence> = HashMap::with_capacity(13);
        defaults.insert(
            Name::Binop("*".to_string()),
            Precedence(Associativity::Left, 7),
        );
        defaults.insert(
            Name::Binop("/".to_string()),
            Precedence(Associativity::Left, 7),
        );
        defaults.insert(
            Name::Binop("+".to_string()),
            Precedence(Associativity::Left, 6),
        );
        defaults.insert(
            Name::Binop("-".to_string()),
            Precedence(Associativity::Left, 6),
        );
        defaults.insert(
            Name::Binop(",".to_string()),
            Precedence(Associativity::Right, 1),
        );
        defaults.insert(
            Name::Binop("::".to_string()),
            Precedence(Associativity::Right, 5),
        );
        defaults.insert(
            Name::Binop("$".to_string()),
            Precedence(Associativity::Right, 0),
        );
        defaults.insert(
            Name::Binop("==".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("!=".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("<".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("<=".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop(">".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop(">=".to_string()),
            Precedence(Associativity::None, 4),
        );

        for (name, prec) in precs {
            defaults.insert(name.clone(), *prec);
        }

        for (_name, defns) in &mut self.assignments {
            for (lhs, rhs) in defns.iter_mut() {
                lhs.apply_precs(&defaults);
                rhs.apply_precs(&defaults);
            }
        }
    }

    pub fn compute_mono_type_vars(&mut self) {
        for (_name, defns) in &mut self.assignments {
            for (_lhs, rhs) in defns.iter_mut() {
                rhs.m = Some(vec![]);
                rhs.compute_mono_type_vars(vec![]);
            }
        }
    }
}

pub type Assignment<'a> = (Lhs<'a>, Expr<'a>);

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

    fn apply_precs(&mut self, precs: &HashMap<Name, Precedence>) {
        match self {
            Lhs::Func { args, .. } => {
                for arg in args {
                    arg.apply_precs(precs);
                }
            }
            Lhs::Binop { a, op: _, b } => {
                a.apply_precs(precs);
                b.apply_precs(precs);
            }
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

impl<'a> Pattern<'a> {
    fn apply_precs(&mut self, precs: &HashMap<Name, Precedence>) {
        match self {
            Pattern::List(args) => {
                for arg in args {
                    arg.apply_precs(precs)
                }
            }
            Pattern::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply_precs(precs);
                if let Pattern::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply_precs(precs);
                    c.apply_precs(precs);

                    let Precedence(l_assoc, l_pri) = precs
                        .get(l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(r_assoc, r_pri) = precs
                        .get(r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri == r_pri
                        && *l_assoc == Associativity::None
                        && *r_assoc == Associativity::None
                    {
                        // @Todo @Errors: throw a proper parse error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l_pri >= r_pri && *l_assoc == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
            }
            Pattern::Destructure { args, .. } => {
                for arg in args {
                    arg.apply_precs(precs)
                }
            }
            _ => (),
        }
    }
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
pub struct Expr<'a> {
    pub node: ExprNode<'a>,
    pub m: Option<Vec<Type>>,
}

impl<'a> Expr<'a> {
    pub fn new(node: ExprNode) -> Expr {
        Expr { node, m: None }
    }

    pub fn compute_mono_type_vars(&mut self, from_parent: Vec<Type>) {
        match &mut self.node {
            ExprNode::Term(_) => (),
            ExprNode::App { func, argument } => {
                func.compute_mono_type_vars(from_parent.clone());
                argument.compute_mono_type_vars(from_parent.clone());
            }
            ExprNode::Binop {
                operator: _operator,
                lhs,
                rhs,
            } => {
                lhs.compute_mono_type_vars(from_parent.clone());
                rhs.compute_mono_type_vars(from_parent.clone());
            }
            ExprNode::Let {
                assignments,
                in_expr,
            } => {
                for (_name, defns) in assignments {
                    for (_lhs, rhs) in defns {
                        // @Note: _lhs contains poly type vars, not mono
                        rhs.compute_mono_type_vars(from_parent.clone());
                    }
                }
                in_expr.compute_mono_type_vars(from_parent.clone());
            } // @Todo: lambdas should do something like the following:
              // ExprNode::Lambda { vars, rhs } => {
              //     rhs.compute_mono_type_vars(from_parent
              //        .clone()
              //        .extend(vars.iter().map(|var| var.get_mono_types());
              // }
        }

        self.m = Some(from_parent);
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum ExprNode<'a> {
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
        assignments: HashMap<Name, Vec<Assignment<'a>>>,
        in_expr: Box<Expr<'a>>,
    },
}

impl<'a> Expr<'a> {
    fn apply_precs(&mut self, precs: &HashMap<Name, Precedence>) {
        match &mut self.node {
            ExprNode::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply_precs(precs);
                if let ExprNode::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut().node
                {
                    b.apply_precs(precs);
                    c.apply_precs(precs);

                    // @Note: this default is borrowed from Haskell; think about the right value
                    let Precedence(l_assoc, l_pri) = precs
                        .get(&l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(r_assoc, r_pri) = precs
                        .get(&r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri == r_pri
                        && *l_assoc == Associativity::None
                        && *r_assoc == Associativity::None
                    {
                        // @Todo @Errors: throw a proper parse error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l_pri >= r_pri && *l_assoc == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
                a.apply_precs(precs);
            }
            ExprNode::App { func, argument } => {
                func.apply_precs(precs);
                argument.apply_precs(precs);
            }
            ExprNode::Term(t) => match t {
                Term::List(v) => {
                    for e in v {
                        e.apply_precs(precs);
                    }
                }
                Term::Parens(e) => e.apply_precs(precs),
                _ => (),
            },
            ExprNode::Let {
                assignments,
                in_expr,
            } => {
                for (_name, defns) in assignments {
                    for (lhs, rhs) in defns.iter_mut() {
                        lhs.apply_precs(precs);
                        rhs.apply_precs(precs);
                    }
                }
                in_expr.apply_precs(precs);
            }
        }
    }
}

impl<'a> Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExprNode::*;
        match &self.node {
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
                assignments,
                in_expr,
            } => {
                write!(f, "let")?;
                for (_name, defns) in assignments {
                    for (lhs, rhs) in defns {
                        write!(f, " {} = {};", lhs, rhs)?;
                    }
                }
                write!(f, " in {}", in_expr)
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

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
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
