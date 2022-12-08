use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};

use crate::parse::precedence::Precedence;
use crate::types::TypeScheme;

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

/// A definition is the correct AST for a given Huck definition,
/// combined from any statements concerning the same Name.
/// This includes any case definitions (Assignments),
/// type declarations,
/// or precedence declarations.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition<'file> {
    pub assignments: Vec<Assignment<'file>>,
    pub explicit_type: Option<TypeScheme>,
    pub precedence: Option<Precedence>,

    dependencies: Option<HashSet<Name>>,
}

impl<'file> Definition<'file> {
    pub fn dependencies(&mut self) -> &HashSet<Name> {
        self.dependencies.get_or_insert_with(|| {
            let mut deps = HashSet::new();

            for (_lhs, expr) in self.assignments.iter() {
                expr.dependencies(&mut deps);
            }

            deps
        })
    }
}

impl<'file> Default for Definition<'file> {
    fn default() -> Self {
        Self {
            assignments: Vec::new(),
            explicit_type: None,
            precedence: None,

            dependencies: None,
        }
    }
}

/// A Module is a dictionary of Huck function definitions.
/// This is produced from a Vec<Statement>,
/// by using the parsed precedence rules to reshape the AST,
/// and collecting statements referring to the same function
/// into a single Definition struct for each function name.
#[derive(Debug, PartialEq, Eq)]
pub struct Module<'file> {
    pub definitions: HashMap<Name, Definition<'file>>,
}

/// A Statement is a sum type for any of the top-level Huck constructs.
#[derive(Debug, PartialEq, Eq)]
pub enum Statement<'file> {
    Assignment(Assignment<'file>),
    TypeDeclaration, // @XXX @Todo
    Precedence(Name, Precedence),
}

// @Todo: change this to an enum with WithType and WithoutType variants
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
    Tuple(Vec<Pattern<'file>>),
    Numeral(Numeral<'file>),
    String(&'file str),
    Binop {
        operator: Name,
        lhs: Box<Pattern<'file>>,
        rhs: Box<Pattern<'file>>,
    },
    UnaryConstructor(Name),
    Unit,
    Destructure {
        constructor: Name,
        args: Vec<Pattern<'file>>,
    },
}

impl<'file> Pattern<'file> {
    /// Returns all the names which are bound by the pattern.
    fn names_bound(&self) -> Vec<Name> {
        match self {
            Pattern::Bind(s) => vec![Name::Ident(s.to_string())],

            Pattern::Destructure { args: pats, .. }
            | Pattern::Tuple(pats)
            | Pattern::List(pats) => pats.iter().flat_map(|pat| pat.names_bound()).collect(),

            Pattern::Binop { lhs, rhs, .. } => {
                let mut names = lhs.names_bound();
                names.extend(rhs.names_bound());
                names
            }

            Pattern::Numeral(_)
            | Pattern::String(_)
            | Pattern::UnaryConstructor(_)
            | Pattern::Unit => Vec::new(),
        }
    }
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
            Tuple(v) => write!(
                f,
                "({})",
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
            Unit => write!(f, "()"),
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
        definitions: HashMap<Name, Vec<Assignment<'file>>>,
        in_expr: Box<Expr<'file>>,
    },
    Lambda {
        lhs: Lhs<'file>,
        rhs: Box<Expr<'file>>,
    },
}

impl<'file> Expr<'file> {
    pub fn dependencies(&self, deps: &mut HashSet<Name>) {
        match self {
            Expr::Term(Term::List(es)) | Expr::Term(Term::Tuple(es)) => {
                es.iter().for_each(|e| e.dependencies(deps));
            }
            Expr::Term(Term::Name(name)) => {
                deps.insert(name.clone());
            }
            Expr::Term(Term::Parens(e)) => e.dependencies(deps),
            Expr::Term(_) => (),

            Expr::App { func, argument } => {
                func.dependencies(deps);
                argument.dependencies(deps);
            }

            Expr::Binop { operator, lhs, rhs } => {
                deps.insert(operator.clone());
                lhs.dependencies(deps);
                rhs.dependencies(deps);
            }

            Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut sub_deps = HashSet::new();

                in_expr.dependencies(&mut sub_deps);

                // Remove variables bound in the definitions
                for name in definitions.keys() {
                    // @Note: if .remove() returns false,
                    // the definition isn't referenced in the in_expr;
                    // therefore it's dead code.
                    // Maybe emit a warning about this.
                    sub_deps.remove(name);
                }

                deps.extend(sub_deps);
            }

            Expr::Lambda { lhs, rhs } => {
                debug_assert!(matches!(lhs, Lhs::Lambda { .. }));

                let args = match lhs {
                    Lhs::Lambda { args } => args,
                    _ => unreachable!(),
                };

                let mut sub_deps = HashSet::new();

                rhs.dependencies(&mut sub_deps);

                // Remove variables bound in the lambda LHS
                for pat in args.iter() {
                    for name in pat.names_bound() {
                        // @Note: if .remove() returns false,
                        // the definition isn't referenced in the in_expr;
                        // therefore it's dead code.
                        // Maybe emit a warning about this.
                        sub_deps.remove(&name);
                    }
                }

                deps.extend(sub_deps);
            }
        }
    }
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
                definitions,
                in_expr,
            } => {
                write!(f, "let")?;
                for (_name, assignments) in definitions {
                    for (lhs, rhs) in assignments {
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
    Tuple(Vec<Expr<'file>>),
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
            Tuple(v) => write!(
                f,
                "({})",
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
