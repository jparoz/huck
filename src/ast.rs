use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};

use crate::parse::precedence::Precedence;

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
    pub assignments: Vec<(Lhs<'file>, Expr<'file>)>,
    pub explicit_type: Option<TypeScheme<'file>>,
    pub precedence: Option<Precedence>,

    dependencies: Option<BTreeSet<Name>>,
}

impl<'file> Definition<'file> {
    pub fn dependencies(&mut self) -> &BTreeSet<Name> {
        self.dependencies.get_or_insert_with(|| {
            let mut deps = BTreeSet::new();

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
    pub definitions: BTreeMap<Name, Definition<'file>>,
    pub type_declarations: Vec<TypeDeclaration<'file>>,
}

/// A Statement is a sum type for any of the top-level Huck constructs.
#[derive(Debug, PartialEq, Eq)]
pub enum Statement<'file> {
    Assignment(Assignment<'file>),
    TypeAnnotation(Name, TypeScheme<'file>),
    Precedence(Name, Precedence),
    TypeDeclaration(TypeDeclaration<'file>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Assignment<'file> {
    WithType(TypeScheme<'file>, Lhs<'file>, Expr<'file>),
    WithoutType(Lhs<'file>, Expr<'file>),
}

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
        // @Todo @Checkme: should this be Assignment instead of the raw tuple?
        definitions: BTreeMap<Name, Vec<(Lhs<'file>, Expr<'file>)>>,
        in_expr: Box<Expr<'file>>,
    },
    Lambda {
        lhs: Lhs<'file>,
        rhs: Box<Expr<'file>>,
    },
}

impl<'file> Expr<'file> {
    pub fn dependencies(&self, deps: &mut BTreeSet<Name>) {
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
                let mut sub_deps = BTreeSet::new();

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

                let mut sub_deps = BTreeSet::new();

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

/// This represents an explicitly-written type scheme, i.e. the RHS of a `:`.
/// e.g. in `id : forall a. a;` the TypeScheme represents `forall a. a`.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct TypeScheme<'file> {
    pub vars: Vec<&'file str>, // @Checkme: &str, or maybe Name?
    pub typ: TypeExpr<'file>,
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum TypeExpr<'file> {
    Term(TypeTerm<'file>),
    App(Box<TypeExpr<'file>>, Box<TypeExpr<'file>>),

    // @Todo: rename either this or Type::Func to match each other
    Arrow(Box<TypeExpr<'file>>, Box<TypeExpr<'file>>),
    // @Todo: type-level binops
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum TypeTerm<'file> {
    Concrete(&'file str),
    Var(&'file str),
    Parens(Box<TypeExpr<'file>>),
    List(Box<TypeExpr<'file>>),
    Tuple(Vec<TypeExpr<'file>>),
    Unit,
}

/// Name of the type,
/// Vec of the introduced type variable names,
/// Vec of the constructors and arguments.
#[derive(Debug, PartialEq, Eq)]
pub struct TypeDeclaration<'file>(
    pub Name,
    pub Vec<&'file str>,
    pub Vec<ConstructorDefinition<'file>>,
);

pub type ConstructorDefinition<'file> = (Name, Vec<TypeTerm<'file>>);

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
