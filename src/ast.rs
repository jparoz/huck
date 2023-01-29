use std::collections::BTreeMap;
use std::fmt::{self, Display};

use crate::module::ModulePath;
use crate::precedence::Precedence;
use crate::types;

/// A definition is the correct AST for a given Huck definition,
/// combined from any statements concerning the same Name.
/// This includes any case definitions (Assignments),
/// explicit type declarations,
/// or precedence declarations.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition<Name, Ty> {
    pub assignments: Vec<Assignment<Name>>,
    pub explicit_type: Option<TypeScheme<Name>>,
    pub precedence: Option<Precedence>,
    pub typ: Ty,
}

impl<Name> Default for Definition<Name, ()> {
    fn default() -> Self {
        Self {
            assignments: Vec::new(),
            explicit_type: None,
            precedence: None,
            typ: (),
        }
    }
}

/// A Statement is a sum type for any of the top-level Huck constructs.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Statement<Name, Ty> {
    Import(ModulePath, Vec<Name>),
    // @Cleanup: combine with the above enum (Vec::length() == 0)
    QualifiedImport(ModulePath),
    /// Includes the quotation marks in the require string
    ForeignImport(&'static str, Vec<ForeignImportItem<Name>>),

    Precedence(Name, Precedence),

    AssignmentWithType(TypeScheme<Name>, Assignment<Name>),
    AssignmentWithoutType(Assignment<Name>),
    TypeAnnotation(Name, TypeScheme<Name>),
    TypeDefinition(TypeDefinition<Name, Ty>),

    /// The str is taken straight from the source
    /// and dumped into the output Lua
    /// without any sort of validation.
    // See parse::statement.
    ForeignExport(&'static str, Expr<Name>),
}

pub type Assignment<Name> = (Lhs<Name>, Expr<Name>);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Lhs<Name> {
    Func {
        name: Name,
        args: Vec<Pattern<Name>>,
    },
    Binop {
        a: Pattern<Name>,
        op: Name,
        b: Pattern<Name>,
    },
    Lambda {
        args: Vec<Pattern<Name>>,
    },
}

impl<Name> Lhs<Name> {
    pub fn name(&self) -> &Name {
        match self {
            Lhs::Func { name, .. } => name,
            Lhs::Binop { op, .. } => op,
            Lhs::Lambda { .. } => {
                unimplemented!();
            }
        }
    }
}

impl<Name: Copy> Lhs<Name> {
    pub fn arg_count(&self) -> usize {
        match self {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => args.len(),
            Lhs::Binop { .. } => 2,
        }
    }

    pub fn args(&self) -> Vec<Pattern<Name>> {
        match self {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => args.clone(),
            Lhs::Binop { a, b, .. } => vec![a.clone(), b.clone()],
        }
    }
}

impl<Name: Display> Display for Lhs<Name> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Func { name, args } => {
                write!(f, "{name}")?;
                for arg in args.iter() {
                    write!(f, " {arg}")?;
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Pattern<Name> {
    Bind(Name),
    List(Vec<Pattern<Name>>),
    Tuple(Vec<Pattern<Name>>),
    Numeral(Numeral),
    String(&'static str),
    Binop {
        operator: Name,
        lhs: Box<Pattern<Name>>,
        rhs: Box<Pattern<Name>>,
    },
    UnaryConstructor(Name),
    Unit,
    Destructure {
        constructor: Name,
        args: Vec<Pattern<Name>>,
    },
}

impl<Name: Copy> Pattern<Name> {
    /// Returns all the names which are bound by the pattern.
    pub fn names_bound(&self) -> Vec<Name> {
        match self {
            Pattern::Bind(name) => vec![*name],

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

impl<Name: Display> Display for Pattern<Name> {
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Expr<Name> {
    Term(Term<Name>),
    App {
        func: Box<Expr<Name>>,
        argument: Box<Expr<Name>>,
    },
    Binop {
        operator: Name,
        lhs: Box<Expr<Name>>,
        rhs: Box<Expr<Name>>,
    },
    Let {
        definitions: BTreeMap<Name, Vec<Assignment<Name>>>,
        in_expr: Box<Expr<Name>>,
    },
    // @Todo: test this
    If {
        cond: Box<Expr<Name>>,
        then_expr: Box<Expr<Name>>,
        else_expr: Box<Expr<Name>>,
    },
    // @Todo: test this
    Case {
        expr: Box<Expr<Name>>,
        arms: Vec<(Pattern<Name>, Expr<Name>)>,
    },
    Lambda {
        lhs: Lhs<Name>,
        rhs: Box<Expr<Name>>,
    },
    // @Todo: test this
    Lua(&'static str),
    // @Todo: test this
    UnsafeLua(&'static str),
}

impl<Name: Display + Copy> Display for Expr<Name> {
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
                for assignments in definitions.values() {
                    for (lhs, rhs) in assignments {
                        write!(f, " {} = {}", lhs, rhs)?;
                        write!(f, "{};{}", DIM, RESET)?;
                    }
                }
                write!(f, " in {}", in_expr)
            }

            If {
                cond,
                then_expr,
                else_expr,
            } => {
                write!(f, "if {} then {} else {}", cond, then_expr, else_expr)
            }
            Case { expr, arms } => {
                write!(f, "case {} of {{", expr)?;
                for (pat, e) in arms {
                    write!(f, "{} -> {};", pat, e)?;
                }
                write!(f, "}}")
            }

            Lambda { lhs, rhs } => {
                write!(f, "\\")?;
                for pat in lhs.args() {
                    write!(f, "{} ", pat)?;
                }
                write!(f, "-> {}", rhs)
            }

            Lua(lua_expr_str) => {
                write!(f, "lua {{ {} }}", lua_expr_str)
            }

            UnsafeLua(lua_expr_str) => {
                write!(f, "unsafe lua {{ {} }}", lua_expr_str)
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Term<Name> {
    Numeral(Numeral),
    String(&'static str),
    List(Vec<Expr<Name>>),
    Name(Name),
    Parens(Box<Expr<Name>>),
    Tuple(Vec<Expr<Name>>),
    Unit,
}

impl<Name: Display + Copy> Display for Term<Name> {
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
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct TypeScheme<Name> {
    pub vars: Vec<&'static str>,
    pub typ: TypeExpr<Name>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum TypeExpr<Name> {
    Term(TypeTerm<Name>),
    App(Box<TypeExpr<Name>>, Box<TypeExpr<Name>>),
    Arrow(Box<TypeExpr<Name>>, Box<TypeExpr<Name>>),
    // @Future @TypeBinops: type-level binops
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum TypeTerm<Name> {
    Concrete(Name),
    Var(&'static str),
    Parens(Box<TypeExpr<Name>>),
    List(Box<TypeExpr<Name>>),
    Tuple(Vec<TypeExpr<Name>>),
    Unit,
}

/// Parsed representation of a new type definition (e.g. `type Foo = Bar;`).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct TypeDefinition<Name, Ty> {
    pub name: Name,
    pub vars: types::TypeVarSet,
    pub constructors: BTreeMap<Name, ConstructorDefinition<Name, Ty>>,
    pub typ: Ty,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ConstructorDefinition<Name, Ty> {
    pub name: Name,
    pub args: Vec<TypeTerm<Name>>,
    pub typ: Ty,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ForeignImportItem<Name>(pub ForeignName, pub Name, pub TypeScheme<Name>);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct ForeignName(pub &'static str);

impl Display for ForeignName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum Numeral {
    Int(&'static str),
    Float(&'static str),
}

impl Display for Numeral {
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
