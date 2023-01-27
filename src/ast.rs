use std::collections::BTreeMap;
use std::fmt::{self, Display};

use crate::parse::precedence::Precedence;

/// A Module is a dictionary of Huck function definitions.
/// This is produced from a Vec<Statement>,
/// by using the parsed precedence rules to reshape the AST,
/// and collecting statements referring to the same function
/// into a single Definition struct for each function name.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Module<Name> {
    pub path: ModulePath,
    pub definitions: BTreeMap<Name, Definition<Name>>,

    pub type_definitions: BTreeMap<Name, TypeDefinition<Name>>,

    /// Note that all the members of this field can also be found
    /// in the values of the `type_definitions` field.
    pub constructors: BTreeMap<Name, Vec<TypeTerm<Name>>>,

    pub imports: BTreeMap<ModulePath, Vec<Name>>,
    pub foreign_imports: BTreeMap<&'static str, Vec<ForeignImportItem<Name>>>,
    pub foreign_exports: Vec<(&'static str, Expr<Name>)>,
}

impl<Name> Module<Name> {
    pub fn new(path: ModulePath) -> Self {
        Self {
            path,
            definitions: BTreeMap::new(),
            type_definitions: BTreeMap::new(),
            constructors: BTreeMap::new(),
            imports: BTreeMap::new(),
            foreign_imports: BTreeMap::new(),
            foreign_exports: Vec::new(),
        }
    }
}

/// A ModulePath is a path to a Huck module, as defined within that module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModulePath(pub &'static str);

impl Display for ModulePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A definition is the correct AST for a given Huck definition,
/// combined from any statements concerning the same Name.
/// This includes any case definitions (Assignments),
/// explicit type declarations,
/// or precedence declarations.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition<Name> {
    pub assignments: Vec<Assignment<Name>>,
    pub explicit_type: Option<TypeScheme<Name>>,
    pub precedence: Option<Precedence>,
}

impl<Name> Default for Definition<Name> {
    fn default() -> Self {
        Self {
            assignments: Vec::new(),
            explicit_type: None,
            precedence: None,
        }
    }
}

/// A Statement is a sum type for any of the top-level Huck constructs.
/// The order here is important! See [`resolve::resolve`](crate::resolve::resolve).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Statement<Name> {
    // @Note: imports MUST come before assignments.
    Import(ModulePath, Vec<Name>),
    QualifiedImport(ModulePath),
    /// Includes the quotation marks in the require string
    ForeignImport(&'static str, Vec<ForeignImportItem<Name>>),

    // @Note: Precedence MUST come before assignments.
    Precedence(Name, Precedence),

    AssignmentWithType(TypeScheme<Name>, Assignment<Name>),
    AssignmentWithoutType(Assignment<Name>),
    TypeAnnotation(Name, TypeScheme<Name>),
    TypeDefinition(TypeDefinition<Name>),

    /// The str is taken straight from the source
    /// and dumped into the output Lua
    /// without any sort of validation.
    /// See [`parse::statement`](crate::parse::statement).
    ForeignExport(&'static str, Expr<Name>),
}

pub type Assignment<Name> = (Lhs<Name>, Expr<Name>);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum UnresolvedName {
    Ident(&'static str),

    // @Todo @Cleanup: remove this (?)
    Binop(&'static str),

    Qualified(ModulePath, &'static str),
}

impl UnresolvedName {
    /// If it's an `Ident` or `Binop`, returns the inner `&'static str`.
    /// If it's a `Qualified` name, returns only the `ident` part (not the path!)
    pub fn ident(&self) -> &'static str {
        match self {
            UnresolvedName::Qualified(_, s)
            | UnresolvedName::Ident(s)
            | UnresolvedName::Binop(s) => s,
        }
    }
}

impl Display for UnresolvedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnresolvedName::Ident(s) | UnresolvedName::Binop(s) => write!(f, "{s}"),
            UnresolvedName::Qualified(path, s) => write!(f, "{path}.{s}"),
        }
    }
}

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

    pub fn names_bound(&self) -> Vec<Name> {
        self.args()
            .into_iter()
            .flat_map(|pat| pat.names_bound())
            .collect()
    }
}

impl<Name: Display> Display for Lhs<Name> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Func { name, args } => {
                // // @Nocommit: put this somewhere like impl Display for UnresolvedName
                // match name {
                //     UnresolvedName::Ident(s) => write!(f, "{s}")?,
                //     UnresolvedName::Binop(s) => write!(f, "({s})")?,
                //     UnresolvedName::Lambda => unreachable!(),
                //     // @Fixme: don't use Debug
                //     UnresolvedName::Qualified(source, s) => write!(f, "{source:?}.{s}")?,
                // }
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
pub struct TypeDefinition<Name> {
    pub name: Name,
    pub vars: Vec<&'static str>,
    pub constructors: Vec<ConstructorDefinition<Name>>,
}

pub type ConstructorDefinition<Name> = (Name, Vec<TypeTerm<Name>>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ForeignImportItem<Name>(pub ForeignName, pub Name, pub TypeScheme<Name>);
// {
//     // @Note: &'static str,
//     // because it's guaranteed to be an ident-legal name
//     // (i.e. parsed by parse::var)
//     SameName(&'static str, TypeScheme<Name>),
//     Rename(ForeignName, UnresolvedName, TypeScheme<Name>),
// }

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
