use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};

use crate::parse::precedence::Precedence;

/// A Module is a dictionary of Huck function definitions.
/// This is produced from a Vec<Statement>,
/// by using the parsed precedence rules to reshape the AST,
/// and collecting statements referring to the same function
/// into a single Definition struct for each function name.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Module {
    pub path: ModulePath,
    pub definitions: BTreeMap<Name, Definition>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
    pub imports: BTreeMap<ModulePath, Vec<Name>>,
    pub foreign_imports: BTreeMap<&'static str, Vec<(ForeignName, Name, TypeScheme)>>,
    pub foreign_exports: Vec<(&'static str, Expr)>,
}

/// A ModulePath is a path to a Huck module, as defined within that module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModulePath(pub &'static str);

// @Cleanup @Todo @DeleteMe
impl Default for ModulePath {
    fn default() -> Self {
        ModulePath("Main")
    }
}

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
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct Definition {
    pub assignments: Vec<Assignment>,
    pub explicit_type: Option<TypeScheme>,
    pub precedence: Option<Precedence>,

    dependencies: Option<BTreeSet<Name>>,
}

impl Definition {
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

/// A Statement is a sum type for any of the top-level Huck constructs.
/// The order here is important! See [`resolve::resolve`](crate::resolve::resolve).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Statement {
    // @Note: imports MUST come before assignments.
    Import(ModulePath, Vec<Name>),
    QualifiedImport(ModulePath),
    /// Includes the quotation marks in the require string
    ForeignImport(&'static str, Vec<ForeignImportItem>),

    // @Note: Precedence MUST come before assignments.
    Precedence(Name, Precedence),

    AssignmentWithType(TypeScheme, Assignment),
    AssignmentWithoutType(Assignment),
    TypeAnnotation(Name, TypeScheme),
    TypeDefinition(TypeDefinition),

    /// The str is taken straight from the source
    /// and dumped into the output Lua
    /// without any sort of validation.
    /// See [`parse::statement`](crate::parse::statement).
    ForeignExport(&'static str, Expr),
}

pub type Assignment = (Lhs, Expr);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Name {
    Ident(&'static str),
    Binop(&'static str),
    Lambda,

    Qualified(ModulePath, &'static str),
}

impl Name {
    pub fn as_str(&self) -> &'static str {
        match self {
            Name::Ident(s) | Name::Binop(s) => s,
            Name::Lambda => "<lambda>",
            Name::Qualified(source, s) => {
                todo!("as_str can't be implemented for qualified names @Fixme: {source:?}.{s}")
            }
        }
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Lhs {
    Func { name: Name, args: Vec<Pattern> },
    Binop { a: Pattern, op: Name, b: Pattern },
    Lambda { args: Vec<Pattern> },
}

impl Lhs {
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

    pub fn args(&self) -> Vec<Pattern> {
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

impl Display for Lhs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lhs::Func { name, args } => {
                match name {
                    Name::Ident(s) => write!(f, "{s}")?,
                    Name::Binop(s) => write!(f, "({s})")?,
                    Name::Lambda => unreachable!(),
                    // @Fixme: don't use Debug
                    Name::Qualified(source, s) => write!(f, "{source:?}.{s}")?,
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Pattern {
    Bind(&'static str),
    List(Vec<Pattern>),
    Tuple(Vec<Pattern>),
    Numeral(Numeral),
    String(&'static str),
    Binop {
        operator: Name,
        lhs: Box<Pattern>,
        rhs: Box<Pattern>,
    },
    UnaryConstructor(Name),
    Unit,
    Destructure {
        constructor: Name,
        args: Vec<Pattern>,
    },
}

impl Pattern {
    /// Returns all the names which are bound by the pattern.
    pub fn names_bound(&self) -> Vec<Name> {
        match self {
            Pattern::Bind(s) => vec![Name::Ident(s)],

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

impl Display for Pattern {
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
pub enum Expr {
    Term(Term),
    App {
        func: Box<Expr>,
        argument: Box<Expr>,
    },
    Binop {
        operator: Name,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Let {
        definitions: BTreeMap<Name, Vec<Assignment>>,
        in_expr: Box<Expr>,
    },
    // @Todo: test this
    If {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    // @Todo: test this
    Case {
        expr: Box<Expr>,
        arms: Vec<(Pattern, Expr)>,
    },
    Lambda {
        lhs: Lhs,
        rhs: Box<Expr>,
    },
    // @Todo: test this
    Lua(&'static str),
    // @Todo: test this
    UnsafeLua(&'static str),
}

impl Expr {
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

            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.dependencies(deps);
                then_expr.dependencies(deps);
                else_expr.dependencies(deps);
            }

            Expr::Case { expr, arms } => {
                // Always include the dependencies of the scrutinised expression.
                expr.dependencies(deps);

                for (arm_pat, arm_expr) in arms {
                    let mut sub_deps = BTreeSet::new();
                    arm_expr.dependencies(&mut sub_deps);

                    // Remove variables bound in the arm pattern
                    for name in arm_pat.names_bound() {
                        sub_deps.remove(&name);
                    }

                    deps.extend(sub_deps);
                }
            }

            Expr::Lambda { lhs, rhs } => {
                assert!(matches!(lhs, Lhs::Lambda { .. }));

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

            // Lua inline expressions can't depend on Huck values,
            // or at least we can't (i.e. won't) check inside Lua for dependencies;
            // so we do nothing.
            Expr::Lua(_) | Expr::UnsafeLua(_) => (),
        }
    }
}

impl Display for Expr {
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
pub enum Term {
    Numeral(Numeral),
    String(&'static str),
    List(Vec<Expr>),
    Name(Name),
    Parens(Box<Expr>),
    Tuple(Vec<Expr>),
    Unit,
}

impl Display for Term {
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
pub struct TypeScheme {
    pub vars: Vec<&'static str>, // @Checkme: &str, or maybe Name?
    pub typ: TypeExpr,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum TypeExpr {
    Term(TypeTerm),
    App(Box<TypeExpr>, Box<TypeExpr>),
    Arrow(Box<TypeExpr>, Box<TypeExpr>),
    // @Future @TypeBinops: type-level binops
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum TypeTerm {
    Concrete(&'static str),
    Var(&'static str),
    Parens(Box<TypeExpr>),
    List(Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    Unit,
}

/// Parsed representation of a new type definition (e.g. `type Foo = Bar;`).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct TypeDefinition {
    pub name: Name,
    pub vars: Vec<&'static str>,
    pub constructors: Vec<ConstructorDefinition>,
}

pub type ConstructorDefinition = (Name, Vec<TypeTerm>);

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ForeignImportItem {
    SameName(Name, TypeScheme),
    Rename(ForeignName, Name, TypeScheme),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct ForeignName(pub &'static str);

impl Display for ForeignName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A ForeignPath describes how to access a Lua function from Huck.
/// It is a sum of a string to be given to `require` in Lua,
/// and the table index to be used on the table returned from `require`,
/// according to common Lua module practices.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct ForeignPath {
    pub require: &'static str,
    pub name: ForeignName,
}

impl Display for ForeignPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, r#"require({})["{}"]"#, self.require, self.name)
    }
}

/// An ImportSource describes where to find a name, whether it's a Huck or foreign import.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ImportSource {
    /// From a Huck module
    Module(ModulePath),
    /// From a foreign (Lua) module
    Foreign(ForeignPath),
    /// From e.g. a let binding
    Local,
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
