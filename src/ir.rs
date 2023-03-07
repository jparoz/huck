//! This module contains the structures needed for Huck's IR (internal representation).
//! The IR is generated from the fully resolved and typechecked modules,
//! and is used to generate code.
//! In between these steps, any optimisation is done,
//! effectively by functions of type `IR -> IR`.

use std::collections::BTreeMap;
use std::fmt::{self, Display};

use crate::ast;
use crate::name::{ModulePath, ResolvedName as Name};
use crate::types::{Type, TypeVarSet};
use crate::utils::leak;

/// We can reuse [`Numeral`] from the `ast` module.
pub use crate::ast::Numeral;

/// Represents all the code in a single Huck module.
#[derive(Debug, Clone)]
pub struct Module {
    pub path: ModulePath,
    pub definitions: BTreeMap<Name, Definition>,
    pub type_definitions: BTreeMap<Name, TypeDefinition>,
    pub exports: Vec<(&'static str, Expression)>,
}

/// Represents the complete definition of a single Huck function.
/// Note that there is no `arguments` field.
/// This is because the arguments from the `ast` are shifted into a lambda in the `rhs`.
#[derive(Debug, Clone)]
pub struct Definition {
    /// The name of the function.
    pub name: Name,

    /// The right-hand-side of the function.
    pub rhs: Expression,
}

/// Represents a Huck expression.
#[derive(Debug, Clone)]
pub enum Expression {
    /// A literal.
    Literal(Literal),

    /// A stream literal.
    Stream(Vec<Expression>),

    /// A tuple literal.
    Tuple(Vec<Expression>),

    /// An occurence of a name.
    /// This is a variable access,
    /// not some kind of reference type as in C or Rust.
    Reference(Name),

    /// Function application (including binops).
    App(Box<Expression>, Box<Expression>),

    /// Let expressions.
    Let {
        definitions: BTreeMap<Name, Definition>,
        expr: Box<Expression>,
    },

    /// Case expressions (including if-then-else).
    Case {
        expr: Box<Expression>,
        arms: Vec<(Pattern, Expression)>,
    },

    /// Lambda expressions.
    Lambda {
        args: Vec<Pattern>,
        expr: Box<Expression>,
    },

    /// Lua literals.
    Lua(&'static str),
}

/// Represents either a string, integer, float, or unit literal.
#[derive(Debug, Clone)]
pub enum Literal {
    String(&'static str),
    Numeral(Numeral),
    Unit,
}

impl Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::String(s) => f.write_str(s),
            Literal::Numeral(num) => write!(f, "{}", num),
            Literal::Unit => f.write_str("nil"),
        }
    }
}

/// Represents a pattern to be matched.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// Match on a literal.
    Literal(Literal),

    /// Match on a stream literal.
    Stream(Vec<Pattern>),

    /// Match on a tuple.
    Tuple(Vec<Pattern>),

    /// Bind a new name.
    Bind(Name),

    /// Don't bind anything.
    Underscore(&'static str),

    /// Destructuring (unary or otherwise).
    Constructor(Name, Vec<Pattern>),
}

impl Pattern {
    /// Returns all the names which are bound by the pattern.
    pub fn names_bound(&self) -> Vec<Name> {
        match self {
            Pattern::Bind(name) => vec![*name],

            Pattern::Constructor(_, pats) | Pattern::Tuple(pats) | Pattern::Stream(pats) => {
                pats.iter().flat_map(|pat| pat.names_bound()).collect()
            }

            Pattern::Literal(_) | Pattern::Underscore(_) => Vec::new(),
        }
    }
}

/// Represents the definition of a new type, and all its constructors.
#[derive(Debug, Clone)]
pub struct TypeDefinition {
    /// The name of the newly-defined type.
    pub name: Name,

    /// The set of type variables bound by the new type.
    pub vars: TypeVarSet<Name>,

    /// The newly-defined type.
    pub typ: Type,

    /// Each of the constructors for this type.
    pub constructors: BTreeMap<Name, Type>,
}

// Conversion from AST

impl From<ast::Module<Name, Type>> for Module {
    fn from(ast_module: ast::Module<Name, Type>) -> Self {
        let definitions = ast_module
            .definitions
            .into_iter()
            .map(|(name, defn)| (name, defn.into()))
            .collect();

        let type_definitions = ast_module
            .type_definitions
            .into_iter()
            .map(|(name, defn)| (name, defn.into()))
            .collect();

        let exports = ast_module
            .foreign_exports
            .into_iter()
            .map(|(lua_ident, ast_expr)| (lua_ident, ast_expr.into()))
            .collect();

        Module {
            path: ast_module.path,
            definitions,
            type_definitions,
            exports,
        }
    }
}

impl From<ast::Definition<Name, Type>> for Definition {
    fn from(definition: ast::Definition<Name, Type>) -> Self {
        // Assert that there is at least one assignment in the definition.
        // This is caught as a parse error.
        assert!(!definition.assignments.is_empty());

        // Assert that either it's a function (i.e. takes arguments),
        // or there's only one assignment (because a non-function can't have multiple values)
        assert!(definition.assignments[0].0.arg_count() > 0 || definition.assignments.len() == 1);

        Definition::from((*definition.assignments[0].0.name(), definition.assignments))
    }
}

impl From<(Name, Vec<ast::Assignment<Name>>)> for Definition {
    fn from((name, mut assignments): (Name, Vec<ast::Assignment<Name>>)) -> Self {
        // Assert that there is at least one assignment.
        // This is caught as a parse error for ast::Definitions,
        // and is impossible by construction for let bindings.
        assert!(!assignments.is_empty());

        // Here we convert multiple assignments into a Case expression in `rhs`,
        // but a single assignment is just transferred into `rhs` directly.
        let rhs = if assignments.len() == 1 {
            // Turn the assignment into a lambda
            assignments.pop().unwrap().into()
        } else {
            // This means there are 2 or more assignments.

            let num_args = assignments[0].0.args().len();

            // Do some sanity checks.
            #[cfg(debug_assertions)]
            {
                for assign in assignments.iter() {
                    // Assert that all the assignments have the same name.
                    // This is true by construction; see Module::from_statements
                    debug_assert_eq!(&name, assign.0.name());

                    // Assert that all the assignments have the same number of arguments.
                    // This is caught as a parse error.
                    debug_assert_eq!(num_args, assign.0.args().len());
                }
            }

            // For each argument in the assignments,
            // make a new lambda argument
            // which will immediately be scrutinised by the case expression.
            let names: Vec<Name> = (0..num_args)
                .map(|n| Name::local(leak!("_arg_{}", n)))
                .collect();
            let args = names.iter().cloned().map(Pattern::Bind).collect();
            let case_expr = Box::new(Expression::Tuple(
                names.into_iter().map(Expression::Reference).collect(),
            ));

            let arms = assignments
                .into_iter()
                .map(|(lhs, rhs)| {
                    let tuple = Pattern::Tuple(lhs.into());
                    let expr = rhs.into();
                    (tuple, expr)
                })
                .collect();

            Expression::Lambda {
                args,
                expr: Box::new(Expression::Case {
                    expr: case_expr,
                    arms,
                }),
            }
        };

        Definition { name, rhs }
    }
}

impl From<ast::Expr<Name>> for Expression {
    fn from(ast_expr: ast::Expr<Name>) -> Self {
        match ast_expr {
            ast::Expr::Term(term) => match term {
                ast::Term::Numeral(numeral) => Expression::Literal(Literal::Numeral(numeral)),
                ast::Term::String(s) => Expression::Literal(Literal::String(s)),
                ast::Term::Unit => Expression::Literal(Literal::Unit),

                ast::Term::Name(name) => Expression::Reference(name),

                ast::Term::Stream(es) => {
                    Expression::Stream(es.into_iter().map(Expression::from).collect())
                }
                ast::Term::Tuple(es) => {
                    Expression::Tuple(es.into_iter().map(Expression::from).collect())
                }

                ast::Term::TypedExpr(e, _) | ast::Term::Parens(e) => Expression::from(*e),
            },

            ast::Expr::App { func, argument } => Expression::App(
                Box::new(Expression::from(*func)),
                Box::new(Expression::from(*argument)),
            ),

            ast::Expr::Binop { operator, lhs, rhs } => {
                let partial = Expression::App(
                    Box::new(Expression::Reference(operator)),
                    Box::new(Expression::from(*lhs)),
                );
                Expression::App(Box::new(partial), Box::new(Expression::from(*rhs)))
            }

            ast::Expr::Let {
                definitions: ast_definitions,
                in_expr,
            } => {
                let definitions = ast_definitions
                    .into_iter()
                    .map(|defn| (defn.0, defn.into()))
                    .collect();

                let expr = Box::new(Expression::from(*in_expr));

                Expression::Let { definitions, expr }
            }

            ast::Expr::Case {
                expr: ast_expr,
                arms: ast_arms,
            } => {
                let expr = Box::new(Expression::from(*ast_expr));

                let arms = ast_arms
                    .into_iter()
                    .map(|(ast_pat, ast_expr)| (ast_pat.into(), ast_expr.into()))
                    .collect();

                Expression::Case { expr, arms }
            }

            ast::Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let expr = Box::new(Expression::from(*cond));

                let true_arm = (
                    Pattern::Constructor(Name::builtin("True"), Vec::new()),
                    Expression::from(*then_expr),
                );
                let false_arm = (
                    Pattern::Constructor(Name::builtin("False"), Vec::new()),
                    Expression::from(*else_expr),
                );

                Expression::Case {
                    expr,
                    arms: vec![true_arm, false_arm],
                }
            }

            ast::Expr::Lambda {
                args: ast_args,
                rhs: ast_expr,
            } => {
                let args = ast_args.into_iter().map(Pattern::from).collect();
                let expr = Box::new(Expression::from(*ast_expr));
                Expression::Lambda { args, expr }
            }

            ast::Expr::Lua(s) | ast::Expr::UnsafeLua(s) => Expression::Lua(s),
        }
    }
}

/// This turns an [`ast::Assignment`] into an [`ir::Expression`](Expression),
/// either a lambda expression (if there are one or more arguments),
/// or whatever the assignment's RHS is (if there are no arguments).
impl From<ast::Assignment<Name>> for Expression {
    fn from((lhs, rhs): ast::Assignment<Name>) -> Self {
        let args: Vec<Pattern> = lhs.into();
        let expr: Expression = rhs.into();

        if args.is_empty() {
            expr
        } else {
            Expression::Lambda {
                args,
                expr: Box::new(expr),
            }
        }
    }
}

impl From<ast::Pattern<Name>> for Pattern {
    fn from(ast_pat: ast::Pattern<Name>) -> Self {
        match ast_pat {
            ast::Pattern::Bind(name) => Pattern::Bind(name),
            ast::Pattern::Underscore(s) => Pattern::Underscore(s),

            ast::Pattern::Stream(pats) => {
                Pattern::Stream(pats.into_iter().map(Pattern::from).collect())
            }
            ast::Pattern::Tuple(pats) => {
                Pattern::Tuple(pats.into_iter().map(Pattern::from).collect())
            }

            ast::Pattern::Int(s) => Pattern::Literal(Literal::Numeral(Numeral::Int(s))),
            ast::Pattern::String(s) => Pattern::Literal(Literal::String(s)),
            ast::Pattern::Unit => Pattern::Literal(Literal::Unit),

            ast::Pattern::UnaryConstructor(name) => Pattern::Constructor(name, Vec::new()),
            ast::Pattern::Destructure { constructor, args } => {
                Pattern::Constructor(constructor, args.into_iter().map(Pattern::from).collect())
            }
            ast::Pattern::Binop { operator, lhs, rhs } => {
                Pattern::Constructor(operator, vec![Pattern::from(*lhs), Pattern::from(*rhs)])
            }
        }
    }
}

/// This turns an [`ast::Lhs`] into a `Vec<Pattern>`.
impl From<ast::Lhs<Name>> for Vec<Pattern> {
    fn from(lhs: ast::Lhs<Name>) -> Self {
        lhs.args().into_iter().map(Pattern::from).collect()
    }
}

impl From<ast::TypeDefinition<Name, Type>> for TypeDefinition {
    fn from(ast_type_defn: ast::TypeDefinition<Name, Type>) -> Self {
        let ast::TypeDefinition {
            name,
            vars,
            typ,
            constructors: ast_constructors,
        } = ast_type_defn;

        let constructors = ast_constructors
            .into_iter()
            .map(|(name, constr_defn)| (name, constr_defn.typ))
            .collect();

        TypeDefinition {
            name,
            vars,
            typ,
            constructors,
        }
    }
}
