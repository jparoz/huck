//! This module contains the structures needed for Huck's IR (internal representation).
//! The IR is generated from the fully resolved and typechecked modules,
//! and is used to generate code.
//! In between these steps, any optimisation is done,
//! effectively by functions of type `IR -> IR`.

use std::collections::BTreeMap;

use crate::name::ResolvedName as Name;
use crate::types::TypeScheme;

// We can reuse [`Numeral`].
pub use crate::ast::Numeral;

/// Represents all the code in a single Huck module.
#[derive(Debug)]
pub struct Module {
    definitions: BTreeMap<Name, Definition>,
}

/// Represents the complete definition of a single Huck function.
/// Note that there is no `arguments` field.
/// This is because the arguments from the `ast` are shifted into a lambda in the `rhs`.
#[derive(Debug)]
pub struct Definition {
    /// The name of the function.
    name: Name,

    /// The type scheme of the function.
    typ: TypeScheme,

    /// The right-hand-side of the function.
    rhs: Expression,
}

/// Represents a Huck expression.
#[derive(Debug)]
pub enum Expression {
    /// A literal.
    Literal(Literal),

    /// A list.
    List(Vec<Expression>),

    /// A tuple.
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
        // @Note: maybe should be Vec<Expression> instead?
        // Patterns can be pushed into expr as a Case
        args: Vec<Pattern>,
        expr: Box<Expression>,
    },

    /// Lua literals.
    Lua(&'static str),
}

/// Represents either a string, integer, float, or unit literal.
#[derive(Debug)]
pub enum Literal {
    String(&'static str),
    Numeral(Numeral),
    Unit,
}

/// Represents a pattern to be matched.
#[derive(Debug)]
pub enum Pattern {
    /// Match on a literal.
    Literal(Literal),

    /// Match on a list.
    List(Vec<Pattern>),

    /// Match on a tuple.
    Tuple(Vec<Pattern>),

    /// Bind a new name.
    Bind(Name),

    /// Don't bind anything.
    Underscore,

    /// Destructuring (unary or otherwise).
    Destructure(Name, Vec<Pattern>),
}
