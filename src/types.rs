use std::collections::HashSet;
use std::fmt::{self, Display};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Prim(Primitive),
    Var(TypeVar),
    Func(Box<Type>, Box<Type>), // @Checkme: needs to be boxed???
}

impl Type {
    fn free_vars(&self) -> Vec<&TypeVar> {
        use Type::*;

        match self {
            Prim(_) => vec![],
            Var(var) => vec![var],
            Func(a, b) => {
                let mut vars = a.free_vars();
                vars.append(&mut b.free_vars());
                vars
            }
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(TypeVar(id)) => write!(f, "t{}", id),
            _ => unimplemented!(),
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct TypeScheme {
    vars: HashSet<TypeVar>,
    typ: Type,
}

impl TypeScheme {
    fn free_vars(&self) -> Vec<&TypeVar> {
        self.typ
            .free_vars()
            .into_iter()
            .filter(|v| !self.vars.contains(v))
            .collect()
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub struct TypeVar(pub usize);

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Primitive {
    Int,
    Float,
    String,
}
