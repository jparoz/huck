// use std::collections::HashSet;
use std::fmt::{self, Display};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Prim(Primitive),
    Var(TypeVar),
    Func(Box<Type>, Box<Type>), // @Checkme: needs to be boxed???
    List(Box<Type>),
    // Scheme(Vec<TypeVar>, Box<Type>),
}

impl Type {
    /*
    pub fn free_vars(&self) -> Vec<TypeVar> {
        use Type::*;

        match self {
            Prim(_) => vec![],
            Var(var) => vec![*var],
            Func(a, b) => {
                let mut vars = a.free_vars();
                vars.append(&mut b.free_vars());
                vars
            }
            List(_) => todo!(),
        }
    }
    */
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(var) => write!(f, "{}", var),
            Type::Prim(p) => write!(f, "{:?}", p), // @Fixme: Display not Debug
            Type::Func(a, b) => write!(f, "{} -> {}", a, b),
            Type::List(inner) => {
                write!(f, "[{}]", inner)
            } // Type::Scheme(vars, typ) => {
              //     write!(f, "∀")?;
              //     for var in vars.iter() {
              //         write!(f, " {}", var)?;
              //     }
              //     write!(f, ". {}", typ)
              // }
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct TypeScheme {
    vars: Vec<TypeVar>,
    typ: Type,
}

impl TypeScheme {
    /*
    pub fn free_vars(&self) -> Vec<TypeVar> {
        self.typ
            .free_vars()
            .into_iter()
            .filter(|v| !self.vars.contains(v))
            .collect()
    }
    */
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "∀")?;
        for var in self.vars.iter() {
            write!(f, " {}", var)?;
        }
        write!(f, ". {}", self.typ)
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub struct TypeVar(pub usize);

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Primitive {
    Int,
    Float,
    String,
}
