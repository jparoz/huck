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
    pub fn get_mono_type_vars(&self) -> Vec<TypeVar> {
        match self {
            Type::Var(var) => vec![*var],
            Type::Prim(_) => vec![],
            Type::List(typ) => typ.get_mono_type_vars(),
            Type::Func(a, b) => {
                let mut res = a.get_mono_type_vars();
                res.extend(b.get_mono_type_vars());
                res
            }
        }
    }
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
