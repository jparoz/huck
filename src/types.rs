use std::collections::HashSet;
use std::fmt::{self, Display};

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Prim(Primitive),
    Var(TypeVar),
    Func(Box<Type>, Box<Type>),
    List(Box<Type>),
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

    pub fn free_vars(&self) -> HashSet<TypeVar> {
        match self {
            Type::Prim(_) => HashSet::new(),
            Type::Var(var) => HashSet::from([*var]),
            Type::Func(a, b) => a.free_vars().union(&b.free_vars()).cloned().collect(),
            Type::List(t) => t.free_vars(),
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
            }
        }
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct TypeScheme {
    vars: HashSet<TypeVar>,
    typ: Type,
}

impl TypeScheme {
    pub fn free_vars(&self) -> HashSet<TypeVar> {
        self.typ
            .free_vars()
            .difference(&self.vars)
            .cloned()
            .collect()
    }
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
