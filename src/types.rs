use std::collections::BTreeSet;
use std::fmt::{self, Display};

use crate::name::ResolvedName;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Type {
    Var(TypeVar<ResolvedName>),
    Concrete(ResolvedName),
    Primitive(Primitive),

    Tuple(Vec<Type>),

    /// The function type
    Arrow(Box<Type>, Box<Type>),

    /// Type application (e.g. `Foo a`)
    App(Box<Type>, Box<Type>),
    // @Future @TypeBinops (maybe as type application)
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(var) => write!(f, "{}", var),
            Type::Concrete(s) => write!(f, "{}", s),

            Type::Primitive(Primitive::Int) => write!(f, "Int"),
            Type::Primitive(Primitive::Float) => write!(f, "Float"),
            Type::Primitive(Primitive::String) => write!(f, "String"),
            Type::Primitive(Primitive::Bool) => write!(f, "Bool"),
            Type::Primitive(Primitive::Unit) => write!(f, "()"),
            Type::Primitive(Primitive::IO) => write!(f, "IO"),

            // @Future @CST: be smarter about when to include brackets
            Type::Arrow(a, b) => write!(f, "({} -> {})", a, b),

            Type::App(a, b) => write!(f, "({} {})", a, b),

            Type::Tuple(v) => write!(
                f,
                "({})",
                v.iter()
                    .map(|x| format!("{}", x))
                    .collect::<Vec<std::string::String>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Primitive {
    Int,
    Float,
    String,
    Bool,
    Unit,

    IO,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct TypeScheme {
    pub vars: TypeVarSet<ResolvedName>,
    pub typ: Type,
}

impl Display for TypeScheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.vars.is_empty() {
            write!(f, "∀")?;
            for var in self.vars.iter() {
                write!(f, " {}", var)?;
            }
            write!(f, ". ")?;
        }
        write!(f, "{}", self.typ)
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum TypeVar<Name: Ord + Copy> {
    Generated(usize),
    Explicit(Name),
}

impl<Name: Display + Ord + Copy> Display for TypeVar<Name> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeVar::Generated(id) => write!(f, "t{}", id),
            TypeVar::Explicit(s) => write!(f, "{}", s),
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct TypeVarSet<Name: Ord + Copy>(BTreeSet<TypeVar<Name>>);

impl<Name: Ord + Clone + Copy> TypeVarSet<Name> {
    pub fn empty() -> TypeVarSet<Name> {
        TypeVarSet(BTreeSet::new())
    }

    pub fn single(elem: TypeVar<Name>) -> TypeVarSet<Name> {
        TypeVarSet(BTreeSet::from([elem]))
    }

    pub fn insert(&mut self, elem: TypeVar<Name>) -> bool {
        self.0.insert(elem)
    }

    pub fn union(&self, other: &TypeVarSet<Name>) -> TypeVarSet<Name> {
        self.0.union(&other.0).cloned().collect()
    }

    pub fn intersection(&self, other: &TypeVarSet<Name>) -> TypeVarSet<Name> {
        self.0.intersection(&other.0).cloned().collect()
    }

    pub fn difference(&self, other: &TypeVarSet<Name>) -> TypeVarSet<Name> {
        self.0.difference(&other.0).cloned().collect()
    }

    pub fn contains(&self, elem: &TypeVar<Name>) -> bool {
        self.0.contains(elem)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &TypeVar<Name>> {
        self.0.iter()
    }

    pub fn remove(&mut self, k: &TypeVar<Name>) -> bool {
        self.0.remove(k)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl<Name: Ord + Copy> IntoIterator for TypeVarSet<Name> {
    type Item = TypeVar<Name>;
    type IntoIter = <BTreeSet<TypeVar<Name>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<Name: Ord + Copy> Extend<TypeVar<Name>> for TypeVarSet<Name> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = TypeVar<Name>>,
    {
        for tv in iter {
            self.insert(tv);
        }
    }
}

impl<Name: Ord + Copy> FromIterator<TypeVar<Name>> for TypeVarSet<Name> {
    fn from_iter<I: IntoIterator<Item = TypeVar<Name>>>(iter: I) -> Self {
        TypeVarSet(BTreeSet::from_iter(iter))
    }
}

impl<Name: Ord + Display + Copy> Display for TypeVarSet<Name> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        for v in self.0.iter() {
            write!(f, "{} ", v)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}
