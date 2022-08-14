use std::collections::HashSet;
use std::fmt::{self, Display};
use std::mem;

pub mod constraint;
pub mod error;
pub mod substitution;

pub use error::Error;
use error::Error as TypeError;
pub use substitution::{ApplySub, Substitution};

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum Type {
    Prim(Primitive),
    Var(TypeVar),
    Func(Box<Type>, Box<Type>),
    List(Box<Type>),
}

impl Type {
    pub fn free_vars(&self) -> TypeVarSet {
        match self {
            Type::Prim(_) => TypeVarSet::empty(),
            Type::Var(var) => TypeVarSet::single(*var),
            Type::Func(a, b) => a.free_vars().union(&b.free_vars()),
            Type::List(t) => t.free_vars(),
        }
    }

    pub fn generalize(&self, type_set: &TypeVarSet) -> TypeScheme {
        TypeScheme {
            vars: self.free_vars().difference(type_set),
            typ: self.clone(),
        }
    }

    /// Finds the most general unifier for two types.
    pub fn unify(self, other: Self) -> Result<Substitution, TypeError> {
        let mut sub = Substitution::empty();

        let mut pairs = vec![(self, other)];

        while let Some((a, b)) = pairs.pop() {
            match (a, b) {
                (t1, t2) if t1 == t2 => (),
                (Type::Var(var), t) | (t, Type::Var(var)) => {
                    if t.free_vars().contains(&var) {
                        // @CheckMe
                        return Err(TypeError::CouldNotUnifyRecursive(t.clone(), Type::Var(var)));
                    } else {
                        let s = Substitution::single(var.clone(), t.clone());
                        for (a2, b2) in pairs.iter_mut() {
                            a2.apply(&s);
                            b2.apply(&s);
                        }
                        sub = sub.then(s);
                    }
                }
                (Type::List(t1), Type::List(t2)) => pairs.push((*t1, *t2)),
                (Type::Func(a1, b1), Type::Func(a2, b2)) => {
                    pairs.push((*a1, *a2));
                    pairs.push((*b1, *b2));
                }
                (t1, t2) => return Err(TypeError::CouldNotUnify(t1, t2)),
            }
        }

        Ok(sub)
    }
}

impl ApplySub for Type {
    fn apply(&mut self, sub: &Substitution) {
        match self {
            Type::Var(var) => {
                if let Some(replacement) = sub.get(&var) {
                    *self = replacement.clone();
                }
            }
            Type::Func(a, b) => {
                a.apply(sub);
                b.apply(sub);
            }
            Type::List(list_t) => list_t.apply(sub),
            Type::Prim(_) => (),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(var) => write!(f, "{}", var),
            Type::Prim(p) => write!(f, "{:?}", p), // @Fixme: Display not Debug
            // @Todo: be smarter about when to include brackets
            Type::Func(a, b) => write!(f, "({} -> {})", a, b),
            Type::List(inner) => {
                write!(f, "[{}]", inner)
            }
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeScheme {
    pub vars: TypeVarSet,
    pub typ: Type,
}

impl TypeScheme {
    pub fn free_vars(&self) -> TypeVarSet {
        self.typ.free_vars().difference(&self.vars)
    }
}

impl ApplySub for TypeScheme {
    fn apply(&mut self, sub: &Substitution) {
        self.vars.apply(sub);
        self.typ.apply(sub);
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
pub struct TypeVarSet(HashSet<TypeVar>);

impl TypeVarSet {
    pub fn empty() -> TypeVarSet {
        TypeVarSet(HashSet::new())
    }

    pub fn single(elem: TypeVar) -> TypeVarSet {
        TypeVarSet(HashSet::from([elem]))
    }

    pub fn insert(&mut self, elem: TypeVar) -> bool {
        self.0.insert(elem)
    }

    pub fn union(&self, other: &TypeVarSet) -> TypeVarSet {
        self.0.union(&other.0).cloned().collect()
    }

    pub fn intersection(&self, other: &TypeVarSet) -> TypeVarSet {
        self.0.intersection(&other.0).cloned().collect()
    }

    pub fn difference(&self, other: &TypeVarSet) -> TypeVarSet {
        self.0.difference(&other.0).cloned().collect()
    }

    pub fn contains(&self, elem: &TypeVar) -> bool {
        self.0.contains(elem)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &TypeVar> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = TypeVar> {
        self.0.into_iter()
    }
}

impl ApplySub for TypeVarSet {
    fn apply(&mut self, sub: &Substitution) {
        let old_set = mem::replace(self, TypeVarSet::empty());
        for v in old_set.0.into_iter() {
            for (fr, to) in sub.iter() {
                if *fr == v {
                    // Type::free_vars just collects all the variables
                    // (i.e. all variables in a Type are free in that type)
                    *self = self.union(&to.free_vars());
                } else {
                    self.insert(v);
                }
            }
        }
    }
}

impl FromIterator<TypeVar> for TypeVarSet {
    fn from_iter<I: IntoIterator<Item = TypeVar>>(iter: I) -> Self {
        TypeVarSet(HashSet::from_iter(iter))
    }
}

impl Display for TypeVarSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ ")?;
        for v in self.0.iter() {
            write!(f, "{} ", v)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum Primitive {
    Int,
    Float,
    String,
}
