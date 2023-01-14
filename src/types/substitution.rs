use std::collections::BTreeMap;
use std::fmt::{self, Debug};

use super::TypeVarSet;
use super::{constraint::Constraint, Type, TypeScheme, TypeVar};

pub struct Substitution(BTreeMap<TypeVar, Type>);

impl Substitution {
    pub fn empty() -> Self {
        Substitution(BTreeMap::new())
    }

    pub fn single(fr: TypeVar, to: Type) -> Self {
        Substitution(BTreeMap::from([(fr, to)]))
    }

    /// s1.then(s2) == s2 . s1
    pub fn then(self, mut next: Self) -> Self {
        for (fr, to) in self.0 {
            let mut new_to = to.clone();
            new_to.apply(&next);
            for (_, b) in next.0.iter_mut() {
                b.apply(&Substitution::single(fr.clone(), to.clone()));
            }

            // Assert because there should never be a swap already in the sub with the same var!
            assert!(next.0.insert(fr, new_to).is_none());
        }
        next
    }

    pub fn iter(&self) -> impl Iterator<Item = (&TypeVar, &Type)> {
        self.0.iter()
    }

    pub fn get(&self, k: &TypeVar) -> Option<&Type> {
        self.0.get(k)
    }
}

impl FromIterator<(TypeVar, Type)> for Substitution {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (TypeVar, Type)>,
    {
        Substitution(BTreeMap::from_iter(iter))
    }
}

impl Debug for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;

        let mut iter = self.iter().peekable();
        while let Some((fr, to)) = iter.next() {
            write!(f, "{} ↦ {}", fr, to)?;
            if !iter.peek().is_none() {
                write!(f, ", ")?;
            }
        }

        write!(f, ")")
    }
}

pub trait ApplySub {
    fn apply(&mut self, sub: &Substitution);
}

impl ApplySub for Constraint {
    fn apply(&mut self, sub: &Substitution) {
        match self {
            Constraint::Equality(t1, t2) => {
                t1.apply(sub);
                t2.apply(sub);
            }
            Constraint::ImplicitInstance(t1, t2, m) => {
                t1.apply(sub);
                t2.apply(sub);
                m.apply(sub);
            }
            Constraint::ExplicitInstance(t, sigma) => {
                t.apply(sub);
                sigma.apply(sub);
            }
        }
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
            Type::Arrow(a, b) | Type::App(a, b) => {
                a.apply(sub);
                b.apply(sub);
            }
            Type::List(list_t) => list_t.apply(sub),
            Type::Tuple(ref mut tuple_v) => tuple_v.iter_mut().for_each(|t| {
                t.apply(sub);
            }),

            Type::Concrete(_) => (),
        }
    }
}

impl ApplySub for TypeScheme {
    fn apply(&mut self, sub: &Substitution) {
        self.vars.apply(sub);
        self.typ.apply(sub);
    }
}

impl ApplySub for TypeVarSet {
    fn apply(&mut self, sub: &Substitution) {
        let start_set = self.clone();
        for var in start_set {
            if let Some(typ) = sub.get(&var) {
                self.remove(&var);
                self.extend(typ.free_vars().into_iter())
            }
        }
    }
}
