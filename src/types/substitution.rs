use std::collections::HashMap;
use std::fmt::{self, Display};

use super::{Type, TypeVar};

#[derive(Debug)]
pub struct Substitution(HashMap<TypeVar, Type>);

impl Substitution {
    pub fn empty() -> Self {
        Substitution(HashMap::new())
    }

    pub fn single(fr: TypeVar, to: Type) -> Self {
        Substitution(HashMap::from([(fr, to)]))
    }

    /// s1.then(s2) == s2 . s1
    pub fn then(self, mut next: Self) -> Self {
        for (fr, to) in self.0 {
            let mut new_to = to.clone();
            new_to.apply(&next);
            for (_, b) in next.0.iter_mut() {
                b.apply(&Substitution::single(fr, to.clone()));
            }

            // Assert because there should never be a swap already in the sub with the same var!
            debug_assert!(next.0.insert(fr, new_to).is_none());
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

impl Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Substitution:")?;
        for (fr, to) in self.iter() {
            writeln!(f, "    {} ↦ {}", fr, to)?;
        }
        Ok(())
    }
}

pub trait ApplySub {
    fn apply(&mut self, sub: &Substitution);
}
