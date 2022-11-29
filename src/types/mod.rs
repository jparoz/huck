use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};
use std::mem;

use crate::ast;
use crate::scope::{Scope, TypedDefinition};

pub mod constraint;
pub mod error;
pub mod substitution;
pub use error::Error;

use constraint::{ConstraintGenerator, GenerateConstraints};
use error::Error as TypeError;
use substitution::{ApplySub, Substitution};

/// Typechecks the given Huck module.
pub fn typecheck(module: ast::Module) -> Result<Scope, TypeError> {
    let mut cg = ConstraintGenerator::new();

    let mut types = HashMap::new();

    // Generate constraints for each definition, while keeping track of inferred types
    for (name, defns) in module.definitions {
        let typ = defns.generate(&mut cg);
        types.insert(name, (typ, defns));
    }

    // @Todo: maybe move this into solve?
    // Add constraints to unify each assumption about the same name
    log::info!("Emitting constraints about assumptions:");
    let mut assumptions: Vec<(ast::Name, Vec<Type>)> = cg
        .assumptions
        .iter()
        .map(|(n, t)| (n.clone(), t.clone()))
        .collect();

    for (name, ref mut assumed_types) in assumptions.iter_mut() {
        // Add the type inferred at the definition (if it exists)
        if let Some(t) = types.get(&name) {
            assumed_types.push(t.0.clone());
        } else {
            // @Todo: Scope error
        }

        // @Todo: add the type declared by the user (if it exists)
    }

    for (_, assumed_types) in assumptions.into_iter() {
        // @Todo @Polymorphism @CheckMe:
        // Maybe this shouldn't be equality constraints,
        // but some kind of instance constraints.
        cg.equate_all(assumed_types);
    }

    // Solve the type constraints
    let soln = cg.solve()?;

    // @Cleanup: This should all be done in a more proper way
    // Apply the solution to the assumption set
    for typ in cg.assumptions.values_mut().flatten() {
        typ.apply(&soln);
    }

    log::trace!("After applying solution: {}", cg);

    let mut scope = Scope::new();

    let assumption_vars = cg.assumption_vars();
    for (name, (mut typ, assignments)) in types.into_iter() {
        typ.apply(&soln);

        let type_scheme = typ.generalize(&assumption_vars);
        log::info!("Inferred type for {} : {}", name, type_scheme);
        let defn = TypedDefinition::new(type_scheme, assignments);
        scope.definitions.insert(name, defn);
    }

    Ok(scope)
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum Type {
    Prim(Primitive),
    Var(TypeVar),
    Func(Box<Type>, Box<Type>),
    List(Box<Type>),
    Tuple(Vec<Type>),
}

impl Type {
    pub fn free_vars(&self) -> TypeVarSet {
        match self {
            Type::Prim(_) => TypeVarSet::empty(),
            Type::Var(var) => TypeVarSet::single(*var),
            Type::Func(a, b) => a.free_vars().union(&b.free_vars()),
            Type::List(t) => t.free_vars(),
            Type::Tuple(v) => v
                .iter()
                .fold(TypeVarSet::empty(), |a, t| a.union(&t.free_vars())),
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
            Type::Tuple(ref mut tuple_v) => tuple_v.iter_mut().for_each(|t| {
                t.apply(sub);
            }),
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
    Unit,
}
