use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};
use std::mem;

use crate::ast;
use crate::scope::{Scope, TypedDefinition};

// @Cleanup: do these all need to be pub?
pub mod constraint;
pub mod error;
pub mod substitution;
pub use error::Error;

#[cfg(test)]
mod test;

use constraint::ConstraintGenerator;
use error::Error as TypeError;
use substitution::{ApplySub, Substitution};

/// Typechecks the given Huck module.
pub fn typecheck(module: ast::Module) -> Result<Scope, TypeError> {
    let mut cg = ConstraintGenerator::new();

    let mut type_definitions = BTreeMap::new();

    // Generate constraints for each definition, while keeping track of inferred types
    for (name, defn) in module.definitions {
        let typ = cg.generate_definition(&defn);
        log::trace!("Initial inferred type for {}: {}", name, typ);

        // @Note: guaranteed to be None,
        // because we're iterating over a BTreeMap.
        debug_assert!(cg.types.insert(name, (typ, defn)).is_none());
    }

    // Generate constraints for each type definition
    for (_name, ast_type_defn) in module.type_definitions {
        let type_defn = cg.convert_ast_type_definition(&ast_type_defn);

        for (constr_name, constr_type) in type_defn.constructors.clone() {
            cg.constructors
                .insert(constr_name.clone(), constr_type.clone());
        }

        // @Note: guaranteed to be None,
        // because we're iterating over a BTreeMap.
        debug_assert!(type_definitions
            .insert(type_defn.name.clone(), type_defn)
            .is_none());
    }

    // Polymorphically bind all top-level variables.
    cg.bind_all_top_level();
    debug_assert!(cg.assumptions.is_empty());

    // Solve the type constraints
    let soln = cg.solve()?;

    log::trace!(
        "ConstraintGenerator after solving type constraints: {:?}",
        cg
    );

    let mut scope = Scope::default();

    // Insert definitions into the Scope.
    let empty = TypeVarSet::empty();
    for (name, (mut typ, definition)) in cg.types.into_iter() {
        typ.apply(&soln);

        let type_scheme = typ.generalize(&empty);
        log::info!("Inferred type for {} : {}", name, type_scheme);
        let defn = TypedDefinition {
            type_scheme,
            definition,
        };
        scope.definitions.insert(name, defn);
    }

    // Insert type definitions into the Scope.
    scope.type_definitions = type_definitions;

    // Insert constructors into the Scope.
    scope.constructors = cg.constructors.keys().cloned().collect();

    Ok(scope)
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum Type {
    Var(TypeVar),
    Concrete(String),
    List(Box<Type>),
    Tuple(Vec<Type>),

    /// The function type
    Arrow(Box<Type>, Box<Type>),

    /// Type application (e.g. `Foo a`)
    App(Box<Type>, Box<Type>),
    // @Future @TypeBinops (maybe as type application)
}

impl Type {
    pub fn free_vars(&self) -> TypeVarSet {
        match self {
            Type::Concrete(_) => TypeVarSet::empty(),

            Type::Var(var) => TypeVarSet::single(*var),
            Type::Arrow(a, b) | Type::App(a, b) => a.free_vars().union(&b.free_vars()),
            Type::List(t) => t.free_vars(),
            Type::Tuple(v) => v
                .iter()
                .fold(TypeVarSet::empty(), |a, t| a.union(&t.free_vars())),
        }
    }

    /// Takes a Type and quantifies all free type variables, except the ones given in type_set.
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
                (Type::Tuple(ts1), Type::Tuple(ts2)) => {
                    for (t1, t2) in ts1.into_iter().zip(ts2.into_iter()) {
                        pairs.push((t1, t2));
                    }
                }
                (Type::Arrow(a1, b1), Type::Arrow(a2, b2))
                | (Type::App(a1, b1), Type::App(a2, b2)) => {
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

impl Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(var) => write!(f, "{}", var),
            Type::Concrete(s) => write!(f, "{}", s),

            // @Future @CST: be smarter about when to include brackets
            Type::Arrow(a, b) => write!(f, "({} -> {})", a, b),

            Type::App(a, b) => write!(f, "{} {}", a, b),

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

// @Todo: make this an enum with TypeVar::Generated(usize) and TypeVar::Explicit(&str)
// @Note: or maybe not? Possibly ast::TypeTerm::Var covers the need,
//        and we can just store a dictionary somewhere mapping from
//        ast::TypeTerm::Var to types::TypeVar.
// @Note: I think we do want to make this an enum.
//        It will probably be helpful when displaying error messages,
//        to ensure that we show the type variable that the user gave.
//        Currently, the map we use gets dropped at the end of converting the parsed TypeScheme,
//        so it's not around long enough to be helpful for errors anyway.
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct TypeVar(pub usize);

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeVarSet(BTreeSet<TypeVar>);

impl TypeVarSet {
    pub fn empty() -> TypeVarSet {
        TypeVarSet(BTreeSet::new())
    }

    pub fn single(elem: TypeVar) -> TypeVarSet {
        TypeVarSet(BTreeSet::from([elem]))
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
        // If it's the empty substitution, return early because there's nothing to do.
        // This was added to prevent a bug where applying the empty substitution
        // would cause all the forall quantifiers to fall off, which is bad.
        if sub.is_empty() {
            return;
        }

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
        TypeVarSet(BTreeSet::from_iter(iter))
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct TypeDefinition {
    /// The name of the type defined in this TypeDefinition.
    pub name: ast::Name,

    /// The type variables introduced in the left-hand-side of the definition.
    pub vars: TypeVarSet,

    /// The type defined in this TypeDefinition.
    pub typ: Type,

    /// A Vec of the constructors introduced in the right-hand-side of the definition,
    /// along with their types.
    pub constructors: BTreeMap<ast::Name, Type>,
}
