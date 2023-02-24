use std::fmt::{self, Debug};
use std::sync::atomic::{self, AtomicUsize};

use crate::log;
use crate::name::ResolvedName;
use crate::types::{Type, TypeScheme, TypeVarSet};

// @Note: The order here is important!
// It's the order that constraints will be processed.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Constraint {
    /// Used when two types should be equal.
    /// Causes the two types to be unified,
    /// and a substitution to the most general unifier to be applied.
    Equality(Type, Type),

    /// Used when one type needs to be an instance of another type,
    /// and the type scheme is explicitly known.
    ExplicitInstance(Type, TypeScheme),

    /// Used when one type needs to be an instance of another type,
    /// but the type scheme isn't yet known.
    /// Includes a [`TypeVarSet`] of the monomorphically-bound type variables in scope,
    /// which should be excluded from quantification by the resulting type scheme.
    ImplicitInstance(Type, Type, TypeVarSet<ResolvedName>),
}

impl Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(a, b) => write!(f, "{a} ≡ {b}"),
            Constraint::ImplicitInstance(a, b, m) => {
                write!(f, "{a} ≤ {b} where M is {m}")
            }
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{tau} ≼ {sigma}")
            }
        }
    }
}

/// Used for explicit type annotations.
/// Causes the inferred type to be unified with the explicit type,
/// and a corresponding substitution to be applied.
/// Solved after all the inferred type constraints.
#[derive(Clone)]
pub struct ExplicitTypeConstraint {
    pub inferred: Type,
    pub explicit: Type,
}

impl Debug for ExplicitTypeConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ExplicitTypeConstraint { inferred, explicit } = self;
        // @Cleanup: better message?
        write!(f, "{inferred} ≡ {explicit} (explicit type)")
    }
}

/// Keeps track of all the emitted constraints,
/// as well as giving them unique IDs for logging.
#[derive(Default)]
pub struct ConstraintSet {
    pub constraints: Vec<(Constraint, usize)>,
    pub explicit_constraints: Vec<(ExplicitTypeConstraint, usize)>,
}

static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(1);

impl ConstraintSet {
    /// Adds the constraint to the set.
    pub fn add(&mut self, constraint: Constraint) {
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);

        log::trace!(
            log::TYPECHECK,
            "    Emitting constraint [{id}]: {constraint:?}"
        );
        self.constraints.push((constraint, id));
    }

    /// Adds the explicit type constraint to the set.
    pub fn add_explicit(&mut self, constraint: ExplicitTypeConstraint) {
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);

        log::trace!(
            log::TYPECHECK,
            "    Emitting explicit type constraint [{id}]: {constraint:?}"
        );
        self.explicit_constraints.push((constraint, id));
    }

    /// Returns the total number of all types of constraints in the set.
    pub fn len(&self) -> usize {
        self.constraints.len() + self.explicit_constraints.len()
    }
}

impl Debug for ConstraintSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Find the length of the string built from formatting the length of constraints
        let width = format!("{}", self.len() - 1).len();

        writeln!(f, "Constraints:")?;
        for (constraint, id) in self.constraints.iter() {
            writeln!(f, "[{id:width$}] {constraint:?}")?;
        }

        writeln!(f, "Explicit type constraints:")?;
        for (constraint, id) in self.explicit_constraints.iter() {
            writeln!(f, "[{id:width$}] {constraint:?}")?;
        }

        Ok(())
    }
}
