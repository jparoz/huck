use std::fmt::{self, Debug, Write};
use std::{collections::BTreeMap, time::Instant};
use std::{iter, mem};

use crate::ast::{self, Module};
use crate::log;
use crate::name::{ModulePath, ResolvedName, Source};
use crate::types::{Primitive, Type, TypeScheme, TypeVar, TypeVarSet};
use crate::utils::unwrap_match;

mod arity;
mod substitution;

use arity::ArityChecker;
use substitution::{ApplySub, Substitution};

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Typechecks the given Huck modules.
pub fn typecheck(
    mut modules: BTreeMap<ModulePath, Module<ResolvedName, ()>>,
) -> Result<BTreeMap<ModulePath, Module<ResolvedName, Type>>, Error> {
    // Start the timer to measure how long typechecking takes.
    let start_time = Instant::now();
    log::info!(log::TYPECHECK, "Typechecking all modules...");

    let mut typechecker = Typechecker::default();

    // Ensure the prelude is typechecked first.
    // Has to be done in this order
    // so that the implicit Prelude import statement
    // can be imported into other modules.
    let prelude_path = ModulePath("Prelude");
    let prelude = modules.remove(&prelude_path).into_iter();

    // Typecheck each module
    for module in prelude.chain(modules.into_values()) {
        typechecker.typecheck_module(module)?;
    }

    // Solve the type constraints
    let typechecked_modules = typechecker.solve()?;

    log::info!(
        log::METRICS,
        "Typechecking completed, {:?} elapsed",
        start_time.elapsed()
    );

    Ok(typechecked_modules)
}

#[derive(PartialEq, Eq, Clone)]
pub enum Constraint {
    /// Used when two types should be equal.
    /// Causes the two types to be unified,
    /// and a substitution to the most general unifier to be applied.
    Equality(Type, Type),

    /// Used for explicit type annotations.
    /// Causes the left type (inferred)
    /// to be unified with the right type (explicit),
    /// and a substitution from the left to the right type to be applied.
    ExplicitType(Type, Type),

    /// Used when one type needs to be an instance of another type,
    /// but the type scheme isn't yet known.
    /// Includes a [`TypeVarSet`] of the monomorphically-bound type variables in scope,
    /// which should be excluded from quantification by the resulting type scheme.
    ImplicitInstance(Type, Type, TypeVarSet<ResolvedName>),

    /// Used when one type needs to be an instance of another type,
    /// and the type scheme is explicitly known.
    ExplicitInstance(Type, TypeScheme),
}

impl Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(a, b) => write!(f, "{} ≡ {}", a, b),
            // @Cleanup: better message?
            Constraint::ExplicitType(a, b) => write!(f, "{} ≡ {} (explicit type)", a, b),
            Constraint::ImplicitInstance(a, b, m) => {
                write!(f, "{} ≤ {} where M is {}", a, b, m)
            }
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{} ≼ {}", tau, sigma)
            }
        }
    }
}

/// Keeps track of all the emitted constraints,
/// as well as giving them unique IDs for logging.
#[derive(Default)]
pub struct ConstraintSet(Vec<(usize, Constraint)>);

impl ConstraintSet {
    /// Adds the constraint to the set.
    fn add(&mut self, constraint: Constraint) {
        use std::sync::atomic::{self, AtomicUsize};

        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);

        log::trace!(log::TYPECHECK, "Emitting constraint [{id}]: {constraint:?}");
        self.0.push((id, constraint));
    }
}

impl Debug for ConstraintSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (id, constraint) in self.0.iter() {
            writeln!(f, "[{id}] {constraint:?}")?;
        }
        Ok(())
    }
}

/// Manages typechecking of a group of modules.
#[derive(Debug, Default)]
struct Typechecker {
    /// The modules for which constraints have so far been generated.
    modules: BTreeMap<ModulePath, Module<ResolvedName, Type>>,

    /// All of the emitted constraints about the modules being typechecked.
    /// These are solved in [`Typechecker::solve`].
    constraints: ConstraintSet,

    /// All the currently assumed types of name uses.
    assumptions: BTreeMap<ResolvedName, Vec<Type>>,

    // @Todo @Cleanup: this has nothing to do with constraints, it's just here for convenience.
    arity_checker: ArityChecker,

    m_stack: Vec<TypeVar<ResolvedName>>,
}

impl Typechecker {
    /// Generates a new and unique TypeVar each time it's called.
    fn fresh_var(&mut self) -> TypeVar<ResolvedName> {
        use std::sync::atomic::{self, AtomicUsize};

        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
        TypeVar::Generated(id)
    }

    fn fresh(&mut self) -> Type {
        Type::Var(self.fresh_var())
    }

    /// If the given name is a builtin, then returns that builtin's type.
    /// Otherwise, emits an assumption binding the name to a fresh type variable.
    fn assume(&mut self, name: ResolvedName) -> Type {
        if name.source == Source::Builtin {
            match name.ident {
                "True" | "False" => Type::Primitive(Primitive::Bool),
                _ => unreachable!("missing a compiler builtin type"),
            }
        } else {
            let typ = self.fresh();
            log::trace!(log::TYPECHECK, "Assuming type: {} : {}", name, typ);
            self.assumptions
                .entry(name)
                .or_insert_with(|| Vec::with_capacity(1))
                .push(typ.clone());
            typ
        }
    }

    /// Constrains all types in the given Vec to be equal, and returns that type.
    fn equate_all(&mut self, typs: Vec<Type>) -> Type {
        if typs.len() == 1 {
            return typs[0].clone();
        }

        let beta = self.fresh();
        for typ in typs {
            self.constraints
                .add(Constraint::Equality(beta.clone(), typ.clone()));
        }
        beta
    }

    /// Takes a TypeScheme and replaces all quantified variables with fresh variables;
    /// then returns the resulting Type.
    fn instantiate(&mut self, ts: TypeScheme) -> Type {
        let TypeScheme { vars, mut typ } = ts;
        let sub = vars
            .into_iter()
            .zip(iter::repeat_with(|| self.fresh()))
            .collect();
        typ.apply(&sub);
        typ
    }

    fn typecheck_module(&mut self, module: Module<ResolvedName, ()>) -> Result<(), Error> {
        log::trace!(log::TYPECHECK, "Typechecking: module {};", module.path);
        // Set the new `Module`'s path.
        let mut typechecked_module = Module::new(module.path);

        // Generate constraints for each definition, while keeping track of inferred types
        for (name, defn) in module.definitions {
            log::trace!(log::TYPECHECK, "Inferring type for {name}");

            let typ = self.generate_definition(&defn);

            log::trace!(
                log::TYPECHECK,
                "Initial inferred type for {}: {}",
                name,
                typ
            );

            let typed_defn = {
                let ast::Definition {
                    assignments,
                    explicit_type,
                    precedence,
                    typ: (),
                } = defn;

                ast::Definition {
                    assignments,
                    explicit_type,
                    precedence,
                    typ,
                }
            };

            // @Note: guaranteed to be None,
            // because we're iterating over a BTreeMap.
            assert!(typechecked_module
                .definitions
                .insert(name, typed_defn)
                .is_none());
        }

        // Generate constraints for each type definition
        for (_name, ast_type_defn) in module.type_definitions {
            let type_defn = self.generate_type_definition(ast_type_defn);

            for (constr_name, constr_defn) in type_defn.constructors.iter() {
                typechecked_module
                    .constructors
                    .insert(*constr_name, constr_defn.clone());
            }

            // @Note: guaranteed to be None,
            // because we're iterating over a BTreeMap.
            assert!(typechecked_module
                .type_definitions
                .insert(type_defn.name, type_defn)
                .is_none());
        }

        // Insert all imported names into the scope.
        for (path, names) in module.imports {
            log::trace!(
                log::IMPORT,
                "Inserting into scope of {insert_path}: import {path} ({names:?})",
                insert_path = module.path
            );
            // @Errors: check for name clashes
            typechecked_module
                .imports
                .entry(path)
                .or_default()
                .extend(names);
        }

        // Insert all (foreign) imported names into the scope.
        for (require_string, imports) in module.foreign_imports {
            for ast::ForeignImportItem {
                foreign_name,
                name,
                type_scheme,
                typ: (),
            } in imports
            {
                log::trace!(
                    log::IMPORT,
                    "Inserting into scope of {module_path}: \
                         foreign import {require_string} ({foreign_name} as {name})",
                    module_path = module.path
                );

                let ts = self.generate_type_scheme(&type_scheme);
                let typ = self.instantiate(ts);

                // @Errors: check for name clashes
                typechecked_module
                    .foreign_imports
                    .entry(require_string)
                    .or_default()
                    .push(ast::ForeignImportItem {
                        foreign_name,
                        name,
                        typ,
                        type_scheme,
                    });
            }
        }

        // Insert all foreign exports into the scope.
        typechecked_module
            .foreign_exports
            .extend(module.foreign_exports);

        // If there is no explicit Prelude import already,
        // import everything in Prelude.
        let prelude_path = ModulePath("Prelude");
        if module.path != prelude_path {
            log::trace!(
                log::IMPORT,
                "Importing contents of Prelude into {}",
                module.path
            );
            let prelude = &self.modules[&prelude_path];

            // @Errors @Warn: name clashes
            typechecked_module
                .imports
                .entry(prelude_path)
                .or_default()
                .extend(
                    prelude
                        .definitions
                        .keys()
                        .chain(prelude.constructors.keys()),
                );
        }

        // Add the Module<ResolvedName, Type> to the typechecker.
        assert!(self
            .modules
            .insert(module.path, typechecked_module)
            .is_none());

        Ok(())
    }

    /// Solves the constraints which have been generated,
    /// and return the typechecked modules.
    fn solve(
        mut self,
    ) -> Result<BTreeMap<ModulePath, Module<ResolvedName, Type>>, crate::typecheck::Error> {
        // Before we can solve, we still need to bind all assumptions.
        self.bind_assumptions_top_level()?;

        // Find the length of the string built from formatting the length of constraints
        let width = format!("{}", self.constraints.0.len()).len();

        log::trace!(log::TYPECHECK, "Starting constraint solving, constraints:");
        for (id, constraint) in self.constraints.0.iter() {
            log::trace!(log::TYPECHECK, "  [{id:width$}] {constraint:?}");
        }

        // Solve the type constraints by iterating over them in passes.
        log::trace!(log::TYPECHECK, "{:-^100}", " START SOLVING ");

        // The solution substitution, built up as we go.
        let mut solution = Substitution::empty();

        // The constraints being processed in the current pass.
        // @Note: have to use mem::take so we can later on use self.fresh()
        let mut constraints = mem::take(&mut self.constraints).0;

        // The constraints to be processed in the next pass.
        let mut next_constraints = Vec::new();

        // This could be const when rust-lang/rust#69821 is closed (const fn is stabilised)
        let explicit_discriminant: mem::Discriminant<Constraint> =
            mem::discriminant(&Constraint::ExplicitType(
                Type::Primitive(Primitive::Unit),
                Type::Primitive(Primitive::Unit),
            ));

        // Find the width of the id column
        let id_width = format!("{}", constraints.len()).len();

        loop {
            // Keep track of whether we've processed any constraints in this pass.
            let mut processed_any_constraint = false;

            while let Some((id, constraint)) = constraints.pop() {
                // Keep track of the processing action, for logging
                let constraint_str = format!("{constraint:?}");
                let mut new_str = String::new();

                let discriminant = mem::discriminant(&constraint);

                match constraint {
                    Constraint::Equality(t1, t2) | Constraint::ExplicitType(t1, t2) => {
                        // If the constraint is an explicit type constraint,
                        // then we pass that fact to `unify`.
                        let new_sub = t1.unify(t2, discriminant == explicit_discriminant)?;

                        for (_id, c) in constraints.iter_mut().chain(next_constraints.iter_mut()) {
                            c.apply(&new_sub);
                        }

                        write!(new_str, "{new_sub:?}").unwrap();
                        solution = new_sub.then(solution);

                        processed_any_constraint = true;
                    }

                    Constraint::ExplicitInstance(t, ts) => {
                        let new_constraint = Constraint::Equality(t, self.instantiate(ts));
                        write!(new_str, "{new_constraint:?}").unwrap();
                        next_constraints.push((id, new_constraint));

                        processed_any_constraint = true;
                    }

                    Constraint::ImplicitInstance(t1, t2, m)
                        if t2
                            .free_vars()
                            .difference(&m)
                            .intersection(
                                &constraints
                                    .active_vars()
                                    .union(&next_constraints.active_vars()),
                            )
                            .is_empty() =>
                    {
                        let new_constraint = Constraint::ExplicitInstance(t1, t2.generalize(&m));
                        write!(new_str, "{new_constraint:?}").unwrap();
                        next_constraints.push((id, new_constraint));

                        processed_any_constraint = true;
                    }

                    constraint @ Constraint::ImplicitInstance(..) => {
                        write!(new_str, "[Skipping for now]").unwrap();
                        next_constraints.push((id, constraint));
                    }
                }

                log::trace!(
                    log::TYPECHECK,
                    "[{id:id_width$}]  {constraint_str:>60} ==> {new_str}"
                );
            }

            // If we didn't push any constraints into the queue, we're done.
            if next_constraints.is_empty() {
                break;
            }

            // If we pushed constraints but didn't process any of them
            // (i.e. if we skipped all the constraints),
            // then we can't proceed any further.
            // This situation might arise when typing a recursive function
            // (mutually or otherwise).
            //
            // @Note:
            // It's possible that we could pick this up during dependency resolution,
            // and then leave some sort of hint for the type system.
            // For now though, that's too clever.
            if !processed_any_constraint {
                // Here we try to detect cyclic type dependencies.
                // If the remaining constraints form a closed loop,
                // the type may be assigned arbitrarily.
                log::trace!(
                    log::TYPECHECK,
                    "Completed a pass of all constraints without processing any"
                );
                log::trace!(
                    log::TYPECHECK,
                    "  Checking if the remaining constraints form a closed loop:"
                );

                let mut cons = next_constraints.clone();
                // Safe unwrap: we checked that !is_empty() above
                let (_id, start) = cons.pop().unwrap();
                let (mut t1, start_t2, mut m) =
                    unwrap_match!(start, Constraint::ImplicitInstance(t1, t2, m) => (t1, t2, m));

                while !cons.is_empty() {
                    // @Checkme: is this always true? bit of a punt
                    assert!(m.is_empty());

                    if let Some(pos) = cons.iter().position(|(_id, c)| {
                        let c_t2 =
                            unwrap_match!(c, Constraint::ImplicitInstance(_t1, t2, _m) => t2);
                        &t1 == c_t2
                    }) {
                        let (_id, removed) = cons.remove(pos);
                        (t1, m) = unwrap_match!(
                            removed,
                            Constraint::ImplicitInstance(t1, _t2, m) => (t1, m)
                        );
                    } else {
                        // @DRY: same error below
                        log::trace!(log::TYPECHECK, "  They did not form a loop.");
                        return Err(Error::CouldNotSolveTypeConstraints(ConstraintSet(
                            next_constraints,
                        )));
                    }
                }

                // Since we made it out of the loop,
                // the constraints Vec is empty.
                debug_assert!(cons.is_empty());

                // Check if the loop is closed.
                if t1 == start_t2 {
                    // The loop is closed,
                    // so add constraints binding all the types to a new variable.
                    log::trace!(log::TYPECHECK, "  The constraints did form a closed loop.");
                    log::trace!(
                        log::TYPECHECK,
                        "  Binding all involved types to the same new type variable."
                    );

                    let new_type = self.fresh();
                    for (_id, c) in next_constraints.iter_mut() {
                        let t1 = unwrap_match!(c, Constraint::ImplicitInstance(t1, _t2, _m) => t1);
                        *c = Constraint::Equality(new_type.clone(), t1.clone())
                    }
                } else {
                    // @DRY: same error above
                    log::trace!(log::TYPECHECK, "  They did not form a loop.");
                    return Err(Error::CouldNotSolveTypeConstraints(ConstraintSet(
                        next_constraints,
                    )));
                }
            }

            // Swap the just-processed constraints with the next-to-be-processed constraints,
            // in time for the next pass.
            mem::swap(&mut constraints, &mut next_constraints);
        }

        log::trace!(log::TYPECHECK, "{:-^100}", " FINISH SOLVING ");
        log::trace!(log::TYPECHECK, "Solution:");
        for (fr, to) in solution.iter() {
            log::trace!(log::TYPECHECK, "  {} ↦ {}", fr, to);
        }

        // Apply the solution to each Module<ResolvedName, Type>.
        for module in self.modules.values_mut() {
            log::info!(log::TYPECHECK, "module {}:", module.path);
            for (name, ref mut definition) in module.definitions.iter_mut() {
                definition.typ.apply(&solution);
                log::info!(
                    log::TYPECHECK,
                    "  Inferred type for {name} : {}",
                    definition.typ
                );
            }
        }

        Ok(self.modules)
    }

    // Generation methods

    fn generate_definition(&mut self, definition: &ast::Definition<ResolvedName, ()>) -> Type {
        // Typecheck each assignment in the definition.
        let typs: Vec<Type> = definition
            .assignments
            .iter()
            .map(|assign| self.generate_assignment(assign))
            .collect();

        // Constrain that each inferred assignment should all be equal.
        let inferred_type = self.equate_all(typs);

        // @Cleanup: Maybe just always return inferred_type
        //
        // If there's an explicit type,
        // constrain that the inferred type should be unified with the explicit type.
        if let Some(ref explicit_type_scheme) = definition.explicit_type {
            log::trace!(
                log::TYPECHECK,
                "Including explicit type scheme: {explicit_type_scheme:?}",
            );
            let ts = self.generate_type_scheme(explicit_type_scheme);
            let explicit_type = self.instantiate(ts);
            self.constraints.add(Constraint::ExplicitType(
                inferred_type,
                explicit_type.clone(),
            ));
            explicit_type
        } else {
            inferred_type
        }
    }

    fn generate_assignment(&mut self, assign: &ast::Assignment<ResolvedName>) -> Type {
        let (lhs, expr) = assign;

        match lhs {
            ast::Lhs::Func { args, .. } => {
                args.iter()
                    .rev()
                    .fold(self.generate_expr(expr), |acc, arg| {
                        let beta = self.bind_pattern(arg);
                        Type::Arrow(Box::new(beta), Box::new(acc))
                    })
            }
            ast::Lhs::Binop { a, b, .. } => {
                let res = self.generate_expr(expr);
                let beta_a = self.bind_pattern(a);
                let beta_b = self.bind_pattern(b);

                Type::Arrow(
                    Box::new(beta_a),
                    Box::new(Type::Arrow(Box::new(beta_b), Box::new(res))),
                )
            }
        }
    }

    fn generate_expr(&mut self, expr: &ast::Expr<ResolvedName>) -> Type {
        match expr {
            ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int(_))) => {
                Type::Primitive(Primitive::Int)
            }
            ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Float(_))) => {
                Type::Primitive(Primitive::Float)
            }
            ast::Expr::Term(ast::Term::String(_)) => Type::Primitive(Primitive::String),
            ast::Expr::Term(ast::Term::Unit) => Type::Primitive(Primitive::Unit),

            ast::Expr::Term(ast::Term::TypedExpr(ast_expr, ast_ts)) => {
                let expr_typ = self.generate_expr(ast_expr);
                let ts = self.generate_type_scheme(ast_ts);
                let typ = self.instantiate(ts);
                self.constraints
                    .add(Constraint::ExplicitType(expr_typ, typ.clone()));
                typ
            }

            ast::Expr::Term(ast::Term::Parens(e)) => self.generate_expr(e),
            ast::Expr::Term(ast::Term::List(es)) => {
                let beta = self.fresh();
                for e in es {
                    let e_type = self.generate_expr(e);
                    self.constraints
                        .add(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }
            ast::Expr::Term(ast::Term::Tuple(es)) => {
                Type::Tuple(es.iter().map(|e| self.generate_expr(e)).collect())
            }

            ast::Expr::Term(ast::Term::Name(name)) => self.assume(*name),

            ast::Expr::App { func, argument } => {
                let t1 = self.generate_expr(func);
                let t2 = self.generate_expr(argument);
                let beta = self.fresh();

                self.constraints.add(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                let t1 = self.assume(*operator);
                let t2 = self.generate_expr(lhs);
                let t3 = self.generate_expr(rhs);
                let beta1 = self.fresh();
                let beta2 = self.fresh();

                self.constraints.add(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta1.clone())),
                ));
                self.constraints.add(Constraint::Equality(
                    beta1,
                    Type::Arrow(Box::new(t3), Box::new(beta2.clone())),
                ));

                beta2
            }

            ast::Expr::Let {
                definitions,
                in_expr,
            } => {
                let beta = self.generate_expr(in_expr);

                for (name, assignments) in definitions {
                    let typs = assignments
                        .iter()
                        .map(|assign| self.generate_assignment(assign))
                        .collect();
                    let typ = self.equate_all(typs);
                    self.bind_assumptions_poly(name, &typ);
                }

                beta
            }

            ast::Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond_type = self.generate_expr(cond);
                let then_type = self.generate_expr(then_expr);
                let else_type = self.generate_expr(else_expr);

                self.constraints.add(Constraint::Equality(
                    cond_type,
                    Type::Primitive(Primitive::Bool),
                ));
                self.constraints
                    .add(Constraint::Equality(then_type.clone(), else_type));

                then_type
            }

            ast::Expr::Case { expr, arms } => {
                let mut pat_types = Vec::new();
                let mut arm_types = Vec::new();
                for (pat, e) in arms {
                    // Use a fresh type variable to represent the newly bound pattern.
                    let typevar = self.fresh_var();

                    // Push the typevar onto the stack while generating the expression.
                    self.m_stack.push(typevar);
                    arm_types.push(self.generate_expr(e));
                    let typevar = self.m_stack.pop().unwrap();

                    // Equate the fresh variable to the rest of the pattern types.
                    pat_types.push(Type::Var(typevar));
                    // Equate the actual type found while binding.
                    pat_types.push(self.bind_pattern(pat));
                }

                // Equate the type of the scrutinised expression to the pattern types.
                pat_types.push(self.generate_expr(expr));

                // Actually equate all the pattern types
                self.equate_all(pat_types);

                // Finally, equate all the arm RHS return types, and return that as the expr type.
                self.equate_all(arm_types)
            }

            ast::Expr::Lambda { args, rhs } => {
                let typevars: Vec<TypeVar<ResolvedName>> =
                    args.iter().map(|_| self.fresh_var()).collect();
                let types: Vec<Type> = typevars.iter().map(|v| Type::Var(*v)).collect();
                let typevar_count = typevars.len();

                self.m_stack.extend(typevars);

                let res = types
                    .iter()
                    .rev()
                    .fold(self.generate_expr(rhs), |acc, beta| {
                        Type::Arrow(Box::new(beta.clone()), Box::new(acc))
                    });

                let total_len = self.m_stack.len();
                self.m_stack.truncate(total_len - typevar_count);

                for (arg, lambda_type) in args.iter().zip(types.into_iter()) {
                    let actual_type = self.bind_pattern(arg);
                    self.constraints
                        .add(Constraint::Equality(actual_type, lambda_type))
                }

                res
            }

            ast::Expr::Lua(_) => Type::App(
                Box::new(Type::Primitive(Primitive::IO)),
                Box::new(self.fresh()),
            ),

            ast::Expr::UnsafeLua(_) => self.fresh(),
        }
    }

    // Type-level generation methods

    fn generate_type_definition(
        &mut self,
        type_defn: ast::TypeDefinition<ResolvedName, ()>,
    ) -> ast::TypeDefinition<ResolvedName, Type> {
        let ast::TypeDefinition {
            name,
            vars,
            constructors: constrs,
            typ: (),
        } = type_defn;

        // We'll build the type by iterating over the type arguments.
        let mut typ = Type::Concrete(name);

        for var in vars.iter() {
            // The final returned type of the constructor needs to reflect this type argument;
            // so we mark that here.
            typ = Type::App(Box::new(typ), Box::new(Type::Var(*var)));
        }

        let mut constructors = BTreeMap::new();

        for constr_defn in constrs.into_values() {
            let constr_type = constr_defn
                .args
                .iter()
                .rev()
                .map(|term| self.generate_type_term(term))
                .fold(typ.clone(), |res, a| {
                    Type::Arrow(Box::new(a), Box::new(res))
                });

            // @Checkme: poly or mono?
            self.bind_assumptions_poly(&constr_defn.name, &constr_type);

            // @Errors @Checkme: no name conflicts
            constructors.insert(
                constr_defn.name,
                ast::ConstructorDefinition {
                    name: constr_defn.name,
                    args: constr_defn.args,
                    typ: constr_type,
                },
            );
        }

        ast::TypeDefinition {
            name,
            vars,
            typ,
            constructors,
        }
    }

    fn generate_type_scheme(&mut self, input: &ast::TypeScheme<ResolvedName>) -> TypeScheme {
        // Recursively generate arity assumptions for this type expression.
        //
        // @Cleanup:
        // This doesn't really need to be here,
        // it's just convenient to call this here
        // while we're already traversing the AST.
        // It might be neater to place this outside of `constraint`.
        self.arity_checker.type_expr(&input.typ, 0);

        let vars: TypeVarSet<ResolvedName> =
            input.vars.iter().map(|v| TypeVar::Explicit(*v)).collect();

        let typ = self.generate_type_expr(&input.typ);

        TypeScheme { vars, typ }
    }

    fn generate_type_expr(&mut self, input: &ast::TypeExpr<ResolvedName>) -> Type {
        match input {
            ast::TypeExpr::Term(term) => self.generate_type_term(term),
            ast::TypeExpr::App(f, x) => Type::App(
                Box::new(self.generate_type_expr(f)),
                Box::new(self.generate_type_expr(x)),
            ),
            ast::TypeExpr::Arrow(a, b) => Type::Arrow(
                Box::new(self.generate_type_expr(a)),
                Box::new(self.generate_type_expr(b)),
            ),
        }
    }

    fn generate_type_term(&mut self, input: &ast::TypeTerm<ResolvedName>) -> Type {
        match input {
            ast::TypeTerm::Concrete(ResolvedName {
                source: Source::Builtin,
                ident: "Int",
            }) => Type::Primitive(Primitive::Int),

            ast::TypeTerm::Concrete(ResolvedName {
                source: Source::Builtin,
                ident: "Float",
            }) => Type::Primitive(Primitive::Float),

            ast::TypeTerm::Concrete(ResolvedName {
                source: Source::Builtin,
                ident: "String",
            }) => Type::Primitive(Primitive::String),

            ast::TypeTerm::Concrete(ResolvedName {
                source: Source::Builtin,
                ident: "Bool",
            }) => Type::Primitive(Primitive::Bool),

            ast::TypeTerm::Concrete(ResolvedName {
                source: Source::Builtin,
                ident: "IO",
            }) => Type::Primitive(Primitive::IO),

            ast::TypeTerm::Unit => Type::Primitive(Primitive::Unit),

            ast::TypeTerm::Concrete(s) => Type::Concrete(*s),

            ast::TypeTerm::Var(v) => Type::Var(TypeVar::Explicit(*v)),

            ast::TypeTerm::Parens(e) => self.generate_type_expr(e),

            ast::TypeTerm::List(e) => Type::List(Box::new(self.generate_type_expr(e))),

            ast::TypeTerm::Tuple(exprs) => {
                Type::Tuple(exprs.iter().map(|e| self.generate_type_expr(e)).collect())
            }
        }
    }

    /// Returns the type of the whole pattern item, as well as emitting constraints for sub-items.
    fn bind_pattern(&mut self, pat: &ast::Pattern<ResolvedName>) -> Type {
        macro_rules! bind_function_args {
            ($cons_type:expr, $iter:expr) => {
                $iter.fold($cons_type, |acc, arg| {
                    let arg_type = self.bind_pattern(arg);
                    let partial_res_type = self.fresh();
                    let partial_cons_type =
                        Type::Arrow(Box::new(arg_type), Box::new(partial_res_type.clone()));

                    self.constraints
                        .add(Constraint::Equality(acc, partial_cons_type));

                    partial_res_type
                })
            };
        }

        match pat {
            ast::Pattern::Bind(name) => {
                let beta = self.fresh();
                self.bind_assumptions_mono(name, &beta);
                beta
            }

            // Don't need to bind anything for underscores,
            // because they're not legal identifiers and can't be used again.
            ast::Pattern::Underscore(_) => self.fresh(),

            ast::Pattern::List(pats) => {
                let beta = self.fresh();

                for pat in pats {
                    let typ = self.bind_pattern(pat);
                    self.constraints
                        .add(Constraint::Equality(beta.clone(), typ));
                }

                Type::List(Box::new(beta))
            }
            ast::Pattern::Tuple(pats) => {
                Type::Tuple(pats.iter().map(|pat| self.bind_pattern(pat)).collect())
            }

            ast::Pattern::Numeral(ast::Numeral::Int(_)) => Type::Primitive(Primitive::Int),
            ast::Pattern::Numeral(ast::Numeral::Float(_)) => Type::Primitive(Primitive::Float),
            ast::Pattern::String(_) => Type::Primitive(Primitive::String),
            ast::Pattern::Unit => Type::Primitive(Primitive::Unit),

            ast::Pattern::Binop { operator, lhs, rhs } => {
                let beta = self.assume(*operator);
                bind_function_args!(beta, iter::once(lhs).chain(iter::once(rhs)))
            }

            ast::Pattern::UnaryConstructor(name) => self.assume(*name),
            ast::Pattern::Destructure { constructor, args } => {
                let beta = self.assume(*constructor);
                bind_function_args!(beta, args.iter())
            }
        }
    }

    /// Binds (monomorphically) any assumptions about the given name to the given type.
    fn bind_assumptions_mono(&mut self, name: &ResolvedName, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constraints
                    .add(Constraint::Equality(assumed, typ.clone()));
                log::trace!(log::TYPECHECK, "Bound (mono): {} to type {}", name, typ);
            }
        }
    }

    /// Binds (polymorphically) any assumptions about the given name to the given type.
    fn bind_assumptions_poly(&mut self, name: &ResolvedName, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constraints.add(Constraint::ImplicitInstance(
                    assumed,
                    typ.clone(),
                    self.m_stack.iter().cloned().collect(),
                ));
                log::trace!(
                    log::TYPECHECK,
                    "Bound (poly): {} to type {} (M = {})",
                    name,
                    typ,
                    self.m_stack
                        .iter()
                        .cloned()
                        .collect::<TypeVarSet<ResolvedName>>()
                );
            }
        }
    }

    /// Binds all assumptions left at the end of typechecking (e.g. from imported names).
    fn bind_assumptions_top_level(&mut self) -> Result<(), Error> {
        log::trace!(log::TYPECHECK, "Emitting constraints about assumptions:");

        for module in self.modules.values() {
            // Constrain assumptions about names defined in this module.
            for (name, defn) in module.definitions.iter() {
                if let Some(assumed_types) = self.assumptions.remove(name) {
                    for assumed_type in assumed_types {
                        let constraint = Constraint::ImplicitInstance(
                            assumed_type,
                            defn.typ.clone(),
                            TypeVarSet::empty(),
                        );
                        self.constraints.add(constraint);
                    }
                } else {
                    // @Note: If a definition isn't used in any of the typechecked code,
                    // we'll find out about it here.
                    // This could be useful for dead code analysis,
                    // although this will currently fire for all definitions,
                    // even if the point of the defninition is to be used from Lua.
                    // Would probably need to have explicit exports for this to be useful.
                    // log::debug!("Possibly unused name: {name}");
                }
            }

            // Constrain assumptions about Huck imports.
            for (import_path, import_names) in module.imports.iter() {
                // Get the imported module.
                let import_module = &self.modules[import_path];

                // Constrain that each assumed type is an instance of the name's inferred type.
                for import_name in import_names {
                    // Find the inferred type.
                    let typ = import_module
                        .constructors
                        .get(import_name)
                        .map(|constr_defn| constr_defn.typ.clone())
                        .or_else(|| {
                            import_module
                                .definitions
                                .get(import_name)
                                .map(|defn| defn.typ.clone())
                        })
                        .expect(
                            "module should have been assigned types before binding assumptions",
                        );

                    // If there are any assumptions about the variable, bind them.
                    if let Some(assumed_types) = self.assumptions.remove(import_name) {
                        // Constrain that the assumed types are instances of the inferred type.
                        for assumed_type in assumed_types {
                            let constraint = Constraint::ImplicitInstance(
                                assumed_type,
                                typ.clone(),
                                TypeVarSet::empty(),
                            );
                            self.constraints.add(constraint);
                        }
                    } else {
                        // @Errors @Warn: emit a warning for unused imports
                        if import_path != &ModulePath("Prelude") {
                            log::warn!(log::IMPORT, "unused: import {import_path} ({import_name})");
                        }
                    }
                }
            }

            // Constrain assumptions about foreign imports.
            for imports in module.foreign_imports.values() {
                for ast::ForeignImportItem { name, typ, .. } in imports {
                    if let Some(assumed_types) = self.assumptions.remove(name) {
                        for assumed_type in assumed_types.iter() {
                            let tau = assumed_type.clone();

                            // @Note: we're just replacing the type variables which are
                            // thrown away when inserting foreign imports into the scope.
                            // This could possibly be done in a more sensible way;
                            // but this is at least consistent and correct.
                            let sigma = typ.clone().generalize(&TypeVarSet::empty());

                            self.constraints
                                .add(Constraint::ExplicitInstance(tau, sigma));
                        }
                    }
                }
            }
        }

        // We should have removed all assumptions by now.
        assert_eq!(self.assumptions, BTreeMap::new());

        // Checks all the arity assumptions are true within the given modules.
        self.arity_checker.finish(&self.modules)?;

        Ok(())
    }
}

trait ActiveVars {
    fn active_vars(&self) -> TypeVarSet<ResolvedName>;
}

impl ActiveVars for Constraint {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        match self {
            // @Checkme: same for explicit type?
            Constraint::Equality(t1, t2) | Constraint::ExplicitType(t1, t2) => {
                t1.free_vars().union(&t2.free_vars())
            }
            Constraint::ExplicitInstance(t, sigma) => t.free_vars().union(&sigma.free_vars()),
            Constraint::ImplicitInstance(t1, t2, m) => {
                t1.free_vars().union(&m.intersection(&t2.free_vars()))
            }
        }
    }
}

impl ActiveVars for &[(usize, Constraint)] {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        self.iter()
            .map(|(_id, c)| c.active_vars())
            .reduce(|vars1, vars2| vars1.union(&vars2))
            .unwrap_or_else(TypeVarSet::empty)
    }
}

impl ActiveVars for Vec<(usize, Constraint)> {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        self.as_slice().active_vars()
    }
}

impl Type {
    fn free_vars(&self) -> TypeVarSet<ResolvedName> {
        match self {
            Type::Concrete(_) | Type::Primitive(_) => TypeVarSet::empty(),

            Type::Var(var) => TypeVarSet::single(*var),
            Type::Arrow(a, b) | Type::App(a, b) => a.free_vars().union(&b.free_vars()),
            Type::List(t) => t.free_vars(),
            Type::Tuple(v) => v
                .iter()
                .fold(TypeVarSet::empty(), |a, t| a.union(&t.free_vars())),
        }
    }

    /// Takes a Type and quantifies all free type variables, except the ones given in type_set.
    fn generalize(self, type_set: &TypeVarSet<ResolvedName>) -> TypeScheme {
        TypeScheme {
            vars: self.free_vars().difference(type_set),
            typ: self,
        }
    }

    /// Finds the most general unifier for two types.
    /// If `is_explicit` is true,
    /// then the unification will be asymmetric
    /// such that the right-hand-side type (`other`) will remain the same.
    fn unify(self, other: Self, is_explicit: bool) -> Result<Substitution, Error> {
        let mut sub = Substitution::empty();

        let mut pairs = vec![(self, other)];

        while let Some((a, b)) = pairs.pop() {
            match (a, b, is_explicit) {
                (t1, t2, _) if t1 == t2 => (),

                // If the LHS might be transformed into the RHS,
                // or the RHS might be transformed inth the LHS
                // *AND* the unification isn't for an explicit type,
                // then we can unify the types.
                (Type::Var(var), t, _) | (t, Type::Var(var), false) => {
                    if t.free_vars().contains(&var) {
                        return Err(Error::CouldNotUnifyRecursive(t, Type::Var(var)));
                    } else {
                        let s = Substitution::single(var, t.clone());
                        for (a2, b2) in pairs.iter_mut() {
                            a2.apply(&s);
                            b2.apply(&s);
                        }
                        sub = sub.then(s);
                    }
                }

                (Type::List(t1), Type::List(t2), _) => pairs.push((*t1, *t2)),
                (Type::Tuple(ts1), Type::Tuple(ts2), _) => {
                    for (t1, t2) in ts1.into_iter().zip(ts2.into_iter()) {
                        pairs.push((t1, t2));
                    }
                }
                (Type::Arrow(a1, b1), Type::Arrow(a2, b2), _)
                | (Type::App(a1, b1), Type::App(a2, b2), _) => {
                    pairs.push((*a1, *a2));
                    pairs.push((*b1, *b2));
                }
                // @Todo: include `self` and `other` in the error as well
                (t1, t2, _) => {
                    if is_explicit {
                        return Err(Error::CouldNotUnifyExplicit(t1, t2));
                    } else {
                        return Err(Error::CouldNotUnify(t1, t2));
                    }
                }
            }
        }

        Ok(sub)
    }
}

impl TypeScheme {
    fn free_vars(&self) -> TypeVarSet<ResolvedName> {
        self.typ.free_vars().difference(&self.vars)
    }
}
