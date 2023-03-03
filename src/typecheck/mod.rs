use std::collections::BTreeMap;
use std::time::Instant;
use std::{iter, mem};

use crate::name::{ModulePath, ResolvedName, Source};
use crate::types::{Primitive, Type, TypeScheme, TypeVar, TypeVarSet};
use crate::utils::unwrap_match;
use crate::{ast, log};

mod arity;
mod constraint;
mod substitution;

use arity::ArityChecker;
use constraint::{Constraint, ConstraintSet, ExplicitTypeConstraint};
use substitution::{ApplySub, Substitution};

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Typechecks the given Huck modules.
pub fn typecheck(
    mut modules: BTreeMap<ModulePath, ast::Module<ResolvedName, ()>>,
) -> Result<BTreeMap<ModulePath, ast::Module<ResolvedName, Type>>, Error> {
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

/// Manages typechecking of a group of modules.
#[derive(Debug, Default)]
struct Typechecker {
    /// The modules for which constraints have so far been generated.
    modules: BTreeMap<ModulePath, ast::Module<ResolvedName, Type>>,

    /// All of the emitted constraints about the modules being typechecked.
    /// These are solved in [`Typechecker::solve`].
    constraints: ConstraintSet,

    /// All the currently assumed types of name uses.
    assumptions: BTreeMap<ResolvedName, Vec<Type>>,

    /// The [`ArityChecker`] which checks that types are used with the correct arity.
    arity_checker: ArityChecker,

    /// The stack of monomorphically-bound type variables.
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
            log::trace!(log::TYPECHECK, "    Assuming type: {} : {}", name, typ);
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

    fn typecheck_module(&mut self, module: ast::Module<ResolvedName, ()>) -> Result<(), Error> {
        log::trace!(log::TYPECHECK, "Typechecking: module {};", module.path);
        // Set the new `Module`'s path.
        let mut typechecked_module = ast::Module::new(module.path);

        // Generate constraints for each definition, while keeping track of inferred types
        for (name, defn) in module.definitions {
            let typ = self.typecheck_definition(&defn);

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
            let type_defn = self.typecheck_type_definition(ast_type_defn);

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
                "  Inserting into scope of {insert_path}: import {path} ({names:?})",
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
                    "  Inserting into scope of {module_path}: \
                         foreign import {require_string} ({foreign_name} as {name})",
                    module_path = module.path
                );

                let ts = self.typecheck_type_scheme(&type_scheme);
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

        // @Todo @Fixme: explicit Prelude imports don't prevent anything
        // If there is no explicit Prelude import already,
        // import everything in Prelude.
        let prelude_path = ModulePath("Prelude");
        if module.path != prelude_path {
            log::trace!(
                log::IMPORT,
                "  Importing contents of Prelude into {}",
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
                        .chain(prelude.constructors.keys())
                        .cloned()
                        .map(ast::ImportItem::from),
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
    ) -> Result<BTreeMap<ModulePath, ast::Module<ResolvedName, Type>>, crate::typecheck::Error>
    {
        // Bind all remaining assumptions.
        self.bind_assumptions_top_level()?;

        // Check that all the arity assumptions are true within the given modules.
        self.arity_checker.finish(&self.modules)?;

        // Now we can solve the type constraints.

        log::trace!(log::TYPECHECK, "Starting constraint solving");
        log::trace!(log::TYPECHECK, "{:?}", self.constraints);

        // Find the width of the id column
        let id_width = format!("{}", self.constraints.len() - 1).len();

        // Solve the type constraints by iterating over them in passes.
        log::trace!(log::TYPECHECK, "{:-^100}", " START SOLVING ");

        // The solution substitution, built up as we go.
        let mut solution = Substitution::empty();

        // The constraints as they are being processed.
        let mut constraint_set = mem::take(&mut self.constraints);
        constraint_set.constraints.sort_unstable();

        // The constraints to be processed in the next pass.
        let mut next_constraints = Vec::new();

        loop {
            // Keep track of whether we've processed any constraints in this pass.
            let mut processed_any_constraint = false;

            while let Some((constraint, id)) = constraint_set.constraints.pop() {
                // Keep a copy of the constraint to log later
                let constraint_str = format!("{constraint:?}");

                let sub = match constraint {
                    Constraint::Equality(t1, t2) => t1.unify(t2)?,

                    Constraint::ExplicitInstance(t1, ts) => {
                        // @Note:
                        // Conceptually,
                        // this is turned into an Equality constraint,
                        // then unified;
                        // but to reduce iterations,
                        // we shortcut by doing it all at once.
                        let new_t2 = self.instantiate(ts);
                        t1.unify(new_t2)?
                    }

                    Constraint::ImplicitInstance(t1, t2, m)
                        if t2
                            .free_vars()
                            .difference(&m)
                            .intersection(
                                &constraint_set
                                    .active_vars()
                                    .union(&next_constraints.active_vars()),
                            )
                            .is_empty() =>
                    {
                        // Make sure that this isn't a recursive constraint.
                        // This is done by temporarily pretending that it's an equality constraint,
                        // because [`unify`](Type::unify) already implements this logic.
                        //
                        // @Errors: this should be done a bit more properly,
                        // and a more specific message given.
                        let _ = t1.clone().unify(t2.clone())?;

                        // @Note:
                        // Conceptually,
                        // this is first turned into an ExplicitInstance constraint,
                        // then into an Equality constraint,
                        // then unified;
                        // but to reduce iterations,
                        // we shortcut by doing it all at once.
                        let ts = t2.generalize(&m);
                        let new_t2 = self.instantiate(ts);
                        t1.unify(new_t2)?
                    }

                    constraint @ Constraint::ImplicitInstance(..) => {
                        // Skip this for now.
                        next_constraints.push((constraint, id));
                        continue;
                    }
                };

                // If we're here,
                // it means we didn't skip the constraint,
                // so we've processed something.
                processed_any_constraint = true;

                // Apply the unifying substitution to the remaining constraints.
                constraint_set.apply(&sub);
                next_constraints.apply(&sub);

                log::trace!(
                    log::TYPECHECK,
                    "[{id:id_width$}]  {constraint_str:>60} ==> {sub:?}"
                );

                // Include this substitution in the solution.
                solution = sub.then(solution);
            }

            // If we didn't push any constraints into the queue, we're done.
            if next_constraints.is_empty() {
                break;
            }

            // Swap the just-processed constraints with the next-to-be-processed constraints,
            // in time for the next pass.
            mem::swap(&mut constraint_set.constraints, &mut next_constraints);

            // As long as we processed at least one constraint,
            // we're good to continue.
            if processed_any_constraint {
                continue;
            }

            // Because we pushed some new constraints
            // and didn't process any others
            // (i.e. if we skipped all the constraints),
            // we can't proceed any further.
            // So, we try to detect a dependency loop,
            // in which case we can assign an arbitrary type and continue.
            //
            // This situation might arise when typing a recursive function
            // (mutually or otherwise).
            //
            // @Note:
            // It's possible that we could pick this up during dependency resolution,
            // and then leave some sort of hint for the type system.
            // For now though, that's too clever.
            //
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

            let mut cons = constraint_set.constraints.clone();
            // Safe unwrap: we checked that !is_empty() above
            let (start, _id) = cons.pop().unwrap();
            let (mut t1, start_t2, mut m) =
                unwrap_match!(start, Constraint::ImplicitInstance(t1, t2, m) => (t1, t2, m));

            while !cons.is_empty() {
                // @Checkme: is this always true? bit of a punt
                assert!(m.is_empty());

                if let Some(pos) = cons.iter().position(|(c, _id)| {
                    let c_t2 = unwrap_match!(c, Constraint::ImplicitInstance(_t1, t2, _m) => t2);
                    &t1 == c_t2
                }) {
                    let (removed, _id) = cons.remove(pos);
                    (t1, m) = unwrap_match!(
                        removed,
                        Constraint::ImplicitInstance(t1, _t2, m) => (t1, m)
                    );
                } else {
                    // @DRY: same error below
                    log::trace!(log::TYPECHECK, "  They did not form a loop.");
                    return Err(Error::CouldNotSolveTypeConstraints(constraint_set));
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
                for (c, _id) in constraint_set.constraints.iter_mut() {
                    let t1 = unwrap_match!(c, Constraint::ImplicitInstance(t1, _t2, _m) => t1);
                    *c = Constraint::Equality(new_type.clone(), t1.clone())
                }
            } else {
                // @DRY: same error above
                log::trace!(log::TYPECHECK, "  They did not form a loop.");
                return Err(Error::CouldNotSolveTypeConstraints(constraint_set));
            }

            // If we've made it this far,
            // we've recovered,
            // and are okay to continue looping through constraints.
            // This is the end of the loop block,
            // so away we go back to the top!
        }

        // Now we've solved all the inferred type constraints,
        // we can solve explicit type constraints.
        while let Some((constraint, id)) = constraint_set.explicit_constraints.pop() {
            let constraint_str = format!("{constraint:?}");

            let ExplicitTypeConstraint { inferred, explicit } = constraint;

            // Make sure the explicit type is compatible with the inferred type.
            let new_sub = inferred.explicit(explicit)?;

            // Apply the unifying substitution to the remaining constraints.
            constraint_set.apply(&new_sub);

            // Include this substitution in the solution.
            log::trace!(
                log::TYPECHECK,
                "[{id:id_width$}]  {constraint_str:>60} ==> {new_sub:?}"
            );
            solution = new_sub.then(solution);
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

    // Value-level typechecking methods

    fn typecheck_definition(&mut self, definition: &ast::Definition<ResolvedName, ()>) -> Type {
        let name = definition.assignments[0].0.name();
        log::trace!(log::TYPECHECK, "  Inferring type for {name}");

        // Typecheck each assignment in the definition.
        let typs: Vec<Type> = definition
            .assignments
            .iter()
            .map(|assign| self.typecheck_assignment(assign))
            .collect();

        // Constrain that each inferred assignment should all be equal.
        let inferred = self.equate_all(typs);

        // @Cleanup: Maybe just always return inferred
        //
        // If there's an explicit type,
        // constrain that the inferred type should be unified with the explicit type.
        let typ = if let Some(ref explicit_type_scheme) = definition.explicit_type {
            log::trace!(
                log::TYPECHECK,
                "    Including explicit type scheme: {explicit_type_scheme:?}",
            );
            let ts = self.typecheck_type_scheme(explicit_type_scheme);
            let explicit_type = self.instantiate(ts);
            self.constraints.add_explicit(ExplicitTypeConstraint {
                inferred,
                explicit: explicit_type.clone(),
            });
            explicit_type
        } else {
            inferred
        };

        log::trace!(log::TYPECHECK, "  Initial inferred type for {name}: {typ}");

        typ
    }

    fn typecheck_assignment(&mut self, assign: &ast::Assignment<ResolvedName>) -> Type {
        let (lhs, rhs) = assign;
        self.typecheck_lambda(&lhs.args(), rhs)
    }

    /// Emits type constraints for a Huck function,
    /// whether that's an assignment as part of a definition,
    /// or a lambda.
    fn typecheck_lambda(
        &mut self,
        args: &[ast::Pattern<ResolvedName>],
        rhs: &ast::Expr<ResolvedName>,
    ) -> Type {
        let typevars: Vec<TypeVar<ResolvedName>> = args.iter().map(|_| self.fresh_var()).collect();
        let types: Vec<Type> = typevars.iter().map(|v| Type::Var(*v)).collect();
        let typevar_count = typevars.len();

        self.m_stack.extend(typevars);

        let res = types
            .iter()
            .rev()
            .fold(self.typecheck_expr(rhs), |acc, beta| {
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

    fn typecheck_expr(&mut self, expr: &ast::Expr<ResolvedName>) -> Type {
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
                let expr_typ = self.typecheck_expr(ast_expr);
                let ts = self.typecheck_type_scheme(ast_ts);
                let typ = self.instantiate(ts);
                self.constraints.add_explicit(ExplicitTypeConstraint {
                    inferred: expr_typ,
                    explicit: typ.clone(),
                });
                typ
            }

            ast::Expr::Term(ast::Term::Parens(e)) => self.typecheck_expr(e),
            ast::Expr::Term(ast::Term::List(es)) => {
                let beta = self.fresh();
                for e in es {
                    let e_type = self.typecheck_expr(e);
                    self.constraints
                        .add(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }
            ast::Expr::Term(ast::Term::Tuple(es)) => {
                Type::Tuple(es.iter().map(|e| self.typecheck_expr(e)).collect())
            }

            ast::Expr::Term(ast::Term::Name(name)) => self.assume(*name),

            ast::Expr::App { func, argument } => {
                let t1 = self.typecheck_expr(func);
                let t2 = self.typecheck_expr(argument);
                let beta = self.fresh();

                self.constraints.add(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                let t1 = self.assume(*operator);
                let t2 = self.typecheck_expr(lhs);
                let t3 = self.typecheck_expr(rhs);
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
                let beta = self.typecheck_expr(in_expr);

                for (name, assignments) in definitions {
                    let typs = assignments
                        .iter()
                        .map(|assign| self.typecheck_assignment(assign))
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
                let cond_type = self.typecheck_expr(cond);
                let then_type = self.typecheck_expr(then_expr);
                let else_type = self.typecheck_expr(else_expr);

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

                    // Push the typevar onto the stack while typechecking the expression.
                    self.m_stack.push(typevar);
                    arm_types.push(self.typecheck_expr(e));
                    let typevar = self.m_stack.pop().unwrap();

                    // Equate the fresh variable to the rest of the pattern types.
                    pat_types.push(Type::Var(typevar));
                    // Equate the actual type found while binding.
                    pat_types.push(self.bind_pattern(pat));
                }

                // Equate the type of the scrutinised expression to the pattern types.
                pat_types.push(self.typecheck_expr(expr));

                // Actually equate all the pattern types
                self.equate_all(pat_types);

                // Finally, equate all the arm RHS return types, and return that as the expr type.
                self.equate_all(arm_types)
            }

            ast::Expr::Lambda { args, rhs } => self.typecheck_lambda(args, rhs),

            ast::Expr::Lua(_) => Type::App(
                Box::new(Type::Primitive(Primitive::IO)),
                Box::new(self.fresh()),
            ),

            ast::Expr::UnsafeLua(_) => self.fresh(),
        }
    }

    // Type-level typechecking methods

    fn typecheck_type_definition(
        &mut self,
        type_defn: ast::TypeDefinition<ResolvedName, ()>,
    ) -> ast::TypeDefinition<ResolvedName, Type> {
        let ast::TypeDefinition {
            name,
            vars,
            constructors: constrs,
            typ: (),
        } = type_defn;

        log::trace!(log::TYPECHECK, "  Typechecking type definition {name}");

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
                .map(|term| self.typecheck_type_term(term))
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

    fn typecheck_type_scheme(&mut self, input: &ast::TypeScheme<ResolvedName>) -> TypeScheme {
        // Recursively check arity assumptions for this type expression.
        self.arity_checker.type_expr(&input.typ, 0);

        let vars: TypeVarSet<ResolvedName> =
            input.vars.iter().map(|v| TypeVar::Explicit(*v)).collect();

        let typ = self.typecheck_type_expr(&input.typ);

        TypeScheme { vars, typ }
    }

    fn typecheck_type_expr(&mut self, input: &ast::TypeExpr<ResolvedName>) -> Type {
        match input {
            ast::TypeExpr::Term(term) => self.typecheck_type_term(term),
            ast::TypeExpr::App(f, x) => Type::App(
                Box::new(self.typecheck_type_expr(f)),
                Box::new(self.typecheck_type_expr(x)),
            ),
            ast::TypeExpr::Arrow(a, b) => Type::Arrow(
                Box::new(self.typecheck_type_expr(a)),
                Box::new(self.typecheck_type_expr(b)),
            ),
        }
    }

    fn typecheck_type_term(&mut self, input: &ast::TypeTerm<ResolvedName>) -> Type {
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

            ast::TypeTerm::Parens(e) => self.typecheck_type_expr(e),

            ast::TypeTerm::List(e) => Type::List(Box::new(self.typecheck_type_expr(e))),

            ast::TypeTerm::Tuple(exprs) => {
                Type::Tuple(exprs.iter().map(|e| self.typecheck_type_expr(e)).collect())
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

            ast::Pattern::Int(_) => Type::Primitive(Primitive::Int),
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
                log::trace!(
                    log::TYPECHECK,
                    "      Bound (mono): {} to type {}",
                    name,
                    typ
                );
            }
        }
    }

    /// Binds (polymorphically) any assumptions about the given name to the given type.
    fn bind_assumptions_poly(&mut self, name: &ResolvedName, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                let constraint = Constraint::ImplicitInstance(
                    assumed,
                    typ.clone(),
                    self.m_stack.iter().cloned().collect(),
                );
                log::trace!(log::TYPECHECK, "      Bound (poly) {name}: {constraint:?}");
                self.constraints.add(constraint);
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
            for (import_path, import_items) in module.imports.iter() {
                // Get the imported module.
                let import_module = &self.modules[import_path];

                // Constrain that each assumed type is an instance of the name's inferred type.
                for import_item in import_items {
                    match import_item {
                        ast::ImportItem::Value { ident, name } => {
                            // Find the inferred type.
                            let typ = import_module
                                .definitions
                                .get(name)
                                .map(|defn| defn.typ.clone())
                                .expect("should have resolved this name to a value");

                            // If there are any assumptions about the variable, bind them.
                            if let Some(assumed_types) = self.assumptions.remove(name) {
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
                                // @Note: it's possible that a name could be used,
                                // and still not have any assumptions drawn about its type;
                                // so this doesn't necessarily mean it's unused.
                                if import_path != &ModulePath("Prelude") {
                                    // log::warn!(log::IMPORT, "unused: import {import_path} ({import_name})");
                                }
                            }
                        }
                        ast::ImportItem::Type {
                            ident,
                            name,
                            constructors,
                        } => {
                            for (cons_name, _cons_ident) in constructors {
                                let typ = import_module
                                    .constructors
                                    .get(cons_name)
                                    .map(|constr_defn| constr_defn.typ.clone())
                                    .expect("should have resolved this name to a type constructor");

                                // If there are any assumptions about the constructor, bind them.
                                if let Some(assumed_types) = self.assumptions.remove(cons_name) {
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
                                    // @Note: it's possible that a name could be used,
                                    // and still not have any assumptions drawn about its type;
                                    // so this doesn't necessarily mean it's unused.
                                    if import_path != &ModulePath("Prelude") {
                                        // log::warn!(log::IMPORT, "unused: import {import_path} ({import_name})");
                                    }
                                }
                            }
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

        Ok(())
    }
}

trait ActiveVars {
    fn active_vars(&self) -> TypeVarSet<ResolvedName>;
}

impl ActiveVars for Constraint {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        match self {
            Constraint::Equality(t1, t2) => t1.free_vars().union(&t2.free_vars()),
            Constraint::ExplicitInstance(t, sigma) => t.free_vars().union(&sigma.free_vars()),
            Constraint::ImplicitInstance(t1, t2, m) => {
                t1.free_vars().union(&m.intersection(&t2.free_vars()))
            }
        }
    }
}

impl ActiveVars for ConstraintSet {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        // @Note: in particular, we don't include explicit constraints in active vars.
        self.constraints.active_vars()
    }
}

impl<C: ActiveVars> ActiveVars for [(C, usize)] {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        self.iter()
            .map(|(c, _id)| c.active_vars())
            .reduce(|vars1, vars2| vars1.union(&vars2))
            .unwrap_or_else(TypeVarSet::empty)
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
    fn unify(self, other: Self) -> Result<Substitution, Error> {
        let mut sub = Substitution::empty();

        let mut pairs = vec![(self.clone(), other.clone())];

        while let Some((a, b)) = pairs.pop() {
            match (a, b) {
                (t1, t2) if t1 == t2 => (),

                (Type::Var(var), t) | (t, Type::Var(var)) => {
                    if t.free_vars().contains(&var) {
                        return Err(Error::CouldNotUnifyRecursive(
                            t,
                            Type::Var(var),
                            self,
                            other,
                        ));
                    } else {
                        let s = Substitution::single(var, t.clone());
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
                (t1, t2) => {
                    return Err(Error::CouldNotUnify(t1, t2, self, other));
                }
            }
        }

        Ok(sub)
    }

    /// Finds a unifier which substitutes the inferred type (self) into the explicit type.
    fn explicit(self, explicit: Self) -> Result<Substitution, Error> {
        let mut sub = Substitution::empty();

        let mut pairs = vec![(self.clone(), explicit.clone())];

        while let Some((a, b)) = pairs.pop() {
            match (a, b) {
                (t1, t2) if t1 == t2 => (),

                (Type::Var(var), t) if !explicit.free_vars().contains(&var) => {
                    if t.free_vars().contains(&var) {
                        return Err(Error::CouldNotUnifyRecursive(
                            t,
                            Type::Var(var),
                            self,
                            explicit,
                        ));
                    } else {
                        let s = Substitution::single(var, t.clone());
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
                (t1, t2) => {
                    return Err(Error::CouldNotUnifyExplicit(t1, t2, self, explicit));
                }
            }
        }

        #[cfg(debug_assertions)]
        {
            // Check that the substitution we've built
            // doesn't modify the explicit type at all.
            let mut explicit_post_sub = explicit.clone();
            explicit_post_sub.apply(&sub);
            assert_eq!(explicit, explicit_post_sub);
        }

        Ok(sub)
    }
}

impl TypeScheme {
    fn free_vars(&self) -> TypeVarSet<ResolvedName> {
        self.typ.free_vars().difference(&self.vars)
    }
}
