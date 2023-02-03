use std::collections::VecDeque;
use std::fmt::{self, Debug, Write};
use std::{collections::BTreeMap, time::Instant};
use std::{iter, mem};

use crate::module::{Module, ModulePath};
use crate::name::{ResolvedName, Source};
use crate::types::{self, Primitive, Type, TypeScheme, TypeVar, TypeVarSet};
use crate::{ast, log};

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
    let prelude = modules
        .remove(&prelude_path)
        .into_iter()
        .map(|m| (prelude_path, m));

    let mut typechecked_modules = BTreeMap::new();

    for (module_path, module) in prelude.chain(modules.into_iter()) {
        log::trace!(log::TYPECHECK, "Typechecking: module {module_path};");
        // Set the new `Module`'s path.
        let mut typechecked_module = Module::new(module_path);

        // Generate constraints for each definition, while keeping track of inferred types
        for (name, defn) in module.definitions {
            log::trace!(log::TYPECHECK, "Inferring type for {name}");

            let typ = typechecker.generate_definition(&defn);

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
            let type_defn = typechecker.generate_type_definition(ast_type_defn);

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
                "Inserting into scope of {module_path}: import {path} ({names:?})"
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
                         foreign import {require_string} ({foreign_name} as {name})"
                );
                // @Errors: check for name clashes
                typechecked_module
                    .foreign_imports
                    .entry(require_string)
                    .or_default()
                    .push(ast::ForeignImportItem {
                        foreign_name,
                        name,
                        typ: typechecker.generate_type_scheme(&type_scheme).instantiate(),
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
        if module_path != prelude_path {
            log::trace!(
                log::IMPORT,
                "Importing contents of Prelude into {module_path}"
            );
            let prelude_gm: &Module<ResolvedName, Type> = &typechecked_modules[&prelude_path];

            // @Errors @Warn: name clashes
            typechecked_module
                .imports
                .entry(prelude_path)
                .or_default()
                .extend(
                    prelude_gm
                        .definitions
                        .keys()
                        .chain(prelude_gm.constructors.keys()),
                );
        }

        // Polymorphically bind all top-level names.
        // If any assumptions were found to be imported,
        // their assumptions are promoted to cross-module level by this method.
        typechecker.bind_all_module_assumptions(&typechecked_module)?;

        // Add the Module<ResolvedName, Type> to the context.
        assert!(typechecked_modules
            .insert(module_path, typechecked_module)
            .is_none());
    }

    // Constrain any names which were promoted to the cross-module level (i.e. imported names).
    typechecker.bind_all_import_assumptions(&typechecked_modules)?;

    // Solve the type constraints
    let soln = typechecker.solve()?;

    // Apply the solution to each Module<ResolvedName, Type>.
    for module in typechecked_modules.values_mut() {
        log::info!(log::TYPECHECK, "module {}:", module.path);
        for (name, ref mut definition) in module.definitions.iter_mut() {
            definition.typ.apply(&soln);
            log::info!(
                log::TYPECHECK,
                "  Inferred type for {name} : {}",
                definition.typ
            );
        }
    }

    log::info!(
        log::METRICS,
        "Typechecking completed, {:?} elapsed",
        start_time.elapsed()
    );

    Ok(typechecked_modules)
}

#[derive(PartialEq, Eq, Clone)]
enum Constraint {
    Equality(Type, Type),
    ImplicitInstance(Type, Type, TypeVarSet<ResolvedName>),
    ExplicitInstance(Type, TypeScheme),
}

impl Debug for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(a, b) => write!(f, "{} ≡ {}", a, b),
            Constraint::ImplicitInstance(a, b, m) => {
                write!(f, "{} ≤ {} where M is {}", a, b, m)
            }
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{} ≼ {}", tau, sigma)
            }
        }
    }
}

/// Manages typechecking of a group of modules.
#[derive(Debug, Default)]
struct Typechecker {
    /// All of the emitted constraints about the modules being typechecked.
    /// These are solved in [`Typechecker::solve`].
    constraints: Vec<Constraint>,

    /// All the currently assumed types of name uses.
    assumptions: BTreeMap<ResolvedName, Vec<Type>>,

    /// Assumptions which need to cross module boundaries to be checked.
    import_assumptions: BTreeMap<ResolvedName, Vec<Type>>,

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

    fn assume(&mut self, name: ResolvedName, typ: Type) {
        log::trace!(log::TYPECHECK, "Assuming type: {} : {}", name, typ);
        self.assumptions
            .entry(name)
            .or_insert_with(|| Vec::with_capacity(1))
            .push(typ);
    }

    fn constrain(&mut self, constraint: Constraint) {
        log::trace!(log::TYPECHECK, "Emitting constraint: {:?}", constraint);
        self.constraints.push(constraint);
    }

    fn equate(&mut self, a: Type, b: Type) {
        self.constrain(Constraint::Equality(a, b));
    }

    fn implicit_instance(&mut self, a: Type, b: Type) {
        self.constrain(Constraint::ImplicitInstance(
            a,
            b,
            self.m_stack.iter().cloned().collect(),
        ));
    }

    fn explicit_instance(&mut self, tau: Type, sigma: TypeScheme) {
        self.constrain(Constraint::ExplicitInstance(tau, sigma));
    }

    /// Constrains all types in the given Vec to be equal, and returns that type.
    fn equate_all(&mut self, typs: Vec<Type>) -> Type {
        if typs.len() == 1 {
            return typs[0].clone();
        }

        let beta = self.fresh();
        for typ in typs {
            self.constrain(Constraint::Equality(beta.clone(), typ.clone()));
        }
        beta
    }

    /// Solves the constraints which have been generated,
    /// and return the solution `Substitution`.
    fn solve(&mut self) -> Result<Substitution, crate::typecheck::Error> {
        log::trace!(
            log::TYPECHECK,
            "Called ConstraintGenerator::solve, starting constraints:"
        );
        for constraint in self.constraints.iter() {
            log::trace!(log::TYPECHECK, "  {:?}", constraint);
        }

        log::trace!(log::TYPECHECK, "{:-^100}", " START SOLVING ");
        let mut solution = Substitution::empty();

        let mut constraints = VecDeque::from(self.constraints.clone());

        while let Some(constraint) = constraints.pop_front() {
            let constraint_str = format!("{constraint:?}");
            let mut new_str = String::new();

            match constraint {
                Constraint::Equality(t1, t2) => {
                    let new_sub = t1.unify(t2)?;

                    for c in constraints.iter_mut() {
                        c.apply(&new_sub);
                    }

                    write!(new_str, "{new_sub:?}").unwrap();
                    solution = new_sub.then(solution);
                }

                Constraint::ExplicitInstance(t, ts) => {
                    let new_constraint = Constraint::Equality(t, ts.instantiate());
                    write!(new_str, "{new_constraint:?}").unwrap();
                    constraints.push_back(new_constraint)
                }

                Constraint::ImplicitInstance(t1, t2, m)
                    if t2
                        .free_vars()
                        .difference(&m)
                        .intersection(&constraints.active_vars())
                        .is_empty() =>
                {
                    let new_constraint = Constraint::ExplicitInstance(t1, t2.generalize(&m));
                    write!(new_str, "{new_constraint:?}").unwrap();
                    constraints.push_back(new_constraint)
                }

                constraint @ Constraint::ImplicitInstance(..) => {
                    // @Note: This should never diverge, i.e. there should always be at least one
                    // constraint in the set that meets the criteria to be solvable. See HHS02.
                    write!(new_str, "[Skipping for now]").unwrap();
                    constraints.push_back(constraint);
                }
            }

            log::trace!(log::TYPECHECK, "{constraint_str:>60} ==> {new_str}");
        }

        log::trace!(log::TYPECHECK, "{:-^100}", " FINISH SOLVING ");
        log::trace!(log::TYPECHECK, "Solution:");
        for (fr, to) in solution.iter() {
            log::trace!(log::TYPECHECK, "  {} ↦ {}", fr, to);
        }

        Ok(solution)
    }

    // Generation methods

    fn generate_definition(&mut self, definition: &ast::Definition<ResolvedName, ()>) -> Type {
        // Typecheck each assignment in the definition.
        let mut typs: Vec<Type> = definition
            .assignments
            .iter()
            .map(|assign| self.generate_assignment(assign))
            .collect();

        // If there's an explicit type, include that as well.
        if let Some(ref explicit_type_scheme) = definition.explicit_type {
            log::trace!(
                log::TYPECHECK,
                "Including explicit type scheme: {explicit_type_scheme:?}",
            );
            let ts = self.generate_type_scheme(explicit_type_scheme);
            typs.push(ts.instantiate());
        }

        // Constrain that each inferred assignment,
        // and the explicit type,
        // should all be equal.
        self.equate_all(typs)
    }

    fn generate_assignment(&mut self, assign: &ast::Assignment<ResolvedName>) -> Type {
        let (lhs, expr) = assign;

        match lhs {
            ast::Lhs::Func { args, .. } | ast::Lhs::Lambda { args } => {
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

            ast::Expr::Term(ast::Term::Parens(e)) => self.generate_expr(e),
            ast::Expr::Term(ast::Term::List(es)) => {
                let beta = self.fresh();
                for e in es {
                    let e_type = self.generate_expr(e);
                    self.constrain(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }
            ast::Expr::Term(ast::Term::Tuple(es)) => {
                Type::Tuple(es.iter().map(|e| self.generate_expr(e)).collect())
            }

            ast::Expr::Term(ast::Term::Name(name)) => {
                let typ = self.fresh();
                self.assume(*name, typ.clone());
                typ
            }

            ast::Expr::App { func, argument } => {
                let t1 = self.generate_expr(func);
                let t2 = self.generate_expr(argument);
                let beta = self.fresh();

                self.constrain(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                let t1 = self.fresh();
                self.assume(*operator, t1.clone());
                let t2 = self.generate_expr(lhs);
                let t3 = self.generate_expr(rhs);
                let beta1 = self.fresh();
                let beta2 = self.fresh();

                self.constrain(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta1.clone())),
                ));
                self.constrain(Constraint::Equality(
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

                // @Note: This constraint elevates the type Bool to being a part of the compiler.
                // This may or may not be what we want;
                // possibly we should remain agnostic about the concrete type,
                // by simply converting `if`s to `case`s by syntactic sugar;
                // then (in theory) the Bool type can be redefined as appropriate.
                // All that said, what is the possibly utility this can provide?
                // It's not as though we can remain morally superior
                // by avoiding elevating any types to compiler status
                // (see Int, Float);
                // so perhaps it's fine to just add Bool to that list.
                self.constrain(Constraint::Equality(
                    cond_type,
                    Type::Primitive(Primitive::Bool),
                ));
                self.constrain(Constraint::Equality(then_type.clone(), else_type));

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

            ast::Expr::Lambda { lhs, rhs } => {
                let args = lhs.args();
                let typevars: Vec<TypeVar<ResolvedName>> =
                    args.iter().map(|_| self.fresh_var()).collect();
                let types: Vec<Type> = typevars.iter().map(|v| Type::Var(v.clone())).collect();
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
                    self.constrain(Constraint::Equality(actual_type, lambda_type))
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
            typ = Type::App(Box::new(typ), Box::new(Type::Var(var.clone())));
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

                    self.constrain(Constraint::Equality(acc, partial_cons_type));

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
            ast::Pattern::Underscore => self.fresh(),

            ast::Pattern::List(pats) => {
                let beta = self.fresh();

                for pat in pats {
                    let typ = self.bind_pattern(pat);
                    self.constraints
                        .push(Constraint::Equality(beta.clone(), typ));
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
                let beta = self.fresh();
                self.assume(*operator, beta.clone());
                bind_function_args!(beta, iter::once(lhs).chain(iter::once(rhs)))
            }

            ast::Pattern::UnaryConstructor(name) => {
                // @Cleanup: is this the only place this can go?
                if name.source == Source::Builtin && (name.ident == "True" || name.ident == "False")
                {
                    let typ = Type::Primitive(Primitive::Bool);
                    self.assume(*name, typ.clone());
                    typ
                } else {
                    let beta = self.fresh();
                    self.assume(*name, beta.clone());
                    beta
                }
            }
            ast::Pattern::Destructure { constructor, args } => {
                let beta = self.fresh();
                self.assume(*constructor, beta.clone());
                bind_function_args!(beta, args.iter())
            }
        }
    }

    /// Binds all top level assumptions to the types found in their definition.
    ///
    /// If the name isn't defined in this module, check if it's imported;
    /// if it is, then this assumption is promoted to cross-module level.
    fn bind_all_module_assumptions(
        &mut self,
        module: &Module<ResolvedName, Type>,
    ) -> Result<(), Error> {
        log::trace!(log::TYPECHECK, "Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.assumptions);

        for (assumed_name, assumed_types) in assumptions {
            if let Some(typ) = module.get_type(&assumed_name) {
                // This means that it was defined in this module.
                for assumed_type in assumed_types {
                    self.implicit_instance(assumed_type, typ.clone());
                }
            } else if let Source::Foreign { require, .. } = assumed_name.source {
                // This means that the name was imported from a foreign (Lua) module;
                // this means that the Huck author gave an explicit type signature at the import.

                let imports = module
                    .foreign_imports
                    .get(require)
                    .expect("should already be resolved");

                for ast::ForeignImportItem { name, typ, .. } in imports {
                    if name == &assumed_name {
                        for assumed_type in assumed_types.iter() {
                            self.explicit_instance(
                                assumed_type.clone(),
                                // @Note: we're just replacing the type variables which are
                                // thrown away when inserting foreign imports into the scope.
                                // This could possibly be done in a more sensible way;
                                // but this is at least consistent and correct.
                                typ.clone().generalize(&TypeVarSet::empty()),
                            );
                        }
                    }
                }
            } else if assumed_name.source == Source::Builtin {
                // @Cleanup: @DRY with Pattern::UnaryConstructor branch
                // in ConstraintGenerator::bind_pattern

                // This means that it's a compiler builtin.
                match assumed_name.ident {
                    "True" | "False" => assumed_types
                        .into_iter()
                        .for_each(|t| self.equate(t, Type::Primitive(types::Primitive::Bool))),
                    _ => unreachable!("missing a compiler builtin type"),
                }
            } else {
                // This means that the name was imported from another Huck module;
                // so we need to resolve it at cross-module level later.
                // We do this by pushing it into self.import_assumptions.
                self.import_assumptions
                    .entry(assumed_name)
                    .or_default()
                    .extend(assumed_types);
            }
        }

        Ok(())
    }

    /// Binds all cross-module-level assumptions (i.e. from imported names).
    //
    // @Note:
    // We used to do this in a similar way to bind_all_module_level_assumptions,
    // by iterating over self.assumptions and binding the names as they appear there.
    // However, this didn't catch the error where
    // an import was unused and also didn't exist in the imported module.
    // By instead iterating over each modules's imported names,
    // we ensure that all imports exist, whether they're used or not.
    fn bind_all_import_assumptions(
        &mut self,
        modules: &BTreeMap<ModulePath, Module<ResolvedName, Type>>,
    ) -> Result<(), Error> {
        log::trace!(
            log::TYPECHECK,
            "Emitting constraints about context-level assumptions:"
        );

        for module in modules.values() {
            // Constrain the types of all assumed types to the inferred type of the name.
            for (import_path, import_names) in module.imports.iter() {
                // Get the imported module.
                // @Note: this should be infallable,
                // because we've already confirmed that this module exists in the resolve step.
                let import_module = modules
                    .get(import_path)
                    .expect("should already be resolved");

                // Constrain that each assumed type is an instance of the name's inferred type.
                for import_name in import_names {
                    // Find the inferred type.
                    // @Note: this should be infallable,
                    // because we've already confirmed everything exists in the resolve step.
                    let typ = import_module
                        .get_type(import_name)
                        .expect("should already be resolved and typechecked");

                    // If there are any assumptions about the variable, bind them.
                    if let Some(assumed_types) = self.import_assumptions.remove(import_name) {
                        // Constrain that the assumed types are instances of the inferred type.
                        for assumed_type in assumed_types {
                            self.implicit_instance(assumed_type, typ.clone());
                        }
                    } else {
                        // @Errors @Warn: emit a warning for unused imports
                        if import_path != &ModulePath("Prelude") {
                            log::warn!(log::IMPORT, "unused: import {import_path} ({import_name})");
                        }
                    }
                }
            }
        }

        // Checks all the assumptions are true within the given modules.
        self.arity_checker.finish(modules)?;

        Ok(())
    }

    /// Binds (monomorphically) any assumptions about the given name to the given type.
    fn bind_assumptions_mono(&mut self, name: &ResolvedName, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::Equality(assumed, typ.clone()));
                log::trace!(log::TYPECHECK, "Bound (mono): {} to type {}", name, typ);
            }
        }
    }

    /// Binds (polymorphically) any assumptions about the given name to the given type.
    fn bind_assumptions_poly(&mut self, name: &ResolvedName, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::ImplicitInstance(
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

impl ActiveVars for &[Constraint] {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        self.iter()
            .map(Constraint::active_vars)
            .reduce(|vars1, vars2| vars1.union(&vars2))
            .unwrap_or_else(TypeVarSet::empty)
    }
}

impl ActiveVars for VecDeque<Constraint> {
    fn active_vars(&self) -> TypeVarSet<ResolvedName> {
        let (a, b) = self.as_slices();
        a.active_vars().union(&b.active_vars())
    }
}

impl Type {
    fn free_vars(&self) -> TypeVarSet<ResolvedName> {
        match self {
            Type::Concrete(_) | Type::Primitive(_) => TypeVarSet::empty(),

            Type::Var(var) => TypeVarSet::single(var.clone()),
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

        let mut pairs = vec![(self, other)];

        while let Some((a, b)) = pairs.pop() {
            match (a, b) {
                (t1, t2) if t1 == t2 => (),
                (Type::Var(var), t) | (t, Type::Var(var)) => {
                    if t.free_vars().contains(&var) {
                        // @CheckMe
                        return Err(Error::CouldNotUnifyRecursive(t, Type::Var(var)));
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
                (t1, t2) => return Err(Error::CouldNotUnify(t1, t2)),
            }
        }

        Ok(sub)
    }
}

impl TypeScheme {
    fn free_vars(&self) -> TypeVarSet<ResolvedName> {
        self.typ.free_vars().difference(&self.vars)
    }

    /// Takes a `TypeScheme` and throws away the quantifier.
    /// This is equivalent to replacing the quantified variables
    /// with new free variables,
    /// but it better preserves variable names.
    // @Note: The doc comment here used to read:
    //
    // Takes a TypeScheme and replaces all quantified variables with fresh variables;
    // then returns the resulting Type.
    //
    // The current implementation doesn't do this;
    // it simply drops the quantification.
    // This is equivalent to the previous behaviour,
    // because it turns all the quantified variables into free variables,
    // just without renaming them.
    #[inline]
    fn instantiate(self) -> Type {
        self.typ
    }
}
