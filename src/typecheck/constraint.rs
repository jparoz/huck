use std::collections::{BTreeMap, VecDeque};
use std::fmt::{self, Debug, Write};
use std::iter;

use crate::ast::{self, Assignment, Expr, Lhs, Numeral, Pattern, Term};
use crate::log;
use crate::name::{ResolvedName, Source};
use crate::types::{Primitive, Type, TypeScheme, TypeVar, TypeVarSet};

use super::substitution::{ApplySub, Substitution};

#[derive(PartialEq, Eq, Clone)]
pub enum Constraint {
    Equality(Type, Type),
    ImplicitInstance(Type, Type, TypeVarSet),
    ExplicitInstance(Type, TypeScheme),
}

trait ActiveVars {
    fn active_vars(&self) -> TypeVarSet;
}

impl ActiveVars for Constraint {
    fn active_vars(&self) -> TypeVarSet {
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
    fn active_vars(&self) -> TypeVarSet {
        self.iter()
            .map(Constraint::active_vars)
            .reduce(|vars1, vars2| vars1.union(&vars2))
            .unwrap_or_else(TypeVarSet::empty)
    }
}

impl ActiveVars for VecDeque<Constraint> {
    fn active_vars(&self) -> TypeVarSet {
        let (a, b) = self.as_slices();
        a.active_vars().union(&b.active_vars())
    }
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

#[derive(Debug, Default)]
pub struct ConstraintGenerator {
    constraints: Vec<Constraint>,

    /// All the currently assumed types of name uses.
    pub(super) assumptions: BTreeMap<ResolvedName, Vec<Type>>,

    m_stack: Vec<TypeVar>,
}

impl ConstraintGenerator {
    /// Generates a new and unique TypeVar each time it's called.
    fn fresh_var(&mut self) -> TypeVar {
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

    pub fn equate(&mut self, a: Type, b: Type) {
        self.constrain(Constraint::Equality(a, b));
    }

    pub fn implicit_instance(&mut self, a: Type, b: Type) {
        self.constrain(Constraint::ImplicitInstance(
            a,
            b,
            self.m_stack.iter().cloned().collect(),
        ));
    }

    pub fn explicit_instance(&mut self, tau: Type, sigma: TypeScheme) {
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

    /// Returns the type of the whole pattern item, as well as emitting constraints for sub-items.
    fn bind_pattern(&mut self, pat: &Pattern<ResolvedName>) -> Type {
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
            Pattern::Bind(name) => {
                let beta = self.fresh();
                self.bind_assumptions_mono(name, &beta);
                beta
            }

            Pattern::List(pats) => {
                let beta = self.fresh();

                for pat in pats {
                    let typ = self.bind_pattern(pat);
                    self.constraints
                        .push(Constraint::Equality(beta.clone(), typ));
                }

                Type::List(Box::new(beta))
            }
            Pattern::Tuple(pats) => {
                Type::Tuple(pats.iter().map(|pat| self.bind_pattern(pat)).collect())
            }

            Pattern::Numeral(Numeral::Int(_)) => Type::Primitive(Primitive::Int),
            Pattern::Numeral(Numeral::Float(_)) => Type::Primitive(Primitive::Float),
            Pattern::String(_) => Type::Primitive(Primitive::String),
            Pattern::Unit => Type::Primitive(Primitive::Unit),

            Pattern::Binop { operator, lhs, rhs } => {
                let beta = self.fresh();
                self.assume(*operator, beta.clone());
                bind_function_args!(beta, iter::once(lhs).chain(iter::once(rhs)))
            }

            Pattern::UnaryConstructor(name) => {
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
            Pattern::Destructure { constructor, args } => {
                let beta = self.fresh();
                self.assume(*constructor, beta.clone());
                bind_function_args!(beta, args.iter())
            }
        }
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
                    self.m_stack.iter().cloned().collect::<TypeVarSet>()
                );
            }
        }
    }

    pub fn solve(&mut self) -> Result<Substitution, crate::typecheck::Error> {
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
                    let new_constraint = Constraint::Equality(t, self.instantiate(ts));
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

    pub fn generate_definition(&mut self, definition: &ast::Definition<ResolvedName, ()>) -> Type {
        // Typecheck each assignment in the definition.
        let mut typs: Vec<Type> = definition
            .assignments
            .iter()
            .map(|assign| self.generate_assignment(assign))
            .collect();

        // If there's an explicit type, include that as well.
        if let Some(ref explicit_type_scheme) = definition.explicit_type {
            let ts = self.generate_type_scheme(explicit_type_scheme);
            typs.push(self.instantiate(ts));
        }

        // Constrain that each inferred assignment,
        // and the explicit type,
        // should all be equal.
        self.equate_all(typs)
    }

    pub fn generate_assignment(&mut self, assign: &Assignment<ResolvedName>) -> Type {
        let (lhs, expr) = assign;

        match lhs {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => {
                args.iter()
                    .rev()
                    .fold(self.generate_expr(expr), |acc, arg| {
                        let beta = self.bind_pattern(arg);
                        Type::Arrow(Box::new(beta), Box::new(acc))
                    })
            }
            Lhs::Binop { a, b, .. } => {
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

    pub fn generate_expr(&mut self, expr: &Expr<ResolvedName>) -> Type {
        match expr {
            Expr::Term(Term::Numeral(Numeral::Int(_))) => Type::Primitive(Primitive::Int),
            Expr::Term(Term::Numeral(Numeral::Float(_))) => Type::Primitive(Primitive::Float),
            Expr::Term(Term::String(_)) => Type::Primitive(Primitive::String),
            Expr::Term(Term::Unit) => Type::Primitive(Primitive::Unit),

            Expr::Term(Term::Parens(e)) => self.generate_expr(e),
            Expr::Term(Term::List(es)) => {
                let beta = self.fresh();
                for e in es {
                    let e_type = self.generate_expr(e);
                    self.constrain(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }
            Expr::Term(Term::Tuple(es)) => {
                Type::Tuple(es.iter().map(|e| self.generate_expr(e)).collect())
            }

            Expr::Term(Term::Name(name)) => {
                let typ = self.fresh();
                self.assume(*name, typ.clone());
                typ
            }

            Expr::App { func, argument } => {
                let t1 = self.generate_expr(func);
                let t2 = self.generate_expr(argument);
                let beta = self.fresh();

                self.constrain(Constraint::Equality(
                    t1,
                    Type::Arrow(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            Expr::Binop { operator, lhs, rhs } => {
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

            Expr::Let {
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

            Expr::If {
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

            Expr::Case { expr, arms } => {
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

            Expr::Lambda { lhs, rhs } => {
                let args = lhs.args();
                let typevars: Vec<TypeVar> = args.iter().map(|_| self.fresh_var()).collect();
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

            Expr::Lua(_) => Type::App(
                Box::new(Type::Primitive(Primitive::IO)),
                Box::new(self.fresh()),
            ),

            Expr::UnsafeLua(_) => self.fresh(),
        }
    }

    // Type-level generation methods

    pub fn generate_type_scheme(&mut self, input: &ast::TypeScheme<ResolvedName>) -> TypeScheme {
        let vars: TypeVarSet = input.vars.iter().map(|v| TypeVar::Explicit(v)).collect();

        let typ = self.generate_type_expr(&input.typ);

        TypeScheme { vars, typ }
    }

    pub fn generate_type_definition(
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

    pub fn generate_type_expr(&mut self, input: &ast::TypeExpr<ResolvedName>) -> Type {
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

    pub fn generate_type_term(&mut self, input: &ast::TypeTerm<ResolvedName>) -> Type {
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

            ast::TypeTerm::Var(v) => Type::Var(TypeVar::Explicit(v)),

            ast::TypeTerm::Parens(e) => self.generate_type_expr(e),
            ast::TypeTerm::List(e) => Type::List(Box::new(self.generate_type_expr(e))),
            ast::TypeTerm::Tuple(exprs) => {
                Type::Tuple(exprs.iter().map(|e| self.generate_type_expr(e)).collect())
            }
        }
    }
}
