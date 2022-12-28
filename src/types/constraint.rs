use std::collections::{BTreeMap, VecDeque};
use std::fmt::{self, Debug};
use std::{iter, mem};

use log::log_enabled;

use crate::ast::{self, Assignment, Definition, Expr, Lhs, Name, Numeral, Pattern, Term};
use crate::codegen::lua::is_lua_binop;
use crate::types::{
    self, ApplySub, Substitution, Type, TypeDefinition, TypeScheme, TypeVar, TypeVarSet,
};

pub trait ActiveVars {
    fn active_vars(&self) -> TypeVarSet;
}

#[derive(PartialEq, Eq, Clone)]
pub enum Constraint {
    Equality(Type, Type),
    ImplicitInstance(Type, Type, TypeVarSet),
    ExplicitInstance(Type, TypeScheme),
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
        self.into_iter()
            .map(Constraint::active_vars)
            .reduce(|vars1, vars2| vars1.union(&vars2))
            .unwrap_or(TypeVarSet::empty())
    }
}

impl ActiveVars for VecDeque<Constraint> {
    fn active_vars(&self) -> TypeVarSet {
        let (a, b) = self.as_slices();
        a.active_vars().union(&b.active_vars())
    }
}

impl<'file> Debug for Constraint {
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

pub struct ConstraintGenerator<'file> {
    constraints: Vec<Constraint>,

    // @Cleanup: shouldn't be pub
    pub assumptions: BTreeMap<Name, Vec<Type>>,

    /// Record of types inferred.
    // @Cleanup: manage this internally instead of in typecheck (??)
    pub types: BTreeMap<Name, (Type, Definition<'file>)>,

    /// Record of constructors defined.
    // @Cleanup: manage this internally instead of in typecheck (??)
    pub constructors: BTreeMap<Name, Type>,

    next_typevar_id: usize,
    m_stack: Vec<TypeVar>,
}

impl<'file> ConstraintGenerator<'file> {
    pub fn new() -> Self {
        ConstraintGenerator {
            constraints: Vec::new(),
            assumptions: BTreeMap::new(),
            types: BTreeMap::new(),
            constructors: BTreeMap::new(),
            next_typevar_id: 0,
            m_stack: Vec::new(),
        }
    }

    fn fresh_var(&mut self) -> TypeVar {
        let id = self.next_typevar_id;
        self.next_typevar_id += 1;
        TypeVar(id)
    }

    fn fresh(&mut self) -> Type {
        Type::Var(self.fresh_var())
    }

    fn assume(&mut self, name: Name, typ: Type) {
        log::trace!("Assuming type: {} : {}", name, typ);
        self.assumptions
            .entry(name)
            .or_insert(Vec::with_capacity(1))
            .push(typ);
    }

    pub fn constrain(&mut self, constraint: Constraint) {
        log::trace!("Emitting constraint: {:?}", constraint);
        self.constraints.push(constraint);
    }

    /// Constrains all types in the given Vec to be equal, and returns that type.
    pub fn equate_all(&mut self, typs: Vec<Type>) -> Type {
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
    pub fn instantiate(&mut self, mut ts: TypeScheme) -> Type {
        let sub = ts.vars.into_iter().fold(Substitution::empty(), |sub, var| {
            sub.then(Substitution::single(var, self.fresh()))
        });
        ts.typ.apply(&sub);
        ts.typ
    }

    /// Returns the type of the whole pattern item, as well as emitting constraints for sub-items.
    fn bind(&mut self, pat: &Pattern) -> Type {
        macro_rules! bind_function_args {
            ($cons_type:expr, $iter:expr) => {
                $iter.fold($cons_type, |acc, arg| {
                    let arg_type = self.bind(arg);
                    let partial_res_type = self.fresh();
                    let partial_cons_type =
                        Type::Arrow(Box::new(arg_type), Box::new(partial_res_type.clone()));

                    self.constrain(Constraint::Equality(acc, partial_cons_type));

                    partial_res_type
                })
            };
        }

        match pat {
            Pattern::Bind(s) => {
                let beta = self.fresh();
                self.bind_name_mono(&Name::Ident(s.to_string()), &beta);
                beta
            }

            Pattern::List(pats) => {
                let beta = self.fresh();

                for pat in pats {
                    let typ = self.bind(pat);
                    self.constraints
                        .push(Constraint::Equality(beta.clone(), typ));
                }

                Type::List(Box::new(beta))
            }
            Pattern::Tuple(pats) => Type::Tuple(pats.iter().map(|pat| self.bind(pat)).collect()),

            Pattern::Numeral(Numeral::Int(_)) => Type::Concrete("Int".to_string()),
            Pattern::Numeral(Numeral::Float(_)) => Type::Concrete("Float".to_string()),
            Pattern::String(_) => Type::Concrete("Float".to_string()),
            Pattern::Unit => Type::Concrete("()".to_string()),

            Pattern::Binop { operator, lhs, rhs } => {
                let beta = self.fresh();
                self.assume(operator.clone(), beta.clone());
                bind_function_args!(beta, iter::once(lhs).chain(iter::once(rhs)))
            }

            Pattern::UnaryConstructor(name) => {
                let beta = self.fresh();
                self.assume(name.clone(), beta.clone());
                beta
            }
            Pattern::Destructure { constructor, args } => {
                let beta = self.fresh();
                self.assume(constructor.clone(), beta.clone());
                bind_function_args!(beta, args.iter())
            }
        }
    }

    fn bind_name_mono(&mut self, name: &Name, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::Equality(assumed, typ.clone()));
                log::trace!("Bound (mono): {} to type {}", name, typ);
            }
        }
    }

    fn bind_name_poly(&mut self, name: &Name, typ: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::ImplicitInstance(
                    assumed,
                    typ.clone(),
                    self.m_stack.iter().cloned().collect(),
                ));
                log::trace!(
                    "Bound (poly): {} to type {} (M = {})",
                    name,
                    typ,
                    self.m_stack.iter().cloned().collect::<TypeVarSet>()
                );
            }
        }
    }

    pub fn bind_all_top_level(&mut self) {
        log::trace!("Emitting constraints about assumptions:");

        let mut assumptions = BTreeMap::new();
        mem::swap(&mut assumptions, &mut self.assumptions);

        // @Todo @Cleanup: this should possibly/probably work on Scope or some ProtoScope,
        // rather than multiple if lets.
        for (name, assumed_types) in assumptions {
            if let Some((typ, _defn)) = self.types.get(&name) {
                // self.bind_name_poly(&name, &t.0); // @Checkme: poly or mono?
                for assumed_type in assumed_types {
                    self.constraints.push(Constraint::ImplicitInstance(
                        assumed_type,
                        typ.clone(),
                        self.m_stack.iter().cloned().collect(),
                    ));
                }
            } else if let Some(typ) = self.constructors.get(&name) {
                // self.bind_name_poly(&name, &t); // @Checkme: poly or mono?
                for assumed_type in assumed_types {
                    self.constraints.push(Constraint::ImplicitInstance(
                        assumed_type,
                        typ.clone(),
                        self.m_stack.iter().cloned().collect(),
                    ));
                }
            } else if is_lua_binop(name.as_str()) {
                // Do nothing. @XXX @Cleanup: don't do this
                // @Prelude
            } else {
                // If there is no inferred type for the name (i.e. it's not in scope),
                // then it's a scope error.
                // @Errors: Scope error
                panic!("scope error: {name}");
            }
        }
    }

    pub fn solve(&mut self) -> Result<Substitution, types::Error> {
        log::trace!("START SOLVING");
        let mut sub = Substitution::empty();

        let mut constraints = VecDeque::from(self.constraints.clone());

        while let Some(c) = constraints.pop_front() {
            log::trace!("-");
            log::trace!("Looking at: {:?}", c);
            match c {
                Constraint::Equality(t1, t2) => {
                    let s = t1.unify(t2)?;

                    for c in constraints.iter_mut() {
                        c.apply(&s);
                    }

                    sub = s.then(sub);
                }

                Constraint::ExplicitInstance(t, ts) => {
                    let cons = Constraint::Equality(t, self.instantiate(ts));
                    log::trace!("Replacing with new constraint: {:?}", cons);
                    constraints.push_back(cons)
                }

                Constraint::ImplicitInstance(t1, t2, m)
                    if t2
                        .free_vars()
                        .difference(&m)
                        .intersection(&constraints.active_vars())
                        .is_empty() =>
                {
                    let cons = Constraint::ExplicitInstance(t1, t2.generalize(&m));
                    log::trace!("Replacing with new constraint: {:?}", cons);
                    constraints.push_back(cons)
                }

                c @ Constraint::ImplicitInstance(..) => {
                    // @Note: This should never diverge, i.e. there should always be at least one
                    // constraint in the set that meets the criteria to be solvable. See HHS02.
                    log::trace!("Skipping for now");
                    constraints.push_back(c);
                }
            }

            if log_enabled!(log::Level::Trace) {
                log::trace!("Substitution:");
                for (fr, to) in sub.iter() {
                    log::trace!("    {:?} ↦ {:?}", fr, to);
                }

                log::trace!("Constraints:");
                for c in constraints.iter() {
                    log::trace!("    {:?}", c);
                }
            }
        }

        log::trace!("-");
        log::trace!("FINISH SOLVING");
        log::trace!("{:?}", self);

        Ok(sub)
    }

    // Conversion methods

    pub fn convert_ast_type_scheme(&mut self, input: &ast::TypeScheme) -> TypeScheme {
        let mut vars_map = BTreeMap::new();
        let vars: TypeVarSet = input
            .vars
            .iter()
            .map(|v| {
                let fresh = self.fresh_var();
                // @Todo: at least assert is_none()
                vars_map.insert(*v, fresh);
                fresh
            })
            .collect();

        let typ = self.convert_ast_type_expr(&input.typ, &vars_map);

        TypeScheme { vars, typ }
    }

    pub fn convert_ast_type_definition(
        &mut self,
        type_defn: &ast::TypeDefinition<'file>,
    ) -> TypeDefinition {
        let ast::TypeDefinition {
            name,
            vars: vars_s,
            constructors: constrs,
        } = type_defn;

        // We'll build all these structures by iterating over the type arguments.
        let mut vars_map = BTreeMap::new();
        let mut vars = TypeVarSet::empty();
        let mut typ = Type::Concrete(name.to_string());

        for v in vars_s.iter() {
            // Make a new type variable to stand in for the &str literal type variable
            let fresh = self.fresh_var();

            // Store it in both the map and set versions
            vars_map.insert(*v, fresh);
            vars.insert(fresh);

            // The final returned type of the constructor needs to reflect this type argument;
            // so we mark that here.
            typ = Type::App(Box::new(typ), Box::new(Type::Var(fresh)));
        }

        let mut constructors = BTreeMap::new();

        for (constr_name, args) in constrs {
            let constr_type = args
                .into_iter()
                .rev()
                .map(|term| self.convert_ast_type_term(term, &vars_map))
                .fold(typ.clone(), |res, a| {
                    Type::Arrow(Box::new(a), Box::new(res))
                });

            // @Checkme: poly or mono?
            self.bind_name_poly(constr_name, &constr_type);

            // @Errors @Checkme: no name conflicts
            constructors.insert(constr_name.clone(), constr_type);
        }

        TypeDefinition {
            name: name.clone(),
            vars,
            typ,
            constructors,
        }
    }

    pub fn convert_ast_type_expr(
        &mut self,
        input: &ast::TypeExpr,
        vars_map: &BTreeMap<&str, TypeVar>,
    ) -> Type {
        match input {
            ast::TypeExpr::Term(term) => self.convert_ast_type_term(term, vars_map),
            ast::TypeExpr::App(f, x) => Type::App(
                Box::new(self.convert_ast_type_expr(f, vars_map)),
                Box::new(self.convert_ast_type_expr(x, vars_map)),
            ),
            ast::TypeExpr::Arrow(a, b) => Type::Arrow(
                Box::new(self.convert_ast_type_expr(a, vars_map)),
                Box::new(self.convert_ast_type_expr(b, vars_map)),
            ),
        }
    }

    pub fn convert_ast_type_term(
        &mut self,
        input: &ast::TypeTerm,
        vars_map: &BTreeMap<&str, TypeVar>,
    ) -> Type {
        match input {
            ast::TypeTerm::Concrete(s) => Type::Concrete(s.to_string()),
            ast::TypeTerm::Unit => Type::Concrete("()".to_string()),

            ast::TypeTerm::Var(v) => {
                if let Some(tv) = vars_map.get(v) {
                    Type::Var(*tv)
                } else {
                    // @Note: returning self.fresh() seems to give behaviour something like
                    // implcit forall. Further investigation is needed though if wanting to use.
                    // For now, just error instead.
                    // self.fresh()

                    // @Errors: ill-formed type expression (should be a syntax or scope error)
                    panic!(
                        "ill-formed type expression, type variable not in scope: {}",
                        v
                    )
                }
            }

            ast::TypeTerm::Parens(e) => self.convert_ast_type_expr(e, vars_map),
            ast::TypeTerm::List(e) => Type::List(Box::new(self.convert_ast_type_expr(e, vars_map))),
            ast::TypeTerm::Tuple(exprs) => Type::Tuple(
                exprs
                    .iter()
                    .map(|e| self.convert_ast_type_expr(e, vars_map))
                    .collect(),
            ),
        }
    }

    // Generation methods

    pub fn generate_definition(&mut self, definition: &Definition<'file>) -> Type {
        // Typecheck each assignment in the definition.
        let mut typs: Vec<Type> = definition
            .assignments
            .iter()
            .map(|assign| self.generate_assignment(assign))
            .collect();

        // If there's an explicit type, include that as well.
        if let Some(ref explicit_type_scheme) = definition.explicit_type {
            let ts = self.convert_ast_type_scheme(explicit_type_scheme);
            typs.push(self.instantiate(ts));
        }

        // Constrain that each inferred assignment,
        // and the explicit type,
        // should all be equal.
        self.equate_all(typs)
    }

    pub fn generate_assignment(&mut self, assign: &Assignment<'file>) -> Type {
        let (lhs, expr) = assign;

        macro_rules! bind {
            ($iter:expr) => {
                $iter.fold(self.generate_expr(expr), |acc, arg| {
                    let beta = self.bind(arg);
                    Type::Arrow(Box::new(beta), Box::new(acc))
                })
            };
        }

        match lhs {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => {
                bind!(args.iter().rev())
            }
            Lhs::Binop { a, b, op: _op } => {
                bind!(iter::once(b).chain(iter::once(a)))
            }
        }
    }

    pub fn generate_expr(&mut self, expr: &Expr<'file>) -> Type {
        match expr {
            Expr::Term(Term::Numeral(Numeral::Int(_))) => Type::Concrete("Int".to_string()),
            Expr::Term(Term::Numeral(Numeral::Float(_))) => Type::Concrete("Float".to_string()),
            Expr::Term(Term::String(_)) => Type::Concrete("String".to_string()),
            Expr::Term(Term::Unit) => Type::Concrete("()".to_string()),

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
                self.assume(name.clone(), typ.clone());
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
                self.assume(operator.clone(), t1.clone());
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
                    self.bind_name_poly(&name, &typ);
                }

                beta
            }

            Expr::Lambda { lhs, rhs } => {
                let args = lhs.args();
                let types: Vec<Type> = args.iter().map(|_| self.fresh()).collect();
                let typevars: Vec<TypeVar> = types
                    .iter()
                    .map(|t| {
                        if let Type::Var(v) = t {
                            *v
                        } else {
                            unreachable!()
                        }
                    })
                    .collect();
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
                    let actual_type = self.bind(arg);
                    self.constrain(Constraint::Equality(actual_type, lambda_type))
                }

                res
            }
        }
    }
}

impl<'file> Debug for ConstraintGenerator<'file> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Constraints:")?;
        for constraint in self.constraints.iter() {
            writeln!(f, "    {:?}", constraint)?;
        }

        if self.assumptions.len() > 0 {
            writeln!(f, "Assumptions:")?;
            for (name, vars) in self.assumptions.iter() {
                for var in vars {
                    writeln!(f, "    {} : {}", name, var)?;
                }
            }
        }

        Ok(())
    }
}
