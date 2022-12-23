use std::collections::{BTreeMap, VecDeque};
use std::fmt::{self, Display};
use std::iter;

use log::log_enabled;

use crate::ast::{self, Definition, Expr, Lhs, Name, Numeral, Pattern, Term};
use crate::types::{
    self, ApplySub, Substitution, Type, TypeDefinition, TypeScheme, TypeVar, TypeVarSet,
};

pub trait ActiveVars {
    fn active_vars(&self) -> TypeVarSet;
}

#[derive(PartialEq, Eq, Clone, Debug)]
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

// because of VecDeque::as_slices
impl ActiveVars for (&[Constraint], &[Constraint]) {
    fn active_vars(&self) -> TypeVarSet {
        let (a, b) = self;
        a.active_vars().union(&b.active_vars())
    }
}

impl<'file> Display for Constraint {
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

#[derive(Debug)]
pub struct ConstraintGenerator {
    constraints: Vec<Constraint>,

    // @Cleanup: shouldn't be pub
    pub assumptions: BTreeMap<Name, Vec<Type>>,

    next_typevar_id: usize,
    m_stack: Vec<TypeVar>,
}

impl<'file> ConstraintGenerator {
    pub fn new() -> Self {
        ConstraintGenerator {
            constraints: Vec::new(),
            assumptions: BTreeMap::new(),
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

    pub fn convert_ast_type_scheme(&mut self, input: &ast::TypeScheme<'file>) -> TypeScheme {
        let mut vars_map = BTreeMap::new();
        let vars: TypeVarSet = input
            .vars
            .iter()
            .map(|v| {
                let fresh = self.fresh_var();
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
        let ast::TypeDefinition(name, vars_s, constrs) = type_defn;

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
                .fold(typ.clone(), |res, a| Type::Func(Box::new(a), Box::new(res)));

            // @Todo @Checkme: no name conflicts
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
        input: &ast::TypeExpr<'file>,
        vars_map: &BTreeMap<&str, TypeVar>,
    ) -> Type {
        match input {
            ast::TypeExpr::Term(term) => self.convert_ast_type_term(term, vars_map),
            ast::TypeExpr::App(f, x) => Type::App(
                Box::new(self.convert_ast_type_expr(f, vars_map)),
                Box::new(self.convert_ast_type_expr(x, vars_map)),
            ),
            ast::TypeExpr::Arrow(a, b) => Type::Func(
                Box::new(self.convert_ast_type_expr(a, vars_map)),
                Box::new(self.convert_ast_type_expr(b, vars_map)),
            ),
        }
    }

    pub fn convert_ast_type_term(
        &mut self,
        input: &ast::TypeTerm<'file>,
        vars_map: &BTreeMap<&str, TypeVar>,
    ) -> Type {
        match input {
            // @Todo @Checkme: type constructors
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

                    // @Todo @Errors: ill-formed type expression (should be a syntax error)
                    todo!()
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

    fn assume(&mut self, name: Name, typ: Type) {
        log::trace!("Assuming type: {} : {}", name, typ);
        self.assumptions
            .entry(name)
            .or_insert(Vec::with_capacity(1))
            .push(typ);
    }

    pub fn assumption_vars(&self) -> TypeVarSet {
        self.assumptions
            .values()
            .flatten()
            .flat_map(|t| t.free_vars().into_iter())
            .collect()
    }

    pub fn constrain(&mut self, constraint: Constraint) {
        log::trace!("Emitting constraint: {}", constraint);
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

    /// Constrains that all types in the given Vec should be instances of
    /// the same shared type scheme.
    pub fn all_instances_of(&mut self, typs: Vec<Type>, ts: TypeScheme) {
        for typ in typs {
            self.constrain(Constraint::ExplicitInstance(typ, ts.clone()));
        }
    }

    // Returns the type of the whole pattern item, as well as emitting constraints for sub-items.
    fn bind(&mut self, pat: &Pattern) -> Type {
        macro_rules! bind {
            ($iter:expr, $cons_type:expr) => {
                $iter.fold($cons_type, |acc, arg| {
                    let arg_type = self.bind(arg);
                    let partial_res_type = self.fresh();
                    let partial_cons_type =
                        Type::Func(Box::new(arg_type), Box::new(partial_res_type.clone()));

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
                bind!(iter::once(lhs).chain(iter::once(rhs)), beta)
            }

            Pattern::UnaryConstructor(name) => {
                let beta = self.fresh();
                self.assume(name.clone(), beta.clone());
                beta
            }
            Pattern::Destructure { constructor, args } => {
                let beta = self.fresh();
                self.assume(constructor.clone(), beta.clone());
                bind!(args.iter(), beta)
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

    /// Takes a TypeScheme and replaces all quantified variables with fresh variables;
    /// then returns the resulting Type.
    pub fn instantiate(&mut self, mut ts: TypeScheme) -> Type {
        let sub = ts.vars.into_iter().fold(Substitution::empty(), |sub, var| {
            sub.then(Substitution::single(var, self.fresh()))
        });
        ts.typ.apply(&sub);
        ts.typ
    }

    pub fn solve(&mut self) -> Result<Substitution, types::Error> {
        log::trace!("START SOLVING");
        let mut sub = Substitution::empty();

        let mut constraints = VecDeque::from(self.constraints.clone());

        while let Some(c) = constraints.pop_front() {
            log::trace!("-");
            log::trace!("Looking at: {}", c);
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
                    log::trace!("Replacing with new constraint: {}", cons);
                    constraints.push_back(cons)
                }

                Constraint::ImplicitInstance(t1, t2, m)
                    if t2
                        .free_vars()
                        .difference(&m)
                        .intersection(&constraints.as_slices().active_vars())
                        .is_empty() =>
                {
                    let cons = Constraint::ExplicitInstance(t1, t2.generalize(&m));
                    log::trace!("Replacing with new constraint: {}", cons);
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
                    log::trace!("    {} ↦ {}", fr, to);
                }

                log::trace!("Constraints:");
                for c in constraints.iter() {
                    log::trace!("    {}", c);
                }
            }
        }

        log::trace!("-");
        log::trace!("FINISH SOLVING");
        log::trace!("{}", self);

        Ok(sub)
    }
}

pub trait GenerateConstraints<'file> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type;
}

impl<'file> GenerateConstraints<'file> for Definition<'file> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        // Typecheck each assignment in the definition.
        let mut typs: Vec<Type> = self
            .assignments
            .iter()
            .map(|assign| assign.generate(cg))
            .collect();

        // If there's an explicit type, include that as well.
        if let Some(ref explicit_type_scheme) = self.explicit_type {
            let ts = cg.convert_ast_type_scheme(explicit_type_scheme);
            typs.push(cg.instantiate(ts));
        }

        // Constrain that each inferred assignment,
        // and the explicit type,
        // should all be equal.
        cg.equate_all(typs)
    }
}

impl<'file> GenerateConstraints<'file> for Vec<(Lhs<'file>, Expr<'file>)> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let beta = cg.fresh();

        let typs: Vec<Type> = self.iter().map(|assign| assign.generate(cg)).collect();
        for typ in typs {
            cg.constrain(Constraint::Equality(beta.clone(), typ));
        }

        beta
    }
}

impl<'file> GenerateConstraints<'file> for (Lhs<'file>, Expr<'file>) {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let (lhs, expr) = self;

        macro_rules! bind {
            ($iter:expr) => {
                $iter.fold(expr.generate(cg), |acc, arg| {
                    let beta = cg.bind(arg);
                    Type::Func(Box::new(beta), Box::new(acc))
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
}

impl<'file> GenerateConstraints<'file> for Expr<'file> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        match self {
            Expr::Term(Term::Numeral(Numeral::Int(_))) => Type::Concrete("Int".to_string()),
            Expr::Term(Term::Numeral(Numeral::Float(_))) => Type::Concrete("Float".to_string()),
            Expr::Term(Term::String(_)) => Type::Concrete("String".to_string()),
            Expr::Term(Term::Unit) => Type::Concrete("()".to_string()),

            Expr::Term(Term::Parens(e)) => e.generate(cg),
            Expr::Term(Term::List(es)) => {
                let beta = cg.fresh();
                for e in es {
                    let e_type = e.generate(cg);
                    cg.constrain(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }
            Expr::Term(Term::Tuple(es)) => Type::Tuple(es.iter().map(|e| e.generate(cg)).collect()),

            Expr::Term(Term::Name(name)) => {
                let typ = cg.fresh();
                cg.assume(name.clone(), typ.clone());
                typ
            }

            Expr::App { func, argument } => {
                let t1 = func.generate(cg);
                let t2 = argument.generate(cg);
                let beta = cg.fresh();

                cg.constrain(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            Expr::Binop { operator, lhs, rhs } => {
                let t1 = cg.fresh();
                cg.assume(operator.clone(), t1.clone());
                let t2 = lhs.generate(cg);
                let t3 = rhs.generate(cg);
                let beta1 = cg.fresh();
                let beta2 = cg.fresh();

                cg.constrain(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta1.clone())),
                ));
                cg.constrain(Constraint::Equality(
                    beta1,
                    Type::Func(Box::new(t3), Box::new(beta2.clone())),
                ));

                beta2
            }

            Expr::Let {
                definitions,
                in_expr,
            } => {
                let beta = in_expr.generate(cg);

                for (name, assignments) in definitions {
                    let typ = assignments.generate(cg);
                    cg.bind_name_poly(&name, &typ);
                }

                beta
            }

            Expr::Lambda { lhs, rhs } => {
                let args = lhs.args();
                let types: Vec<Type> = args.iter().map(|_| cg.fresh()).collect();
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

                cg.m_stack.extend(typevars);

                let res = types.iter().rev().fold(rhs.generate(cg), |acc, beta| {
                    Type::Func(Box::new(beta.clone()), Box::new(acc))
                });

                let total_len = cg.m_stack.len();
                cg.m_stack.truncate(total_len - typevar_count);

                for (arg, lambda_type) in args.iter().zip(types.into_iter()) {
                    let actual_type = cg.bind(arg);
                    cg.constrain(Constraint::Equality(actual_type, lambda_type))
                }

                res
            }
        }
    }
}

impl<'file> Display for ConstraintGenerator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Constraints:")?;
        for constraint in self.constraints.iter() {
            writeln!(f, "    {}", constraint)?;
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
