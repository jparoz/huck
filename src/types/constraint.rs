use std::collections::{HashMap, VecDeque};
use std::fmt::{self, Display};
use std::iter;

use log::log_enabled;

use crate::ast::{Assignment, Definition, Expr, Lhs, Name, Numeral, Pattern, Term};
use crate::types::{
    self, ApplySub, Primitive, Substitution, Type, TypeScheme, TypeVar, TypeVarSet,
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
    pub assumptions: HashMap<Name, Vec<Type>>,

    next_typevar_id: usize,
    m_stack: Vec<TypeVar>,
}

impl ConstraintGenerator {
    pub fn new() -> Self {
        ConstraintGenerator {
            constraints: Vec::new(),
            assumptions: HashMap::new(),
            next_typevar_id: 0,
            m_stack: Vec::new(),
        }
    }

    fn fresh(&mut self) -> Type {
        let id = self.next_typevar_id;
        self.next_typevar_id += 1;
        Type::Var(TypeVar(id))
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
            .map(|t| t.free_vars().iter().cloned().collect::<Vec<TypeVar>>())
            .flatten()
            .collect()
    }

    pub fn constrain(&mut self, constraint: Constraint) {
        log::info!("Emitting constraint: {}", constraint);
        self.constraints.push(constraint);
    }

    // Constrains all types in the given Vec to be equal.
    pub fn equate_all(&mut self, typs: Vec<Type>) {
        let beta = self.fresh();
        for typ in typs {
            self.constrain(Constraint::Equality(beta.clone(), typ.clone()));
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

            Pattern::Numeral(Numeral::Int(_)) => Type::Prim(Primitive::Int),
            Pattern::Numeral(Numeral::Float(_)) => Type::Prim(Primitive::Float),

            Pattern::String(_) => Type::Prim(Primitive::String),

            Pattern::Binop { operator, lhs, rhs } => {
                let beta = self.fresh();
                self.assume(operator.clone(), beta.clone());
                bind!(iter::once(lhs).chain(iter::once(rhs)), beta)
            }

            Pattern::Unit => Type::Prim(Primitive::Unit),

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
                log::info!("Bound (mono): {} to type {}", name, typ);
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
                log::info!(
                    "Bound (poly): {} to type {} (M = {})",
                    name,
                    typ,
                    self.m_stack.iter().cloned().collect::<TypeVarSet>()
                );
            }
        }
    }

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
                    log::info!("Replacing with new constraint: {}", cons);
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
                    log::info!("Replacing with new constraint: {}", cons);
                    constraints.push_back(cons)
                }

                c @ Constraint::ImplicitInstance(..) => {
                    // @Note: This should never diverge, i.e. there should always be at least one
                    // constraint in the set that meets the criteria to be solvable. See HHS02.
                    log::info!("Skipping for now");
                    constraints.push_back(c);
                }
            }

            log::trace!("Substitution:");
            if log_enabled!(log::Level::Trace) {
                for (fr, to) in sub.iter() {
                    log::trace!("    {} ↦ {}", fr, to);
                }
            }

            log::trace!("Constraints:");
            if log_enabled!(log::Level::Trace) {
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

pub trait GenerateConstraints {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type;
}

impl<'file> GenerateConstraints for Definition<'file> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        self.assignments.generate(cg)
    }
}

impl<'file> GenerateConstraints for Vec<Assignment<'file>> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let beta = cg.fresh();

        let typs: Vec<Type> = self.iter().map(|defn| defn.generate(cg)).collect();
        for typ in typs {
            // @Note: If we want polymorphic bindings at top level, this might want to be a
            // different type of constraint.
            cg.constrain(Constraint::Equality(beta.clone(), typ));
        }

        beta
    }
}

impl<'file> GenerateConstraints for Assignment<'file> {
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

impl<'file> GenerateConstraints for Expr<'file> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        match self {
            Expr::Term(Term::Numeral(Numeral::Int(_))) => Type::Prim(Primitive::Int),
            Expr::Term(Term::Numeral(Numeral::Float(_))) => Type::Prim(Primitive::Float),
            Expr::Term(Term::String(_)) => Type::Prim(Primitive::String),
            Expr::Term(Term::Unit) => Type::Prim(Primitive::Unit),
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
