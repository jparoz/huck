use std::collections::{HashMap, VecDeque};
use std::fmt::{self, Display};
use std::iter;

use crate::ast::{Assignment, Expr, Lhs, Name, Numeral, Pattern, Term};
use crate::types::{Primitive, Type, TypeScheme, TypeVar, TypeVarSet};

#[derive(PartialEq, Eq, Clone, Debug)]
enum Constraint {
    Equality(Type, Type),
    ImplicitInstance(Type, Type, TypeVarSet),
    ExplicitInstance(Type, TypeScheme),
}

pub trait ActiveVars {
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

impl<'a> Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(a, b) => write!(f, "{} ≡ {}", a, b),
            Constraint::ImplicitInstance(a, b, m) => {
                write!(f, "{} ≤ {} where M is {{ ", a, b)?;
                for var in m.iter() {
                    write!(f, "{} ", var)?;
                }
                write!(f, "}}")
            }
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{} ≼ {}", tau, sigma)
            }
        }
    }
}

#[derive(Debug)]
pub struct Substitution(HashMap<TypeVar, Type>);

impl Substitution {
    pub fn empty() -> Self {
        Substitution(HashMap::new())
    }

    pub fn single(fr: TypeVar, to: Type) -> Self {
        Substitution(HashMap::from([(fr, to)]))
    }

    /// s1.then(s2) == s2 . s1
    pub fn then(self, mut next: Self) -> Self {
        for (fr, to) in self.0 {
            for (_, b) in next.0.iter_mut() {
                Substitution::single(fr, to.clone()).apply(b);
            }
            next.0.insert(fr, to);
        }
        next
    }

    /// Applies the substitution to the given type.
    pub fn apply(&self, t: &mut Type) {
        match t {
            Type::Var(var) => {
                if let Some(replacement) = self.0.get(&var) {
                    *t = replacement.clone();
                }
            }
            Type::Func(a, b) => {
                self.apply(a);
                self.apply(b);
            }
            Type::List(list_t) => self.apply(list_t),
            Type::Prim(_) => (),
        }
    }
}

#[derive(Debug)]
pub struct ConstraintGenerator {
    constraints: Vec<Constraint>,
    assumptions: HashMap<Name, Vec<Type>>,
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

    fn assume(&mut self, name: Name) -> Type {
        let beta = self.fresh();
        self.assumptions
            .entry(name)
            .or_insert(Vec::with_capacity(1))
            .push(beta.clone());
        beta
    }

    fn constrain(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
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

            Pattern::Numeral(Numeral::Int(_)) => Type::Prim(Primitive::Int),
            Pattern::Numeral(Numeral::Float(_)) => Type::Prim(Primitive::Float),

            Pattern::String(_) => Type::Prim(Primitive::String),

            Pattern::Binop { operator, lhs, rhs } => {
                let cons_type = self.assume(operator.clone());
                bind!(iter::once(lhs).chain(iter::once(rhs)), cons_type)
            }

            Pattern::UnaryConstructor(name) => self.assume(name.clone()),
            Pattern::Destructure { constructor, args } => {
                let cons_type = self.assume(constructor.clone());
                bind!(args.iter(), cons_type)
            }
        }
    }

    fn bind_name_mono(&mut self, name: &Name, beta: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::Equality(assumed, beta.clone()));
            }
        }
    }

    fn bind_name_poly(&mut self, name: &Name, beta: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constrain(Constraint::ImplicitInstance(
                    assumed,
                    beta.clone(),
                    self.m_stack.iter().cloned().collect(),
                ));
            }
        }
    }

    pub fn instantiate(&mut self, mut ts: TypeScheme) -> Type {
        let sub = ts.vars.into_iter().fold(Substitution::empty(), |sub, var| {
            sub.then(Substitution::single(var, self.fresh()))
        });
        sub.apply(&mut ts.typ);
        ts.typ
    }

    pub fn solve(&mut self) -> Option<Substitution> {
        let mut sub = Substitution::empty();

        let mut constraints = VecDeque::from(self.constraints.clone());

        while let Some(c) = constraints.pop_front() {
            match c {
                Constraint::Equality(t1, t2) => sub = sub.then(t1.unify(t2)?),

                Constraint::ExplicitInstance(t, ts) => {
                    constraints.push_back(Constraint::Equality(t, self.instantiate(ts)))
                }

                Constraint::ImplicitInstance(t1, t2, m)
                    if t2
                        .free_vars()
                        .difference(&m)
                        .intersection(&constraints.as_slices().active_vars())
                        .is_empty() =>
                {
                    constraints.push_back(Constraint::ExplicitInstance(t1, t2.generalize(&m)));
                }

                _ => return None,
            }
        }

        Some(sub)
    }
}

pub trait GenerateConstraints {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type;
}

// This impl assumes that each assignment in the Vec is a definition of the same function.
impl<'a> GenerateConstraints for Vec<Assignment<'a>> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let beta = cg.fresh();

        let typs: Vec<Type> = self.iter().map(|defn| defn.generate(cg)).collect();
        for typ in typs {
            // @Fixme: This sometimes needs to be other types of constraint
            // @Note: I don't think the above is true? @RemoveMe: the comment
            // @Note: It might be true if we want polymorphic bindings at top level.
            //        If this is the case, then I think this function will just go away,
            //        and we'll decide at the callsite which type of constraint to use.
            cg.constrain(Constraint::Equality(beta.clone(), typ));
        }

        beta
    }
}

impl<'a> GenerateConstraints for Assignment<'a> {
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
            Lhs::Func { args, name: _name } => {
                bind!(args.iter().rev())
            }
            Lhs::Binop { a, b, op: _op } => {
                bind!(iter::once(b).chain(iter::once(a)))
            }
        }
    }
}

impl<'a> GenerateConstraints for Expr<'a> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        match self {
            Expr::Term(Term::Numeral(Numeral::Int(_))) => Type::Prim(Primitive::Int),
            Expr::Term(Term::Numeral(Numeral::Float(_))) => Type::Prim(Primitive::Float),
            Expr::Term(Term::String(_)) => Type::Prim(Primitive::String),
            Expr::Term(Term::Parens(e)) => e.generate(cg),
            Expr::Term(Term::List(es)) => {
                let beta = cg.fresh();
                for e in es {
                    let e_type = e.generate(cg);
                    cg.constrain(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }

            Expr::Term(Term::Name(name)) => cg.assume(name.clone()),

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
                let t1 = cg.assume(operator.clone());
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
                assignments,
                in_expr,
            } => {
                let beta = in_expr.generate(cg);

                for (name, defns) in assignments {
                    // @Fixme @Scope: these should be local to the in_expr, obviously!
                    let typ = defns.generate(cg);
                    cg.bind_name_poly(&name, &typ);
                }

                // @Todo @Fixme @Scope: remove the let bindings???

                // @Note: It's possible that the above comments about scope aren't actually
                // necessary. That is, when a variable is bound, its assumptions are removed from
                // the assumption set; this means that e.g. two separate variables both named `f` in
                // separate let bindings will be assigned separate types.

                beta
            }

            Expr::Lambda { args, rhs } => {
                let types: Vec<Type> = args.iter().map(|_| cg.fresh()).collect();
                let typevars: Vec<TypeVar> = types
                    .iter()
                    .flat_map(|typ| typ.get_mono_type_vars())
                    .collect();
                let typevar_count = typevars.len();

                cg.m_stack.extend(typevars);

                let res = types.iter().rev().fold(rhs.generate(cg), |acc, beta| {
                    Type::Func(Box::new(beta.clone()), Box::new(acc))
                });

                let total_len = cg.m_stack.len();
                cg.m_stack.truncate(total_len - typevar_count);

                for (arg, lambda_type) in args.iter().zip(types.into_iter()) {
                    // @Hack: There is a circular dependency in the logic here.
                    //        First we need some types to put into cg.m_stack, so that they can
                    //        appear in the context of implicit instance constraints in rhs.
                    //        But then, after rhs.generate(cg), we need to bind the args to types.
                    //        This removes assumptions, and we can't do this until after
                    //        rhs.generate(cg).
                    //        So, we need access to the types both before and after
                    //        rhs.generate(cg). To get around this, we simply make a fresh type for
                    //        each argument first; then later on we bind the argument to another
                    //        type (often being totally redundant); and finally we make another
                    //        equality constraint, which will later unify the two types.
                    //        Really, we would like to not generate another constraint, but instead
                    //        somehow provide the type to cg.bind. e.g. cg.bind_with_type(arg, typ)
                    let actual_type = cg.bind(arg);
                    cg.constrain(Constraint::Equality(actual_type, lambda_type))
                }

                res
            }
        }
    }
}

impl Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Substitution:")?;
        for (fr, to) in self.0.iter() {
            writeln!(f, "    {} ↦ {}", fr, to)?;
        }
        Ok(())
    }
}

impl<'a> Display for ConstraintGenerator {
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
