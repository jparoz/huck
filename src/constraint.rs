use std::collections::HashMap;
use std::fmt::{self, Display};

use crate::ast::{Assignment, Expr, Lhs, Name, Pattern, Term};
use crate::types::{Primitive, Type, TypeScheme, TypeVar};

pub trait GenerateConstraints {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type;
}

#[derive(Debug)]
pub struct ConstraintGenerator {
    constraints: Vec<Constraint>,
    assumptions: HashMap<Name, Vec<TypeVar>>,
    next_typevar_id: usize,
}

impl ConstraintGenerator {
    pub fn new() -> Self {
        ConstraintGenerator {
            constraints: Vec::new(),
            assumptions: HashMap::new(),
            next_typevar_id: 0,
        }
    }

    fn fresh(&mut self) -> TypeVar {
        let id = self.next_typevar_id;
        self.next_typevar_id += 1;
        TypeVar(id)
    }

    fn assume(&mut self, name: Name) -> TypeVar {
        let beta = self.fresh();
        self.assumptions
            .entry(name)
            .or_insert(Vec::with_capacity(1))
            .push(beta);
        beta
    }

    // Returns the type of the whole pattern item, as well as emitting constraints for sub-items.
    fn bind(&mut self, pat: &Pattern) -> Type {
        match pat {
            Pattern::Bind(s) => {
                let beta = Type::Var(self.fresh());
                self.bind_name(&Name::Ident(s.to_string()), &beta);
                beta
            }
            Pattern::Destructure { constructor, args } => {
                let cons_type = Type::Var(self.assume(constructor.clone()));

                args.iter().fold(cons_type, |acc, arg| {
                    let arg_type = self.bind(arg);
                    let partial_res_type = Type::Var(self.fresh());
                    let partial_cons_type =
                        Type::Func(Box::new(arg_type), Box::new(partial_res_type.clone()));
                    self.constraints
                        .push(Constraint::Equality(acc, partial_cons_type));
                    partial_res_type
                })
            }
            _ => unimplemented!(),
        }
    }

    fn bind_name(&mut self, name: &Name, beta: &Type) {
        if let Some(assumptions) = self.assumptions.remove(name) {
            for assumed in assumptions {
                self.constraints
                    .push(Constraint::Equality(Type::Var(assumed), beta.clone()));
            }
        }
    }
}

impl<'a> GenerateConstraints for Assignment<'a> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let (lhs, expr) = self;
        match lhs {
            Lhs::Func { name: _name, args } => {
                args.iter().rev().fold(expr.generate(cg), |acc, arg| {
                    let beta = cg.bind(arg);

                    Type::Func(Box::new(beta), Box::new(acc))
                })
            }
            _ => unimplemented!(),
        }
    }
}

impl<'a> GenerateConstraints for Expr<'a> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        match self {
            Expr::Term(Term::Numeral(_)) => Type::Prim(Primitive::Int), // @Fixme: Int/Float???
            Expr::Term(Term::String(_)) => Type::Prim(Primitive::String),
            Expr::Term(Term::List(_)) => unimplemented!(), // @Todo
            Expr::Term(Term::Parens(e)) => e.generate(cg),

            Expr::Term(Term::Name(name)) => Type::Var(cg.assume(name.clone())),

            Expr::App { func, argument } => {
                let t1 = func.generate(cg);
                let t2 = argument.generate(cg);
                let beta = Type::Var(cg.fresh());

                cg.constraints.push(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            Expr::Binop { operator, lhs, rhs } => {
                let t1 = Type::Var(cg.assume(operator.clone()));
                let t2 = lhs.generate(cg);
                let t3 = rhs.generate(cg);
                let beta1 = Type::Var(cg.fresh());
                let beta2 = Type::Var(cg.fresh());

                cg.constraints.push(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta1.clone())),
                ));
                cg.constraints.push(Constraint::Equality(
                    beta1,
                    Type::Func(Box::new(t3), Box::new(beta2.clone())),
                ));

                beta2
            }
        }
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

#[derive(PartialEq, Eq, Debug)]
enum Constraint {
    Equality(Type, Type),
    ExplicitInstance(Type, TypeScheme),
    ImplicitInstance(Type, Type, Vec<TypeVar>),
}

impl<'a> Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Equality(a, b) => write!(f, "{} == {}", a, b),
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{} is an instance of {}", tau, sigma)
            }
            Constraint::ImplicitInstance(a, b, m) => {
                // write!(f, "{} is an instance of {}, generalized under {}", a, b, m)
                unimplemented!()
            }
        }
    }
}
