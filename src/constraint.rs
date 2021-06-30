use std::collections::HashMap;
use std::fmt::{self, Display};

use crate::ast::{Assignment, Expr, Lhs, Name, Pattern, Term};
use crate::types::{Primitive, Type, TypeScheme, TypeVar};

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

    pub fn generate_assign(&mut self, subject: Assignment) -> Type {
        let (lhs, expr) = subject;
        match lhs {
            Lhs::Func { name: _name, args } => {
                args.iter().rev().fold(self.generate(&expr), |acc, arg| {
                    let beta = Type::Var(self.fresh());

                    match arg {
                        Pattern::Bind(s) => {
                            if let Some(assumptions) =
                                self.assumptions.remove(&Name::Ident(s.to_string()))
                            {
                                for assumed in assumptions {
                                    self.constraints.push(Constraint::Equality(
                                        Type::Var(assumed),
                                        beta.clone(),
                                    ));
                                }
                            }
                        }
                        _ => unimplemented!(),
                    }

                    Type::Func(Box::new(beta), Box::new(acc))
                })
            }
            _ => unimplemented!(),
        }
    }

    pub fn generate(&mut self, subject: &Expr) -> Type {
        match subject {
            Expr::Term(Term::Numeral(_)) => Type::Prim(Primitive::Int), // @Fixme: Int/Float???
            Expr::Term(Term::String(_)) => Type::Prim(Primitive::String),
            Expr::Term(Term::List(_)) => unimplemented!(), // @Todo
            Expr::Term(Term::Parens(e)) => self.generate(e),

            Expr::Term(Term::Name(name)) => Type::Var(self.assume(name.clone())),

            Expr::App { func, argument } => {
                let t1 = self.generate(func);
                let t2 = self.generate(argument);
                let beta = Type::Var(self.fresh());

                self.constraints.push(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            Expr::Binop { operator, lhs, rhs } => {
                let t1 = Type::Var(self.assume(operator.clone()));
                let t2 = self.generate(lhs);
                let t3 = self.generate(rhs);
                let beta1 = Type::Var(self.fresh());
                let beta2 = Type::Var(self.fresh());

                self.constraints.push(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta1.clone())),
                ));
                self.constraints.push(Constraint::Equality(
                    beta1,
                    Type::Func(Box::new(t3), Box::new(beta2.clone())),
                ));

                beta2
            }
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

        write!(f, "Next typevar ID: {}", self.next_typevar_id)
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
