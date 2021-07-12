use std::collections::HashMap;
use std::fmt::{self, Display};
use std::iter;

use crate::ast::{Assignment, Expr, ExprNode, Lhs, Name, Numeral, Pattern, Term};
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

    fn fresh(&mut self) -> Type {
        Type::Var(self.fresh_var())
    }

    fn fresh_var(&mut self) -> TypeVar {
        let id = self.next_typevar_id;
        self.next_typevar_id += 1;
        TypeVar(id)
    }

    fn assume(&mut self, name: Name) -> TypeVar {
        let beta = self.fresh_var();
        self.assumptions
            .entry(name)
            .or_insert(Vec::with_capacity(1))
            .push(beta);
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

                    self.constraints
                        .push(Constraint::Equality(acc, partial_cons_type));

                    partial_res_type
                })
            };
        }

        match pat {
            Pattern::Bind(s) => {
                let beta = self.fresh();
                self.bind_name(&Name::Ident(s.to_string()), &beta);
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
                let cons_type = Type::Var(self.assume(operator.clone()));
                bind!(iter::once(lhs).chain(iter::once(rhs)), cons_type)
            }

            Pattern::UnaryConstructor(name) => Type::Var(self.assume(name.clone())),
            Pattern::Destructure { constructor, args } => {
                let cons_type = Type::Var(self.assume(constructor.clone()));
                bind!(args.iter(), cons_type)
            }
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

// This impl assumes that each assignment is a definition of the same function.
impl<'a> GenerateConstraints for Vec<Assignment<'a>> {
    fn generate(&self, cg: &mut ConstraintGenerator) -> Type {
        let beta = cg.fresh();

        // @Cleanup: can this be merged into a single expression to avoid collect()?
        let typs: Vec<Type> = self.iter().map(|defn| defn.generate(cg)).collect();
        for typ in typs {
            // @Fixme: This sometimes needs to be other types of constraint
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
        match &self.node {
            ExprNode::Term(Term::Numeral(Numeral::Int(_))) => Type::Prim(Primitive::Int),
            ExprNode::Term(Term::Numeral(Numeral::Float(_))) => Type::Prim(Primitive::Float),
            ExprNode::Term(Term::String(_)) => Type::Prim(Primitive::String),
            ExprNode::Term(Term::Parens(e)) => e.generate(cg),
            ExprNode::Term(Term::List(es)) => {
                let beta = cg.fresh();
                for e in es {
                    let e_type = e.generate(cg);
                    cg.constraints
                        .push(Constraint::Equality(beta.clone(), e_type));
                }
                Type::List(Box::new(beta))
            }

            ExprNode::Term(Term::Name(name)) => Type::Var(cg.assume(name.clone())),

            ExprNode::App { func, argument } => {
                let t1 = func.generate(cg);
                let t2 = argument.generate(cg);
                let beta = cg.fresh();

                cg.constrain(Constraint::Equality(
                    t1,
                    Type::Func(Box::new(t2), Box::new(beta.clone())),
                ));

                beta
            }
            ExprNode::Binop { operator, lhs, rhs } => {
                let t1 = Type::Var(cg.assume(operator.clone()));
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

            ExprNode::Let {
                assignments,
                in_expr,
            } => {
                let beta = in_expr.generate(cg);

                for (name, defns) in assignments {
                    // @Fixme @Scope: these should be local to the in_expr, obviously!
                    let typ = defns.generate(cg);
                    cg.bind_name(&name, &typ);
                }

                // @Todo @Fixme @Scope: remove the let bindings???

                // @Note: It's possible that the above comments about scope aren't actually
                // necessary. That is, when a variable is bound, its assumptions are removed from
                // the assumption set; this means that e.g. two separate variables both named `f` in
                // separate let bindings will be assigned separate types.

                beta
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
            Constraint::Equality(a, b) => write!(f, "{} ≡ {}", a, b),
            Constraint::ExplicitInstance(tau, sigma) => {
                write!(f, "{} ≼ {}", tau, sigma)
            }
            Constraint::ImplicitInstance(a, b, _m) => {
                write!(f, "{} ≤M {}", a, b) //, where M is {}", a, b, m)
            }
        }
    }
}
