use std::collections::BTreeMap;

use crate::ast::{Assignment, Definition, Expr, Lhs, Pattern, Term};
use crate::name::ResolvedName;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Precedence(pub Associativity, pub u8);

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum Associativity {
    Left,
    Right,
    None,
}

pub trait ApplyPrecedence {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>);
}

impl ApplyPrecedence for Definition<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        self.assignments.iter_mut().for_each(|a| a.apply(precs));
    }
}

impl ApplyPrecedence for Assignment<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        // LHS
        self.0.apply(precs);
        // RHS
        self.1.apply(precs);
    }
}

impl ApplyPrecedence for Lhs<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            Lhs::Func { args, .. } | Lhs::Lambda { args } => {
                for arg in args {
                    arg.apply(precs);
                }
            }
            Lhs::Binop { a, op: _, b } => {
                a.apply(precs);
                b.apply(precs);
            }
        }
    }
}

impl ApplyPrecedence for Pattern<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            Pattern::List(args) => {
                for arg in args {
                    arg.apply(precs)
                }
            }
            Pattern::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply(precs);
                if let Pattern::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply(precs);
                    c.apply(precs);

                    let Precedence(l_assoc, l_pri) = precs
                        .get(l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(r_assoc, r_pri) = precs
                        .get(r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri == r_pri
                        && *l_assoc == Associativity::None
                        && *r_assoc == Associativity::None
                    {
                        // @Errors: throw a proper parse error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l_pri >= r_pri && *l_assoc == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
            }
            Pattern::Destructure { args, .. } => {
                for arg in args {
                    arg.apply(precs)
                }
            }
            _ => (),
        }
    }
}

impl ApplyPrecedence for Expr<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            Expr::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply(precs);
                if let Expr::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply(precs);
                    c.apply(precs);

                    // @Note: this default is borrowed from Haskell; think about the right value
                    let Precedence(l_assoc, l_pri) = precs
                        .get(l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(r_assoc, r_pri) = precs
                        .get(r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri == r_pri
                        && *l_assoc == Associativity::None
                        && *r_assoc == Associativity::None
                    {
                        // @Errors: throw a proper parse error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l_pri >= r_pri && *l_assoc == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
                a.apply(precs);
            }
            Expr::App { func, argument } => {
                func.apply(precs);
                argument.apply(precs);
            }
            Expr::Term(t) => match t {
                Term::List(v) => {
                    for e in v {
                        e.apply(precs);
                    }
                }
                Term::Parens(e) => e.apply(precs),
                _ => (),
            },
            Expr::Let {
                definitions,
                in_expr,
            } => {
                for defn in definitions.values_mut() {
                    for (lhs, rhs) in defn.iter_mut() {
                        lhs.apply(precs);
                        rhs.apply(precs);
                    }
                }
                in_expr.apply(precs);
            }

            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.apply(precs);
                then_expr.apply(precs);
                else_expr.apply(precs);
            }

            Expr::Case { expr, arms } => {
                expr.apply(precs);
                for (_pat, arm_expr) in arms.iter_mut() {
                    arm_expr.apply(precs);
                }
            }

            Expr::Lambda { lhs, rhs } => {
                for mut pat in lhs.args() {
                    pat.apply(precs);
                }
                rhs.apply(precs);
            }

            Expr::Lua(_) | Expr::UnsafeLua(_) => (),
        }
    }
}
