//! This module handles the rearranging required of the AST to correct for operator precedences.
//! Until we have parsed each module and resolved names,
//! we don't know what the declared precedence of each operator is.
//! So we need to do our "best effort" when parsing
//! (which amounts to parsing everything as equally left-associative);
//! and then later on in compilation
//! we modify the AST to reflect the precedences which we have learned.

use std::collections::BTreeMap;

use crate::ast::{self, Module};
use crate::name::ResolvedName;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct Precedence {
    pub associativity: Associativity,
    pub priority: u8,
}

impl Default for Precedence {
    fn default() -> Self {
        Precedence {
            associativity: Associativity::Left,
            priority: 9,
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub enum Associativity {
    Left,
    Right,
    None,
}

pub trait ApplyPrecedence {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>);
}

impl ApplyPrecedence for Module<ResolvedName, ()> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        for defn in self.definitions.values_mut() {
            defn.apply(precs);
        }
    }
}

impl<Ty> ApplyPrecedence for ast::Definition<ResolvedName, Ty> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        self.assignments.iter_mut().for_each(|a| a.apply(precs));
    }
}

impl ApplyPrecedence for ast::Assignment<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        // LHS
        self.0.apply(precs);
        // RHS
        self.1.apply(precs);
    }
}

impl ApplyPrecedence for ast::Lhs<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            ast::Lhs::Func { args, .. } => {
                for arg in args {
                    arg.apply(precs);
                }
            }
            ast::Lhs::Binop { a, op: _, b } => {
                a.apply(precs);
                b.apply(precs);
            }
        }
    }
}

impl ApplyPrecedence for ast::Pattern<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            ast::Pattern::Stream(args) => {
                for arg in args {
                    arg.apply(precs)
                }
            }
            ast::Pattern::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply(precs);
                if let ast::Pattern::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply(precs);
                    c.apply(precs);

                    let l = precs.get(l_op).cloned().unwrap_or_default();
                    let r = precs.get(r_op).cloned().unwrap_or_default();

                    if l.priority == r.priority
                        && l.associativity == Associativity::None
                        && r.associativity == Associativity::None
                    {
                        // @Errors: throw a proper error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l.priority >= r.priority && l.associativity == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
            }
            ast::Pattern::Destructure { args, .. } => {
                for arg in args {
                    arg.apply(precs)
                }
            }
            _ => (),
        }
    }
}

impl ApplyPrecedence for ast::Expr<ResolvedName> {
    fn apply(&mut self, precs: &BTreeMap<ResolvedName, Precedence>) {
        match self {
            ast::Expr::Binop {
                operator: ref mut l_op,
                lhs: ref mut a,
                ref mut rhs,
            } => {
                rhs.apply(precs);
                if let ast::Expr::Binop {
                    operator: ref mut r_op,
                    lhs: ref mut b,
                    rhs: ref mut c,
                } = rhs.as_mut()
                {
                    b.apply(precs);
                    c.apply(precs);

                    // @Note: this default is borrowed from Haskell; think about the right value
                    let l = precs.get(l_op).cloned().unwrap_or_default();
                    let r = precs.get(r_op).cloned().unwrap_or_default();

                    if l.priority == r.priority
                        && l.associativity == Associativity::None
                        && r.associativity == Associativity::None
                    {
                        // @Errors: throw a proper error
                        panic!(
                            "Can't combine infix operators of same precedence and no associativity"
                        );
                    }

                    if l.priority >= r.priority && l.associativity == Associativity::Left {
                        // Change from right-assoc to left-assoc
                        std::mem::swap(l_op, r_op);

                        std::mem::swap(c, b);
                        std::mem::swap(b, a);

                        std::mem::swap(a, rhs);
                    }
                }
                a.apply(precs);
            }
            ast::Expr::App { func, argument } => {
                func.apply(precs);
                argument.apply(precs);
            }
            ast::Expr::Term(t) => match t {
                ast::Term::Stream(v) => {
                    for e in v {
                        e.apply(precs);
                    }
                }
                ast::Term::Parens(e) => e.apply(precs),
                _ => (),
            },
            ast::Expr::Let {
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

            ast::Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.apply(precs);
                then_expr.apply(precs);
                else_expr.apply(precs);
            }

            ast::Expr::Case { expr, arms } => {
                expr.apply(precs);
                for (_pat, arm_expr) in arms.iter_mut() {
                    arm_expr.apply(precs);
                }
            }

            ast::Expr::Lambda { args, rhs } => {
                for arg in args {
                    arg.apply(precs);
                }
                rhs.apply(precs);
            }

            ast::Expr::Lua(_) | ast::Expr::UnsafeLua(_) => (),
        }
    }
}
