use std::collections::BTreeMap;

use crate::ast::{Definition, Expr, Lhs, Name, Pattern, Term};

// @Note @Cleanup: These defaults should one day be replaced with source code.
pub fn default_precs() -> BTreeMap<Name, Precedence> {
    BTreeMap::from([
        (
            Name::Binop("*".to_string()),
            Precedence(Associativity::Left, 7),
        ),
        (
            Name::Binop("/".to_string()),
            Precedence(Associativity::Left, 7),
        ),
        (
            Name::Binop("+".to_string()),
            Precedence(Associativity::Left, 6),
        ),
        (
            Name::Binop("-".to_string()),
            Precedence(Associativity::Left, 6),
        ),
        (
            Name::Binop(",".to_string()),
            Precedence(Associativity::Right, 1),
        ),
        (
            Name::Binop("::".to_string()),
            Precedence(Associativity::Right, 5),
        ),
        (
            Name::Binop("$".to_string()),
            Precedence(Associativity::Right, 0),
        ),
        (
            Name::Binop("==".to_string()),
            Precedence(Associativity::None, 4),
        ),
        (
            Name::Binop("!=".to_string()),
            Precedence(Associativity::None, 4),
        ),
        (
            Name::Binop("<".to_string()),
            Precedence(Associativity::None, 4),
        ),
        (
            Name::Binop("<=".to_string()),
            Precedence(Associativity::None, 4),
        ),
        (
            Name::Binop(">".to_string()),
            Precedence(Associativity::None, 4),
        ),
        (
            Name::Binop(">=".to_string()),
            Precedence(Associativity::None, 4),
        ),
    ])
}

// @Cleanup: move to AST (probably)
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Precedence(pub Associativity, pub u8);

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Associativity {
    Left,
    Right,
    None,
}

pub trait ApplyPrecedence {
    fn apply(&mut self, precs: &BTreeMap<Name, Precedence>);
}

impl<'a> ApplyPrecedence for Definition<'a> {
    fn apply(&mut self, precs: &BTreeMap<Name, Precedence>) {
        for (lhs, rhs) in self.assignments.iter_mut() {
            lhs.apply(precs);
            rhs.apply(precs);
        }
    }
}

impl<'a> ApplyPrecedence for Lhs<'a> {
    fn apply(&mut self, precs: &BTreeMap<Name, Precedence>) {
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

impl<'a> ApplyPrecedence for Pattern<'a> {
    fn apply(&mut self, precs: &BTreeMap<Name, Precedence>) {
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
                        // @Todo @Errors: throw a proper parse error
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

impl<'a> ApplyPrecedence for Expr<'a> {
    fn apply(&mut self, precs: &BTreeMap<Name, Precedence>) {
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
                        .get(&l_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));
                    let Precedence(r_assoc, r_pri) = precs
                        .get(&r_op)
                        .unwrap_or(&Precedence(Associativity::Left, 9));

                    if l_pri == r_pri
                        && *l_assoc == Associativity::None
                        && *r_assoc == Associativity::None
                    {
                        // @Todo @Errors: throw a proper parse error
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
                definitions: assignments,
                in_expr,
            } => {
                for (_name, defns) in assignments {
                    for (lhs, rhs) in defns.iter_mut() {
                        lhs.apply(precs);
                        rhs.apply(precs);
                    }
                }
                in_expr.apply(precs);
            }
            Expr::Lambda { lhs, rhs } => {
                for mut pat in lhs.args() {
                    pat.apply(precs);
                }
                rhs.apply(precs);
            }
        }
    }
}
