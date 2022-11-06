use std::collections::HashMap;

use crate::ast::{Chunk, Expr, Lhs, Name, Pattern, Term};

/*
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct PrecTable(HashMap<Name, Precedence>);

impl PrecTable {
    pub fn new() -> Self {
        PrecTable(HashMap::new())
    }
}
*/

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Precedence(pub Associativity, pub u8);

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Associativity {
    Left,
    Right,
    None,
}

pub trait ApplyPrecedence {
    fn apply(&mut self, precs: &HashMap<Name, Precedence>);
}

impl<'a> ApplyPrecedence for Chunk<'a> {
    fn apply(&mut self, precs: &HashMap<Name, Precedence>) {
        // @Note @Cleanup: These defaults should one day be replaced with source code.

        let mut defaults: HashMap<Name, Precedence> = HashMap::with_capacity(13);
        defaults.insert(
            Name::Binop("*".to_string()),
            Precedence(Associativity::Left, 7),
        );
        defaults.insert(
            Name::Binop("/".to_string()),
            Precedence(Associativity::Left, 7),
        );
        defaults.insert(
            Name::Binop("+".to_string()),
            Precedence(Associativity::Left, 6),
        );
        defaults.insert(
            Name::Binop("-".to_string()),
            Precedence(Associativity::Left, 6),
        );
        defaults.insert(
            Name::Binop(",".to_string()),
            Precedence(Associativity::Right, 1),
        );
        defaults.insert(
            Name::Binop("::".to_string()),
            Precedence(Associativity::Right, 5),
        );
        defaults.insert(
            Name::Binop("$".to_string()),
            Precedence(Associativity::Right, 0),
        );
        defaults.insert(
            Name::Binop("==".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("!=".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("<".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop("<=".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop(">".to_string()),
            Precedence(Associativity::None, 4),
        );
        defaults.insert(
            Name::Binop(">=".to_string()),
            Precedence(Associativity::None, 4),
        );

        for (name, prec) in precs {
            defaults.insert(name.clone(), *prec);
        }

        for (_name, defns) in &mut self.assignments {
            for (lhs, rhs) in defns.iter_mut() {
                lhs.apply(&defaults);
                rhs.apply(&defaults);
            }
        }
    }
}

impl<'a> ApplyPrecedence for Lhs<'a> {
    fn apply(&mut self, precs: &HashMap<Name, Precedence>) {
        match self {
            Lhs::Func { args, .. } => {
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
    fn apply(&mut self, precs: &HashMap<Name, Precedence>) {
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
    fn apply(&mut self, precs: &HashMap<Name, Precedence>) {
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
            Expr::Lambda { args: pats, rhs } => {
                for pat in pats {
                    pat.apply(precs);
                }
                rhs.apply(precs);
            }
        }
    }
}
