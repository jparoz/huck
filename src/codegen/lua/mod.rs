use crate::ast;
use crate::scope::Scope;

use std::sync::atomic::{self, AtomicU64};

const HUCK_TABLE_NAME: &str = "Huck";

static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);
/// Generates a new and unique u64 each time it's called.
fn unique() -> u64 {
    UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed)
}

pub trait Generate {
    fn generate(&self) -> String;
}

impl<'file> Generate for Scope<'file> {
    /// Generate Lua code for the given Scope.
    /// This will generate a Lua chunk which returns a table containing the definitions given in the
    /// Huck scope.
    fn generate(&self) -> String {
        let mut lua = "return {\n".to_string();

        for (name, typed_defn) in self.iter() {
            lua.push_str(&format!("[\"{}\"] = ", name));
            lua.push_str(&typed_defn.definition.generate());
            lua.push_str(",\n");
        }

        lua.push('}');

        lua
    }
}

impl<'file> Generate for ast::Definition<'file> {
    /// Generates a Lua expression representing a Huck definition,
    /// even if it's defined on multiple lines.
    /// This has to be generated from the Vec<Assignment>,
    /// because in the case of multiple definitions,
    /// we have to generate a Lua 'switch' statement.
    fn generate(&self) -> String {
        debug_assert!(self.len() > 0);

        let mut lua = String::new();

        if self.len() == 1 {
            // No need for a switch
            let (lhs, expr) = &self[0];
            match lhs {
                ast::Lhs::Func { args, .. } => {
                    if args.len() == 0 {
                        // should be a value
                        lua.push_str(&expr.generate());
                    } else {
                        // should be a function
                        lua.push_str("function(");
                        lua.push_str(&args.generate());
                        lua.push_str(")\nreturn ");
                        lua.push_str(&expr.generate());
                        lua.push_str("\nend");
                    }
                }
                ast::Lhs::Binop { a, op, b } => todo!(),
            }
        } else {
            // self.len() > 1
            // Need to switch on the assignment LHSs using if-thens
            lua.push_str("function(");

            let arg_count = self[0].0.arg_count();
            let mut ids = Vec::with_capacity(arg_count);
            for i in 0..arg_count {
                let id = unique();
                ids.push(id);
                lua.push_str(&format!("_HUCK_{}", id));
                if i < arg_count - 1 {
                    lua.push_str(", ");
                }
            }

            lua.push_str(")\n");

            for (lhs, expr) in self.iter() {
                // @Fixme @Errors: this should be a compile error, not an assert
                assert_eq!(arg_count, lhs.arg_count());

                let args = match lhs {
                    ast::Lhs::Func { args, .. } => args.clone(),
                    ast::Lhs::Binop { a, b, .. } => vec![a.clone(), b.clone()],
                };

                let mut conditions = Vec::new();
                let mut bindings = Vec::new();

                for i in 0..arg_count {
                    match &args[i] {
                        ast::Pattern::Bind(s) => {
                            bindings.push(format!("local {} = _HUCK_{}\n", s, ids[i]));
                        }
                        ast::Pattern::List(v) => {
                            todo!();
                            for j in 0..v.len() {
                                // @Fixme: probably wrong, need to do something with v[j]
                                bindings.push(format!(
                                    "local {} = _HUCK_{}[{}]\n",
                                    v[j],
                                    ids[i],
                                    j + 1,
                                ));
                            }
                        }
                        ast::Pattern::Destructure { args: v, .. } => {
                            todo!();
                            for j in 0..v.len() {
                                // @Fixme: probably wrong, need to do something with v[j]
                                bindings.push(format!(
                                    "local {} = _HUCK_{}[{}]\n",
                                    v[j],
                                    ids[i],
                                    j + 1,
                                ));
                            }
                        }
                        ast::Pattern::Numeral(lit) => {
                            conditions.push(format!("_HUCK_{} == {}", ids[i], lit));
                        }
                        ast::Pattern::String(lit) => {
                            conditions.push(format!("_HUCK_{} == {}", ids[i], lit));
                        }
                        ast::Pattern::Binop { lhs, rhs, operator } => {
                            conditions.push(format!(
                                r#"getmetatable(_HUCK_{}).__variant == "{}""#,
                                ids[i], operator
                            ));
                            // @Todo: generate conditions for pattern matches on operands

                            // @Fixme: probably wrong, need to do something with lhs/rhs
                            bindings.push(format!("local {} = _HUCK_{}[1]\n", lhs, ids[i],));
                            bindings.push(format!("local {} = _HUCK_{}[2]\n", rhs, ids[i],));
                        }
                        ast::Pattern::UnaryConstructor(name) => {
                            debug_assert!(matches!(name, ast::Name::Ident(_)));
                            conditions.push(format!(
                                r#"getmetatable(_HUCK_{}).__variant == "{}""#,
                                ids[i], name
                            ));
                        }
                    };
                }

                if conditions.is_empty() {
                    lua.push_str("do\n");
                } else {
                    lua.push_str("if ");
                    for i in 0..conditions.len() {
                        lua.push_str(&format!("({})", conditions[i]));
                        if i < conditions.len() - 1 {
                            lua.push_str("\nand ");
                        }
                    }
                    lua.push_str(" then\n")
                }

                for b in bindings {
                    lua.push_str(&b);
                }

                lua.push_str("return ");
                lua.push_str(&expr.generate());
                lua.push_str("\nend\n")
            }

            lua.push_str(&format!(
                r#"error("Unmatched pattern in function `{}`")"#,
                &self[0].0.name()
            ));

            lua.push_str("\nend");
        }

        lua
    }
}

impl<'file> Generate for Vec<ast::Pattern<'file>> {
    /// Generates a Lua argument list.
    fn generate(&self) -> String {
        debug_assert!(self.len() > 0);

        let mut lua = String::new();

        for i in 0..self.len() {
            let arg = match &self[i] {
                ast::Pattern::Bind(var) => var.to_string(),
                ast::Pattern::List(_) => todo!(),
                ast::Pattern::Numeral(_) => todo!(),
                ast::Pattern::String(_) => todo!(),
                ast::Pattern::Binop { operator, lhs, rhs } => todo!(),
                ast::Pattern::UnaryConstructor(name) => todo!(),
                ast::Pattern::Destructure { constructor, args } => todo!(),
            };
            lua.push_str(&arg);
            if i < self.len() - 1 {
                lua.push_str(", ");
            }
        }

        lua
    }
}

impl Generate for ast::Name {
    /// Generates a Lua-safe name for the Huck Name.
    fn generate(&self) -> String {
        match self {
            ast::Name::Ident(s) => s.clone(),
            ast::Name::Binop(s) => {
                // @Todo: Convert the binop into some kind of Lua identifier.
                // Maybe something like this conversion:
                //      >>=     ->      _HUCK_RANGLE_RANGLE_EQUALS
                //      <*>     ->      _HUCK_LANGLE_STAR_RANGLE
                //      &&      ->      _HUCK_AMPERS_AMPERS
                // Note that the binop might be a valid Lua binop
                // (which possibly will/should never happen),
                // but this method should probably still do the conversion.
                todo!("Convert the binop into some kind of Lua identifier: {}", s)
            }
        }
    }
}

impl<'file> Generate for ast::Expr<'file> {
    fn generate(&self) -> String {
        match self {
            ast::Expr::Term(term) => term.generate(),
            ast::Expr::App { func, argument } => {
                let mut lua = String::new();

                // Func (as an expr, surrounded in brackets)
                lua.push('('); // @Note: not strictly necessary?
                lua.push_str(&func.generate());
                lua.push(')'); // @Note: not strictly necessary?

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                lua.push('(');
                lua.push_str(&argument.generate());
                lua.push(')');

                lua
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                let mut lua = String::new();

                // @Note @Fixme: this should check for Lua's builtin operators and use those
                // if available

                // Op
                lua.push_str(&format!("{}[\"{}\"]", HUCK_TABLE_NAME, operator));

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                lua.push('(');
                lua.push_str(&lhs.generate());
                lua.push_str(", ");
                lua.push_str(&rhs.generate());
                lua.push(')');

                lua
            }
            ast::Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut lua = String::new();

                // Open a new function, and local variable declaration
                lua.push_str("(function()\n");

                // Make a new local variable for each assignment
                for definition in definitions.values() {
                    let (lhs, _expr) = &definition[0];
                    lua.push_str("local ");
                    lua.push_str(&lhs.name().generate());
                    lua.push_str(" = ");
                    lua.push_str(&definition.generate());
                    lua.push('\n');
                }

                // Generate the in_expr
                lua.push_str("return ");
                lua.push_str(&in_expr.generate());
                lua.push('\n');

                lua.push_str("\nend)()");

                lua
            }
            ast::Expr::Lambda { args, rhs } => {
                debug_assert!(args.len() > 0);

                let mut lua = String::new();

                lua.push_str("function(");
                lua.push_str(&args.generate());
                lua.push_str(")\nreturn ");

                lua.push_str(&rhs.generate());

                lua.push_str("\nend");

                lua
            }
        }
    }
}

impl<'file> Generate for ast::Term<'file> {
    fn generate(&self) -> String {
        match self {
            ast::Term::Numeral(num) => num.generate(),

            // possible @XXX, @Todo: escape (or check escaping) better
            // @Note: includes the quotes
            ast::Term::String(s) => s.to_string(),

            ast::Term::List(v) => {
                // @Note: this is where the semantics for Huck Lists are decided.
                // The below simply converts them as Lua lists;
                // possibly one day we should instead convert them to Lua iterators.
                let mut lua = String::new();
                lua.push('{');
                for item in v {
                    lua.push_str(&item.generate());
                    lua.push_str(", ");
                }
                lua.push('}');
                lua
            }
            ast::Term::Name(name) => name.generate(),
            ast::Term::Parens(expr) => {
                let mut lua = String::new();

                lua.push('(');
                lua.push_str(&expr.generate());
                lua.push(')');

                lua
            }
        }
    }
}

impl<'file> Generate for ast::Numeral<'file> {
    fn generate(&self) -> String {
        match self {
            ast::Numeral::Int(s) | ast::Numeral::Float(s) => s.to_string(),
        }
    }
}
