use crate::ast;
use crate::scope::Scope;

use std::sync::atomic::{self, AtomicU64};

const HUCK_TABLE_NAME: &str = "Huck";

/// Generates a new and unique u64 each time it's called.
fn unique() -> u64 {
    static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);
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
                        lua.push_str(&generate_curried_function(args, &expr));
                    }
                }
                ast::Lhs::Binop { a, op, b } => {
                    // It's a binop, so we should generate a function
                    lua.push_str(&generate_curried_function(
                        &vec![a.clone(), b.clone()],
                        &expr,
                    ));
                }
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
                    lua.push_str(", "); // @Currying
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
                    let lua_arg_name = format!("_HUCK_{}", ids[i]);
                    generate_pattern_match(&args[i], &lua_arg_name, &mut conditions, &mut bindings);
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

fn generate_pattern_match<'file>(
    pat: &ast::Pattern<'file>,
    lua_arg_name: &str,
    conditions: &mut Vec<String>,
    bindings: &mut Vec<String>,
) {
    // This function takes a Lua argument name,
    // e.g. _HUCK_0, _HUCK_12[3], _HUCK_3[13][334] or whatever.
    // This is to allow nested pattern matches.
    match pat {
        ast::Pattern::Bind(s) => {
            bindings.push(format!("local {} = {}\n", s, lua_arg_name));
        }
        ast::Pattern::List(list) => {
            // Check that the list is the correct length
            conditions.push(format!("#{} == {}", lua_arg_name, list.len()));

            // Check that each pattern matches
            for j in 0..list.len() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, j + 1);
                generate_pattern_match(&list[j], &new_lua_arg_name, conditions, bindings);
            }
        }
        ast::Pattern::Numeral(lit) => {
            conditions.push(format!("{} == {}", lua_arg_name, lit));
        }
        ast::Pattern::String(lit) => {
            conditions.push(format!("{} == {}", lua_arg_name, lit));
        }
        ast::Pattern::Destructure { constructor, args } => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, constructor
            ));

            // Check that each pattern matches
            for j in 0..args.len() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, j + 1);
                generate_pattern_match(&args[j], &new_lua_arg_name, conditions, bindings);
            }
        }
        ast::Pattern::Binop { lhs, rhs, operator } => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, operator
            ));

            // Check that the LHS pattern matches
            generate_pattern_match(
                &lhs,
                &format!("{}[{}]", lua_arg_name, 1),
                conditions,
                bindings,
            );

            // Check that the RHS pattern matches
            generate_pattern_match(
                &rhs,
                &format!("{}[{}]", lua_arg_name, 2),
                conditions,
                bindings,
            );
        }
        ast::Pattern::UnaryConstructor(name) => {
            debug_assert!(matches!(name, ast::Name::Ident(_)));
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, name
            ));
        }
    };
}

fn generate_curried_function<'file>(args: &[ast::Pattern<'file>], expr: &ast::Expr) -> String {
    let mut lua = String::new();

    lua.push_str("function(");
    lua.push_str(&args.generate()); // @Currying
    lua.push_str(")\nreturn ");
    lua.push_str(&expr.generate());
    lua.push_str("\nend");

    lua
}

impl<'file> Generate for [ast::Pattern<'file>] {
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
                lua.push_str(", "); // @Currying
            }
        }

        lua
    }
}

impl Generate for ast::Name {
    /// Generates a Lua-safe name for the Huck Name.
    fn generate(&self) -> String {
        match self {
            // @Todo: remap Lua keywords
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
                lua.push_str(&argument.generate()); // @Currying
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
                lua.push_str(", "); // @Currying
                lua.push_str(&rhs.generate());
                lua.push(')');

                lua
            }
            ast::Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut lua = String::new();

                // Open a new scope (i.e. an immediately-called function so that return works)
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
                lua.push_str(&args.generate()); // @Currying
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
