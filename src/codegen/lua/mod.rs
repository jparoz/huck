use crate::ast;
use crate::scope::Scope;

use std::fmt::Write;
use std::sync::atomic::{self, AtomicU64};

type WriteResult = Result<(), std::fmt::Error>;

// @Cleanup: maybe move this onto CodeGenerator?
/// Generates a new and unique u64 each time it's called.
fn unique() -> u64 {
    static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);
    UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed)
}

/// Generates Lua code, and maintains all necessary state to do so.
/// Methods on this struct should generally correspond to Lua constructs,
/// not to Huck constructs.
#[derive(Debug)]
pub struct CodeGenerator {
    // @Cleanup: not pub, use a wrapper function
    pub lua: String,

    // @Todo: this shouldn't be static, should be an option at transpile time
    generated_name_prefix: &'static str,
}

impl CodeGenerator {
    pub fn new() -> Self {
        CodeGenerator {
            lua: String::new(),
            generated_name_prefix: "_HUCK", // @Hardcode
        }
    }

    // Generate methods

    /// Generate Lua code for the given Scope.
    /// This will generate a Lua chunk which returns a table containing the definitions given in the
    /// Huck scope.
    pub fn scope<'file>(&mut self, scope: &Scope<'file>) -> WriteResult {
        // @Hardcode @Todo: this should be derived from the filename or something
        let module_name = "M";

        write!(self.lua, "local {} = {{}}\n\n", module_name)?;

        for (name, typed_defn) in scope.iter() {
            write!(self.lua, r#"{}["{}"] = "#, module_name, name)?;
            self.definition(&typed_defn.definition)?;
            self.lua.write_str("\n\n")?;
        }

        self.lua.write_str(&format!("return {}", module_name))
    }

    /// Generates a Lua expression representing a Huck definition,
    /// even if it's defined on multiple lines.
    /// This has to be generated from the Vec<Assignment>,
    /// because in the case of multiple definitions,
    /// we have to generate a Lua 'switch' statement.
    fn definition<'file>(&mut self, defn: &ast::Definition<'file>) -> WriteResult {
        debug_assert!(defn.len() > 0);

        if defn.len() == 1 {
            // No need for a switch
            let (lhs, expr) = &defn[0];

            self.curried_function(&lhs.args(), expr)?;
        } else {
            // self.len() > 1
            // Need to switch on the assignment LHSs using if-thens
            self.lua.write_str("function(")?;

            let arg_count = defn[0].0.arg_count();
            let mut ids = Vec::with_capacity(arg_count);
            for i in 0..arg_count {
                let id = unique();
                ids.push(id);
                write!(self.lua, "{}_{}", self.generated_name_prefix, id)?;
                if i < arg_count - 1 {
                    self.lua.write_str(", ")?; // @Currying
                }
            }

            self.lua.write_str(")\n")?;

            for (lhs, expr) in defn.iter() {
                // @Fixme @Errors: this should be a compile error, not an assert
                assert_eq!(arg_count, lhs.arg_count());

                let args = lhs.args();
                let mut conditions = Vec::new();
                let mut bindings = Vec::new();

                for i in 0..arg_count {
                    let lua_arg_name = format!("{}_{}", self.generated_name_prefix, ids[i]);
                    self.pattern_match(&args[i], &lua_arg_name, &mut conditions, &mut bindings)?;
                }

                // @DRY
                if conditions.is_empty() {
                    self.lua.write_str("do\n")?;
                } else {
                    self.lua.write_str("if ")?;
                    for i in 0..conditions.len() {
                        self.lua.write_char('(')?;
                        self.lua.write_str(&conditions[i])?;
                        self.lua.write_char(')')?;
                        if i < conditions.len() - 1 {
                            self.lua.write_str("\nand ")?;
                        }
                    }
                    self.lua.write_str(" then\n")?;
                }

                for b in bindings {
                    self.lua.write_str(&b)?;
                }

                self.lua.write_str("return ")?;
                self.expr(expr)?;
                self.lua.write_str("\nend\n")?;
            }

            write!(
                self.lua,
                r#"Unmatched pattern in function `{}`"#,
                &defn[0].0.name()
            )?;

            self.lua.write_str("\nend")?;
        }

        Ok(())
    }

    fn expr<'file>(&mut self, expr: &ast::Expr<'file>) -> WriteResult {
        match expr {
            ast::Expr::Term(term) => self.term(term),
            ast::Expr::App { func, argument } => {
                // Func (as an expr, surrounded in brackets)
                self.lua.write_char('(')?; // @Note: not strictly necessary?
                self.expr(func)?;
                self.lua.write_char(')')?; // @Note: not strictly necessary?

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                self.lua.write_char('(')?;
                self.expr(argument)?; // @Currying
                self.lua.write_char(')')?;
                Ok(())
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                // @Note @Fixme: this should check for Lua's builtin operators and use those
                // if available

                // Op
                // @Fixme: this should refer to a local, not some weird global table
                self.lua
                    .write_str(&format!("{}[\"{}\"]", self.generated_name_prefix, operator))?;

                // Argument (function call syntax)
                // @Note: this assumes functions are curried (? maybe not if tuples desugar to
                // bare (func)(a, b) instead of (func)((a, b)) which doesn't make sense anyway)
                self.lua.write_char('(')?;
                self.expr(lhs)?;
                self.lua.write_str(", ")?; // @Currying
                self.expr(rhs)?;
                self.lua.write_char(')')?;
                Ok(())
            }
            ast::Expr::Let {
                definitions,
                in_expr,
            } => {
                // Open a new scope (i.e. an immediately-called function so that return works)
                self.lua.write_str("(function()\n")?;

                // Make a new local variable for each assignment
                for definition in definitions.values() {
                    write!(self.lua, "local {} = ", definition[0].0.name())?;
                    self.definition(definition)?;
                    self.lua.write_char('\n')?;
                }

                // Generate the in_expr
                self.lua.write_str("return ")?;
                self.expr(in_expr)?;

                self.lua.write_str("\nend)()")
            }
            ast::Expr::Lambda { args, rhs } => {
                debug_assert!(args.len() > 0);
                self.curried_function(args, rhs)
            }
        }
    }

    fn term<'file>(&mut self, term: &ast::Term<'file>) -> WriteResult {
        match term {
            // @Inline?
            ast::Term::Numeral(num) => self.numeric_literal(num),

            // possible @XXX, @Todo: escape (or check escaping) better
            // @Note: includes the quotes
            ast::Term::String(s) => self.lua.write_str(s),

            // @Note: this is where the semantics for Huck Lists are decided.
            // The below simply converts them as Lua lists;
            // possibly one day we should instead convert them to Lua iterators.
            ast::Term::List(v) => {
                self.lua.write_char('{')?;
                for (i, e) in v.iter().enumerate() {
                    self.expr(e)?;
                    if i < v.len() {
                        write!(self.lua, ", ")?;
                    }
                }
                self.lua.write_char('}')
            }

            // @Inline?
            ast::Term::Name(name) => self.name(name),

            ast::Term::Parens(expr) => {
                self.lua.write_char('(')?;
                self.expr(expr)?;
                self.lua.write_char(')')
            }
        }
    }

    fn curried_function<'file>(
        &mut self,
        args: &[ast::Pattern<'file>],
        expr: &ast::Expr,
    ) -> WriteResult {
        let arg_count = args.len();
        let mut ids = Vec::with_capacity(arg_count);

        let mut conditions: Vec<String> = Vec::new();
        let mut bindings: Vec<String> = Vec::new();

        // Start the functions
        for i in 0..arg_count {
            let id = unique();
            ids.push(id);

            self.lua.write_str("function(")?;
            self.lua
                .write_str(&format!("{}_{}", self.generated_name_prefix, id))?;
            self.lua.write_str(")\n")?;

            self.pattern_match(
                &args[i],
                &format!("{}_{}", self.generated_name_prefix, id),
                &mut conditions,
                &mut bindings,
            )?;

            for b in bindings.drain(..) {
                self.lua.write_str(&b)?;
            }

            if i < arg_count - 1 {
                self.lua.write_str("return ")?;
            }
        }

        // Return the expr

        // @DRY
        if conditions.is_empty() {
            // If we have no Huck arguments,
            // then we should be a Lua value, not a Lua function;
            // so we don't return, we just are.
            if arg_count > 0 {
                self.lua.write_str("return ")?;
            }

            self.expr(expr)?;
        } else {
            self.lua.write_str("if ")?;
            for i in 0..conditions.len() {
                self.lua.write_char('(')?;
                self.lua.write_str(&conditions[i])?;
                self.lua.write_char(')')?;
                if i < conditions.len() - 1 {
                    self.lua.write_str("\nand ")?;
                }
            }
            self.lua.write_str(" then\n")?;
            self.lua.write_str("return ")?;
            self.expr(expr)?;
            self.lua.write_str("\nend")?;
        }

        // End the functions
        for _ in 0..arg_count {
            self.lua.write_str("\nend")?;
        }
        Ok(())
    }

    fn pattern_match<'file>(
        &mut self,
        pat: &ast::Pattern<'file>,
        lua_arg_name: &str,
        conditions: &mut Vec<String>,
        bindings: &mut Vec<String>,
    ) -> WriteResult {
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
                    self.pattern_match(&list[j], &new_lua_arg_name, conditions, bindings)?;
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
                    self.pattern_match(&args[j], &new_lua_arg_name, conditions, bindings)?;
                }
            }
            ast::Pattern::Binop { lhs, rhs, operator } => {
                // Check that it's the right variant
                conditions.push(format!(
                    r#"getmetatable({}).__variant == "{}""#,
                    lua_arg_name, operator
                ));

                // Check that the LHS pattern matches
                self.pattern_match(
                    &lhs,
                    &format!("{}[{}]", lua_arg_name, 1),
                    conditions,
                    bindings,
                )?;

                // Check that the RHS pattern matches
                self.pattern_match(
                    &rhs,
                    &format!("{}[{}]", lua_arg_name, 2),
                    conditions,
                    bindings,
                )?;
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

        Ok(())
    }

    /// Generates a Lua-safe name for the Huck Name.
    fn name<'file>(&mut self, name: &ast::Name) -> WriteResult {
        match name {
            // @Todo: remap Lua keywords
            ast::Name::Ident(s) => write!(self.lua, "{}", s),
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

    fn numeric_literal<'file>(&mut self, lit: &ast::Numeral<'file>) -> WriteResult {
        match lit {
            ast::Numeral::Int(s) | ast::Numeral::Float(s) => write!(self.lua, "{}", s),
        }
    }
}
