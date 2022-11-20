#[cfg(test)]
mod test;

use crate::ast;
use crate::scope::Scope;

use std::fmt::Write;

use super::Error as CodegenError;

/// Generates Lua for the given Huck Scope.
pub fn generate<'file>(scope: &Scope<'file>) -> Result<String, CodegenError> {
    let mut cg = CodeGenerator::default();
    cg.scope(scope)?;
    Ok(cg.lua)
}

type CodegenResult = Result<(), CodegenError>;

/// Generates Lua code, and maintains all necessary state to do so.
/// Methods on this struct should generally correspond to Lua constructs,
/// not to Huck constructs.
#[derive(Debug)]
struct CodeGenerator<'a> {
    lua: String,

    // These are used in generating curried functions.
    conditions: Vec<String>,
    bindings: Vec<String>,

    generated_name_prefix: &'a str,
    module_name: &'a str,

    id_counter: u64,
}

impl<'a> CodeGenerator<'a> {
    fn new(generated_name_prefix: &'a str, module_name: &'a str) -> Self {
        CodeGenerator {
            lua: String::new(),

            conditions: Vec::new(),
            bindings: Vec::new(),

            generated_name_prefix,
            module_name,

            id_counter: 0,
        }
    }

    /// Generate Lua code for the given Scope.
    /// This will generate a Lua chunk which returns a table containing the definitions given in the
    /// Huck scope.
    fn scope<'file>(&mut self, scope: &Scope<'file>) -> CodegenResult {
        write!(self.lua, "local {} = {{}}\n\n", self.module_name)?;

        for (name, typed_defn) in scope.iter() {
            write!(self.lua, r#"{}["{}"] = "#, self.module_name, name)?;
            self.definition(&typed_defn.definition)?;
            self.lua.write_str("\n\n")?;
        }

        Ok(self
            .lua
            .write_str(&format!("return {}", self.module_name))?)
    }

    /// Generates a Lua expression representing a Huck definition,
    /// even if it's defined on multiple lines.
    /// This has to be generated from the Vec<Assignment>,
    /// because in the case of multiple definitions,
    /// we have to generate a Lua 'switch' statement.
    fn definition<'file>(&mut self, defn: &ast::Definition<'file>) -> CodegenResult {
        self.curried_function(defn)
    }

    fn expr<'file>(&mut self, expr: &ast::Expr<'file>) -> CodegenResult {
        match expr {
            ast::Expr::Term(term) => self.term(term),
            ast::Expr::App { func, argument } => {
                // Func (as an expr, surrounded in brackets)
                self.lua.write_char('(')?; // @Note: not strictly necessary?
                self.expr(func)?;
                self.lua.write_char(')')?; // @Note: not strictly necessary?

                // Argument (function call syntax)
                self.lua.write_char('(')?;
                self.expr(argument)?;
                self.lua.write_char(')')?;
                Ok(())
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                if is_lua_binop(operator.as_str()) {
                    write!(self.lua, "({} {} {})", lhs, operator, rhs)?; // @Checkme: test better
                } else {
                    // Op
                    // @Fixme: this should refer to a local, not some weird global table
                    self.lua
                        .write_str(&format!("{}[\"{}\"]", self.generated_name_prefix, operator))?;

                    // Argument (function call syntax)
                    self.lua.write_char('(')?;
                    self.expr(lhs)?;
                    self.lua.write_str(")(")?;
                    self.expr(rhs)?;
                    self.lua.write_char(')')?;
                }

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

                self.lua.write_str("\nend)()")?;
                Ok(())
            }
            ast::Expr::Lambda { lhs, rhs } => {
                debug_assert!(lhs.arg_count() > 0);
                self.curried_function(&vec![(lhs.clone(), *rhs.clone())]) // @Fixme: don't clone?
            }
        }
    }

    fn term<'file>(&mut self, term: &ast::Term<'file>) -> CodegenResult {
        match term {
            // @Inline?
            ast::Term::Numeral(num) => self.numeric_literal(num),

            // possible @XXX, @Todo: escape (or check escaping) better
            // @Note: includes the quotes
            ast::Term::String(s) => Ok(self.lua.write_str(s)?),

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
                Ok(self.lua.write_char('}')?)
            }

            // @Inline?
            ast::Term::Name(name) => self.name(name),

            ast::Term::Parens(expr) => {
                self.lua.write_char('(')?;
                self.expr(expr)?;
                Ok(self.lua.write_char(')')?)
            }
        }
    }

    fn curried_function<'file>(&mut self, definition: &ast::Definition) -> CodegenResult {
        debug_assert!(definition.len() > 0);

        let arg_count = definition[0].0.arg_count();
        let mut ids = Vec::with_capacity(arg_count);

        // Start the functions
        for i in 0..arg_count {
            let id = self.unique();
            ids.push(id);

            self.lua.write_str("function(")?;
            self.lua
                .write_str(&format!("{}_{}", self.generated_name_prefix, ids[i]))?;
            self.lua.write_str(")\n")?;

            if i < arg_count - 1 {
                self.lua.write_str("return ")?;
            }
        }

        // Return the expr

        let mut has_any_conditions = false;
        let mut has_unconditional_branch = false;

        for (lhs, expr) in definition {
            let args = lhs.args();
            if arg_count != args.len() {
                return Err(CodegenError::IncorrectArgumentCount(format!(
                    "{}",
                    lhs.name()
                )));
            }

            for i in 0..arg_count {
                self.pattern_match(
                    &args[i],
                    &format!("{}_{}", self.generated_name_prefix, ids[i]),
                )?;
            }

            has_any_conditions = has_any_conditions || !self.conditions.is_empty();

            if self.conditions.is_empty() {
                has_unconditional_branch = true;

                // If we have no Huck arguments,
                // then we should be a Lua value, not a Lua function;
                // so we don't return, we just are.
                if arg_count > 0 {
                    // First bind the bindings
                    for b in self.bindings.drain(..) {
                        self.lua.write_str(&b)?;
                    }
                    // Then return the return value
                    self.lua.write_str("return ")?;
                }

                self.expr(expr)?;
            } else {
                // Check the conditions
                self.lua.write_str("if ")?;
                let condition_count = self.conditions.len();
                for (i, cond) in self.conditions.drain(..).enumerate() {
                    write!(self.lua, "({})", cond)?;
                    if i < condition_count - 1 {
                        self.lua.write_str("\nand ")?;
                    }
                }
                self.lua.write_str(" then\n")?;

                // If the conditions are met, then bind the bindings
                for b in self.bindings.drain(..) {
                    self.lua.write_str(&b)?;
                }

                // Return the return value
                self.lua.write_str("return ")?;
                self.expr(expr)?;

                // End the if
                self.lua.write_str("\nend\n")?;
            }
        }

        // Emit a runtime error in case no pattern matches
        if has_any_conditions && !has_unconditional_branch {
            write!(
                self.lua,
                "\nerror(\"Unmatched pattern in function `{}`\")",
                &definition[0].0.name()
            )?;
        }

        // End the functions
        for _ in 0..arg_count {
            self.lua.write_str("\nend")?;
        }
        Ok(())
    }

    /// Generates code for a pattern match.
    /// Note: This _does not_ modify self.lua at all, only `self.conditions` and `self.bindings`.
    fn pattern_match<'file>(
        &mut self,
        pat: &ast::Pattern<'file>,
        lua_arg_name: &str,
    ) -> CodegenResult {
        // This function takes a Lua argument name,
        // e.g. _HUCK_0, _HUCK_12[3], _HUCK_3[13][334] or whatever.
        // This is to allow nested pattern matches.
        match pat {
            ast::Pattern::Bind(s) => {
                self.bindings
                    .push(format!("local {} = {}\n", s, lua_arg_name));
            }
            ast::Pattern::List(list) => {
                // Check that the list is the correct length
                self.conditions
                    .push(format!("#{} == {}", lua_arg_name, list.len()));

                // Check that each pattern matches
                for j in 0..list.len() {
                    let new_lua_arg_name = format!("{}[{}]", lua_arg_name, j + 1);
                    self.pattern_match(&list[j], &new_lua_arg_name)?;
                }
            }
            ast::Pattern::Numeral(lit) => {
                self.conditions.push(format!("{} == {}", lua_arg_name, lit));
            }
            ast::Pattern::String(lit) => {
                self.conditions.push(format!("{} == {}", lua_arg_name, lit));
            }
            ast::Pattern::Destructure { constructor, args } => {
                // Check that it's the right variant
                self.conditions.push(format!(
                    r#"getmetatable({}).__variant == "{}""#,
                    lua_arg_name, constructor
                ));

                // Check that each pattern matches
                for j in 0..args.len() {
                    let new_lua_arg_name = format!("{}[{}]", lua_arg_name, j + 1);
                    self.pattern_match(&args[j], &new_lua_arg_name)?;
                }
            }
            ast::Pattern::Binop { lhs, rhs, operator } => {
                // Check that it's the right variant
                self.conditions.push(format!(
                    r#"getmetatable({}).__variant == "{}""#,
                    lua_arg_name, operator
                ));

                // Check that the LHS pattern matches
                self.pattern_match(&lhs, &format!("{}[{}]", lua_arg_name, 1))?;

                // Check that the RHS pattern matches
                self.pattern_match(&rhs, &format!("{}[{}]", lua_arg_name, 2))?;
            }
            ast::Pattern::UnaryConstructor(name) => {
                debug_assert!(matches!(name, ast::Name::Ident(_)));
                // Check that it's the right variant
                self.conditions.push(format!(
                    r#"getmetatable({}).__variant == "{}""#,
                    lua_arg_name, name
                ));
            }
        };

        Ok(())
    }

    /// Generates a Lua-safe name for the Huck Name.
    fn name<'file>(&mut self, name: &ast::Name) -> CodegenResult {
        match name {
            // @Todo: remap Lua keywords
            ast::Name::Ident(s) => Ok(write!(self.lua, "{}", s)?),
            ast::Name::Lambda => Ok(write!(self.lua, "lambda")?), // @Checkme: should be unreachable
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

    fn numeric_literal<'file>(&mut self, lit: &ast::Numeral<'file>) -> CodegenResult {
        match lit {
            ast::Numeral::Int(s) | ast::Numeral::Float(s) => Ok(write!(self.lua, "{}", s)?),
        }
    }

    fn unique(&mut self) -> u64 {
        let id = self.id_counter;
        self.id_counter += 1;
        id
    }
}

impl<'a> Default for CodeGenerator<'a> {
    fn default() -> Self {
        CodeGenerator {
            lua: String::new(),

            conditions: Vec::new(),
            bindings: Vec::new(),

            generated_name_prefix: "_HUCK",
            module_name: "M",

            id_counter: 0,
        }
    }
}

fn is_lua_binop(op: &str) -> bool {
    // @Todo: maybe we want these ops to have different names in Huck to in Lua.
    // For now, just pass them through.
    match op {
        "+" | "-" | "*" | "/" | "//" | "^" | "%" | "&" | "~" | "|" | ">>" | "<<" | ".." | "<"
        | "<=" | ">" | ">=" | "==" | "~=" | "and" | "or" => true,
        _ => false,
    }
}
