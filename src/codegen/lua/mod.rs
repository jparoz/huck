#[cfg(test)]
mod test;

use crate::ast;
use crate::scope::Scope;
use crate::types::{Type, TypeDefinition};

use std::collections::BTreeSet;
use std::fmt::Write;

use super::Error as CodegenError;

const PREFIX: &str = "_HUCK";

/// Generates Lua for the given Huck Scope.
pub fn generate(scope: &Scope) -> Result<String> {
    CodeGenerator::new(scope).generate()
}

type Result<T> = std::result::Result<T, CodegenError>;

/// Generates Lua code, and maintains all necessary state to do so.
/// Methods on this struct should generally correspond to Lua constructs,
/// not to Huck constructs.
#[derive(Debug)]
struct CodeGenerator<'a> {
    // These are used in generating curried functions.
    conditions: Vec<String>,
    bindings: Vec<String>,

    // This is a String containing the contents of the Lua table which shall be returned.
    return_entries: String,

    // This is the set of definitions which have already been generated.
    generated: BTreeSet<ast::Name>,

    scope: &'a Scope,

    id_counter: u64,
}

impl<'a> CodeGenerator<'a> {
    fn new(scope: &'a Scope) -> Self {
        CodeGenerator {
            conditions: Vec::new(),
            bindings: Vec::new(),

            return_entries: String::new(),

            generated: BTreeSet::new(),

            scope,

            id_counter: 0,
        }
    }

    /// Generate Lua code for the Scope used in CodeGenerator::new.
    /// This will generate a Lua chunk which returns a table
    /// containing the definitions given in the Huck scope.
    fn generate(mut self) -> Result<String> {
        log::trace!(
            "Starting code generation for module {}",
            self.scope.module_path
        );

        let mut lua = String::new();

        writeln!(lua, "local {} = {{}}", PREFIX)?;

        // First, generate code for all the type definitions (i.e. for their constructors).
        // This can be done first
        // because they don't have a real RHS,
        // so they can't refer to anything else.

        log::trace!("  Generating type definitions");
        for (_name, type_defn) in self.scope.type_definitions.iter() {
            write!(lua, "{}", self.type_definition(type_defn)?)?;
        }

        // Next import all the imports.
        log::trace!("  Generating import statements");
        for (name, (_path, stem)) in self.scope.imports.iter() {
            writeln!(lua, r#"{PREFIX}["{name}"] = require("{stem}")["{name}"]"#)?;

            // Mark the import as generated.
            // @Checkme: name clashes? Maybe already caught this?
            assert!(self.generated.insert(name.clone()));
        }

        // Next import all the foreign imports.
        log::trace!("  Generating foreign import statements");
        for (name, (require_string, lua_name, _type_scheme)) in self.scope.foreign_imports.iter() {
            writeln!(
                lua,
                r#"{PREFIX}["{name}"] = require({require_string})["{lua_name}"]"#
            )?;

            // Mark the foreign import as generated.
            // @Checkme: name clashes? Maybe already caught this?
            assert!(self.generated.insert(name.clone()));
        }

        // Next, we can generate all the definitions.
        log::trace!("  Generating definitions");

        // Start by putting all definitions in the queue to be generated.
        // @Fixme: this probably doesn't need to be entirely cloned
        let mut current_pass: Vec<_> = self.scope.definitions.clone().into_iter().collect();
        let mut next_pass = Vec::new();

        loop {
            // If the queue is empty, we're done.
            if current_pass.len() == 0 {
                break;
            }

            log::trace!("  Started a new generation pass");
            // Keep track of whether we've generated anything in this pass.
            let mut generated_anything = false;

            for (name, mut typed_defn) in current_pass.drain(..) {
                log::trace!("    Checking if we can generate {name}...");
                let defn = &mut typed_defn.1;

                // @Errors: this should throw an error saying that
                // there was a type annotation without a corresponding definition.
                assert!(defn.assignments.len() > 0);

                // @Lazy @Laziness: lazy values can be generated in any order

                // If the definition has any arguments, then it will become a Lua function;
                // this means we can generate it in any order.
                // Note that if it has missing dependencies, it will error at runtime;
                // so we should have already caught this in a compile error.
                let has_any_args = defn.assignments[0].0.arg_count() > 0;

                // If the definition has no un-generated dependencies,
                // then we're ready generate it.
                let has_all_deps = defn
                    .dependencies()
                    .iter()
                    // @Fixme: this should check the scope as well,
                    // for e.g. imported functions,
                    // rather than just checking if it's a builtin Lua binop.
                    .all(|n| self.generated.contains(n) || is_lua_binop(n.as_str()));

                if has_any_args || has_all_deps {
                    // Because there are arguments, it's going to be a Lua function.
                    // Thus, we can generate in any order.
                    log::trace!("    Generating {name}");
                    write!(lua, "{}", self.definition(&name, &defn)?)?;

                    // Mark that we have generated something in this pass.
                    generated_anything = true;
                } else {
                    // Skip it for now
                    log::trace!("    Skipping for now.");
                    next_pass.push((name, typed_defn));
                }
            }

            // If we didn't generate anything in this pass,
            // it means we have a cyclic dependency.
            // @Checkme: is this the only time this happens?
            if !generated_anything {
                log::error!(
                    "Error, didn't generate anything in one pass. Next in queue: {:?}",
                    next_pass
                );
                return Err(CodegenError::CyclicDependency(
                    next_pass
                        .iter()
                        .map(|t| {
                            // @Fixme @Errors: filter out entries which depend on the cycle,
                            // but are not part of the cycle themselves.
                            t.0.clone()
                        })
                        .collect(),
                ));
            }

            log::trace!("  Finished generation pass");

            std::mem::swap(&mut current_pass, &mut next_pass);
        }

        log::trace!("Finished generating definitions");

        write!(lua, "return {{\n{}}}", self.return_entries)?;

        Ok(lua)
    }

    // @Todo @Cleanup: move most of this comment to earlier in the pipe, when we make Definitions.
    /// Generates a Lua expression representing a Huck definition,
    /// even if it's defined on multiple lines.
    /// This has to be generated from the Vec<Assignment>,
    /// because in the case of multiple definitions,
    /// we have to generate a Lua 'switch' statement.
    fn definition(&mut self, name: &ast::Name, defn: &ast::Definition) -> Result<String> {
        let mut lua = String::new();

        // Write the definition to the `lua` string.
        write!(lua, r#"{}["{}"] = "#, PREFIX, name)?;
        writeln!(lua, "{}", self.curried_function(&defn.assignments)?)?;
        writeln!(
            self.return_entries,
            r#"["{name}"] = {prefix}["{name}"],"#,
            name = name,
            prefix = PREFIX,
        )?;

        // Mark this definition as generated.
        self.generated.insert(name.clone());

        Ok(lua)
    }

    fn expr(&mut self, expr: &ast::Expr) -> Result<String> {
        match expr {
            ast::Expr::Term(term) => self.term(term),
            ast::Expr::App { func, argument } => {
                Ok(format!("({})({})", self.expr(func)?, self.expr(argument)?))
            }
            ast::Expr::Binop { operator, lhs, rhs } => {
                if is_lua_binop(operator.as_str()) {
                    Ok(format!(
                        "({} {} {})",
                        self.expr(lhs)?,
                        operator,
                        self.expr(rhs)?
                    ))
                } else {
                    Ok(format!(
                        "{}({})({})",
                        self.reference(operator)?,
                        self.expr(lhs)?,
                        self.expr(rhs)?
                    ))
                }
            }

            ast::Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut lua = String::new();

                // Open a new scope (i.e. an immediately-called function so that return works)
                writeln!(lua, "(function()")?;

                // Make a new local variable for each assignment
                for definition in definitions.values() {
                    writeln!(
                        lua,
                        "local {} = {}",
                        definition[0].0.name(),
                        self.curried_function(definition)?
                    )?;
                }

                // Generate the in_expr
                writeln!(lua, "return {}", self.expr(in_expr)?)?;

                // End and call the function
                writeln!(lua, "end)()")?;

                Ok(lua)
            }

            ast::Expr::If {
                cond,
                then_expr,
                else_expr,
            } => Ok(format!(
                "(({}) and ({}) or ({}))",
                self.expr(cond)?,
                self.expr(then_expr)?,
                self.expr(else_expr)?,
            )),

            ast::Expr::Case { expr, arms } => self.case(expr, arms),

            ast::Expr::Lambda { lhs, rhs } => {
                assert!(lhs.arg_count() > 0);
                self.curried_function(&vec![(lhs.clone(), *rhs.clone())]) // @Fixme: don't clone?
            }

            ast::Expr::Lua(lua) | ast::Expr::UnsafeLua(lua) => Ok(format!("({})", lua)),
        }
    }

    fn term(&mut self, term: &ast::Term) -> Result<String> {
        match term {
            ast::Term::Numeral(num) => match num {
                ast::Numeral::Int(s) | ast::Numeral::Float(s) => Ok(s.to_string()),
            },

            // @Note: includes the quotes
            ast::Term::String(s) => Ok(s.to_string()),

            ast::Term::Unit => Ok("nil".to_string()),

            // @Note: this is where the semantics for Huck Lists are decided.
            // The below simply converts them as Lua lists;
            // possibly one day we should instead convert them to Lua iterators.
            ast::Term::List(v) => Ok(format!(
                "{{{}}}",
                v.iter()
                    .map(|e| self.expr(e))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            )),

            ast::Term::Tuple(v) => Ok(format!(
                "{{{}}}",
                v.iter()
                    .map(|e| self.expr(e))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            )),

            ast::Term::Name(name) => self.reference(name),

            ast::Term::Parens(expr) => Ok(format!("({})", self.expr(expr)?)),
        }
    }

    fn case(&mut self, expr: &ast::Expr, arms: &Vec<(ast::Pattern, ast::Expr)>) -> Result<String> {
        let mut lua = String::new();

        let mut has_any_conditions = false;
        let mut has_unconditional_branch = false;

        let id = self.unique();

        // Start a new scope.
        writeln!(lua, "(function()")?;

        // Store the value of expr in a local.
        let expr_s = self.expr(expr)?;
        writeln!(lua, "local {}_{} = {}", PREFIX, id, expr_s)?;

        for (pat, expr) in arms {
            self.pattern_match(pat, &format!("{}_{}", PREFIX, id))?;

            has_any_conditions = has_any_conditions || !self.conditions.is_empty();

            if self.conditions.is_empty() {
                has_unconditional_branch = true;

                // First bind the bindings
                for b in self.bindings.drain(..) {
                    lua.write_str(&b)?;
                }
                // Then return the return value
                writeln!(lua, "return {}", self.expr(expr)?)?;
            } else {
                // Check the conditions
                lua.write_str("if ")?;
                let condition_count = self.conditions.len();
                for (i, cond) in self.conditions.drain(..).enumerate() {
                    write!(lua, "({})", cond)?;
                    if i < condition_count - 1 {
                        lua.write_str("\nand ")?;
                    }
                }
                writeln!(lua, " then")?;

                // If the conditions are met, then bind the bindings
                for b in self.bindings.drain(..) {
                    lua.write_str(&b)?;
                }

                // Return the return value
                writeln!(lua, "return {}", self.expr(expr)?)?;

                // End the if
                writeln!(lua, "end")?;
            }
        }

        // Emit a runtime error in case no pattern matches
        // @Warn: emit a compile time warning as well
        // @Exhaustiveness: do some exhaustiveness checking before emitting these warnings/errors
        if has_any_conditions && !has_unconditional_branch {
            writeln!(lua, r#"error("Unmatched pattern in case expression")"#,)?;
        }

        // End the scope (by calling the anonymous function)
        writeln!(lua, "end)()")?;

        Ok(lua)
    }

    fn curried_function(&mut self, assignments: &Vec<(ast::Lhs, ast::Expr)>) -> Result<String> {
        assert!(assignments.len() > 0);

        let arg_count = assignments[0].0.arg_count();
        let mut ids = Vec::with_capacity(arg_count);

        let mut lua = String::new();

        // Start the functions
        for i in 0..arg_count {
            let id = self.unique();
            ids.push(id);

            writeln!(lua, "function({}_{})", PREFIX, ids[i])?;

            if i < arg_count - 1 {
                write!(lua, "return ")?;
            }
        }

        // Return the expr
        // @DRY: case

        let mut has_any_conditions = false;
        let mut has_unconditional_branch = false;

        for (lhs, expr) in assignments {
            let args = lhs.args();
            if arg_count != args.len() {
                return Err(CodegenError::IncorrectArgumentCount(format!(
                    "{}",
                    lhs.name()
                )));
            }

            for i in 0..arg_count {
                self.pattern_match(&args[i], &format!("{}_{}", PREFIX, ids[i]))?;
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
                        lua.write_str(&b)?;
                    }
                    // Then return the return value
                    write!(lua, "return ")?;
                }

                writeln!(lua, "{}", self.expr(expr)?)?;
            } else {
                // Check the conditions
                lua.write_str("if ")?;
                let condition_count = self.conditions.len();
                for (i, cond) in self.conditions.drain(..).enumerate() {
                    write!(lua, "({})", cond)?;
                    if i < condition_count - 1 {
                        lua.write_str("\nand ")?;
                    }
                }
                writeln!(lua, " then")?;

                // If the conditions are met, then bind the bindings
                for b in self.bindings.drain(..) {
                    lua.write_str(&b)?;
                }

                // Return the return value
                writeln!(lua, "return {}", self.expr(expr)?)?;

                // End the if
                writeln!(lua, "end")?;
            }
        }

        // Emit a runtime error in case no pattern matches
        // @Warn: emit a compile time warning as well
        // @Exhaustiveness: do some exhaustiveness checking before emitting these warnings/errors
        if has_any_conditions && !has_unconditional_branch {
            writeln!(
                lua,
                r#"error("Unmatched pattern in function `{}`")"#,
                &assignments[0].0.name()
            )?;
        }

        // End the functions
        for _ in 0..arg_count {
            writeln!(lua, "end")?;
        }

        Ok(lua)
    }

    /// Generates code for a pattern match.
    /// Note: This only modified `self.conditions` and `self.bindings`.
    fn pattern_match(&mut self, pat: &ast::Pattern, lua_arg_name: &str) -> Result<()> {
        // This function takes a Lua argument name,
        // e.g. _HUCK_0, _HUCK_12[3], _HUCK_3[13][334] or whatever.
        // This is to allow nested pattern matches.
        match pat {
            ast::Pattern::Bind(s) => {
                self.bindings
                    .push(format!("local {} = {}\n", lua_safe(s), lua_arg_name));
            }

            // @Note: the Lua logic is identical for Huck lists and tuples.
            // This is because they have the same representation in Lua: a heterogenous list!
            ast::Pattern::List(list) | ast::Pattern::Tuple(list) => {
                // @Fixme @Errors: for tuples,
                // this should give a runtime error saying something like
                // "tuple of incorrect length",
                // instead of just failing to pattern match.
                //
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

            // @Hardcode @Hack-ish @Prelude
            ast::Pattern::UnaryConstructor(name)
                if name.as_str() == "True" || name.as_str() == "False" =>
            {
                let mut name_string = name.as_str().to_string();
                name_string.make_ascii_lowercase();
                self.conditions
                    .push(format!(r#"{} == {}"#, lua_arg_name, name_string));
            }

            ast::Pattern::UnaryConstructor(name) => {
                assert!(matches!(name, ast::Name::Ident(_)));
                // Check that it's the right variant
                self.conditions.push(format!(
                    r#"getmetatable({}).__variant == "{}""#,
                    lua_arg_name, name
                ));
            }

            ast::Pattern::Unit => (), // Don't need to do anything because unit is ignored
        };

        Ok(())
    }

    /// Generates all the type constructors found in the type definition.
    fn type_definition(&mut self, type_defn: &TypeDefinition) -> Result<String> {
        let mut lua = String::new();

        // Write each constructor to the `lua` string.
        for (name, typ) in type_defn.constructors.iter() {
            write!(lua, r#"{}["{}"] = "#, PREFIX, name)?;
            writeln!(lua, "{}", self.constructor(name, typ)?)?;
            writeln!(
                self.return_entries,
                r#"["{name}"] = {prefix}["{name}"],"#,
                name = name,
                prefix = PREFIX,
            )?;

            // Mark this constructor as generated.
            self.generated.insert(name.clone());
        }

        Ok(lua)
    }

    /// Generates code for a constructor.
    fn constructor(&mut self, name: &ast::Name, mut constr_type: &Type) -> Result<String> {
        // @Errors: maybe we should do some runtime type checking in Lua?

        let mut ids = Vec::new();

        let mut lua = String::new();

        // Start the functions
        while let Type::Arrow(_a, b) = constr_type {
            let id = self.unique();
            ids.push(id);

            writeln!(lua, "function({}_{})", PREFIX, id)?;
            write!(lua, "return ")?;

            constr_type = &b;
        }

        // @Errors: assert that we have the terminal type left?

        let tupled_args = ids
            .iter()
            .map(|id| format!("{}_{}", PREFIX, id))
            .collect::<Vec<_>>()
            .join(", ");

        writeln!(
            lua,
            r#"setmetatable({{{}}}, {{__variant = "{}"}})"#,
            tupled_args, name
        )?;

        // End the functions
        for _ in 0..ids.len() {
            writeln!(lua, "end")?;
        }

        Ok(lua)
    }

    fn reference(&mut self, name: &ast::Name) -> Result<String> {
        if self.scope.contains(name) {
            // It's a top-level definition,
            // so we should emit e.g. _HUCK["var"]
            Ok(format!(r#"{}["{}"]"#, PREFIX, name))
        } else if name.as_str() == "True" || name.as_str() == "False" {
            // @Hardcode @Hack-ish @Prelude
            let mut name_string = name.as_str().to_string();
            name_string.make_ascii_lowercase();
            Ok(name_string)
        } else {
            // It's a locally-bound definition,
            // so we should emit e.g. var
            Ok(format!(r#"{}"#, lua_safe(name.as_str())))
        }
    }

    fn unique(&mut self) -> u64 {
        let id = self.id_counter;
        self.id_counter += 1;
        id
    }
}

// @Cleanup: not pub
pub fn is_lua_binop(op: &str) -> bool {
    // @Prelude: we will want these ops to have different names in Huck to in Lua,
    // but for now, just pass them through.
    match op {
        "+" | "-" | "*" | "/" | "//" | "^" | "%" | "&" | "~" | "|" | ">>" | "<<" | ".." | "<"
        | "<=" | ">" | ">=" | "==" | "~=" | "and" | "or" => true,
        _ => false,
    }
}

/// Returns a Lua-safe version of a Huck identifier.
///
/// Guaranteed to return the same string each time it's called with the same argument.
fn lua_safe(s: &str) -> String {
    let mut output = String::new();

    for c in s.chars() {
        match c {
            '=' => output.push_str("_EQUALS"),
            '+' => output.push_str("_PLUS"),
            '-' => output.push_str("_MINUS"),
            '|' => output.push_str("_BAR"),
            '!' => output.push_str("_BANG"),
            '@' => output.push_str("_AT"),
            '#' => output.push_str("_HASH"),
            '$' => output.push_str("_DOLLAR"),
            '%' => output.push_str("_PERCENT"),
            '^' => output.push_str("_CARET"),
            '&' => output.push_str("_AMPERS"),
            '*' => output.push_str("_STAR"),
            ':' => output.push_str("_COLON"),
            '.' => output.push_str("_DOT"),
            ',' => output.push_str("_COMMA"),
            '/' => output.push_str("_SLASH"),
            '~' => output.push_str("_TILDE"),
            '\'' => output.push_str("_TICK"),
            c => output.push(c),
        }
    }

    output
}
