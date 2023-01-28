mod error;

#[cfg(test)]
mod test;

use crate::generatable_module::GeneratableModule;
use crate::name::{ResolvedName, Source};
use crate::types::{Type, TypeDefinition};
use crate::{ast, log};

use std::collections::BTreeSet;
use std::fmt::Write;
use std::sync::atomic::{self, AtomicU64};
use std::time::Instant;

pub use error::Error;
use error::Error as CodegenError;

/// Used for generating unique variable IDs.
static UNIQUE_COUNTER: AtomicU64 = AtomicU64::new(0);

const PREFIX: &str = "_HUCK";

/// Generates Lua for the given Huck module.
pub fn generate(module: &GeneratableModule) -> Result<String> {
    let start_time = Instant::now();

    let generated = CodeGenerator::new(module).generate()?;

    log::trace!(
        log::CODEGEN,
        "Generated module {}:\n{}",
        module.path,
        generated
    );

    log::info!(
        log::METRICS,
        "Generated module {}, {:?} elapsed",
        module.path,
        start_time.elapsed()
    );

    Ok(generated)
}

type Result<T> = std::result::Result<T, CodegenError>;

/// Generates Lua code, and maintains all necessary state to do so.
/// Methods on this struct should generally correspond to Lua constructs,
/// not to Huck constructs.
#[derive(Debug)]
struct CodeGenerator<'a> {
    // This is a String containing the contents of the Lua table which shall be returned.
    return_entries: String,

    // This is the set of definitions which have already been generated.
    generated: BTreeSet<ResolvedName>,

    module: &'a GeneratableModule,
}

impl<'a> CodeGenerator<'a> {
    fn new(module: &'a GeneratableModule) -> Self {
        CodeGenerator {
            return_entries: String::new(),

            generated: BTreeSet::new(),

            module,
        }
    }

    /// Generate Lua code for the GeneratableModule used in CodeGenerator::new.
    /// This will generate a Lua chunk which returns a table
    /// containing the definitions given in the Huck module.
    fn generate(mut self) -> Result<String> {
        let mut lua = String::new();

        writeln!(lua, "local {} = {{}}", PREFIX)?;

        // First, generate code for all the type definitions (i.e. for their constructors).
        // This can be done first
        // because they don't have a real RHS,
        // so they can't refer to anything else.

        log::trace!(log::CODEGEN, "  Generating type definitions");
        for (_name, type_defn) in self.module.type_definitions.iter() {
            write!(lua, "{}", self.type_definition(type_defn)?)?;
        }

        // Next, we can generate all the definitions.
        log::trace!(log::CODEGEN, "  Generating definitions");

        // Start by putting all definitions in the queue to be generated.
        // @Fixme: this probably doesn't need to be entirely cloned
        let mut current_pass: Vec<_> = self.module.definitions.clone().into_iter().collect();
        let mut next_pass = Vec::new();

        loop {
            // If the queue is empty, we're done.
            if current_pass.is_empty() {
                break;
            }

            log::trace!(log::CODEGEN, "  Started a new generation pass");
            // Keep track of whether we've generated anything in this pass.
            let mut generated_anything = false;

            for (name, mut typed_defn) in current_pass.drain(..) {
                let defn = &mut typed_defn.1;

                // @Errors: this should throw an error saying that
                // there was a type annotation without a corresponding definition.
                assert!(!defn.assignments.is_empty());

                // @Lazy @Laziness: lazy values can be generated in any order

                // If the definition has any arguments, then it will become a Lua function;
                // this means we can generate it in any order.
                // Note that if it has missing dependencies, it will error at runtime;
                // so we should have already caught this in a compile error.
                let has_any_args = defn.assignments[0].0.arg_count() > 0;

                // If the definition has no un-generated dependencies from this module,
                // then we're ready generate it.
                let has_all_deps = defn
                    .dependencies()
                    .iter()
                    .filter(|n| n.source == Source::Module(self.module.path))
                    .all(|n| self.generated.contains(n));

                if has_any_args || has_all_deps {
                    // Because there are arguments, it's going to be a Lua function.
                    // Thus, we can generate in any order.
                    log::trace!(log::CODEGEN, "    Generating {name}");
                    write!(lua, "{}", self.definition(&name, defn)?)?;

                    // Mark that we have generated something in this pass.
                    generated_anything = true;
                } else {
                    // Skip it for now
                    log::trace!(log::CODEGEN, "    Skipping {name}");
                    next_pass.push((name, typed_defn));
                }
            }

            // If we didn't generate anything in this pass,
            // it means we have a cyclic dependency.
            // @Checkme: is this the only time this happens?
            if !generated_anything {
                log::error!(
                    log::CODEGEN,
                    "Error, didn't generate anything in one pass. Next in queue: {:?}",
                    next_pass
                );
                return Err(CodegenError::CyclicDependency(
                    next_pass
                        .iter()
                        // @Fixme @Errors: filter out entries which depend on the cycle,
                        // but are not part of the cycle themselves.
                        .map(|t| t.0)
                        .collect(),
                ));
            }

            log::trace!(log::CODEGEN, "  Finished generation pass");

            std::mem::swap(&mut current_pass, &mut next_pass);
        }

        // Write out foreign exports
        for (lua_lhs, expr) in self.module.foreign_exports.iter() {
            writeln!(lua, "{} = {}", lua_lhs, self.expr(expr)?)?;
        }

        // Write out the return statement
        write!(lua, "return {{\n{}}}", self.return_entries)?;

        Ok(lua)
    }

    // @Todo @Cleanup: move most of this comment to earlier in the pipe, when we make Definitions.
    /// Generates a Lua expression representing a Huck definition,
    /// even if it's defined on multiple lines.
    /// This has to be generated from the Vec<Assignment>,
    /// because in the case of multiple definitions,
    /// we have to generate a Lua 'switch' statement.
    fn definition(
        &mut self,
        name: &ResolvedName,
        defn: &ast::Definition<ResolvedName>,
    ) -> Result<String> {
        let mut lua = String::new();

        // Write the definition to the `lua` string.
        write!(lua, r#"{}["{}"] = "#, PREFIX, name.ident)?;
        writeln!(lua, "{}", self.curried_function(&defn.assignments)?)?;
        writeln!(
            self.return_entries,
            r#"["{name}"] = {prefix}["{name}"],"#,
            name = name.ident,
            prefix = PREFIX,
        )?;

        // Mark this definition as generated.
        self.generated.insert(*name);

        Ok(lua)
    }

    fn expr(&mut self, expr: &ast::Expr<ResolvedName>) -> Result<String> {
        match expr {
            ast::Expr::Term(term) => self.term(term),
            ast::Expr::App { func, argument } => {
                Ok(format!("({})({})", self.expr(func)?, self.expr(argument)?))
            }
            ast::Expr::Binop { operator, lhs, rhs } => Ok(format!(
                "{}({})({})",
                self.reference(operator)?,
                self.expr(lhs)?,
                self.expr(rhs)?
            )),

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

    fn term(&mut self, term: &ast::Term<ResolvedName>) -> Result<String> {
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

    fn case(
        &mut self,
        expr: &ast::Expr<ResolvedName>,
        arms: &Vec<(ast::Pattern<ResolvedName>, ast::Expr<ResolvedName>)>,
    ) -> Result<String> {
        let mut lua = String::new();

        let mut has_unconditional_branch = false;

        let id = Self::unique();

        // Start a new scope.
        writeln!(lua, "(function()")?;

        // Store the value of expr in a local.
        let expr_s = self.expr(expr)?;
        writeln!(lua, "local {}_{} = {}", PREFIX, id, expr_s)?;

        for (pat, expr) in arms {
            let (conditions, bindings) = pattern_match(pat, &format!("{}_{}", PREFIX, id))?;

            if conditions.is_empty() {
                has_unconditional_branch = true;

                // First bind the bindings
                for b in bindings {
                    lua.write_str(&b)?;
                }
                // Then return the return value
                writeln!(lua, "return {}", self.expr(expr)?)?;
            } else {
                // Check the conditions
                lua.write_str("if ")?;
                let condition_count = conditions.len();
                for (i, cond) in conditions.into_iter().enumerate() {
                    write!(lua, "({})", cond)?;
                    if i < condition_count - 1 {
                        lua.write_str("\nand ")?;
                    }
                }
                writeln!(lua, " then")?;

                // If the conditions are met, then bind the bindings
                for b in bindings {
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
        if !has_unconditional_branch {
            writeln!(lua, r#"error("Unmatched pattern in case expression")"#,)?;
        }

        // End the scope (by calling the anonymous function)
        writeln!(lua, "end)()")?;

        Ok(lua)
    }

    fn curried_function(
        &mut self,
        assignments: &Vec<(ast::Lhs<ResolvedName>, ast::Expr<ResolvedName>)>,
    ) -> Result<String> {
        assert!(!assignments.is_empty());

        let arg_count = assignments[0].0.arg_count();
        let mut ids = Vec::with_capacity(arg_count);

        let mut lua = String::new();

        // Start the functions
        for i in 0..arg_count {
            let id = Self::unique();
            ids.push(id);

            writeln!(lua, "function({}_{})", PREFIX, ids[i])?;

            if i < arg_count - 1 {
                write!(lua, "return ")?;
            }
        }

        // Some @DRY: CodeGenerator::case
        //
        // Before returning the expression,
        // we split the branches based on whether or not they have any conditions.
        // This is to make sure that unconditional branch(es) go at the end.
        let branches = assignments
            .iter()
            .map(|(lhs, expr)| {
                let args = lhs.args();
                if arg_count != args.len() {
                    return Err(CodegenError::IncorrectArgumentCount(format!(
                        "{}",
                        lhs.name()
                    )));
                }

                let mut conds = Vec::new();
                let mut binds = Vec::new();
                for i in 0..arg_count {
                    let (cond, bind) = pattern_match(&args[i], &format!("{}_{}", PREFIX, ids[i]))?;
                    conds.extend(cond);
                    binds.extend(bind);
                }

                Ok((conds, binds, expr))
            })
            .collect::<Result<Vec<_>>>()?;

        let (unconditional, conditional): (Vec<_>, Vec<_>) = branches
            .into_iter()
            .partition(|(conds, _binds, _expr)| conds.is_empty());

        let has_unconditional_branch = !unconditional.is_empty();

        // !conds.is_empty()
        for (conds, binds, expr) in conditional {
            // Check the conditions
            lua.write_str("if ")?;
            let condition_count = conds.len();
            for (i, cond) in conds.into_iter().enumerate() {
                write!(lua, "({})", cond)?;
                if i < condition_count - 1 {
                    lua.write_str("\nand ")?;
                }
            }
            writeln!(lua, " then")?;

            // If the conditions are met, then bind the bindings
            for b in binds {
                lua.write_str(&b)?;
            }

            // Return the return value
            writeln!(lua, "return {}", self.expr(expr)?)?;

            // End the if
            writeln!(lua, "end")?;
        }

        // conds.is_empty()
        for (_conds, binds, expr) in unconditional {
            // If we have no Huck arguments,
            // then we should be a Lua value, not a Lua function;
            // so we don't return, we just are.
            if arg_count > 0 {
                // First bind the bindings
                for b in binds {
                    lua.write_str(&b)?;
                }
                // Then return the return value
                write!(lua, "return ")?;
            }

            writeln!(lua, "{}", self.expr(expr)?)?;
        }

        // Emit a runtime error in case no pattern matches
        // @Warn: emit a compile time warning as well
        // @Exhaustiveness: do some exhaustiveness checking before emitting these warnings/errors
        if !has_unconditional_branch {
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
            self.generated.insert(*name);
        }

        Ok(lua)
    }

    /// Generates code for a constructor.
    fn constructor(&mut self, name: &ResolvedName, mut constr_type: &Type) -> Result<String> {
        // @Errors: maybe we should do some runtime type checking in Lua?

        let mut ids = Vec::new();

        let mut lua = String::new();

        // Start the functions
        while let Type::Arrow(_a, b) = constr_type {
            let id = Self::unique();
            ids.push(id);

            writeln!(lua, "function({}_{})", PREFIX, id)?;
            write!(lua, "return ")?;

            constr_type = b;
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

    fn reference(&mut self, name: &ResolvedName) -> Result<String> {
        match name.source {
            Source::Module(path) if path == self.module.path => {
                // It's a top-level definition from this module,
                // so we should emit e.g. _HUCK["var"]
                Ok(format!(r#"{}["{}"]"#, PREFIX, name.ident))
            }

            Source::Module(path) => {
                // It's a top-level definition from a different module,
                // so we should emit e.g. require("Bar")["var"]
                //
                // @Fixme: need to look up the file_stem instead of just using path
                Ok(format!(r#"require("{}")["{}"]"#, path, name.ident))
            }

            Source::Foreign {
                require,
                foreign_name,
            } => {
                // e.g. require("inspect")["inspect"]
                Ok(format!(r#"require({require})["{foreign_name}"]"#))
            }

            Source::Local(_id) => {
                // It's a locally-bound definition,
                // so we should emit e.g. var
                Ok(lua_local(name.ident))
            }

            Source::Builtin => {
                // At the moment, these are the only builtin values.
                assert!(matches!(name.ident, "True" | "False"));

                let mut name_string = name.ident.to_string();
                name_string.make_ascii_lowercase();
                Ok(name_string)
            }
        }
    }

    /// Generates a new and unique u64 each time it's called.
    fn unique() -> u64 {
        UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed)
    }

    /// Resets the unique ID counter.
    #[cfg(test)]
    pub fn reset_unique() {
        UNIQUE_COUNTER.store(0, atomic::Ordering::Relaxed);
    }
}

/// Generates code for a pattern match.
/// Returns `conditions` and `bindings`,
/// which are `Vec`s of Lua segments used to implement the pattern match.
fn pattern_match(
    pat: &ast::Pattern<ResolvedName>,
    lua_arg_name: &str,
) -> Result<(Vec<String>, Vec<String>)> {
    // This function takes a Lua argument name,
    // e.g. _HUCK_0, _HUCK_12[3], _HUCK_3[13][334] or whatever.
    // This is to allow nested pattern matches.

    let mut conditions = Vec::new();
    let mut bindings = Vec::new();

    match pat {
        ast::Pattern::Bind(s) => {
            assert!(s.is_local());
            bindings.push(format!("local {} = {}\n", lua_local(s.ident), lua_arg_name));
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
            conditions.push(format!("#{} == {}", lua_arg_name, list.len()));

            // Check that each pattern matches
            for (i, pat) in list.iter().enumerate() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, i + 1);
                let (sub_conds, sub_binds) = pattern_match(pat, &new_lua_arg_name)?;
                conditions.extend(sub_conds);
                bindings.extend(sub_binds);
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
            for (i, pat) in args.iter().enumerate() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, i + 1);
                let (sub_conds, sub_binds) = pattern_match(pat, &new_lua_arg_name)?;
                conditions.extend(sub_conds);
                bindings.extend(sub_binds);
            }
        }

        ast::Pattern::Binop { lhs, rhs, operator } => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, operator
            ));

            // Check that the LHS pattern matches
            let (sub_conds, sub_binds) = pattern_match(lhs, &format!("{}[{}]", lua_arg_name, 1))?;
            conditions.extend(sub_conds);
            bindings.extend(sub_binds);

            // Check that the RHS pattern matches
            let (sub_conds, sub_binds) = pattern_match(rhs, &format!("{}[{}]", lua_arg_name, 2))?;
            conditions.extend(sub_conds);
            bindings.extend(sub_binds);
        }

        // @Hardcode @Hack-ish @Prelude
        ast::Pattern::UnaryConstructor(name) if name.ident == "True" || name.ident == "False" => {
            let mut name_string = name.ident.to_string();
            name_string.make_ascii_lowercase();
            conditions.push(format!(r#"{} == {}"#, lua_arg_name, name_string));
        }

        ast::Pattern::UnaryConstructor(name) => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, name
            ));
        }

        ast::Pattern::Unit => (), // Don't need to do anything because unit is ignored
    };

    Ok((conditions, bindings))
}

/// Returns a Lua-safe version of a Huck identifier.
/// Used when binding local variable names.
/// Guaranteed to return the same string each time it's called with the same argument.
fn lua_local(ident: &'static str) -> String {
    let mut output = String::new();

    for c in ident.chars() {
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
