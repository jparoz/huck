use crate::ir::{self, Module};
use crate::log;
use crate::name::{Ident, ModulePath};
use crate::name::{ResolvedName, Source};
use crate::types::Type;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::mem;
use std::time::Instant;

mod error;
pub use error::Error;

#[cfg(test)]
mod test;

/// Generates Lua for the given Huck module.
/// `requires` is a mapping from a module's `ModulePath`
/// to the segment of a filepath to be given to Lua's `require` function to load that module.
pub fn generate(module: ir::Module, requires: &BTreeMap<ModulePath, String>) -> Result<String> {
    let start_time = Instant::now();

    let module_path = module.path;

    log::trace!(log::CODEGEN, "Generating code for module {}", module_path);

    let generated = CodeGenerator::new(module, requires).generate()?;

    log::trace!(
        log::CODEGEN,
        "Generated module {}:\n{}",
        module_path,
        generated
    );

    log::info!(
        log::METRICS,
        "Generated module {}, {:?} elapsed",
        module_path,
        start_time.elapsed()
    );

    Ok(generated)
}

type Result<T> = std::result::Result<T, Error>;

/// Generates Lua code, and maintains all necessary state to do so.
/// Methods on this struct should generally correspond to Lua constructs,
/// not to Huck constructs.
#[derive(Debug)]
struct CodeGenerator<'a> {
    // This is a String containing the contents of the Lua table which shall be returned.
    return_entries: String,

    // This is the set of definitions which have already been generated.
    generated: BTreeSet<ResolvedName>,

    /// This is the module being generated.
    module: ir::Module,

    /// This is a map from a module's path to its Lua require string.
    requires: &'a BTreeMap<ModulePath, String>,

    /// Used for generating unique variable IDs.
    unique_counter: u64,
}

impl<'a> CodeGenerator<'a> {
    fn new(module: Module, requires: &'a BTreeMap<ModulePath, String>) -> Self {
        CodeGenerator {
            module,
            requires,
            generated: BTreeSet::new(),
            return_entries: String::new(),
            unique_counter: 0,
        }
    }

    /// Generate Lua code for the Module used in CodeGenerator::new.
    /// This will generate a Lua chunk which returns a table
    /// containing the definitions given in the Huck module.
    fn generate(mut self) -> Result<String> {
        let mut lua = String::new();

        writeln!(lua, "local {} = {{}}", lua_module_path(self.module.path))?;

        // First, generate code for all the type definitions (i.e. for their constructors).
        // This can be done first
        // because they don't have a real RHS,
        // so they can't refer to anything else.

        log::trace!(log::CODEGEN, "  Generating type definitions");
        for (_name, type_defn) in mem::take(&mut self.module.type_definitions) {
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

            for (name, mut defn) in current_pass.drain(..) {
                // @Lazy @Laziness: lazy values can be generated in any order

                // If the definition is a lambda,
                // then it will become a Lua function;
                // this means we can generate it in any order.
                // Note that if it has missing dependencies,
                // it will error at runtime;
                // so we need to catch this in a compile error.
                let has_any_args = matches!(defn.rhs, ir::Expression::Lambda { .. });

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
                    write!(lua, "{}", self.definition(name, defn)?)?;

                    // Mark that we have generated something in this pass.
                    generated_anything = true;
                } else {
                    // Skip it for now
                    log::trace!(log::CODEGEN, "    Skipping {name}");
                    next_pass.push((name, defn));
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
                return Err(Error::CyclicDependency(
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
        for (lua_lhs, expr) in mem::take(&mut self.module.exports) {
            writeln!(lua, "{} = {}", lua_lhs, self.expression(expr)?)?;
        }

        // Write out the return statement
        writeln!(lua, "return {{\n{}}}", self.return_entries)?;

        Ok(lua)
    }

    /// Generates a Lua expression representing a top-level Huck definition.
    fn definition(&mut self, name: ResolvedName, defn: ir::Definition) -> Result<String> {
        let mut lua = String::new();

        // Write the definition to the `lua` string.
        write!(
            lua,
            r#"{}["{}"] = "#,
            lua_module_path(self.module.path),
            name.ident
        )?;
        writeln!(lua, "{}", self.expression(defn.rhs)?)?;
        writeln!(
            self.return_entries,
            r#"["{name}"] = {prefix}["{name}"],"#,
            name = name.ident,
            prefix = lua_module_path(self.module.path),
        )?;

        // Mark this definition as generated.
        self.generated.insert(name);

        Ok(lua)
    }

    fn expression(&mut self, expr: ir::Expression) -> Result<String> {
        match expr {
            ir::Expression::Reference(name) => self.reference(name),

            ir::Expression::Literal(lit) => Ok(format!("{}", lit)),
            // @Note: this is where the semantics for Huck Lists are decided.
            // The below simply converts them as Lua lists;
            // possibly one day we should instead convert them to Lua iterators.
            ir::Expression::List(v) => Ok(format!(
                "{{{}}}",
                v.into_iter()
                    .map(|e| self.expression(e))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            )),

            ir::Expression::Tuple(v) => Ok(format!(
                "{{{}}}",
                v.into_iter()
                    .map(|e| self.expression(e))
                    .collect::<Result<Vec<_>>>()?
                    .join(", ")
            )),

            ir::Expression::App(func, argument) => Ok(format!(
                "({})({})",
                self.expression(*func)?,
                self.expression(*argument)?
            )),

            ir::Expression::Let { definitions, expr } => {
                let mut lua = String::new();

                // Open a new scope (i.e. an immediately-called function so that return works)
                writeln!(lua, "(function()")?;

                // Make a new local variable for each assignment
                for definition in definitions.into_values() {
                    writeln!(
                        lua,
                        "local {} = {}",
                        definition.name,
                        self.expression(definition.rhs)?
                    )?;
                }

                // Generate the in_expr
                writeln!(lua, "return {}", self.expression(*expr)?)?;

                // End and call the function
                writeln!(lua, "end)()")?;

                Ok(lua)
            }

            ir::Expression::Case { expr, arms } => self.case(*expr, arms),

            ir::Expression::Lambda { args, expr } => {
                assert!(!args.is_empty());
                self.curried_function(args, *expr)
            }

            ir::Expression::Lua(lua) => Ok(format!("({})", lua)),
        }
    }

    fn case(
        &mut self,
        expr: ir::Expression,
        arms: Vec<(ir::Pattern, ir::Expression)>,
    ) -> Result<String> {
        let mut lua = String::new();

        // @Errors: do this in a different way
        // Store a string describing the expression, to use in error messages.
        let expr_s = format!("{expr:?}");

        let id = self.unique();

        // Start a new scope.
        writeln!(lua, "(function()")?;

        // Store the value of expr in a local,
        // which is accessed within the conditions and bindings.
        writeln!(
            lua,
            "local {}_{} = {}",
            lua_module_path(self.module.path),
            id,
            self.expression(expr)?
        )?;

        // Before returning the expression,
        // we split the branches based on whether or not they have any conditions.
        // This is to make sure that unconditional branch(es) go at the end.
        let branches = arms
            .into_iter()
            .map(|(pat, expr)| {
                let (conds, binds) = pattern_match(
                    pat,
                    &format!("{}_{}", lua_module_path(self.module.path), id),
                )?;
                Ok((conds, binds, expr))
            })
            .collect::<Result<Vec<_>>>()?;

        let (unconditional, conditional): (Vec<_>, Vec<_>) = branches
            .into_iter()
            .partition(|(conds, _binds, _expr)| conds.is_empty());

        // !conds.is_empty()
        for (conds, binds, expr) in conditional {
            // Check the conditions
            lua.write_str("if ")?;
            {
                let mut iter = conds.into_iter().peekable();
                while let Some(cond) = iter.next() {
                    write!(lua, "({})", cond)?;
                    if iter.peek().is_some() {
                        lua.write_str("\nand ")?;
                    }
                }
            }
            writeln!(lua, " then")?;

            // If the conditions are met, then bind the bindings
            for b in binds {
                lua.write_str(&b)?;
            }

            // Return the return value
            writeln!(lua, "return {}", self.expression(expr)?)?;

            // End the if
            writeln!(lua, "end")?;
        }

        // Assert that there aren't multiple unconditional branches.
        assert!(unconditional.len() <= 1);

        let has_unconditional_branch = !unconditional.is_empty();

        // conds.is_empty()
        if let Some((_conds, binds, expr)) = unconditional.into_iter().next() {
            // First bind the bindings
            for b in binds {
                lua.write_str(&b)?;
            }
            // Then return the return value
            write!(lua, "return ")?;

            writeln!(lua, "{}", self.expression(expr)?)?;
        } else {
            // Emit a runtime error in case no pattern matches
            // @Exhaustiveness: do some exhaustiveness checking before emitting these warnings/errors
            // @Errors: these should have better information about the source of the case expression
            // @Errors: shouldn't use Debug
            log::warn!(
                log::CODEGEN,
                "Warning: possible partial definition when matching expression `{expr_s}`, \
                 try adding an unconditional pattern match"
            );
            if !has_unconditional_branch {
                writeln!(lua, r#"error("Unmatched pattern")"#)?;
            }
        }

        // End the scope (by calling the anonymous function)
        writeln!(lua, "end)()")?;

        Ok(lua)
    }

    fn curried_function(&mut self, args: Vec<ir::Pattern>, expr: ir::Expression) -> Result<String> {
        let mut lua = String::new();

        let arg_count = args.len();

        let mut ids = Vec::with_capacity(arg_count);

        // Start the functions
        {
            let mut iter = (0..arg_count).peekable();
            while iter.next().is_some() {
                let id = self.unique();
                ids.push(id);

                writeln!(
                    lua,
                    "function({}_{})",
                    lua_module_path(self.module.path),
                    id
                )?;

                if iter.peek().is_some() {
                    write!(lua, "return ")?;
                }
            }
        }

        // Match the patterns
        let (mut conds, mut binds) = (Vec::new(), Vec::new());
        for (i, pat) in args.into_iter().enumerate() {
            let (cs, bs) = pattern_match(
                pat,
                &format!("{}_{}", lua_module_path(self.module.path), ids[i]),
            )?;
            conds.extend(cs);
            binds.extend(bs);
        }

        if conds.is_empty() {
            // First bind the bindings
            for b in binds {
                lua.write_str(&b)?;
            }
            // Then return the return value
            writeln!(lua, "return {}", self.expression(expr)?)?;
        } else {
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
            writeln!(lua, "return {}", self.expression(expr)?)?;

            // End the if
            writeln!(lua, "end")?;
        }

        // End the functions
        for _ in 0..arg_count {
            writeln!(lua, "end")?;
        }

        Ok(lua)
    }

    /// Generates all the type constructors found in the type definition.
    fn type_definition(&mut self, type_defn: ir::TypeDefinition) -> Result<String> {
        let mut lua = String::new();

        // Write each constructor to the `lua` string.
        for (name, constr_typ) in type_defn.constructors.into_iter() {
            write!(
                lua,
                r#"{}["{}"] = "#,
                lua_module_path(self.module.path),
                name
            )?;
            writeln!(lua, "{}", self.constructor(name, constr_typ)?)?;
            writeln!(
                self.return_entries,
                r#"["{name}"] = {prefix}["{name}"],"#,
                name = name,
                prefix = lua_module_path(self.module.path),
            )?;

            // Mark this constructor as generated.
            self.generated.insert(name);
        }

        Ok(lua)
    }

    /// Generates code for a constructor.
    fn constructor(&mut self, name: ResolvedName, mut constr_type: Type) -> Result<String> {
        // @Errors: maybe we should do some runtime type checking in Lua?

        let mut ids = Vec::new();

        let mut lua = String::new();

        // Start the functions
        while let Type::Arrow(_a, b) = constr_type {
            let id = self.unique();
            ids.push(id);

            writeln!(
                lua,
                "function({}_{})",
                lua_module_path(self.module.path),
                id
            )?;
            write!(lua, "return ")?;

            constr_type = *b;
        }

        // @Errors: assert that we have the terminal type left?

        let tupled_args = ids
            .iter()
            .map(|id| format!("{}_{}", lua_module_path(self.module.path), id))
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

    fn reference(&mut self, name: ResolvedName) -> Result<String> {
        match name.source {
            Source::Module(path) if path == self.module.path => {
                // It's a top-level definition from this module,
                // so we should emit e.g. _Module_Name["var"]
                Ok(format!(
                    r#"{}["{}"]"#,
                    lua_module_path(self.module.path),
                    name.ident
                ))
            }

            Source::Module(path) => {
                // It's a top-level definition from a different module,
                // so we should emit e.g. require("Bar")["var"]
                Ok(format!(
                    r#"require("{}")["{}"]"#,
                    self.requires[&path], name.ident
                ))
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
    fn unique(&mut self) -> u64 {
        let id = self.unique_counter;
        self.unique_counter += 1;
        id
    }
}

/// Generates code for a pattern match.
/// Returns `conditions` and `bindings`,
/// which are `Vec`s of Lua segments used to implement the pattern match.
fn pattern_match(pat: ir::Pattern, lua_arg_name: &str) -> Result<(Vec<String>, Vec<String>)> {
    // This function takes a Lua argument name,
    // e.g. _Module_0, _Module_12[3], _Module_3[13][334] or whatever.
    // This is to allow nested pattern matches.

    let mut conditions = Vec::new();
    let mut bindings = Vec::new();

    match pat {
        ir::Pattern::Bind(s) => {
            assert!(s.is_local());
            bindings.push(format!("local {} = {}\n", lua_local(s.ident), lua_arg_name));
        }

        // Because underscore is not a legal identifier,
        // we don't need to bind anything at all.
        ir::Pattern::Underscore => (),

        // @Note: the Lua logic is identical for Huck lists and tuples.
        // This is because they have the same representation in Lua: a heterogenous list!
        ir::Pattern::List(list) | ir::Pattern::Tuple(list) => {
            // @Fixme @Errors: for tuples,
            // this should give a runtime error saying something like
            // "tuple of incorrect length",
            // instead of just failing to pattern match.
            //
            // Check that the list is the correct length
            conditions.push(format!("#{} == {}", lua_arg_name, list.len()));

            // Check that each pattern matches
            for (i, pat) in list.into_iter().enumerate() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, i + 1);
                let (sub_conds, sub_binds) = pattern_match(pat, &new_lua_arg_name)?;
                conditions.extend(sub_conds);
                bindings.extend(sub_binds);
            }
        }

        // Don't need to do anything because unit is ignored
        ir::Pattern::Literal(ir::Literal::Unit) => (),

        ir::Pattern::Literal(lit) => {
            conditions.push(format!("{} == {}", lua_arg_name, lit));
        }

        // @Cleanup @Hardcode @Hack-ish
        ir::Pattern::Constructor(name, args)
            if args.is_empty()
                && name.is_builtin()
                && (name.ident == "True" || name.ident == "False") =>
        {
            let mut name_string = name.ident.to_string();
            name_string.make_ascii_lowercase();
            conditions.push(format!(r#"{} == {}"#, lua_arg_name, name_string));
        }

        ir::Pattern::Constructor(name, args) if args.is_empty() => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, name
            ));
        }

        ir::Pattern::Constructor(name, args) => {
            // Check that it's the right variant
            conditions.push(format!(
                r#"getmetatable({}).__variant == "{}""#,
                lua_arg_name, name
            ));

            // Check that each pattern matches
            for (i, pat) in args.into_iter().enumerate() {
                let new_lua_arg_name = format!("{}[{}]", lua_arg_name, i + 1);
                let (sub_conds, sub_binds) = pattern_match(pat, &new_lua_arg_name)?;
                conditions.extend(sub_conds);
                bindings.extend(sub_binds);
            }
        }
    };

    Ok((conditions, bindings))
}

/// Returns a Lua-safe version of a Huck identifier.
/// Used when binding local variable names.
/// Guaranteed to return the same string each time it's called with the same argument.
fn lua_local(ident: Ident) -> String {
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

/// Returns a Lua-safe version of a Huck module path.
/// Used when creating and referencing the Lua table of functions from the module.
fn lua_module_path(path: ModulePath) -> String {
    // Replace dots with underscores
    let mut s = path.0.replace('.', "_");

    // Prefix with an underscore
    s.insert(0, '_');

    s
}

impl ir::Definition {
    fn dependencies(&mut self) -> BTreeSet<ResolvedName> {
        let mut deps = BTreeSet::new();
        self.rhs.dependencies(&mut deps);
        deps
    }
}

impl ir::Expression {
    fn dependencies(&self, deps: &mut BTreeSet<ResolvedName>) {
        use ir::*;
        match self {
            Expression::Reference(name) => {
                deps.insert(*name);
            }

            Expression::List(es) | Expression::Tuple(es) => {
                es.iter().for_each(|e| e.dependencies(deps));
            }
            Expression::Literal(_) => (),

            Expression::App(func, argument) => {
                func.dependencies(deps);
                argument.dependencies(deps);
            }

            Expression::Let { definitions, expr } => {
                let mut sub_deps = BTreeSet::new();

                expr.dependencies(&mut sub_deps);

                // Remove variables bound in the definitions
                for name in definitions.keys() {
                    // @Note @Errors: if .remove() returns false,
                    // the definition isn't referenced in the in_expr;
                    // therefore it's dead code.
                    // Maybe emit a warning about this.
                    sub_deps.remove(name);
                }

                deps.extend(sub_deps);
            }

            Expression::Case { expr, arms } => {
                // Always include the dependencies of the scrutinised expression.
                expr.dependencies(deps);

                for (arm_pat, arm_expr) in arms {
                    let mut sub_deps = BTreeSet::new();
                    arm_expr.dependencies(&mut sub_deps);

                    // Remove variables bound in the arm pattern
                    for name in arm_pat.names_bound() {
                        sub_deps.remove(&name);
                    }

                    deps.extend(sub_deps);
                }
            }

            Expression::Lambda { args, expr } => {
                let mut sub_deps = BTreeSet::new();

                expr.dependencies(&mut sub_deps);

                // Remove variables bound in the lambda LHS
                for pat in args.iter() {
                    for name in pat.names_bound() {
                        // @Note @Errors: if .remove() returns false,
                        // the definition isn't referenced in the in_expr;
                        // therefore it's dead code.
                        // Maybe emit a warning about this.
                        sub_deps.remove(&name);
                    }
                }

                deps.extend(sub_deps);
            }

            // Lua inline expressions can't depend on Huck values,
            // or at least we can't (i.e. won't) check inside Lua for dependencies;
            // so we do nothing.
            Expression::Lua(_) => (),
        }
    }
}
