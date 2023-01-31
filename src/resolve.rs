use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::atomic::{self, AtomicUsize};
use std::time::Instant;

use crate::module::{Module, ModulePath};
use crate::name::{ResolvedName, Source, UnresolvedName};
use crate::types::TypeVar;
use crate::utils::unwrap_match;
use crate::{ast, log};

/// This struct manages name resolution across all modules.
/// The following example illustrates which names are held in which `Scope`
/// (value-level or type-level):
/// `type Foo a = Bar a Int;`
/// In this example, `Foo`, `a`, and `Int` are all type-level names;
/// `Bar` is a value-level name.
pub struct Resolver {
    /// The modules which have already been resolved.
    pub modules: BTreeMap<ModulePath, Module<ResolvedName, ()>>,

    /// The `Scope` used for implicitly-imported value-level names.
    scope: Scope,

    /// The `Scope` used for implicitly-imported type-level names.
    type_scope: TypeScope,

    /// Holds assumptions about imported names,
    /// without knowing whether they're value- or type-level.
    assumptions: Vec<ResolvedName>,

    /// Assumptions about imported modules,
    /// regardless of whether they have any explicitly imported names.
    module_assumptions: Vec<ModulePath>,
}

impl Resolver {
    /// Makes a new `Resolver`, including builtin names in the relevant scopes.
    pub fn new() -> Self {
        let scope = Scope {
            names: BTreeMap::from([
                (UnresolvedName::Unqualified("True"), vec![Source::Builtin]),
                (UnresolvedName::Unqualified("False"), vec![Source::Builtin]),
            ]),
            ..Scope::default()
        };

        let type_scope = TypeScope {
            names: BTreeMap::from([
                (UnresolvedName::Unqualified("Int"), vec![Source::Builtin]),
                (UnresolvedName::Unqualified("Float"), vec![Source::Builtin]),
                (UnresolvedName::Unqualified("String"), vec![Source::Builtin]),
                (UnresolvedName::Unqualified("Bool"), vec![Source::Builtin]),
                (UnresolvedName::Unqualified("IO"), vec![Source::Builtin]),
            ]),
            ..Scope::default()
        };

        Resolver {
            scope,
            type_scope,
            modules: BTreeMap::new(),
            assumptions: Vec::new(),
            module_assumptions: Vec::new(),
        }
    }

    /// Resolves the given module as the Prelude, adding it to self.modules.
    pub fn resolve_prelude(&mut self, module: Module<UnresolvedName, ()>) -> Result<(), Error> {
        let module_resolver = ModuleResolver::new(self, module.path);

        // Keep the Prelude module's scopes,
        // because they'll be used in resolving other modules.
        let (resolved, scope, type_scope) = module_resolver.resolve(module)?;
        self.modules.insert(resolved.path, resolved);

        // Include the module_resolver's environment into the self,
        // so that it will be implicitly imported into other modules.
        self.scope.names.extend(scope.names);
        self.type_scope.names.extend(type_scope.names);

        Ok(())
    }

    /// Resolves the given module, adding it to self.modules.
    pub fn resolve_module(&mut self, module: Module<UnresolvedName, ()>) -> Result<(), Error> {
        let module_resolver = ModuleResolver::new(self, module.path);

        // Throw away the module's scopes,
        // because they're not used in resolving other modules.
        let (resolved, _scope, _type_scope) = module_resolver.resolve(module)?;
        self.modules.insert(resolved.path, resolved);

        Ok(())
    }

    /// Checks that any assumptions made in the resolved modules,
    /// and return the resolved modules.
    pub fn check_assumptions(
        mut self,
    ) -> Result<BTreeMap<ModulePath, Module<ResolvedName, ()>>, Error> {
        log::trace!(log::RESOLVE, "Checking resolution assumptions");

        // Assumptions about modules
        for assumption in self.module_assumptions.drain(..) {
            if !self.modules.contains_key(&assumption) {
                return Err(Error::NonexistentModule(assumption));
            }
        }

        // Assumptions about value-level names
        for assumption in self.scope.assumptions.drain(..) {
            let path = unwrap_match!(assumption.source, Source::Module(path) => path);

            let module = self
                .modules
                .get(&path)
                .ok_or(Error::NonexistentModule(path))?;

            if !(module.definitions.contains_key(&assumption)
                || module.constructors.contains_key(&assumption))
            {
                return Err(Error::NonexistentValueName(
                    assumption.ident,
                    assumption.source,
                ));
            }

            log::trace!(log::RESOLVE, "  Found name {assumption}");
        }

        // Assumptions about type-level names
        for assumption in self.type_scope.assumptions.drain(..) {
            let path = unwrap_match!(assumption.source, Source::Module(path) => path);

            let module = self
                .modules
                .get(&path)
                .ok_or(Error::NonexistentModule(path))?;

            if !(module.type_definitions.contains_key(&assumption)) {
                return Err(Error::NonexistentTypeName(
                    assumption.ident,
                    assumption.source,
                ));
            }

            log::trace!(log::RESOLVE, "  Found name {assumption}");
        }

        // Assumptions arising from imports (so we don't know if type- or value-level)
        for assumption in self.assumptions.drain(..) {
            let path = unwrap_match!(assumption.source, Source::Module(path) => path);

            let module = self
                .modules
                .get(&path)
                .ok_or(Error::NonexistentModule(path))?;

            if !(module.definitions.contains_key(&assumption)
                || module.constructors.contains_key(&assumption)
                || module.type_definitions.contains_key(&assumption))
            {
                return Err(Error::NonexistentName(assumption.ident, assumption.source));
            }

            log::trace!(log::RESOLVE, "  Found name {assumption}");
        }

        Ok(self.modules)
    }
}

impl fmt::Debug for Resolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Resolver:")?;
        for (name, sources) in self.scope.names.iter() {
            if sources.is_empty() {
                // writeln!(f, "  {name}: \t\t[no longer in scope]")?;
            } else {
                // @Todo: something better here
                writeln!(f, "  {name}: \t{sources:?}")?;
            }
        }

        for (name, sources) in self.type_scope.names.iter() {
            if sources.is_empty() {
                // writeln!(f, "  {name}: \t\t[no longer in scope]")?;
            } else {
                // @Todo: something better here
                writeln!(f, "  type {name}: \t{sources:?}")?;
            }
        }

        writeln!(f, "Assumptions: {{")?;
        for assumption in self.scope.assumptions.iter() {
            writeln!(f, "  {assumption:?}")?;
        }
        for assumption in self.type_scope.assumptions.iter() {
            writeln!(f, "  {assumption:?}")?;
        }
        writeln!(f, "}}")?;

        Ok(())
    }
}

pub struct ModuleResolver<'a> {
    /// The parent `Resolver`, which contains implicit imports (e.g. builtins, Prelude)
    resolver: &'a mut Resolver,

    /// The path of the module being resolved.
    module_path: ModulePath,

    /// The `Scope` used for value-level names.
    scope: Scope,

    /// The `Scope` used for type-level names.
    type_scope: TypeScope,
}

impl<'a> ModuleResolver<'a> {
    fn new(resolver: &'a mut Resolver, module_path: ModulePath) -> Self {
        ModuleResolver {
            resolver,
            module_path,
            scope: Scope::default(),
            type_scope: TypeScope::default(),
        }
    }

    fn resolve(
        mut self,
        module: Module<UnresolvedName, ()>,
    ) -> Result<(Module<ResolvedName, ()>, Scope, TypeScope), Error> {
        let start_time = Instant::now();
        log::trace!(log::RESOLVE, "Resolving module {}", module.path);

        // This is the new module we'll be building as we resolve names.
        let mut resolved_module: Module<ResolvedName, ()> = Module::new(module.path);

        // Add all the top-level definitions (including type constructors) to the scope
        let defns_iter = module.definitions.keys();
        let constrs_iter = module
            .type_definitions
            .values()
            .flat_map(|td| td.constructors.iter())
            .map(|(name, _term)| name);

        for name in defns_iter.chain(constrs_iter) {
            log::trace!(log::RESOLVE, "Adding `{name}` to the top-level scope");
            // @Todo @Checkme @Errors: can we collide here? if so, we should check that first.
            self.bind(Binding::module(module.path, *name));
        }

        // Add all the type names to the scope
        for type_name in module.type_definitions.keys() {
            log::trace!(
                log::RESOLVE,
                "Adding `{type_name}` to the top-level type scope"
            );
            // @Todo @Checkme @Errors: can we collide here? if so, we should check that first.
            self.bind_type(Binding::module(module.path, *type_name));
        }

        // Add all the imports to the scope as well as resolving the names.
        for (path, names) in module.imports {
            // Assume that the module exists, to be checked later.
            self.resolver.module_assumptions.push(path);

            // Handle the imported names.
            for name in names {
                log::trace!(
                    log::RESOLVE,
                    "Importing `{path}.{name}` to the top-level scope"
                );

                // Check that it's the right type of name.
                // @Todo @Errors: this should throw an error
                // (that is, if this is reachable; maybe it's already a parse error.
                // Actually, this should definitely be a parse error.)
                assert!(matches!(name, UnresolvedName::Unqualified(_)));

                let resolved = ResolvedName {
                    source: Source::Module(path),
                    ident: name.ident(),
                };

                // Assume that the module and the imported name both exist,
                // to be checked later.
                self.resolver.assumptions.push(resolved);
                log::trace!(log::RESOLVE, "  Assumed name `{resolved}` exists");

                // Replicate into the new module, resolving the import's name.
                resolved_module
                    .imports
                    .entry(path)
                    .or_default()
                    .push(resolved);

                // Insert it into the scope
                // @Todo @Checkme @Errors: can we collide here? if so, we should check that first.
                self.bind(Binding::module(path, name));
            }
        }

        // Add all the foreign imports to the scope as well as resolving the names.
        for (require, items) in module.foreign_imports {
            for ast::ForeignImportItem {
                foreign_name,
                name,
                type_scheme,
                typ: (),
            } in items
            {
                log::trace!(
                    log::RESOLVE,
                    "Importing `require({require})[\"{foreign_name}\"]` \
                    to the top-level scope as {name}"
                );

                // Check that it's the right type of name.
                // @Todo @Errors: this should throw an error
                // (that is, if this is reachable; maybe it's already a parse error.
                // Actually, this should definitely be a parse error.)
                assert!(matches!(name, UnresolvedName::Unqualified(_)));

                let source = Source::Foreign {
                    require,
                    foreign_name,
                };

                // Replicate into the new module, resolving the import's name.
                resolved_module
                    .foreign_imports
                    .entry(require)
                    .or_default()
                    .push(ast::ForeignImportItem {
                        foreign_name,
                        name: ResolvedName {
                            source,
                            ident: name.ident(),
                        },
                        type_scheme: self.resolve_type_scheme(type_scheme.clone())?,
                        typ: (),
                    });

                // Insert it into the scope
                // @Todo @Checkme @Errors: can we collide here? if so, we should check that first.
                self.bind(Binding::foreign(require, foreign_name, name));
            }
        }

        // Now we have all the top-level names in scope,
        // we're good to go with the rest of the module.
        log::trace!(
            log::RESOLVE,
            "Finished building now resolving the rest of the module."
        );

        // Resolve definitions
        for (unres_name, unres_defn) in module.definitions {
            log::trace!(log::RESOLVE, "Resolving definition for `{unres_name}`");
            let res_name = self.resolve_name(unres_name)?;
            let res_defn = self.resolve_definition(unres_defn)?;

            // @Note: can't have clashes because we're iterating a BTreeMap
            assert!(resolved_module
                .definitions
                .insert(res_name, res_defn)
                .is_none());
        }

        // Resolve type definitions
        for (unres_name, unres_type_defn) in module.type_definitions {
            log::trace!(log::RESOLVE, "Resolving type definition for `{unres_name}`");
            let res_name = self.resolve_type_name(unres_name)?;
            let res_type_defn = self.resolve_type_definition(unres_type_defn)?;

            // @Note: can't have clashes because we're iterating a BTreeMap
            assert!(resolved_module
                .type_definitions
                .insert(res_name, res_type_defn)
                .is_none());
        }

        // Resolve foreign exports
        for (lua_lhs, unres_expr) in module.foreign_exports {
            log::trace!(log::RESOLVE, "Resolving foreign export `{lua_lhs}`");
            let res_expr = self.resolve_expr(unres_expr)?;
            resolved_module.foreign_exports.push((lua_lhs, res_expr));
        }

        log::info!(
            log::METRICS,
            "Resolved module {}, {:?} elapsed",
            module.path,
            start_time.elapsed()
        );

        Ok((resolved_module, self.scope, self.type_scope))
    }

    /// Adds the given `Binding` to the value scope.
    fn bind(&mut self, b @ Binding(source, name): Binding) {
        log::trace!(log::RESOLVE, "    Binding name `{name}` (from {source})");
        self.scope.bind(b)
    }

    /// Removes the `Binding` on top of the value scope stack,
    /// and asserts that it's equal to the given `Binding`.
    fn unbind(&mut self, b @ Binding(source, name): Binding) {
        log::trace!(log::RESOLVE, "    Unbinding name `{name}` (from {source})");
        self.scope.unbind(b)
    }

    /// Adds the given `Binding` to the type scope.
    fn bind_type(&mut self, b @ Binding(source, name): Binding) {
        log::trace!(
            log::RESOLVE,
            "    Binding type name `{name}` (from {source})"
        );
        self.type_scope.bind(b)
    }

    /// Removes the `Binding` on top of the type scope stack,
    /// and asserts that it's equal to the given `Binding`.
    fn unbind_type(&mut self, b @ Binding(source, name): Binding) {
        log::trace!(
            log::RESOLVE,
            "    Unbinding type name `{name}` (from {source})"
        );
        self.type_scope.unbind(b)
    }

    // Resolution methods

    fn resolve_name(&mut self, name: UnresolvedName) -> Result<ResolvedName, Error> {
        log::trace!(log::RESOLVE, "  Attempting to resolve name `{name}`");
        // First check the current module...
        self.scope
            .resolve_name(name, self.module_path)
            // then check the parent scope (builtins and Prelude).
            .or_else(|_| self.resolver.scope.resolve_name(name, self.module_path))
    }

    fn resolve_type_name(&mut self, name: UnresolvedName) -> Result<ResolvedName, Error> {
        log::trace!(log::RESOLVE, "  Attempting to resolve type name `{name}`");
        // First check the current module...
        self.type_scope
            .resolve_name(name, self.module_path)
            // then check the parent type scope (builtins and Prelude).
            .or_else(|_| {
                self.resolver
                    .type_scope
                    .resolve_name(name, self.module_path)
            })
    }

    fn resolve_definition(
        &mut self,
        defn: ast::Definition<UnresolvedName, ()>,
    ) -> Result<ast::Definition<ResolvedName, ()>, Error> {
        let assignments = defn
            .assignments
            .into_iter()
            .map(|assign| self.resolve_assignment(assign))
            .collect::<Result<Vec<_>, _>>()?;

        let explicit_type = if let Some(ts) = defn.explicit_type {
            Some(self.resolve_type_scheme(ts)?)
        } else {
            None
        };

        Ok(ast::Definition {
            assignments,
            explicit_type,
            precedence: defn.precedence,
            typ: defn.typ,
        })
    }

    fn resolve_assignment(
        &mut self,
        assign: ast::Assignment<UnresolvedName>,
    ) -> Result<ast::Assignment<ResolvedName>, Error> {
        // Bind the arguments on the LHS
        let (arg_bindings, lhs) = self.resolve_lhs(assign.0)?;
        for b in arg_bindings.iter() {
            self.bind(*b);
        }

        // Resolve the RHS, possibly including the bound arguments
        let rhs = self.resolve_expr(assign.1)?;

        // Unbind the arguments
        for b in arg_bindings {
            self.unbind(b);
        }

        Ok((lhs, rhs))
    }

    fn resolve_expr(
        &mut self,
        expr: ast::Expr<UnresolvedName>,
    ) -> Result<ast::Expr<ResolvedName>, Error> {
        match expr {
            ast::Expr::Term(term) => Ok(ast::Expr::Term(match term {
                ast::Term::Name(name) => ast::Term::Name(self.resolve_name(name)?),

                ast::Term::List(unres_es) => {
                    let mut res_es = Vec::new();
                    for e in unres_es {
                        res_es.push(self.resolve_expr(e)?);
                    }
                    ast::Term::List(res_es)
                }
                ast::Term::Tuple(unres_es) => {
                    let mut res_es = Vec::new();
                    for e in unres_es {
                        res_es.push(self.resolve_expr(e)?);
                    }
                    ast::Term::Tuple(res_es)
                }

                ast::Term::Parens(e) => ast::Term::Parens(Box::new(self.resolve_expr(*e)?)),

                ast::Term::Numeral(s) => ast::Term::Numeral(s),
                ast::Term::String(s) => ast::Term::String(s),
                ast::Term::Unit => ast::Term::Unit,
            })),

            ast::Expr::App {
                func: unres_func,
                argument: unres_arg,
            } => {
                let func = Box::new(self.resolve_expr(*unres_func)?);
                let argument = Box::new(self.resolve_expr(*unres_arg)?);
                Ok(ast::Expr::App { func, argument })
            }

            ast::Expr::Binop {
                operator: unres_op,
                lhs: unres_lhs,
                rhs: unres_rhs,
            } => {
                let operator = self.resolve_name(unres_op)?;
                let lhs = Box::new(self.resolve_expr(*unres_lhs)?);
                let rhs = Box::new(self.resolve_expr(*unres_rhs)?);
                Ok(ast::Expr::Binop { operator, lhs, rhs })
            }

            ast::Expr::Let {
                definitions: unres_defns,
                in_expr: unres_in,
            } => {
                let mut definitions = BTreeMap::new();
                for (unres_name, unres_assigns) in unres_defns {
                    // @Checkme: is this binding stuff right?
                    let binding = Binding::local(unres_name);
                    self.bind(binding);

                    let res_name = self.resolve_name(unres_name)?;

                    let mut res_assigns = Vec::new();
                    for unres_assign in unres_assigns {
                        let res_assign = self.resolve_assignment(unres_assign)?;
                        res_assigns.push(res_assign);
                    }
                    definitions.insert(res_name, res_assigns);

                    self.unbind(binding);
                }

                let in_expr = Box::new(self.resolve_expr(*unres_in)?);

                Ok(ast::Expr::Let {
                    definitions,
                    in_expr,
                })
            }

            ast::Expr::If {
                cond: unres_cond,
                then_expr: unres_then,
                else_expr: unres_else,
            } => {
                let cond = Box::new(self.resolve_expr(*unres_cond)?);
                let then_expr = Box::new(self.resolve_expr(*unres_then)?);
                let else_expr = Box::new(self.resolve_expr(*unres_else)?);
                Ok(ast::Expr::If {
                    cond,
                    then_expr,
                    else_expr,
                })
            }

            ast::Expr::Case {
                expr: unres_expr,
                arms: unres_arms,
            } => {
                let expr = Box::new(self.resolve_expr(*unres_expr)?);
                let mut arms = Vec::new();
                for (unres_pat, unres_rhs) in unres_arms {
                    let (bindings, res_pat) = self.resolve_pattern(unres_pat)?;
                    for b in bindings.iter() {
                        self.bind(*b);
                    }
                    let res_rhs = self.resolve_expr(unres_rhs)?;
                    for b in bindings {
                        self.unbind(b);
                    }
                    arms.push((res_pat, res_rhs));
                }
                Ok(ast::Expr::Case { expr, arms })
            }

            ast::Expr::Lambda {
                lhs: unres_lhs,
                rhs: unres_rhs,
            } => {
                let (bindings, lhs) = self.resolve_lhs(unres_lhs)?;
                for b in bindings.iter() {
                    self.bind(*b);
                }
                let rhs = Box::new(self.resolve_expr(*unres_rhs)?);
                for b in bindings {
                    self.unbind(b);
                }
                Ok(ast::Expr::Lambda { lhs, rhs })
            }

            ast::Expr::Lua(s) => Ok(ast::Expr::Lua(s)),
            ast::Expr::UnsafeLua(s) => Ok(ast::Expr::UnsafeLua(s)),
        }
    }

    /// Returns a `Vec` of bound variables which have been added to the scope,
    /// as well as the resolved `Lhs`.
    fn resolve_lhs(
        &mut self,
        unres_lhs: ast::Lhs<UnresolvedName>,
    ) -> Result<(Vec<Binding>, ast::Lhs<ResolvedName>), Error> {
        // These are the variables bound in this LHS.
        let mut bindings = Vec::new();

        let res_lhs = match unres_lhs {
            ast::Lhs::Func {
                name: unres_name,
                args: unres_args,
            } => {
                // @Errors @Checkme: try to define a function with its own name as an argument e.g.
                //      foo   x = 1;
                //      foo foo = 2;
                // Possible this should be an error earlier, but not sure.

                let name = self.resolve_name(unres_name)?;

                let mut args = Vec::new();
                for unres_pat in unres_args {
                    let (bound, res_pat) = self.resolve_pattern(unres_pat)?;
                    bindings.extend(bound);
                    args.push(res_pat);
                }

                ast::Lhs::Func { name, args }
            }

            ast::Lhs::Binop {
                a: unres_a,
                op: unres_op,
                b: unres_b,
            } => {
                let op = self.resolve_name(unres_op)?;

                let (bound_a, a) = self.resolve_pattern(unres_a)?;
                bindings.extend(bound_a);

                let (bound_b, b) = self.resolve_pattern(unres_b)?;
                bindings.extend(bound_b);

                ast::Lhs::Binop { a, op, b }
            }

            ast::Lhs::Lambda { args: unres_args } => {
                let mut args = Vec::new();

                for unres_pat in unres_args {
                    let (bound, res_pat) = self.resolve_pattern(unres_pat)?;
                    bindings.extend(bound);
                    args.push(res_pat);
                }

                ast::Lhs::Lambda { args }
            }
        };

        Ok((bindings, res_lhs))
    }

    /// Returns a `Vec` of bound variables which have been added to the scope,
    /// as well as the resolved `Pattern`.
    fn resolve_pattern(
        &mut self,
        unres_pat: ast::Pattern<UnresolvedName>,
    ) -> Result<(Vec<Binding>, ast::Pattern<ResolvedName>), Error> {
        // These are the variables bound in this pattern.
        let mut bindings = Vec::new();

        let res_pat = match unres_pat {
            ast::Pattern::Bind(name) => {
                let binding = Binding::local(name);
                bindings.push(binding);
                ast::Pattern::Bind(binding.into())
            }

            ast::Pattern::List(pats) => {
                let mut res_pats = Vec::new();
                for pat in pats {
                    let (sub_bindings, sub_pat) = self.resolve_pattern(pat)?;
                    bindings.extend(sub_bindings);
                    res_pats.push(sub_pat);
                }
                ast::Pattern::List(res_pats)
            }
            ast::Pattern::Tuple(pats) => {
                let mut res_pats = Vec::new();
                for pat in pats {
                    let (sub_bindings, sub_pat) = self.resolve_pattern(pat)?;
                    bindings.extend(sub_bindings);
                    res_pats.push(sub_pat);
                }
                ast::Pattern::Tuple(res_pats)
            }

            ast::Pattern::Binop {
                operator: unres_op,
                lhs: unres_lhs,
                rhs: unres_rhs,
            } => {
                let operator = self.resolve_name(unres_op)?;

                let (bound_lhs, lhs) = self.resolve_pattern(*unres_lhs)?;
                bindings.extend(bound_lhs);

                let (bound_rhs, rhs) = self.resolve_pattern(*unres_rhs)?;
                bindings.extend(bound_rhs);

                ast::Pattern::Binop {
                    operator,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }

            ast::Pattern::Destructure {
                constructor: unres_constr,
                args: unres_args,
            } => {
                let constructor = self.resolve_name(unres_constr)?;

                let mut args = Vec::new();
                for pat in unres_args {
                    let (sub_bindings, sub_pat) = self.resolve_pattern(pat)?;
                    bindings.extend(sub_bindings);
                    args.push(sub_pat);
                }

                ast::Pattern::Destructure { constructor, args }
            }

            ast::Pattern::UnaryConstructor(constructor) => {
                ast::Pattern::UnaryConstructor(self.resolve_name(constructor)?)
            }

            ast::Pattern::Numeral(s) => ast::Pattern::Numeral(s),
            ast::Pattern::String(s) => ast::Pattern::String(s),
            ast::Pattern::Unit => ast::Pattern::Unit,
        };

        Ok((bindings, res_pat))
    }

    fn resolve_type_definition<Ty>(
        &mut self,
        type_defn: ast::TypeDefinition<UnresolvedName, Ty>,
    ) -> Result<ast::TypeDefinition<ResolvedName, Ty>, Error> {
        let name = self.resolve_type_name(type_defn.name)?;

        let bindings: Vec<_> = type_defn
            .vars
            .iter()
            .flat_map(|v| {
                if let TypeVar::Explicit(name) = v {
                    Some(Binding::local(*name))
                } else {
                    None
                }
            })
            .collect();

        // Add the type variables from the type definition LHS into the scope
        for b in bindings.iter() {
            self.bind_type(*b);
        }

        let mut constructors = BTreeMap::new();
        for unres_constr in type_defn.constructors.into_values() {
            let name = self.resolve_name(unres_constr.name)?;

            let mut args = Vec::new();
            for unres_type_term in unres_constr.args {
                let res_type_term = self.resolve_type_term(unres_type_term)?;
                args.push(res_type_term);
            }

            constructors.insert(
                name,
                ast::ConstructorDefinition {
                    name,
                    args,
                    typ: unres_constr.typ,
                },
            );
        }

        let mut vars = Vec::new();
        for var in type_defn.vars {
            let res_var = match var {
                TypeVar::Explicit(name) => TypeVar::Explicit(self.resolve_type_name(name)?),
                TypeVar::Generated(id) => TypeVar::Generated(id),
            };
            vars.push(res_var);
        }
        let vars = vars.into_iter().collect();

        // Take the type variables out of scope
        for b in bindings {
            self.unbind_type(b);
        }

        Ok(ast::TypeDefinition {
            name,
            constructors,
            vars,
            typ: type_defn.typ,
        })
    }

    fn resolve_type_scheme(
        &mut self,
        unres_ts: ast::TypeScheme<UnresolvedName>,
    ) -> Result<ast::TypeScheme<ResolvedName>, Error> {
        let bindings: Vec<_> = unres_ts.vars.iter().map(|v| Binding::local(*v)).collect();

        for b in bindings.iter() {
            self.bind_type(*b);
        }

        let typ = self.resolve_type_expr(unres_ts.typ)?;

        let mut vars = Vec::new();
        for var in unres_ts.vars {
            vars.push(self.resolve_type_name(var)?);
        }

        for b in bindings {
            self.unbind_type(b);
        }

        Ok(ast::TypeScheme { vars, typ })
    }

    fn resolve_type_expr(
        &mut self,
        unres_type_expr: ast::TypeExpr<UnresolvedName>,
    ) -> Result<ast::TypeExpr<ResolvedName>, Error> {
        match unres_type_expr {
            ast::TypeExpr::Term(term) => Ok(ast::TypeExpr::Term(self.resolve_type_term(term)?)),

            ast::TypeExpr::App(a, b) => {
                let a = self.resolve_type_expr(*a)?;
                let b = self.resolve_type_expr(*b)?;
                Ok(ast::TypeExpr::App(Box::new(a), Box::new(b)))
            }
            ast::TypeExpr::Arrow(a, b) => {
                let a = self.resolve_type_expr(*a)?;
                let b = self.resolve_type_expr(*b)?;
                Ok(ast::TypeExpr::Arrow(Box::new(a), Box::new(b)))
            }
        }
    }

    fn resolve_type_term(
        &mut self,
        type_term: ast::TypeTerm<UnresolvedName>,
    ) -> Result<ast::TypeTerm<ResolvedName>, Error> {
        match type_term {
            ast::TypeTerm::Concrete(unres_type_name) => {
                let res_type_name = self.resolve_type_name(unres_type_name)?;
                Ok(ast::TypeTerm::Concrete(res_type_name))
            }

            ast::TypeTerm::Var(var) => Ok(ast::TypeTerm::Var(self.resolve_type_name(var)?)),

            ast::TypeTerm::Parens(type_expr) => Ok(ast::TypeTerm::Parens(Box::new(
                self.resolve_type_expr(*type_expr)?,
            ))),

            ast::TypeTerm::List(type_expr) => Ok(ast::TypeTerm::List(Box::new(
                self.resolve_type_expr(*type_expr)?,
            ))),

            ast::TypeTerm::Tuple(unres_type_exprs) => {
                let mut res_type_exprs = Vec::new();
                for unres_type_expr in unres_type_exprs {
                    let res_type_expr = self.resolve_type_expr(unres_type_expr)?;
                    res_type_exprs.push(res_type_expr);
                }
                Ok(ast::TypeTerm::Tuple(res_type_exprs))
            }

            ast::TypeTerm::Unit => Ok(ast::TypeTerm::Unit),
        }
    }
}

impl<'a> fmt::Debug for ModuleResolver<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ModuleResolver (module {}):", self.module_path)?;
        for (name, sources) in self.scope.names.iter() {
            if sources.is_empty() {
                // writeln!(f, "  {name}: \t\t[no longer in scope]")?;
            } else {
                // @Todo: something better here
                writeln!(f, "  {name}: \t{sources:?}")?;
            }
        }

        for (name, sources) in self.type_scope.names.iter() {
            if sources.is_empty() {
                // writeln!(f, "  {name}: \t\t[no longer in scope]")?;
            } else {
                // @Todo: something better here
                writeln!(f, "  type {name}: \t{sources:?}")?;
            }
        }

        writeln!(f, "Assumptions: {{")?;
        for assumption in self.scope.assumptions.iter() {
            writeln!(f, "  {assumption:?}")?;
        }
        for assumption in self.type_scope.assumptions.iter() {
            writeln!(f, "  {assumption:?}")?;
        }
        writeln!(f, "}}")?;

        Ok(())
    }
}

/// A `Scope` records which names are defined in a given scope.
#[derive(Debug, Default, Clone)]
struct Scope {
    /// Names which are in scope.
    names: BTreeMap<UnresolvedName, Vec<Source>>,

    /// This field records assumptions made that names will exist in external modules.
    /// See [`resolve_name`](Scope::resolve_name) for more information.
    assumptions: Vec<ResolvedName>,
}

/// A `TypeScope` is just a `Scope`, but aliased for clearer usage.
type TypeScope = Scope;

impl Scope {
    /// Adds the given `Binding` to the scope.
    fn bind(&mut self, Binding(source, name): Binding) {
        self.names.entry(name).or_default().push(source);
    }

    /// Removes the `Binding` on top of the scope stack,
    /// and asserts that it's equal to the given `Binding`.
    fn unbind(&mut self, Binding(source, name): Binding) {
        let popped_source = self.names.get_mut(&name).and_then(|names| names.pop());
        assert_eq!(
            Some(source),
            popped_source,
            "Internal compiler error: unbound the wrong variable"
        );
    }

    /// Does the work for resolving a name in this scope.
    /// `module_path` is just used for error messages.
    ///
    /// See also [`ModuleResolver::resolve_name`] and [`ModuleResolver::resolve_type_name`].
    fn resolve_name(
        &mut self,
        name: UnresolvedName,
        module_path: ModulePath,
    ) -> Result<ResolvedName, Error> {
        match name {
            UnresolvedName::Qualified(path, ident) => {
                let resolved = ResolvedName {
                    source: Source::Module(path),
                    ident,
                };

                // @Note:
                // Here we need to check that the name actually exists in the module,
                // e.g. check that in `Foo.bar`, module `Foo` defined a name `bar`.
                // However, because we don't have the information at hand,
                // we'll just defer that check until the end of the resolve step,
                // when we've resolved all the rest of the names in all modules.
                // This `assumptions` entry is to mark that we still need to do this check.
                self.assumptions.push(resolved);
                log::trace!(log::RESOLVE, "  Assumed name `{resolved}` exists");

                Ok(resolved)
            }
            unres_name => self
                .names
                .get(&unres_name)
                .and_then(|v| v.last())
                .map(|source| {
                    let resolved = ResolvedName {
                        source: *source,
                        ident: unres_name.ident(),
                    };
                    log::trace!(log::RESOLVE, "  Resolved name `{resolved}`");
                    resolved
                })
                .ok_or(Error::NotInScope(module_path, unres_name)),
        }
    }
}

/// `Binding` represents a binding of an unresolved identifier to a particular binding site.
#[derive(Debug, Clone, Copy)]
struct Binding(Source, UnresolvedName);

impl Binding {
    fn local(name: UnresolvedName) -> Self {
        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
        Binding(Source::Local(id), name)
    }

    fn module(path: ModulePath, name: UnresolvedName) -> Self {
        Binding(Source::Module(path), name)
    }

    fn foreign(
        require: &'static str,
        foreign_name: ast::ForeignName,
        name: UnresolvedName,
    ) -> Self {
        Binding(
            Source::Foreign {
                require,
                foreign_name,
            },
            name,
        )
    }
}

impl From<Binding> for ResolvedName {
    fn from(Binding(source, name): Binding) -> Self {
        ResolvedName {
            source,
            ident: name.ident(),
        }
    }
}

impl From<ResolvedName> for Binding {
    fn from(name: ResolvedName) -> Self {
        Binding(name.source, UnresolvedName::Unqualified(name.ident))
    }
}

impl<Ty> ast::Definition<ResolvedName, Ty> {
    pub fn dependencies(&mut self) -> BTreeSet<ResolvedName> {
        let mut deps = BTreeSet::new();

        for (_lhs, expr) in self.assignments.iter() {
            expr.dependencies(&mut deps);
        }

        deps
    }
}

impl ast::Expr<ResolvedName> {
    pub fn dependencies(&self, deps: &mut BTreeSet<ResolvedName>) {
        use ast::*;
        match self {
            Expr::Term(Term::List(es)) | Expr::Term(Term::Tuple(es)) => {
                es.iter().for_each(|e| e.dependencies(deps));
            }
            Expr::Term(Term::Name(name)) => {
                deps.insert(*name);
            }
            Expr::Term(Term::Parens(e)) => e.dependencies(deps),
            Expr::Term(_) => (),

            Expr::App { func, argument } => {
                func.dependencies(deps);
                argument.dependencies(deps);
            }

            Expr::Binop { operator, lhs, rhs } => {
                deps.insert(*operator);
                lhs.dependencies(deps);
                rhs.dependencies(deps);
            }

            Expr::Let {
                definitions,
                in_expr,
            } => {
                let mut sub_deps = BTreeSet::new();

                in_expr.dependencies(&mut sub_deps);

                // Remove variables bound in the definitions
                for name in definitions.keys() {
                    // @Note: if .remove() returns false,
                    // the definition isn't referenced in the in_expr;
                    // therefore it's dead code.
                    // Maybe emit a warning about this.
                    sub_deps.remove(name);
                }

                deps.extend(sub_deps);
            }

            Expr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                cond.dependencies(deps);
                then_expr.dependencies(deps);
                else_expr.dependencies(deps);
            }

            Expr::Case { expr, arms } => {
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

            Expr::Lambda { lhs, rhs } => {
                assert!(matches!(lhs, Lhs::Lambda { .. }));
                let args = unwrap_match!(lhs, Lhs::Lambda { args } => args);

                let mut sub_deps = BTreeSet::new();

                rhs.dependencies(&mut sub_deps);

                // Remove variables bound in the lambda LHS
                for pat in args.iter() {
                    for name in pat.names_bound() {
                        // @Note: if .remove() returns false,
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
            Expr::Lua(_) | Expr::UnsafeLua(_) => (),
        }
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Identifier not in scope (module {0}): {1}")]
    NotInScope(ModulePath, UnresolvedName),

    #[error("Module `{0}` doesn't exist")]
    NonexistentModule(ModulePath),

    #[error("Variable `{0}` doesn't exist in module `{1}`")]
    NonexistentValueName(&'static str, Source),

    #[error("Type `{0}` doesn't exist in module `{1}`")]
    NonexistentTypeName(&'static str, Source),

    #[error("Identifier `{0}` doesn't exist in module `{1}`")]
    NonexistentName(&'static str, Source),
}
