use std::collections::BTreeMap;
use std::time::Instant;
use std::{fmt, mem};

use crate::ast::Module;
use crate::types::TypeVar;
use crate::utils::unwrap_match;
use crate::{ast, log};

use super::{Error, Ident, ModulePath, ResolvedName, Source, UnresolvedName};

/// This struct manages name resolution across all modules.
/// The following example illustrates which names are held in which `Scope`
/// (value-level or type-level):
/// `type Foo a = Bar a Int;`
/// In this example, `Foo`, `a`, and `Int` are all type-level names;
/// `Bar` is a value-level name.
#[derive(Debug, Default)]
pub struct Resolver {
    /// The modules which have already been resolved.
    pub modules: BTreeMap<ModulePath, Module<ResolvedName, ()>>,

    /// The `Scope` used for builtin value-level names.
    scope: Scope,

    /// The `Scope` used for builtin type-level names.
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
            idents: BTreeMap::from([
                ("True", vec![ResolvedName::builtin("True")]),
                ("False", vec![ResolvedName::builtin("False")]),
            ]),
            ..Scope::default()
        };

        let type_scope = TypeScope {
            idents: BTreeMap::from([
                ("Int", vec![ResolvedName::builtin("Int")]),
                ("Float", vec![ResolvedName::builtin("Float")]),
                ("String", vec![ResolvedName::builtin("String")]),
                ("Bool", vec![ResolvedName::builtin("Bool")]),
                ("IO", vec![ResolvedName::builtin("IO")]),
            ]),
            ..Scope::default()
        };

        Resolver {
            scope,
            type_scope,
            ..Resolver::default()
        }
    }

    /// Resolves the given module, adding it to self.modules.
    /// Takes an optional pair of `Scope` and `TypeScope`,
    /// representing the scope of the Prelude.
    /// These scopes are implicitly imported into any module
    /// which doesn't have an explicit `import Prelude;` statement.
    pub fn resolve_module(
        &mut self,
        module: Module<UnresolvedName, ()>,
        prelude: Option<(Scope, TypeScope)>,
    ) -> Result<(Scope, TypeScope), Error> {
        let module_resolver = ModuleResolver::new(self, module.path, prelude);

        let (resolved, mut scope, mut type_scope) = module_resolver.resolve(module)?;

        // Pass on any assumptions
        self.scope
            .assumptions
            .extend(mem::take(&mut scope.assumptions));
        self.type_scope
            .assumptions
            .extend(mem::take(&mut type_scope.assumptions));

        self.modules.insert(resolved.path, resolved);

        // Return the scope and type scope (sans assumptions)
        Ok((scope, type_scope))
    }

    /// Checks that any assumptions made in the resolved modules,
    /// and return the resolved modules.
    pub fn finish(mut self) -> Result<BTreeMap<ModulePath, Module<ResolvedName, ()>>, Error> {
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
            match assumption.source {
                Source::Module(path) => {
                    let module = self
                        .modules
                        .get(&path)
                        .ok_or(Error::NonexistentModule(path))?;

                    if !(module.definitions.contains_key(&assumption)
                        || module.type_definitions.contains_key(&assumption))
                    {
                        return Err(Error::NonexistentName(assumption.ident, assumption.source));
                    }

                    log::trace!(log::RESOLVE, "  Found name {assumption}");
                }

                Source::Constructor(path, type_ident) => {
                    let module = self
                        .modules
                        .get(&path)
                        .ok_or(Error::NonexistentModule(path))?;

                    if !(module
                        .type_definitions
                        .get(&ResolvedName::module(path, type_ident))
                        .map(|type_definition| {
                            type_definition.constructors.contains_key(&assumption)
                        })
                        .unwrap_or(false))
                    {
                        return Err(Error::NonexistentConstructorName(
                            assumption.ident,
                            assumption.source,
                        ));
                    }
                }

                Source::Foreign { .. } => {
                    unreachable!("import assumptions can't be generated for foreign names")
                }
                Source::Local(_) => {
                    unreachable!("import assumptions can't be generated for local names")
                }
                Source::Builtin => {
                    unreachable!("import assumptions can't be generated for builtin names")
                }
            }
        }

        Ok(self.modules)
    }
}

struct ModuleResolver<'a> {
    /// The parent `Resolver`, which contains implicitly imported builtins.
    resolver: &'a mut Resolver,

    /// The path of the module being resolved.
    module_path: ModulePath,

    /// The `Scope` used for value-level names.
    scope: Scope,

    /// The `Scope` used for type-level names.
    type_scope: TypeScope,

    /// The optional Prelude `Scope` and `TypeScope`,
    /// to be implicitly imported if there is no explicit `import Prelude;`.
    prelude: Option<(Scope, TypeScope)>,
}

impl<'a> ModuleResolver<'a> {
    fn new(
        resolver: &'a mut Resolver,
        module_path: ModulePath,
        prelude: Option<(Scope, TypeScope)>,
    ) -> Self {
        ModuleResolver {
            resolver,
            module_path,
            prelude,
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

        // Add all the top-level definitions to the scope
        for name in module.definitions.keys() {
            log::trace!(log::RESOLVE, "Adding `{name}` to the top-level scope");
            let ident = name.ident();
            let resolved_name = ResolvedName::module(module.path, ident);
            self.bind(ident, resolved_name);
        }

        // Add all the type names (and constructors) to the scope
        for (type_name, type_defn) in module.type_definitions.iter() {
            log::trace!(
                log::RESOLVE,
                "Adding `{type_name}` to the top-level type scope"
            );
            let type_ident = type_name.ident();
            let resolved_name = ResolvedName::module(module.path, type_ident);
            self.bind_type(type_ident, resolved_name);

            // Add its constructors
            for cons_name in type_defn.constructors.keys() {
                let cons_ident = cons_name.ident();
                log::trace!(
                    log::RESOLVE,
                    "Adding constructor `{type_ident}.{cons_ident}` to the top-level scope"
                );

                let resolved_name = ResolvedName::constructor(module.path, type_ident, cons_ident);
                self.bind(cons_ident, resolved_name);
            }
        }

        // If there is no explicit Prelude import,
        // and we have a Prelude,
        // implicitly import the contents of the Prelude.
        let prelude_path = ModulePath("Prelude");
        if !module.imports.contains_key(&prelude_path) {
            if let Some((prelude_scope, prelude_type_scope)) = self.prelude.take() {
                log::trace!(
                    log::IMPORT,
                    "Implicitly importing contents of {prelude_path} into {path}",
                    path = module.path
                );

                // Check that there are no name clashes in `prelude_scope`.
                for (ident, names) in prelude_scope.idents {
                    // If `names` is empty,
                    // that means there was a non-top-level binding of `ident` in the Prelude;
                    // this is fine, is not a clash, and should be ignored.
                    if names.is_empty() {
                        continue;
                    }

                    // If the name already resolves to something,
                    // that means it's defined in this module as well as being imported.
                    // This is a name clash, so error.
                    if let Ok(existing_name) = self.resolve_name(UnresolvedName::Unqualified(ident))
                    {
                        return Err(Error::ImportClash(names[0], existing_name));
                    }

                    // Because there were no clashes,
                    // we're okay to include it in the scope.
                    assert!(self.scope.idents.insert(ident, names).is_none());
                }

                // Check that there are no name clashes in `prelude_type_scope`.
                for (type_ident, names) in prelude_type_scope.idents {
                    // If `names` is empty,
                    // that means there was a non-top-level binding of `ident` in the Prelude;
                    // this is fine, is not a clash, and should be ignored.
                    if names.is_empty() {
                        continue;
                    }

                    // If the name already resolves to something,
                    // that means it's defined in this module as well as being imported.
                    // This is a name clash, so error.
                    if let Ok(existing_name) =
                        self.resolve_type_name(UnresolvedName::Unqualified(type_ident))
                    {
                        return Err(Error::ImportClash(names[0], existing_name));
                    }

                    // Because there were no clashes,
                    // we're okay to include it in the scope.
                    assert!(self.type_scope.idents.insert(type_ident, names).is_none());
                }
            }
        }

        // Add all the imports to the scope as well as resolving the names.
        for (path, import_items) in module.imports {
            // Assume that the module exists, to be checked later.
            self.resolver.module_assumptions.push(path);
            log::trace!(log::RESOLVE, "  Assumed module `{path}` exists");

            // Handle the imported names.
            for import_item in import_items {
                let (is_value, ident, name, constructors) = match import_item {
                    ast::ImportItem::Value { ident, name } => (true, ident, name, Vec::new()),
                    ast::ImportItem::Type {
                        ident,
                        name,
                        constructors,
                    } => (false, ident, name, constructors),
                };

                let import_ident = name.ident();
                let resolved_name = ResolvedName::module(path, import_ident);

                log::trace!(
                    log::RESOLVE,
                    "Importing `{resolved_name}` to the top-level scope as `{module_path}.{ident}`",
                    module_path = module.path
                );

                // If the name already resolves to something,
                // that means it's defined in this module as well as being imported.
                // This is a name clash, so error.
                if is_value {
                    if let Ok(existing_name) = self.resolve_name(UnresolvedName::Unqualified(ident))
                    {
                        return Err(Error::ImportClash(resolved_name, existing_name));
                    }
                } else {
                    if let Ok(existing_name) =
                        self.resolve_type_name(UnresolvedName::Unqualified(ident))
                    {
                        return Err(Error::ImportClash(resolved_name, existing_name));
                    }
                }

                // Assume that the imported name exists, to be checked later.
                self.resolver.assumptions.push(resolved_name);
                log::trace!(log::RESOLVE, "  Assumed name `{name}` exists");

                // Assume that any constructors exist, to be checked later.
                let mut resolved_constructors = Vec::new();
                for (cons_name, cons_ident) in constructors {
                    // There's only ever constructors if resolved_name is a type name.
                    assert!(!is_value);

                    let cons_resolved_name =
                        ResolvedName::constructor(path, resolved_name.ident, cons_name.ident());

                    // If the name already resolves to something,
                    // that means it's defined in this module as well as being imported.
                    // This is a name clash, so error.
                    if let Ok(existing_name) =
                        self.resolve_name(UnresolvedName::Unqualified(cons_ident))
                    {
                        return Err(Error::ImportClash(cons_resolved_name, existing_name));
                    }

                    // @Errors: is this the right place to push the assumption?
                    // Maybe should be into a value-level specific assumption vec, e.g.
                    // self.scope.assumptions.push(cons_resolved_name);
                    self.resolver.assumptions.push(cons_resolved_name);
                    resolved_constructors.push((cons_resolved_name, cons_ident));
                    log::trace!(
                        log::RESOLVE,
                        "    Assumed type constructor `{cons_resolved_name}` exists"
                    )
                }

                // Insert the name into the scope
                if is_value {
                    self.bind(ident, resolved_name);
                } else {
                    self.bind_type(ident, resolved_name);
                }

                // Insert any constructors into the scope
                for (cons_name, cons_ident) in resolved_constructors.iter().cloned() {
                    self.bind(cons_ident, cons_name);
                }

                // Replicate into the new module, resolving the import's name.
                resolved_module
                    .imports
                    .entry(path)
                    .or_default()
                    .push(if is_value {
                        ast::ImportItem::Value {
                            ident,
                            name: resolved_name,
                        }
                    } else {
                        ast::ImportItem::Type {
                            ident,
                            name: resolved_name,
                            constructors: resolved_constructors,
                        }
                    });
            }
        }

        // Add all the foreign imports to the scope as well as resolving the names.
        // @Note: This *must* be done after the local definitions,
        // because the type signatures of foreign imports
        // could depend on locally-defined names (specifically type definitions).
        for (require, items) in module.foreign_imports {
            for ast::ForeignImportItem {
                foreign_name,
                name,
                type_scheme,
                typ: (),
            } in items
            {
                // Make sure that it's the right type of name.
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

                let ident = name.ident();
                let resolved_name = ResolvedName::foreign(require, foreign_name, ident);

                log::trace!(
                    log::RESOLVE,
                    "Importing `require({require})[\"{foreign_name}\"]` \
                    to the top-level scope as `{resolved_name}`"
                );

                // If the name already resolves to something,
                // that means it's defined in this module as well as being imported.
                // This is a name clash, so error.
                if let Ok(existing_name) = self.resolve_name(UnresolvedName::Unqualified(ident)) {
                    return Err(Error::ImportClash(resolved_name, existing_name));
                }

                // Insert it into the scope
                self.bind(ident, resolved_name);
            }
        }

        // Now we have all the top-level names in scope,
        // we're good to go with the rest of the module.
        log::trace!(
            log::RESOLVE,
            "Finished building scope, now resolving the rest of the module."
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

        log::trace!(log::RESOLVE, "{self:?}");

        log::info!(
            log::METRICS,
            "Resolved module {}, {:?} elapsed",
            module.path,
            start_time.elapsed()
        );

        Ok((resolved_module, self.scope, self.type_scope))
    }

    /// Binds an identifier to a `ResolvedName` in the value scope.
    fn bind(&mut self, ident: Ident, name: ResolvedName) {
        log::trace!(
            log::RESOLVE,
            "    Binding identifier `{ident}` to resolved name `{name}`"
        );
        self.scope.bind(ident, name)
    }

    /// Removes the `ResolvedName` on top of the value scope stack,
    /// and asserts that it's equal to the given `ResolvedName`.
    fn unbind(&mut self, ident: Ident, name: ResolvedName) {
        log::trace!(log::RESOLVE, "    Unbinding ident `{ident}` (`{name}`)");
        self.scope.unbind(ident, name)
    }

    /// Binds an identifier to a `ResolvedName` in the type scope.
    fn bind_type(&mut self, ident: Ident, name: ResolvedName) {
        log::trace!(
            log::RESOLVE,
            "    Binding type identifier `{ident}` to resolved name `{name}`"
        );
        self.type_scope.bind(ident, name)
    }

    /// Removes the `ResolvedName` on top of the type scope stack,
    /// and asserts that it's equal to the given `ResolvedName`.
    fn unbind_type(&mut self, ident: Ident, name: ResolvedName) {
        log::trace!(log::RESOLVE, "    Unbinding type ident `{ident}` ({name})");
        self.type_scope.unbind(ident, name)
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
            self.bind(b.ident, *b);
        }

        // Resolve the RHS, possibly including the bound arguments
        let rhs = self.resolve_expr(assign.1)?;

        // Unbind the arguments
        for b in arg_bindings {
            self.unbind(b.ident, b);
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

                ast::Term::TypedExpr(unres_expr, unres_ts) => {
                    let res_expr = self.resolve_expr(*unres_expr)?;
                    let res_ts = self.resolve_type_scheme(unres_ts)?;
                    ast::Term::TypedExpr(Box::new(res_expr), res_ts)
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
                let mut to_unbind = Vec::new();
                for (unres_name, unres_assigns) in unres_defns {
                    let ident = unres_name.ident();
                    let res_name = ResolvedName::local(ident);
                    self.bind(ident, res_name);
                    to_unbind.push((ident, res_name));

                    let mut res_assigns = Vec::new();
                    for unres_assign in unres_assigns {
                        let res_assign = self.resolve_assignment(unres_assign)?;
                        res_assigns.push(res_assign);
                    }
                    definitions.insert(res_name, res_assigns);
                }

                // Resolve the expression while the variables are in scope.
                let in_expr = Box::new(self.resolve_expr(*unres_in)?);

                for (ident, name) in to_unbind {
                    self.unbind(ident, name);
                }

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
                        self.bind(b.ident, *b);
                    }
                    let res_rhs = self.resolve_expr(unres_rhs)?;
                    for b in bindings {
                        self.unbind(b.ident, b);
                    }
                    arms.push((res_pat, res_rhs));
                }
                Ok(ast::Expr::Case { expr, arms })
            }

            ast::Expr::Lambda {
                args: unres_args,
                rhs: unres_rhs,
            } => {
                let (bindings, args) = self.resolve_args(unres_args)?;
                for b in bindings.iter() {
                    self.bind(b.ident, *b);
                }
                let rhs = Box::new(self.resolve_expr(*unres_rhs)?);
                for b in bindings {
                    self.unbind(b.ident, b);
                }
                Ok(ast::Expr::Lambda { args, rhs })
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
    ) -> Result<(Vec<ResolvedName>, ast::Lhs<ResolvedName>), Error> {
        match unres_lhs {
            ast::Lhs::Func {
                name: unres_name,
                args: unres_args,
            } => {
                // @Errors @Checkme: try to define a function with its own name as an argument e.g.
                //      foo   x = 1;
                //      foo foo = 2;
                // Possible this should be an error earlier, but not sure.

                let name = self.resolve_name(unres_name)?;
                let (bindings, args) = self.resolve_args(unres_args)?;
                Ok((bindings, ast::Lhs::Func { name, args }))
            }

            ast::Lhs::Binop {
                a: unres_a,
                op: unres_op,
                b: unres_b,
            } => {
                // These are the variables bound in this LHS.
                let mut bindings = BTreeMap::new();

                let op = self.resolve_name(unres_op)?;

                let (a_bindings, a) = self.resolve_pattern(unres_a)?;
                for bound @ ResolvedName {
                    ident: bound_ident, ..
                } in a_bindings
                {
                    if let Some(ResolvedName {
                        ident: existing_ident,
                        ..
                    }) = bindings.insert(bound_ident, bound)
                    {
                        return Err(Error::DuplicateBinding(existing_ident, op));
                    }
                }

                let (b_bindings, b) = self.resolve_pattern(unres_b)?;
                for bound @ ResolvedName {
                    ident: bound_ident, ..
                } in b_bindings
                {
                    if let Some(ResolvedName {
                        ident: existing_ident,
                        ..
                    }) = bindings.insert(bound_ident, bound)
                    {
                        return Err(Error::DuplicateBinding(existing_ident, op));
                    }
                }

                Ok((
                    bindings.into_values().collect(),
                    ast::Lhs::Binop { a, op, b },
                ))
            }
        }
    }

    /// Returns a `Vec` of bound variables which have been added to the scope,
    /// as well as the resolved `Vec<Pattern>`.
    fn resolve_args(
        &mut self,
        unres_args: Vec<ast::Pattern<UnresolvedName>>,
    ) -> Result<(Vec<ResolvedName>, Vec<ast::Pattern<ResolvedName>>), Error> {
        let mut bindings = BTreeMap::new();

        let mut args = Vec::new();

        for unres_pat in unres_args {
            let (pat_bindings, res_pat) = self.resolve_pattern(unres_pat)?;
            for bound @ ResolvedName {
                ident: bound_ident, ..
            } in pat_bindings
            {
                if let Some(ResolvedName {
                    ident: existing_ident,
                    ..
                }) = bindings.insert(bound_ident, bound)
                {
                    return Err(Error::DuplicateBindingLambda(existing_ident));
                }
            }
            args.push(res_pat);
        }

        Ok((bindings.into_values().collect(), args))
    }

    /// Returns a `Vec` of bound variables which have been added to the scope,
    /// as well as the resolved `Pattern`.
    fn resolve_pattern(
        &mut self,
        unres_pat: ast::Pattern<UnresolvedName>,
    ) -> Result<(Vec<ResolvedName>, ast::Pattern<ResolvedName>), Error> {
        // These are the variables bound in this pattern.
        let mut bindings = Vec::new();

        let res_pat = match unres_pat {
            ast::Pattern::Bind(name) => {
                let binding = ResolvedName::local(name.ident());
                bindings.push(binding);
                ast::Pattern::Bind(binding)
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

            ast::Pattern::Int(s) => ast::Pattern::Int(s),
            ast::Pattern::String(s) => ast::Pattern::String(s),
            ast::Pattern::Unit => ast::Pattern::Unit,
            ast::Pattern::Underscore(s) => ast::Pattern::Underscore(s),
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
                    Some(ResolvedName::local(name.ident()))
                } else {
                    None
                }
            })
            .collect();

        // Add the type variables from the type definition LHS into the scope
        for b in bindings.iter() {
            self.bind_type(b.ident, *b);
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
            self.unbind_type(b.ident, b);
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
        let bindings: Vec<_> = unres_ts
            .vars
            .iter()
            .map(|v| ResolvedName::local(v.ident()))
            .collect();

        for b in bindings.iter() {
            self.bind_type(b.ident, *b);
        }

        let typ = self.resolve_type_expr(unres_ts.typ)?;

        let mut vars = Vec::new();
        for var in unres_ts.vars {
            vars.push(self.resolve_type_name(var)?);
        }

        for b in bindings {
            self.unbind_type(b.ident, b);
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
        for (name, sources) in self.scope.idents.iter() {
            if !sources.is_empty() {
                writeln!(f, "  {name}: \t{sources:?}")?;
            }
        }

        for (name, sources) in self.type_scope.idents.iter() {
            if !sources.is_empty() {
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
pub struct Scope {
    /// Identifiers which are in scope.
    /// Maps the bare identifier to its resolved name.
    idents: BTreeMap<Ident, Vec<ResolvedName>>,

    /// This field records assumptions made that names will exist in external modules.
    /// See [`resolve_name`](Scope::resolve_name) for more information.
    assumptions: Vec<ResolvedName>,
}

/// A `TypeScope` is just a `Scope`, but aliased for clearer usage.
type TypeScope = Scope;

impl Scope {
    /// Binds an identifier to a `ResolvedName` in the scope.
    fn bind(&mut self, ident: Ident, name: ResolvedName) {
        self.idents.entry(ident).or_default().push(name);
    }

    /// Removes the `ResolvedName` on top of the identifier's scope stack,
    /// and asserts that it's equal to the given `ResolvedName`.
    fn unbind(&mut self, ident: Ident, name: ResolvedName) {
        let popped_name = self.idents.get_mut(ident).and_then(|names| names.pop());
        assert_eq!(
            Some(name),
            popped_name,
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
                let resolved = ResolvedName::module(path, ident);

                // @Note:
                // Here we need to check that the name actually exists in the module,
                // e.g. check that in `Foo.bar`, module `Foo` defined a name `bar`.
                // However, because we don't have the information at hand,
                // we'll just defer that check until the end of the resolve step,
                // when we've resolved all the rest of the names in all modules.
                // This `assumptions` entry is to mark that we still need to do this check.
                self.assumptions.push(resolved);
                log::trace!(log::RESOLVE, "    Assumed name `{resolved}` exists");

                Ok(resolved)
            }
            UnresolvedName::Unqualified(ident) => {
                let resolved = self
                    .idents
                    .get(&ident)
                    .and_then(|names| names.last())
                    // @Todo @Errors:
                    // This error should be different for type- and value-level names.
                    // This means the error handling will have to be pushed back up
                    // to ModuleResolver::{resolve_name, resolve_type_name}.
                    .ok_or(Error::NotInScope(module_path, ident))?;
                log::trace!(log::RESOLVE, "    Resolved name `{resolved}`");
                Ok(*resolved)
            }
        }
    }
}
