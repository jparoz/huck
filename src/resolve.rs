use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display};
use std::sync::atomic::{self, AtomicUsize};
use std::time::Instant;

use crate::ast::UnresolvedName;
use crate::context::Context;
use crate::{ast, log};

/// A `ResolvedName` is a unique token, used in the compiler to uniquely identify a value.
/// After name resolution:
/// all names have been confirmed to exist,
/// and all references to a function have the same `ResolvedName`,
/// no matter where the references appear.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct ResolvedName {
    pub source: Source,
    pub ident: &'static str,
}

impl ResolvedName {
    pub fn is_builtin(&self) -> bool {
        self.source == Source::Builtin
    }

    pub fn is_local(&self) -> bool {
        matches!(self.source, Source::Local(..))
    }
}

impl Display for ResolvedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.source, self.ident)
    }
}

/// A `Source` describes where to find an identifier,
/// whether it's a Huck or foreign import,
/// or a local variable (let-binding, etc.).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum Source {
    /// From a Huck module.
    Module(ast::ModulePath),

    /// From a foreign (Lua) module.
    Foreign {
        /// Includes the quotation marks.
        require: &'static str,
        foreign_name: ast::ForeignName,
    },

    /// From e.g. a let binding.
    /// Contains a unique ID,
    /// so that we can tell apart identically-named but different `ResolvedName`s.
    Local(usize),

    /// Compiler builtin
    Builtin,
}

impl Display for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Source::Module(path) => path.fmt(f),
            Source::Foreign {
                require,
                foreign_name,
            } => write!(f, r#"require({require})["{foreign_name}"]"#),
            Source::Local(id) => write!(f, "<local {id}>"),
            Source::Builtin => write!(f, "<compiler builtin>"),
        }
    }
}

/// This struct manages name resolution in a single module.
/// The following example illustrates which names are held in which `Scope`
/// (value-level or type-level):
/// `type Foo a = Bar a Int;`
/// In this example, `Foo`, `a`, and `Int` are all type-level names;
/// `Bar` is a value-level name.
#[derive(Clone)]
pub struct Resolver {
    /// The path of the module which the `Scope` represents.
    module_path: ast::ModulePath,

    /// The `Scope` used for value-level names.
    scope: Scope,

    /// The `Scope` used for type-level names.
    type_scope: Scope,
}

impl Resolver {
    /// Makes a new `Resolver`, including builtin names in the relevant scopes.
    pub fn new() -> Self {
        let scope = Scope {
            names: BTreeMap::from([
                (UnresolvedName::Ident("True"), vec![Source::Builtin]),
                (UnresolvedName::Ident("False"), vec![Source::Builtin]),
            ]),
            ..Scope::default()
        };

        let type_scope = Scope {
            names: BTreeMap::from([
                (UnresolvedName::Ident("Int"), vec![Source::Builtin]),
                (UnresolvedName::Ident("Float"), vec![Source::Builtin]),
                (UnresolvedName::Ident("String"), vec![Source::Builtin]),
                (UnresolvedName::Ident("Bool"), vec![Source::Builtin]),
                (UnresolvedName::Ident("IO"), vec![Source::Builtin]),
            ]),
            ..Scope::default()
        };

        Resolver {
            // @XXX @Fixme: use an Option or something
            module_path: ast::ModulePath("XXX"),
            scope,
            type_scope,
        }
    }

    pub fn resolve(
        &mut self,
        module: ast::Module<UnresolvedName>,
    ) -> Result<ast::Module<ResolvedName>, Error> {
        let start_time = Instant::now();
        log::trace!(log::RESOLVE, "Resolving module {}", module.path);

        // @Note @Performance:
        // Throughout this function,
        // we don't use the originating module by value.
        // That is, the way it's currently written,
        // we really might as well use &Module.
        // This is because we have a reference to the module in the Scope.
        // Just easier for now, rather than trying to update in place;
        // but would be better to do it in place.

        // This is the new module we'll be building as we resolve names.
        let mut resolved_module: ast::Module<ResolvedName> = ast::Module::new(module.path);

        // Set the current module path.
        self.module_path = module.path;

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

        // Add all the imports to the as well as resolving the names.
        // @Cleanup: don't clone
        for (path, names) in module.imports.clone() {
            for name in names {
                log::trace!(
                    log::RESOLVE,
                    "Importing `{path}.{name}` to the top-level scope"
                );

                // Check that it's the right type of name.
                // @Todo @Errors: this should throw an error
                // (that is, if this is reachable; maybe it's already a parse error.
                // Actually, this should definitely be a parse error.)
                assert!(matches!(
                    name,
                    UnresolvedName::Ident(_) | UnresolvedName::Binop(_)
                ));

                // Replicate into the new module, resolving the import's name.
                resolved_module
                    .imports
                    .entry(path)
                    .or_default()
                    .push(ResolvedName {
                        source: Source::Module(path),
                        ident: name.ident(),
                    });

                // Insert it into the scope
                // @Todo @Checkme @Errors: can we collide here? if so, we should check that first.
                self.bind(Binding::module(path, name));
            }
        }

        // Add all the foreign imports to the as well as resolving the names.
        // @Cleanup: don't clone
        for (require, tuples) in module.foreign_imports.clone() {
            for (foreign_name, name, ts) in tuples {
                log::trace!(
                    log::RESOLVE,
                    "Importing `require({require})[\"{foreign_name}\"]` \
                    to the top-level scope as {name}"
                );

                // Check that it's the right type of name.
                // @Todo @Errors: this should throw an error
                // (that is, if this is reachable; maybe it's already a parse error.
                // Actually, this should definitely be a parse error.)
                assert!(matches!(
                    name,
                    UnresolvedName::Ident(_) | UnresolvedName::Binop(_)
                ));

                let source = Source::Foreign {
                    require,
                    foreign_name,
                };

                // Replicate into the new module, resolving the import's name.
                resolved_module
                    .foreign_imports
                    .entry(require)
                    .or_default()
                    .push((
                        foreign_name,
                        ResolvedName {
                            source,
                            ident: name.ident(),
                        },
                        self.resolve_type_scheme(ts.clone())?,
                    ));

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
        // @Cleanup: don't clone
        for (unres_name, unres_defn) in module.definitions.clone() {
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
        // @Cleanup: don't clone
        for (unres_name, unres_type_defn) in module.type_definitions.clone() {
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
        // @Cleanup: don't clone
        for (lua_lhs, unres_expr) in module.foreign_exports.clone() {
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

        Ok(resolved_module)
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
        self.scope.resolve_name(name, self.module_path)
    }

    fn resolve_type_name(&mut self, name: UnresolvedName) -> Result<ResolvedName, Error> {
        log::trace!(log::RESOLVE, "  Attempting to resolve type name `{name}`");
        self.type_scope.resolve_name(name, self.module_path)
    }

    fn resolve_definition(
        &mut self,
        defn: ast::Definition<UnresolvedName>,
    ) -> Result<ast::Definition<ResolvedName>, Error> {
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

    fn resolve_type_definition(
        &mut self,
        type_defn: ast::TypeDefinition<UnresolvedName>,
    ) -> Result<ast::TypeDefinition<ResolvedName>, Error> {
        // @Checkme: do we need to bind any more names,
        // or did we do that already in resolve?

        // @Cleanup: do we need to resolve this?
        let name = self.resolve_type_name(type_defn.name)?;

        let mut constructors = Vec::new();
        for (unres_constr_name, unres_type_terms) in type_defn.constructors {
            // @Cleanup: do we need to resolve this?
            let res_constr_name = self.resolve_name(unres_constr_name)?;

            let mut res_type_terms = Vec::new();
            for unres_type_term in unres_type_terms {
                let res_type_term = self.resolve_type_term(unres_type_term)?;
                res_type_terms.push(res_type_term);
            }

            constructors.push((res_constr_name, res_type_terms))
        }

        Ok(ast::TypeDefinition {
            name,
            constructors,
            vars: type_defn.vars,
        })
    }

    fn resolve_type_scheme(
        &mut self,
        unres_ts: ast::TypeScheme<UnresolvedName>,
    ) -> Result<ast::TypeScheme<ResolvedName>, Error> {
        let bindings: Vec<_> = unres_ts
            .vars
            .iter()
            // @Cleanup: this doesn't seem like the right place to make it an UnresolvedName...
            .map(|v| Binding::local(UnresolvedName::Ident(v)))
            .collect();

        for b in bindings.iter() {
            self.bind_type(*b);
        }

        let typ = self.resolve_type_expr(unres_ts.typ)?;

        for b in bindings {
            self.unbind_type(b);
        }

        Ok(ast::TypeScheme {
            vars: unres_ts.vars,
            typ,
        })
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

            // @Todo @Checkme: do we need to do something here? Oh well for now
            // ast::TypeTerm::Var(var_s) => {
            //     let res_type_name =
            //         // @Cleanup: This matches the UnresolvedName::Ident in resolve_type_scheme
            //         self.resolve_type_name(UnresolvedName::Ident(var_s))?;
            //     Ok((ast::TypeTerm::Var(res_type_name)))
            // }
            ast::TypeTerm::Var(v) => Ok(ast::TypeTerm::Var(v)),

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

impl fmt::Debug for Resolver {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Resolver (current module {}):", self.module_path)?;
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
    /// See also [`Resolver::resolve_name`] and [`Resolver::resolve_type_name`].
    fn resolve_name(
        &mut self,
        name: UnresolvedName,
        module_path: ast::ModulePath,
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
                log::trace!(log::RESOLVE, "  Assumed name `{resolved}`");

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

/// @Nocommit: document this
// @Note: guaranteed that it's an `ImportSource::Local`
#[derive(Debug, Clone, Copy)]
struct Binding(Source, UnresolvedName);

impl Binding {
    fn local(name: UnresolvedName) -> Self {
        static UNIQUE_COUNTER: AtomicUsize = AtomicUsize::new(0);
        let id = UNIQUE_COUNTER.fetch_add(1, atomic::Ordering::Relaxed);
        Binding(Source::Local(id), name)
    }

    fn module(path: ast::ModulePath, name: UnresolvedName) -> Self {
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
        Binding(name.source, UnresolvedName::Ident(name.ident))
    }
}

impl ast::Definition<ResolvedName> {
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

                let args = match lhs {
                    Lhs::Lambda { args } => args,
                    _ => unreachable!(),
                };

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
    NotInScope(ast::ModulePath, UnresolvedName),

    #[error("Module `{0}` doesn't exist")]
    NonexistentModule(ast::ModulePath),

    #[error("Identifier `{1}` doesn't exist in module `{0}`")]
    NonexistentImport(ast::ModulePath, UnresolvedName),
}
