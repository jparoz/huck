use test_log::test;

use std::collections::BTreeMap;

use crate::module::{Module, ModulePath};
use crate::name::{ResolvedName, Source};
use crate::parse::parse;
use crate::precedence::ApplyPrecedence;
use crate::resolve::Resolver;
use crate::typecheck::{Error as TypeError, Typechecker};
use crate::types::{Primitive, Type};
use crate::utils::unwrap_match;

use crate::error::Error as HuckError;

/// Shorthand to make a ResolvedName.
macro_rules! name {
    ($name:expr) => {
        ResolvedName {
            source: Source::Module(ModulePath("Test")),
            ident: $name,
        }
    };
}

/// Shorthand to assert that a value matches a pattern, with extra debug printing.
macro_rules! assert_matches {
    ($val:expr, $($pat:tt)+) => {
        assert!(matches!(dbg!(&$val), $($pat)+))
    };
}

const PRELUDE_SRC: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"));

/// Typechecks the given module and returns the resulting GeneratableModule.
fn typ_module(huck: &'static str) -> Result<Module<ResolvedName, Type>, HuckError> {
    let module = Box::leak(format!("module Test; {huck}").into_boxed_str());

    // Parse
    let mut parsed = Vec::new();
    for src in [PRELUDE_SRC, module] {
        let (module_path, statements) = parse(src)?;
        parsed.push((module_path, statements));
    }

    // Post-parse processing
    let mut modules = BTreeMap::new();
    for (path, stats) in parsed {
        modules.insert(path, Module::from_statements(path, stats)?);
    }

    // Resolve
    let mut resolver = Resolver::new();

    // Start with the prelude...
    let prelude_path = ModulePath("Prelude");
    if let Some(unresolved_prelude) = modules.remove(&prelude_path) {
        resolver.resolve_prelude(unresolved_prelude)?;
    }

    // Then resolve all other modules.
    for module in modules.into_values() {
        resolver.resolve_module(module)?;
    }

    // Check that any qualified names used actually exist.
    let mut resolved_modules = resolver.check_assumptions()?;

    // Apply operator precedences
    let mut precs = BTreeMap::new();
    for module in resolved_modules.values() {
        for (name, defn) in module.definitions.iter() {
            precs.extend(std::iter::repeat(name).zip(defn.precedence.iter()));
        }
    }

    for module in resolved_modules.values_mut() {
        module.apply(&precs);
    }

    // Typecheck
    let mut typechecker = Typechecker::new();
    let mut gen_mods = typechecker.typecheck(resolved_modules)?;
    Ok(gen_mods.remove(&ModulePath("Test")).unwrap())
}

/// Infers the type of the given definition.
fn typ(s: &'static str) -> Result<Type, HuckError> {
    Ok(typ_module(s)?.definitions.into_values().next().unwrap().typ)
}

#[test]
fn tuple_is_ordered() {
    let the_typ = typ(r#"a = (1, "hi");"#).unwrap();
    assert_eq!(the_typ, typ(r#"a = (3, "hello");"#).unwrap());
    assert_ne!(the_typ, typ(r#"a = ("hello", 3);"#).unwrap());
    assert_ne!(the_typ, typ(r#"a = (3, "hello", 1);"#).unwrap());
}

#[test]
fn literal_int() {
    assert_eq!(typ(r#"a = 123;"#).unwrap(), Type::Primitive(Primitive::Int));
}

#[test]
fn literal_float() {
    assert_eq!(
        typ(r#"a = 1.23;"#).unwrap(),
        Type::Primitive(Primitive::Float)
    );
}

#[test]
fn literal_string() {
    assert_eq!(
        typ(r#"a = "Hello, world!";"#).unwrap(),
        Type::Primitive(Primitive::String)
    );
}

#[test]
fn literal_unit() {
    assert_eq!(typ(r#"a = ();"#).unwrap(), Type::Primitive(Primitive::Unit));
}

#[test]
fn literal_tuple_int_string() {
    assert_eq!(
        typ(r#"a = (123, "Hello, world!");"#).unwrap(),
        Type::Tuple(vec![
            Type::Primitive(Primitive::Int),
            Type::Primitive(Primitive::String)
        ])
    );
}

#[test]
fn literal_list_int() {
    assert_eq!(
        typ(r#"a = [123, 456];"#).unwrap(),
        Type::List(Box::new(Type::Primitive(Primitive::Int)))
    );
}

// @Note: This would be better if we could use matches! to avoid `TypeVar::Generated(1)`
// (could instead be `TypeVar::Generated(_)`),
// but the boxes prevent this.
// Also true for lots of other tests.
#[test]
fn function_id() {
    let typ = typ(r#"id a = a;"#).unwrap();

    assert_matches!(typ, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(typ, Type::Arrow(l, r) => (l, r));

    assert_matches!(*l, Type::Var(_));
    let l_var = unwrap_match!(*l, Type::Var(var) => var);

    assert_matches!(*r, Type::Var(_));
    let r_var = unwrap_match!(*r, Type::Var(var) => var);

    assert_eq!(l_var, r_var);
}

#[test]
fn function_const() {
    let typ = typ(r#"const a b = a;"#).unwrap();

    assert_matches!(typ, Type::Arrow(_, _));

    let (l, r) = unwrap_match!(typ, Type::Arrow(l, r) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::Arrow(_, _));

    let (r_l, r_r) = unwrap_match!(*r, Type::Arrow(l, r) => (l, r));
    assert_matches!(*r_l, Type::Var(_));
    assert_matches!(*r_r, Type::Var(_));
}

#[test]
fn function_add() {
    assert_eq!(
        typ(r#"f x = x + 5;"#).unwrap(),
        Type::Arrow(
            Box::new(Type::Primitive(Primitive::Int)),
            Box::new(Type::Primitive(Primitive::Int))
        )
    );
}

#[test]
fn constructor_unary() {
    let module = typ_module(
        r#"
            type Foo = Bar;
            val = Bar;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Concrete(name!("Foo")))
}

#[test]
fn constructor_unary_returned() {
    let module = typ_module(
        r#"
            type Foo = Bar;
            val a = Bar;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap().clone();

    assert_matches!(val.typ, Type::Arrow(_, _));

    let (l, r) = unwrap_match!(val.typ, Type::Arrow(l, r) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::Concrete(foo) if foo == &name!("Foo"));
}

#[test]
fn constructor_unary_argument() {
    let module = typ_module(
        r#"
            type Foo = Bar;
            val Bar = 123;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(
        val.typ,
        Type::Arrow(
            Box::new(Type::Concrete(name!("Foo"))),
            Box::new(Type::Primitive(Primitive::Int)),
        ),
    )
}

#[test]
fn constructor_newtype_int() {
    let module = typ_module(
        r#"
            type Foo = Foo Int;
            val = Foo 123;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Concrete(name!("Foo")))
}

#[test]
fn constructor_newtype_unwrap_int() {
    let module = typ_module(
        r#"
            type Foo = Foo Int;
            toBeUnwrapped = Foo 123;
            unwrap (Foo x) = x;
            val = unwrap toBeUnwrapped;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Primitive(Primitive::Int))
}

#[test]
fn constructor_newtype_generic_int() {
    let module = typ_module(
        r#"
            type Foo a = Foo a;
            val = Foo 123;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(
        val.typ,
        Type::App(
            Box::new(Type::Concrete(name!("Foo"))),
            Box::new(Type::Primitive(Primitive::Int))
        ),
    )
}

#[test]
fn constructor_newtype_generic_var() {
    let module = typ_module(
        r#"
            type Foo a = Foo a;
            val x = Foo x;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap().clone();

    assert_matches!(val.typ, Type::Arrow(_, _));

    let (l, r) = unwrap_match!(val.typ, Type::Arrow(l, r) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::App(_, _));

    let (constr, inner) = unwrap_match!(*r, Type::App(c, i) => (c, i));
    assert_matches!(*constr, Type::Concrete(foo) if foo == &name!("Foo"));
    assert_matches!(*inner, Type::Var(_));
}

#[test]
fn constructor_newtype_generic_unwrap_int() {
    let module = typ_module(
        r#"
            type Foo a = Foo a;
            toBeUnwrapped = Foo 123;
            unwrap (Foo x) = x;
            val = unwrap toBeUnwrapped;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Primitive(Primitive::Int))
}

#[test]
fn function_apply_to_literal() {
    let module = typ_module(
        r#"
            foo 123 = 234;
            val = foo 1;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Primitive(Primitive::Int))
}

#[test]
fn function_apply_to_variable() {
    let module = typ_module(
        r#"
            foo 123 = 234;
            anInt = 3;
            val = foo anInt;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Primitive(Primitive::Int))
}

#[test]
fn function_apply_to_variable_indirect() {
    let module = typ_module(
        r#"
            bar 123 = 234;
            foo x = bar x;
            anInt = 3;
            val = foo anInt;
        "#,
    )
    .unwrap();

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.typ, Type::Primitive(Primitive::Int))
}

#[test]
fn arity_int() {
    assert!(matches!(
        typ("foo : Int;"),
        Ok(Type::Primitive(Primitive::Int))
    ));
    assert!(matches!(
        typ("foo : Int ();"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 1, 0)))
    ));
}

#[test]
fn arity_io() {
    let the_typ = typ("foo : IO ();");

    assert_matches!(the_typ, Ok(Type::App(..)));

    let (l, r) = unwrap_match!(the_typ, Ok(Type::App(l, r)) => (l, r));
    assert_matches!(*l, Type::Primitive(Primitive::IO));
    assert_matches!(*r, Type::Primitive(Primitive::Unit));

    assert!(matches!(
        typ("foo : IO;"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 0, 1)))
    ));

    assert!(matches!(
        typ("foo : IO () Int;"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 2, 1)))
    ));
}

#[test]
fn arity_custom() {
    assert_matches!(
        typ("type Foo a b c = Bar a | Baz b c; foo : Foo Int;"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 1, 3)))
    );

    assert_matches!(
        typ("type Foo a b c = Bar a | Baz b c; foo : Foo Int () () Float;"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 4, 3)))
    );

    assert_matches!(
        typ("type Foo a b c = Bar a | Baz b c; foo : Foo Int () Float;"),
        Ok(_)
    );
}
