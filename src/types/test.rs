use std::collections::BTreeMap;

use crate::context::Context;
use crate::generatable_module::GeneratableModule;
use crate::module::ModulePath;
use crate::name::{ResolvedName, Source};
use crate::resolve::Resolver;
use crate::types::{Primitive, Type};

/// Shorthand to make a ResolvedName.
macro_rules! name {
    ($name:expr) => {
        ResolvedName {
            source: Source::Module(ModulePath("Test")),
            ident: $name,
        }
    };
}

/// Typechecks the given module and returns the resulting GeneratableModule.
fn typ_module(s: &'static str) -> GeneratableModule {
    let mut ctx = Context::new();
    ctx.include_file(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"))
        .unwrap();
    let s = Box::leak(format!("module Test; {s}").into_boxed_str());

    // Parse
    ctx.include_string(s).unwrap();

    // Post-parse
    let modules = ctx.post_parse(ctx.parsed.clone()).unwrap();

    // Resolve
    let mut resolved_modules = BTreeMap::new();
    let mut resolver = Resolver::new();
    for (path, module) in modules {
        let resolved_module = resolver.resolve(module).unwrap();
        resolved_modules.insert(path, resolved_module);
        resolver.clear_scopes();
    }

    // @Todo: apply precedence

    let mut gen_mods = ctx.typecheck(resolved_modules).unwrap();
    gen_mods.remove(&ModulePath("Test")).unwrap()
}

/// Infers the type of the given definition.
fn typ(s: &'static str) -> Type {
    typ_module(s).definitions.into_values().next().unwrap().0
}

#[test]
fn tuple_is_ordered() {
    let the_typ = typ(r#"a = (1, "hi");"#);
    assert_eq!(the_typ, typ(r#"a = (3, "hello");"#));
    assert_ne!(the_typ, typ(r#"a = ("hello", 3);"#));
    assert_ne!(the_typ, typ(r#"a = (3, "hello", 1);"#));
}

#[test]
fn literal_int() {
    assert_eq!(typ(r#"a = 123;"#), Type::Primitive(Primitive::Int));
}

#[test]
fn literal_float() {
    assert_eq!(typ(r#"a = 1.23;"#), Type::Primitive(Primitive::Float));
}

#[test]
fn literal_string() {
    assert_eq!(
        typ(r#"a = "Hello, world!";"#),
        Type::Primitive(Primitive::String)
    );
}

#[test]
fn literal_unit() {
    assert_eq!(typ(r#"a = ();"#), Type::Primitive(Primitive::Unit));
}

#[test]
fn literal_tuple_int_string() {
    assert_eq!(
        typ(r#"a = (123, "Hello, world!");"#),
        Type::Tuple(vec![
            Type::Primitive(Primitive::Int),
            Type::Primitive(Primitive::String)
        ])
    );
}

#[test]
fn literal_list_int() {
    assert_eq!(
        typ(r#"a = [123, 456];"#),
        Type::List(Box::new(Type::Primitive(Primitive::Int)))
    );
}

// @Note: This would be better if we could use matches! to avoid `TypeVar::Generated(1)`
// (could instead be `TypeVar::Generated(_)`),
// but the boxes prevent this.
// Also true for lots of other tests.
#[test]
fn function_id() {
    let typ = typ(r#"id a = a;"#);

    assert!(matches!(typ, Type::Arrow(_, _)));

    let (l, r) = if let Type::Arrow(l, r) = typ {
        (l, r)
    } else {
        unreachable!()
    };

    assert!(matches!(*l, Type::Var(_)));
    let l_var = if let Type::Var(var) = *l {
        var
    } else {
        unreachable!()
    };

    assert!(matches!(*r, Type::Var(_)));
    let r_var = if let Type::Var(var) = *r {
        var
    } else {
        unreachable!()
    };

    assert_eq!(l_var, r_var);
}

#[test]
fn function_const() {
    let typ = typ(r#"const a b = a;"#);

    assert!(matches!(typ, Type::Arrow(_, _)));

    let (l, r) = if let Type::Arrow(l, r) = typ {
        (l, r)
    } else {
        unreachable!()
    };
    assert!(matches!(*l, Type::Var(_)));
    assert!(matches!(*r, Type::Arrow(_, _)));

    let (r_l, r_r) = if let Type::Arrow(r_l, r_r) = *r {
        (r_l, r_r)
    } else {
        unreachable!()
    };
    assert!(matches!(*r_l, Type::Var(_)));
    assert!(matches!(*r_r, Type::Var(_)));
}

// @Prelude
#[ignore]
#[test]
fn function_add() {
    assert_eq!(
        typ(r#"f x = x + 5;"#),
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
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Concrete(name!("Foo")))
}

#[test]
fn constructor_unary_returned() {
    let module = typ_module(
        r#"
            type Foo = Bar;
            val a = Bar;
        "#,
    );

    let val = module.definitions.get(&name!("val")).unwrap().clone();

    assert!(matches!(val.0, Type::Arrow(_, _)));

    let (l, r) = if let Type::Arrow(l, r) = val.0 {
        (l, r)
    } else {
        unreachable!()
    };
    assert!(matches!(*l, Type::Var(_)));
    assert!(matches!(*r, Type::Concrete(foo) if foo == name!("Foo")));
}

#[test]
fn constructor_unary_argument() {
    let module = typ_module(
        r#"
            type Foo = Bar;
            val Bar = 123;
        "#,
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(
        val.0,
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
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Concrete(name!("Foo")))
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
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Primitive(Primitive::Int))
}

#[test]
fn constructor_newtype_generic_int() {
    let module = typ_module(
        r#"
            type Foo a = Foo a;
            val = Foo 123;
        "#,
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(
        val.0,
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
    );

    let val = module.definitions.get(&name!("val")).unwrap().clone();

    assert!(matches!(val.0, Type::Arrow(_, _)));

    let (l, r) = if let Type::Arrow(l, r) = val.0 {
        (l, r)
    } else {
        unreachable!()
    };
    assert!(matches!(*l, Type::Var(_)));
    assert!(matches!(*r, Type::App(_, _)));

    let (constr, inner) = if let Type::App(constr, inner) = *r {
        (constr, inner)
    } else {
        unreachable!()
    };
    assert!(matches!(*constr, Type::Concrete(foo) if foo == name!("Foo")));
    assert!(matches!(*inner, Type::Var(_)));
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
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Primitive(Primitive::Int))
}

#[test]
fn function_apply_to_literal() {
    let module = typ_module(
        r#"
            foo 123 = 234;
            val = foo 1;
        "#,
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Primitive(Primitive::Int))
}

#[test]
fn function_apply_to_variable() {
    let module = typ_module(
        r#"
            foo 123 = 234;
            anInt = 3;
            val = foo anInt;
        "#,
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Primitive(Primitive::Int))
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
    );

    let val = module.definitions.get(&name!("val")).unwrap();

    assert_eq!(val.0, Type::Primitive(Primitive::Int))
}
