use crate::ast::{ModulePath, Name};
use crate::context::Context;
use crate::scope::Scope;
use crate::types::Type;

/// Typechecks the given module and returns the resulting Scope.
fn typ_module(s: &'static str) -> Scope {
    let mut ctx = Context::new();
    ctx.include_file(concat!(env!("CARGO_MANIFEST_DIR"), "/huck/Prelude.hk"))
        .unwrap();
    let s = Box::leak(format!("module Test; {s}").into_boxed_str());
    ctx.include_string(s).unwrap();
    let modules = ctx.resolve(ctx.parsed.clone()).unwrap();
    let mut scopes = ctx.typecheck(modules).unwrap();
    scopes.remove(&ModulePath("Test")).unwrap()
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
    assert_eq!(typ(r#"a = 123;"#), Type::Concrete("Int".to_string()));
}

#[test]
fn literal_float() {
    assert_eq!(typ(r#"a = 1.23;"#), Type::Concrete("Float".to_string()));
}

#[test]
fn literal_string() {
    assert_eq!(
        typ(r#"a = "Hello, world!";"#),
        Type::Concrete("String".to_string())
    );
}

#[test]
fn literal_unit() {
    assert_eq!(typ(r#"a = ();"#), Type::Concrete("()".to_string()));
}

#[test]
fn literal_tuple_int_string() {
    assert_eq!(
        typ(r#"a = (123, "Hello, world!");"#),
        Type::Tuple(vec![
            Type::Concrete("Int".to_string()),
            Type::Concrete("String".to_string())
        ])
    );
}

#[test]
fn literal_list_int() {
    assert_eq!(
        typ(r#"a = [123, 456];"#),
        Type::List(Box::new(Type::Concrete("Int".to_string())))
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
            Box::new(Type::Concrete("Int".to_string())),
            Box::new(Type::Concrete("Int".to_string()))
        )
    );
}

#[test]
fn constructor_unary() {
    let scope = typ_module(
        r#"
            type Foo = Bar;
            val = Bar;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Foo".to_string()),)
}

#[test]
fn constructor_unary_returned() {
    let scope = typ_module(
        r#"
            type Foo = Bar;
            val a = Bar;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap()
        .clone();

    assert!(matches!(val.0, Type::Arrow(_, _)));

    let (l, r) = if let Type::Arrow(l, r) = val.0 {
        (l, r)
    } else {
        unreachable!()
    };
    assert!(matches!(*l, Type::Var(_)));
    assert!(matches!(*r, Type::Concrete(foo) if foo == "Foo"));
}

#[test]
fn constructor_unary_argument() {
    let scope = typ_module(
        r#"
            type Foo = Bar;
            val Bar = 123;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(
        val.0,
        Type::Arrow(
            Box::new(Type::Concrete("Foo".to_string())),
            Box::new(Type::Concrete("Int".to_string())),
        ),
    )
}

#[test]
fn constructor_newtype_int() {
    let scope = typ_module(
        r#"
            type Foo = Foo Int;
            val = Foo 123;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Foo".to_string()),)
}

#[test]
fn constructor_newtype_unwrap_int() {
    let scope = typ_module(
        r#"
            type Foo = Foo Int;
            toBeUnwrapped = Foo 123;
            unwrap (Foo x) = x;
            val = unwrap toBeUnwrapped;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Int".to_string()))
}

#[test]
fn constructor_newtype_generic_int() {
    let scope = typ_module(
        r#"
            type Foo a = Foo a;
            val = Foo 123;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(
        val.0,
        Type::App(
            Box::new(Type::Concrete("Foo".to_string())),
            Box::new(Type::Concrete("Int".to_string()))
        ),
    )
}

#[test]
fn constructor_newtype_generic_var() {
    let scope = typ_module(
        r#"
            type Foo a = Foo a;
            val x = Foo x;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap()
        .clone();

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
    assert!(matches!(*constr, Type::Concrete(foo) if foo == "Foo"));
    assert!(matches!(*inner, Type::Var(_)));
}

#[test]
fn constructor_newtype_generic_unwrap_int() {
    let scope = typ_module(
        r#"
            type Foo a = Foo a;
            toBeUnwrapped = Foo 123;
            unwrap (Foo x) = x;
            val = unwrap toBeUnwrapped;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Int".to_string()))
}

#[test]
fn function_apply_to_literal() {
    let scope = typ_module(
        r#"
            foo 123 = 234;
            val = foo 1;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Int".to_string()))
}

#[test]
fn function_apply_to_variable() {
    let scope = typ_module(
        r#"
            foo 123 = 234;
            anInt = 3;
            val = foo anInt;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Int".to_string()))
}

#[test]
fn function_apply_to_variable_indirect() {
    let scope = typ_module(
        r#"
            bar 123 = 234;
            foo x = bar x;
            anInt = 3;
            val = foo anInt;
        "#,
    );

    let val = scope
        .definitions
        .get(&Name::Ident("val".to_string()))
        .unwrap();

    assert_eq!(val.0, Type::Concrete("Int".to_string()))
}
