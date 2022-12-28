use crate::scope::Scope;
use crate::{ast::Name, parse::parse};

use super::{
    constraint::ConstraintGenerator, substitution::ApplySub, typecheck, Type, TypeScheme, TypeVar,
    TypeVarSet,
};

fn typ(s: &str) -> Type {
    let parsed = parse(s).unwrap();

    assert!(parsed.definitions.len() == 1);
    let (_name, defn) = parsed.definitions.into_iter().next().unwrap();

    let mut cg = ConstraintGenerator::new();
    let mut typ = cg.generate_definition(&defn);

    let soln = cg.solve().unwrap();
    typ.apply(&soln);

    typ
}

fn typ_module(s: &str) -> Scope {
    let parsed = parse(s).unwrap();
    typecheck(parsed).unwrap()
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

// @Note @Cleanup: This would be better if we could use matches! to avoid `TypeVar::Generated(1)`
// (could instead be `TypeVar::Generated(_)`),
// but the boxes prevent this.
// Also true for lots of other tests.
#[test]
fn function_id() {
    assert_eq!(
        typ(r#"id a = a;"#),
        Type::Arrow(
            Box::new(Type::Var(TypeVar::Generated(1))),
            Box::new(Type::Var(TypeVar::Generated(1)))
        )
    );
}

#[test]
fn function_const() {
    assert_eq!(
        typ(r#"const a b = a;"#),
        Type::Arrow(
            Box::new(Type::Var(TypeVar::Generated(2))),
            Box::new(Type::Arrow(
                Box::new(Type::Var(TypeVar::Generated(1))),
                Box::new(Type::Var(TypeVar::Generated(2)))
            ))
        )
    );
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Foo".to_string()),
        }
    )
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
        .unwrap();
    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::single(TypeVar::Generated(1)),
            typ: Type::Arrow(
                Box::new(Type::Var(TypeVar::Generated(1))),
                Box::new(Type::Concrete("Foo".to_string())),
            ),
        }
    )
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
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Arrow(
                Box::new(Type::Concrete("Foo".to_string())),
                Box::new(Type::Concrete("Int".to_string())),
            ),
        }
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Foo".to_string()),
        }
    )
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Int".to_string())
        }
    )
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
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::App(
                Box::new(Type::Concrete("Foo".to_string())),
                Box::new(Type::Concrete("Int".to_string()))
            ),
        }
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
        .unwrap();

    let var = TypeVar::Generated(4);
    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::single(var.clone()),
            typ: Type::Arrow(
                Box::new(Type::Var(var.clone())),
                Box::new(Type::App(
                    Box::new(Type::Concrete("Foo".to_string())),
                    Box::new(Type::Var(var))
                ))
            ),
        }
    )
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Int".to_string())
        }
    )
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Int".to_string())
        }
    )
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Int".to_string())
        }
    )
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

    assert_eq!(
        val.type_scheme,
        TypeScheme {
            vars: TypeVarSet::empty(),
            typ: Type::Concrete("Int".to_string())
        }
    )
}
