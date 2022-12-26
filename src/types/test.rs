use crate::parse::parse;

use super::{
    constraint::{ConstraintGenerator, GenerateConstraints},
    substitution::ApplySub,
    Type, TypeVar,
};

fn typ(s: &str) -> Type {
    let parsed = parse(s).unwrap();

    assert!(parsed.definitions.len() == 1);
    let (_name, defns) = parsed.definitions.into_iter().next().unwrap();

    let mut cg = ConstraintGenerator::new();
    let mut typ = defns.generate(&mut cg);

    let soln = cg.solve().unwrap();
    typ.apply(&soln);

    typ
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

// @Note @Cleanup: This would be better if we could use matches! to avoid `TypeVar(1)`
// (could instead be `TypeVar(_)`),
// but the boxes prevent this.
// Also true for lots of other tests.
#[test]
fn function_id() {
    assert_eq!(
        typ(r#"id a = a;"#),
        Type::Func(
            Box::new(Type::Var(TypeVar(1))),
            Box::new(Type::Var(TypeVar(1)))
        )
    );
}

#[test]
fn function_const() {
    assert_eq!(
        typ(r#"const a b = a;"#),
        Type::Func(
            Box::new(Type::Var(TypeVar(2))),
            Box::new(Type::Func(
                Box::new(Type::Var(TypeVar(1))),
                Box::new(Type::Var(TypeVar(2)))
            ))
        )
    );
}

// @Todo: Prelude
#[ignore]
#[test]
fn function_add() {
    assert_eq!(
        typ(r#"f x = x + 5;"#),
        Type::Func(
            Box::new(Type::Concrete("Int".to_string())),
            Box::new(Type::Concrete("Int".to_string()))
        )
    );
}
