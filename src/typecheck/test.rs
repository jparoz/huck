use test_log::test;

use crate::name::{ModulePath, ResolvedName, Source};
use crate::typecheck::Error as TypeError;
use crate::types::{Primitive, Type};
use crate::utils::{self, assert_matches, unwrap_match};

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

#[test]
fn error_could_not_unify() {
    assert_matches!(
        utils::test::typecheck("foo = 5; bar = foo <> foo;"),
        Err(HuckError::Type(TypeError::CouldNotUnify(
            Type::Primitive(Primitive::Int),
            Type::Primitive(Primitive::String),
            _,
            _
        )))
    );
}

#[test]
fn error_could_not_unify_recursive() {
    assert_matches!(
        utils::test::typecheck("type Wrap a = Wrap a; foo x = Wrap (foo x);"),
        Err(HuckError::Type(TypeError::CouldNotUnifyRecursive(..)))
    );
}

#[test]
fn error_could_not_unify_explicit() {
    assert_matches!(
        utils::test::typecheck("foo : forall a. a = 5;"),
        Err(HuckError::Type(TypeError::CouldNotUnifyExplicit(..)))
    );
    assert_matches!(
        utils::test::typecheck("foo = (5 : forall a. a);"),
        Err(HuckError::Type(TypeError::CouldNotUnifyExplicit(..)))
    );
}

// @Note: how to test this?
//
// The only situation when this comes up is
// when only ImplicitInstance constraints are remaining,
// and none of them can be processed.
//
// This means that all of the remaining constraints have active type vars,
// which seems to imply that they must be used in the other constraints,
// which seems to imply that there is a loop of some kind,
// which should have been detected and resolved.
//
// It could be that it's not really possible,
// in which case we should replace the error constructor with unreachable!().
//
// #[test]
// fn error_could_not_solve_type_constraints() {}

#[test]
fn error_incorrect_arity() {
    // Int correctly
    assert_matches!(
        utils::test::typecheck("foo : Int; foo = unsafe lua {};").map(|mut module| module
            .definitions
            .remove(&name!("foo"))
            .unwrap()
            .typ),
        Ok(Type::Primitive(Primitive::Int))
    );

    // Int incorrectly
    assert_matches!(
        utils::test::typecheck("foo : Int (); foo = unsafe lua {};").map(|mut module| module
            .definitions
            .remove(&name!("foo"))
            .unwrap()
            .typ),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 1, 0)))
    );

    // IO correctly
    let typ = utils::test::typecheck("foo : IO (); foo = unsafe lua {};")
        .map(|mut module| module.definitions.remove(&name!("foo")).unwrap().typ);

    assert_matches!(typ, Ok(Type::App(..)));

    let (l, r) = unwrap_match!(typ, Ok(Type::App(l, r)) => (l, r));
    assert_matches!(*l, Type::Primitive(Primitive::IO));
    assert_matches!(*r, Type::Primitive(Primitive::Unit));

    // IO incorrectly
    assert_matches!(
        utils::test::typecheck("foo : IO; foo = unsafe lua {};"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 0, 1)))
    );
    assert_matches!(
        utils::test::typecheck("foo : IO () Int; foo = unsafe lua {};"),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 2, 1)))
    );

    // Custom type correctly
    assert_matches!(
        utils::test::typecheck(
            "type Foo a b c = Bar a | Baz b c; foo : Foo Int () Float; foo = unsafe lua {};"
        ),
        Ok(_)
    );

    // Custom type incorrectly
    assert_matches!(
        utils::test::typecheck(
            "type Foo a b c = Bar a | Baz b c; foo : Foo Int; foo = unsafe lua {};"
        ),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 1, 3)))
    );
    assert_matches!(
        utils::test::typecheck(
            "type Foo a b c = Bar a | Baz b c; foo : Foo Int () () Float; foo = unsafe lua {};"
        ),
        Err(HuckError::Type(TypeError::IncorrectArity(_, 4, 3)))
    );
}

#[test]
fn error_incorrect_arity_type_variable() {
    // Correct
    assert_matches!(
        utils::test::typecheck("id : forall a. a -> a; id x = x;"),
        Ok(_)
    );

    // Incorrect
    assert_matches!(
        utils::test::typecheck("foo : forall a. a Int -> a; foo = unsafe lua {};"),
        Err(HuckError::Type(TypeError::IncorrectArityTypeVariable(..)))
    );
}

#[test]
fn explicit_type_id_general() {
    utils::test::typecheck("id : forall a. a -> a; id x = x;").expect("should typecheck correctly");
}

#[test]
fn explicit_type_id_specific() {
    utils::test::typecheck("id : Int -> Int; id x = x;").expect("should typecheck correctly");
}

#[test]
fn explicit_type_id_too_general() {
    assert_matches!(
        utils::test::typecheck("id : forall a b. a -> b; id x = x;"),
        Err(HuckError::Type(..))
    );
}

#[test]
fn explicit_type_id_wrong_input_type() {
    assert_matches!(
        utils::test::typecheck("id : forall a. Int -> a; id x = x;"),
        Err(HuckError::Type(..))
    );
}

#[test]
fn explicit_type_id_wrong_output_type() {
    assert_matches!(
        utils::test::typecheck("id : forall a. a -> Int; id x = x;"),
        Err(HuckError::Type(..))
    );
}

#[test]
fn wrap_recursive_wrong_explicit_type() {
    assert_matches!(
        utils::test::typecheck("type Wrap a = Wrap a; foo : forall a b. a -> b; foo x = Wrap x;"),
        Err(HuckError::Type(..))
    );
}

#[test]
fn linked_list_map() {
    let module = utils::test::typecheck(
        r#"
            type LinkedList a = Cons a (LinkedList a) | Nil;

            map : forall a b. (a -> b) -> LinkedList a -> LinkedList b;
            map f (Cons x xs) = Cons (f x) (map f xs);
            map _ Nil = Nil;

            myLinkedList : LinkedList Int = Cons 1 (Cons 2 (Cons 3 Nil));
            mapped = map (\x -> x*2) myLinkedList;
        "#,
    )
    .unwrap();

    let typ = module.definitions[&name!("map")].typ.clone();
    let (f, rest) = unwrap_match!(typ, Type::Arrow(f, rest) => (*f, *rest));

    let (f_l, f_r) = unwrap_match!(f, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(f_l, Type::Var(_));
    assert_matches!(f_r, Type::Var(_));

    let (list, result) = unwrap_match!(rest, Type::Arrow(l, r) => (*l, *r));

    let (list_cons, list_elem) = unwrap_match!(list, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(list_cons, Type::Concrete(name!("LinkedList")));
    assert_matches!(list_elem, Type::Var(_));

    let (result_cons, result_elem) = unwrap_match!(result, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(result_cons, Type::Concrete(name!("LinkedList")));
    assert_matches!(result_elem, Type::Var(_));
}

#[test]
fn linked_list_fold() {
    let module = utils::test::typecheck(
        r#"
            type LinkedList a = Cons a (LinkedList a) | Nil;

            fold : forall a b. ((a, b) -> b) -> b -> LinkedList a -> b;
            fold f acc (Cons x xs) = fold f (f (x, acc)) xs;
            fold _ acc Nil = acc;

            myLinkedList : LinkedList Int = Cons 1 (Cons 2 (Cons 3 Nil));
            sumOfList = fold (\(n, acc) -> n + acc) 0 myLinkedList;
        "#,
    )
    .unwrap();

    let typ = module.definitions[&name!("fold")].typ.clone();
    let (f, rest) = unwrap_match!(typ, Type::Arrow(f, rest) => (*f, *rest));

    let (f_l, f_r) = unwrap_match!(f, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(f_l, Type::Tuple(_));
    assert_matches!(f_r, Type::Var(_));

    let (zero, rest) = unwrap_match!(rest, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(zero, Type::Var(_));

    let (list, result) = unwrap_match!(rest, Type::Arrow(l, r) => (*l, *r));

    let (list_cons, list_elem) = unwrap_match!(list, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(list_cons, Type::Concrete(name!("LinkedList")));
    assert_matches!(list_elem, Type::Var(_));

    assert_matches!(result, Type::Var(_));

    assert_eq!(zero, result);
}

#[test]
fn linked_list_unfold_direct() {
    let module = utils::test::typecheck(
        r#"
            type LinkedList a = Cons a (LinkedList a) | Nil;
            type Maybe a = Just a | Nothing;

            unfold : forall a b. (b -> Maybe (a, b)) -> b -> LinkedList a;
            unfold f seed = case f seed of {
                    (Just (x, seed')) -> Cons x (unfold f seed');
                    Nothing -> Nil;
                };

            thousand = unfold (\n -> if n > 0 then Just (n, n-1) else Nothing) 1000;
        "#,
    )
    .unwrap();

    // @Checkme: not yet confirmed that this code is correct, becuase the unwrap above fails first
    let typ = module.definitions[&name!("unfold")].typ.clone();
    let (f, rest) = unwrap_match!(typ, Type::Arrow(f, rest) => (*f, *rest));

    let (f_l, f_r) = unwrap_match!(f, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(f_l, Type::Var(_));

    let (f_r_cons, f_r_elem) = unwrap_match!(f_r, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(f_r_cons, Type::Concrete(name!("Maybe")));
    assert_matches!(f_r_elem, Type::Tuple(_));

    let (seed, result) = unwrap_match!(rest, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(seed, Type::Var(_));

    let (result_cons, result_elem) = unwrap_match!(result, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(result_cons, Type::Concrete(name!("LinkedList")));
    assert_matches!(result_elem, Type::Var(_));

    assert_eq!(f_l, seed);
}

#[test]
fn linked_list_unfold_let() {
    let module = utils::test::typecheck(
        r#"
            type LinkedList a = Cons a (LinkedList a) | Nil;
            type Maybe a = Just a | Nothing;

            unfold : forall a b. (b -> Maybe (a, b)) -> b -> LinkedList a;
            unfold f seed =
                let go s = case f s of {
                    (Just (x, s')) -> Cons x (go s');
                    Nothing -> Nil;
                } in go seed;

            thousand = unfold (\n -> if n > 0 then Just (n, n-1) else Nothing) 1000;
        "#,
    )
    .unwrap();

    // @Checkme: not yet confirmed that this code is correct, becuase the unwrap above fails first
    let typ = module.definitions[&name!("unfold")].typ.clone();
    let (f, rest) = unwrap_match!(typ, Type::Arrow(f, rest) => (*f, *rest));

    let (f_l, f_r) = unwrap_match!(f, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(f_l, Type::Var(_));

    let (f_r_cons, f_r_elem) = unwrap_match!(f_r, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(f_r_cons, Type::Concrete(name!("Maybe")));
    assert_matches!(f_r_elem, Type::Tuple(_));

    let (seed, result) = unwrap_match!(rest, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(seed, Type::Var(_));

    let (result_cons, result_elem) = unwrap_match!(result, Type::App(cons, elem) => (*cons, *elem));
    assert_eq!(result_cons, Type::Concrete(name!("LinkedList")));
    assert_matches!(result_elem, Type::Var(_));

    assert_eq!(f_l, seed);
}

#[test]
fn tuple_is_ordered() {
    let module = utils::test::typecheck(
        r#"
            a = (1, "hi");
            b = (3, "hello");
            c = ("hello", 3);
            d = (3, "hello", 1);
        "#,
    )
    .unwrap();

    assert_eq!(
        module.definitions[&name!("a")].typ,
        module.definitions[&name!("b")].typ
    );
    assert_ne!(
        module.definitions[&name!("a")].typ,
        module.definitions[&name!("c")].typ
    );
    assert_ne!(
        module.definitions[&name!("a")].typ,
        module.definitions[&name!("d")].typ
    );
}

#[test]
fn literal_int() {
    assert_matches!(
        utils::test::typecheck(r#"a = 123;"#).map(|mut module| module
            .definitions
            .remove(&name!("a"))
            .unwrap()
            .typ),
        Ok(Type::Primitive(Primitive::Int))
    );
}

#[test]
fn literal_float() {
    assert_matches!(
        utils::test::typecheck(r#"a = 1.23;"#).map(|mut module| module
            .definitions
            .remove(&name!("a"))
            .unwrap()
            .typ),
        Ok(Type::Primitive(Primitive::Float))
    );
}

#[test]
fn literal_string() {
    assert_matches!(
        utils::test::typecheck(r#"a = "Hello, world!";"#).map(|mut module| module
            .definitions
            .remove(&name!("a"))
            .unwrap()
            .typ),
        Ok(Type::Primitive(Primitive::String))
    );
}

#[test]
fn literal_unit() {
    assert_matches!(
        utils::test::typecheck(r#"a = ();"#).map(|mut module| module
            .definitions
            .remove(&name!("a"))
            .unwrap()
            .typ),
        Ok(Type::Primitive(Primitive::Unit))
    );
}

#[test]
fn literal_tuple_int_string() {
    assert_eq!(
        utils::test::typecheck(r#"a = (123, "Hello, world!");"#)
            .map(|mut module| module.definitions.remove(&name!("a")).unwrap().typ)
            .unwrap(),
        Type::Tuple(vec![
            Type::Primitive(Primitive::Int),
            Type::Primitive(Primitive::String)
        ])
    );
}

#[test]
fn literal_list_int() {
    assert_eq!(
        utils::test::typecheck(r#"a = [123, 456];"#)
            .map(|mut module| module.definitions.remove(&name!("a")).unwrap().typ)
            .unwrap(),
        Type::List(Box::new(Type::Primitive(Primitive::Int)))
    );
}

// @Note: This would be better if we could use matches! to avoid `TypeVar::Generated(1)`
// (could instead be `TypeVar::Generated(_)`),
// but the boxes prevent this.
// Also true for lots of other tests.
#[test]
fn function_id() {
    let typ = utils::test::typecheck(r#"id a = a;"#)
        .map(|mut module| module.definitions.remove(&name!("id")).unwrap().typ);

    assert_matches!(typ, Ok(Type::Arrow(_, _)));
    let (l, r) = unwrap_match!(typ, Ok(Type::Arrow(l, r)) => (l, r));

    assert_matches!(*l, Type::Var(_));
    let l_var = unwrap_match!(*l, Type::Var(var) => var);

    assert_matches!(*r, Type::Var(_));
    let r_var = unwrap_match!(*r, Type::Var(var) => var);

    assert_eq!(l_var, r_var);
}

#[test]
fn function_id_used() {
    let module = utils::test::typecheck(r#"id a = a; foo = id 5; bar = id "hi";"#).unwrap();

    let id = &module.definitions[&name!("id")].typ;
    assert_matches!(id, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(id, Type::Arrow(l, r) => (l, r));

    assert_matches!(**l, Type::Var(_));
    let l_var = unwrap_match!(&**l, Type::Var(var) => var);

    assert_matches!(**r, Type::Var(_));
    let r_var = unwrap_match!(&**r, Type::Var(var) => var);

    assert_eq!(l_var, r_var);

    let foo = &module.definitions[&name!("foo")].typ;
    assert_eq!(*foo, Type::Primitive(Primitive::Int));

    let bar = &module.definitions[&name!("bar")].typ;
    assert_eq!(*bar, Type::Primitive(Primitive::String));
}

#[test]
fn function_id_let() {
    let module = utils::test::typecheck(r#"foo = let id a = a in (id 5, id "hi");"#).unwrap();

    let foo = &module.definitions[&name!("foo")].typ;
    assert_eq!(
        *foo,
        Type::Tuple(vec![
            Type::Primitive(Primitive::Int),
            Type::Primitive(Primitive::String)
        ])
    );
}

#[test]
fn function_id_let_generic() {
    let module = utils::test::typecheck(r#"foo x = let id a = a in id x;"#).unwrap();

    let foo = module.definitions[&name!("foo")].typ.clone();

    let (l, r) = unwrap_match!(foo, Type::Arrow(l, r) => (*l, *r));
    assert_matches!(l, Type::Var(_));
    assert_matches!(r, Type::Var(_));
    assert_eq!(l, r);
}

#[test]
fn function_const() {
    let typ = utils::test::typecheck(r#"const a b = a;"#)
        .map(|mut module| module.definitions.remove(&name!("const")).unwrap().typ);

    assert_matches!(typ, Ok(Type::Arrow(_, _)));

    let (l, r) = unwrap_match!(typ, Ok(Type::Arrow(l, r)) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::Arrow(_, _));

    let (r_l, r_r) = unwrap_match!(*r, Type::Arrow(l, r) => (l, r));
    assert_matches!(*r_l, Type::Var(_));
    assert_matches!(*r_r, Type::Var(_));
}

#[test]
fn function_add() {
    assert_eq!(
        utils::test::typecheck(r#"f x = x + 5;"#)
            .map(|mut module| module.definitions.remove(&name!("f")).unwrap().typ)
            .unwrap(),
        Type::Arrow(
            Box::new(Type::Primitive(Primitive::Int)),
            Box::new(Type::Primitive(Primitive::Int))
        )
    );
}

#[test]
fn function_binop_backticks() {
    let module = utils::test::typecheck(r#"foo x y = 123; bar = 4 `foo` 5;"#).unwrap();

    let foo = &module.definitions[&name!("foo")].typ;
    assert_matches!(foo, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(foo, Type::Arrow(l, r) => (l, r));
    assert_matches!(**l, Type::Var(_));
    let (r_l, r_r) = unwrap_match!(&**r, Type::Arrow(l, r) => (l, r));
    assert_matches!(**r_l, Type::Var(_));
    assert_matches!(**r_r, Type::Primitive(Primitive::Int));

    assert_eq!(
        module.definitions[&name!("bar")].typ,
        Type::Primitive(Primitive::Int)
    );
}

#[test]
fn function_define_binop_backticks() {
    let module = utils::test::typecheck(r#"x `foo` y = 123; bar = 4 `foo` 5;"#).unwrap();

    let foo = &module.definitions[&name!("foo")].typ;
    assert_matches!(foo, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(foo, Type::Arrow(l, r) => (l, r));
    assert_matches!(**l, Type::Var(_));
    let (r_l, r_r) = unwrap_match!(&**r, Type::Arrow(l, r) => (l, r));
    assert_matches!(**r_l, Type::Var(_));
    assert_matches!(**r_r, Type::Primitive(Primitive::Int));

    assert_eq!(
        module.definitions[&name!("bar")].typ,
        Type::Primitive(Primitive::Int)
    );
}

#[test]
fn constructor_unary() {
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
    let module = utils::test::typecheck(
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
fn function_self_recursive() {
    let mut module = utils::test::typecheck(
        r#"
            foo x = foo x;
        "#,
    )
    .unwrap();

    let typ = module.definitions.remove(&name!("foo")).unwrap().typ;

    assert_matches!(typ, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(typ, Type::Arrow(l, r) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::Var(_));
}

#[test]
fn function_mutually_recursive() {
    let mut module = utils::test::typecheck(
        r#"
            foo x = bar x;
            bar x = baz x;
            baz x = foo x;
        "#,
    )
    .unwrap();

    let typ = module.definitions.remove(&name!("foo")).unwrap().typ;

    assert_matches!(typ, Type::Arrow(_, _));
    let (l, r) = unwrap_match!(typ, Type::Arrow(l, r) => (l, r));
    assert_matches!(*l, Type::Var(_));
    assert_matches!(*r, Type::Var(_));
}
