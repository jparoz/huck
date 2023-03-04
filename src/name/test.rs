use test_log::test;

use crate::utils::{assert_matches, test::transpile};

use crate::error::Error as HuckError;
use crate::name::Error as NameError;
use crate::parse::Error as ParseError;

#[test]
fn error_value_not_in_scope() {
    assert_matches!(
        transpile("foo = 123; bar = baz;"),
        Err(HuckError::NameResolution(NameError::ValueNotInScope(..)))
    )
}

#[test]
fn error_type_not_in_scope() {
    assert_matches!(
        transpile("foo : Int = 3; bar : Foo = unsafe lua {nil};"),
        Err(HuckError::NameResolution(NameError::TypeNotInScope(..)))
    )
}

#[test]
fn error_import_clash() {
    assert_matches!(
        transpile("import Foo (foo); foo = 123;"),
        Err(HuckError::NameResolution(NameError::ImportClash(..)))
    )
}

#[test]
fn error_nonexistent_module() {
    assert_matches!(
        transpile("import Foo;"),
        Err(HuckError::NameResolution(NameError::NonexistentModule(..)))
    )
}

#[test]
fn error_nonexistent_value_name() {
    assert_matches!(
        transpile("import Prelude; foo = Prelude.nothing;"),
        Err(HuckError::NameResolution(NameError::NonexistentValueName(
            ..
        )))
    )
}

#[test]
fn error_nonexistent_type_name() {
    assert_matches!(
        transpile("import Prelude; foo : Prelude.Nothing = unsafe lua {};"),
        Err(HuckError::NameResolution(NameError::NonexistentTypeName(
            ..
        )))
    )
}

#[test]
fn error_nonexistent_constructor_name() {
    assert_matches!(
        transpile("import Prelude (Maybe (Just, Nothing, Foo));"),
        Err(HuckError::NameResolution(
            NameError::NonexistentConstructorName(..)
        ))
    )
}

#[test]
fn error_nonexistent_name() {
    assert_matches!(
        transpile("import Prelude (nothing);"),
        Err(HuckError::NameResolution(NameError::NonexistentName(..)))
    )
}

#[test]
fn error_duplicate_binding() {
    assert_matches!(
        transpile("a ++ a = 123;"),
        Err(HuckError::NameResolution(NameError::DuplicateBinding(..)))
    )
}

#[test]
fn error_duplicate_binding_lambda() {
    assert_matches!(
        transpile(r#"foo = \a a -> 123;"#),
        Err(HuckError::NameResolution(
            NameError::DuplicateBindingLambda(..)
        ))
    )
}

#[test]
fn name_in_scope() {
    assert_matches!(transpile("foo = 123; bar = foo;"), Ok(_));
}

#[test]
fn let_binding_in_scope() {
    assert_matches!(transpile("foo = let bar = 123 in bar;"), Ok(_));
}

#[test]
fn clashes_type_names() {
    assert_matches!(
        transpile("type Foo = Con; type Foo = Verse;"),
        Err(HuckError::Parse(ParseError::MultipleTypeDefinitions(..)))
    )
}

#[test]
fn clashes_type_constructors() {
    assert_matches!(
        transpile("type Foo = Con; type Bar = Con;"),
        Err(HuckError::Parse(ParseError::MultipleTypeConstructors(..)))
    )
}

#[test]
fn clashes_import_redefinition_implicit_prelude() {
    assert_matches!(
        transpile("length 1 = 2;"),
        Err(HuckError::NameResolution(NameError::ImportClash(..)))
    )
}

#[test]
fn clashes_import_type() {
    assert_matches!(
        transpile("import Foo (Data); type Data = MkData;"),
        Err(HuckError::NameResolution(NameError::ImportClash(..)))
    )
}

#[test]
fn clashes_foreign_import() {
    assert_matches!(
        transpile(r#"foreign import "inspect" (inspect : forall a. a -> String); inspect = 123;"#),
        Err(HuckError::NameResolution(NameError::ImportClash(..)))
    )
}
