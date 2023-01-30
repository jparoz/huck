use std::collections::BTreeMap;

use crate::ast;
use crate::module::ModulePath;
use crate::name::UnresolvedName;
use crate::precedence::{Associativity, Precedence};
use crate::{parse, types};

#[test]
fn module_declaration() {
    assert_eq!(
        parse::module_declaration(r#"module Foo.Bar;"#),
        Ok(("", ModulePath("Foo.Bar")))
    )
}

#[test]
fn statement_import_qualified() {
    assert_eq!(
        parse::statement(r#"import Foo.Bar;"#),
        Ok((
            "",
            ast::Statement::Import(ModulePath("Foo.Bar"), Vec::new())
        ))
    )
}

#[test]
fn statement_import_unqualified() {
    assert_eq!(
        parse::statement(r#"import Foo.Bar (foo, Bar);"#),
        Ok((
            "",
            ast::Statement::Import(
                ModulePath("Foo.Bar"),
                vec![
                    UnresolvedName::Unqualified("foo"),
                    UnresolvedName::Unqualified("Bar")
                ]
            )
        ))
    )
}

#[test]
fn statement_import_foreign() {
    assert_eq!(
        parse::statement(r#"foreign import "inspect" (inspect : forall a. a -> String);"#),
        Ok((
            "",
            ast::Statement::ForeignImport(
                r#""inspect""#,
                vec![ast::ForeignImportItem {
                    foreign_name: ast::ForeignName("inspect"),
                    name: UnresolvedName::Unqualified("inspect"),
                    type_scheme: ast::TypeScheme {
                        typ: ast::TypeExpr::Arrow(
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Var("a"))),
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Concrete(
                                UnresolvedName::Unqualified("String")
                            )))
                        ),
                        vars: vec!["a"]
                    },
                    typ: (),
                }]
            )
        ))
    )
}

#[test]
fn statement_assign_without_type() {
    // AssignmentWithoutType(Assignment<'file>),
    assert_eq!(
        parse::statement("a = 123;").unwrap().1,
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name: UnresolvedName::Unqualified("a"),
                args: vec![]
            },
            ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("123")))
        ))
    );
}

#[test]
fn statement_assign_with_type() {
    // AssignmentWithType(TypeScheme<'file>, Assignment<'file>),
    assert_eq!(
        parse::statement("a: Int = 123;").unwrap().1,
        ast::Statement::AssignmentWithType(
            ast::TypeScheme {
                vars: vec![],
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete(UnresolvedName::Unqualified(
                    "Int"
                )))
            },
            (
                ast::Lhs::Func {
                    name: UnresolvedName::Unqualified("a"),
                    args: vec![]
                },
                ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("123")))
            )
        )
    );
}

#[test]
fn statement_type_annotation() {
    // TypeAnnotation(Name, TypeScheme<'file>),
    assert_eq!(
        parse::statement("a: Int;").unwrap().1,
        ast::Statement::TypeAnnotation(
            UnresolvedName::Unqualified("a"),
            ast::TypeScheme {
                vars: vec![],
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete(UnresolvedName::Unqualified(
                    "Int"
                )))
            },
        )
    );
}

#[test]
fn statement_precedence() {
    // Precedence(Name, Precedence),
    assert_eq!(
        parse::statement("infixl 5 >>;").unwrap().1,
        ast::Statement::Precedence(
            UnresolvedName::Unqualified(">>"),
            Precedence {
                associativity: Associativity::Left,
                priority: 5
            }
        )
    );
}

#[test]
fn statement_type_definition() {
    // TypeDefinition(TypeDefinition<'file>),
    assert_eq!(
        parse::statement("type Foo = Bar | Baz Int;").unwrap().1,
        ast::Statement::TypeDefinition(ast::TypeDefinition {
            name: UnresolvedName::Unqualified("Foo"),
            vars: types::TypeVarSet::empty(),
            typ: (),
            constructors: BTreeMap::from([
                (
                    UnresolvedName::Unqualified("Bar"),
                    ast::ConstructorDefinition {
                        name: UnresolvedName::Unqualified("Bar"),
                        args: vec![],
                        typ: (),
                    }
                ),
                (
                    UnresolvedName::Unqualified("Baz"),
                    ast::ConstructorDefinition {
                        name: UnresolvedName::Unqualified("Baz"),
                        args: vec![ast::TypeTerm::Concrete(UnresolvedName::Unqualified("Int"))],
                        typ: (),
                    }
                ),
            ]),
        })
    );
}

#[test]
fn binop_plus() {
    assert_eq!(
        parse::statement(r#"val = 1 + 2;"#).unwrap(),
        parse::statement(r#"val=1+2;"#).unwrap()
    )
}

#[test]
fn name_qualified_lower() {
    assert_eq!(
        parse::name(r#"Foo.bar"#).unwrap(),
        ("", UnresolvedName::Qualified(ModulePath("Foo"), "bar"))
    )
}

#[test]
fn name_qualified_upper() {
    assert_eq!(
        parse::name(r#"Foo.Bar"#).unwrap(),
        ("", UnresolvedName::Qualified(ModulePath("Foo"), "Bar"))
    )
}

#[test]
fn unit() {
    assert_eq!(parse::statement(r#"unit = ();"#).unwrap().1, {
        let name = UnresolvedName::Unqualified("unit");
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func { name, args: vec![] },
            ast::Expr::Term(ast::Term::Unit),
        ))
    })
}

#[test]
fn apply_to_unit() {
    assert_eq!(parse::statement(r#"applyToUnit f = f ();"#).unwrap().1, {
        let name = UnresolvedName::Unqualified("applyToUnit");
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name,
                args: vec![ast::Pattern::Bind(UnresolvedName::Unqualified("f"))],
            },
            ast::Expr::App {
                func: Box::new(ast::Expr::Term(ast::Term::Name(
                    UnresolvedName::Unqualified("f"),
                ))),
                argument: Box::new(ast::Expr::Term(ast::Term::Unit)),
            },
        ))
    })
}

#[test]
fn case() {
    assert_eq!(
        parse::statement(
            r#"foo x = case x of {
                    1 -> "one";
                    2 -> "two";
                    3 -> "three";
                };"#
        )
        .unwrap()
        .1,
        {
            let name = UnresolvedName::Unqualified("foo");
            ast::Statement::AssignmentWithoutType((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind(UnresolvedName::Unqualified("x"))],
                },
                ast::Expr::Case {
                    expr: Box::new(ast::Expr::Term(ast::Term::Name(
                        UnresolvedName::Unqualified("x"),
                    ))),
                    arms: vec![
                        (
                            ast::Pattern::Numeral(ast::Numeral::Int("1")),
                            ast::Expr::Term(ast::Term::String(r#""one""#)),
                        ),
                        (
                            ast::Pattern::Numeral(ast::Numeral::Int("2")),
                            ast::Expr::Term(ast::Term::String(r#""two""#)),
                        ),
                        (
                            ast::Pattern::Numeral(ast::Numeral::Int("3")),
                            ast::Expr::Term(ast::Term::String(r#""three""#)),
                        ),
                    ],
                },
            ))
        }
    )
}
