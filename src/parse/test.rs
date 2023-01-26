use crate::{
    ast::{self, Statement},
    parse,
};

#[test]
fn module_declaration() {
    assert_eq!(
        parse::module_declaration(r#"module Foo.Bar;"#),
        Ok(("", ast::ModulePath("Foo.Bar")))
    )
}

#[test]
fn statement_import_qualified() {
    assert_eq!(
        parse::statement(r#"import Foo.Bar;"#),
        Ok((
            "",
            ast::Statement::QualifiedImport(ast::ModulePath("Foo.Bar"))
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
                ast::ModulePath("Foo.Bar"),
                vec![
                    ast::UnresolvedName::Ident("foo"),
                    ast::UnresolvedName::Ident("Bar")
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
                vec![ast::ForeignImportItem::SameName(
                    ast::UnresolvedName::Ident("inspect"),
                    ast::TypeScheme {
                        typ: ast::TypeExpr::Arrow(
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Var("a"))),
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Concrete("String")))
                        ),
                        vars: vec!["a"]
                    }
                )]
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
                name: ast::UnresolvedName::Ident("a"),
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
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete("Int"))
            },
            (
                ast::Lhs::Func {
                    name: ast::UnresolvedName::Ident("a"),
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
            ast::UnresolvedName::Ident("a"),
            ast::TypeScheme {
                vars: vec![],
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete("Int"))
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
            ast::UnresolvedName::Binop(">>"),
            parse::precedence::Precedence(parse::precedence::Associativity::Left, 5)
        )
    );
}

#[test]
fn statement_type_definition() {
    // TypeDefinition(TypeDefinition<'file>),
    assert_eq!(
        parse::statement("type Foo = Bar | Baz Int;").unwrap().1,
        ast::Statement::TypeDefinition(ast::TypeDefinition {
            name: ast::UnresolvedName::Ident("Foo"),
            vars: vec![],
            constructors: vec![
                (ast::UnresolvedName::Ident("Bar"), vec![]),
                (
                    ast::UnresolvedName::Ident("Baz"),
                    vec![ast::TypeTerm::Concrete("Int")]
                ),
            ]
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
        (
            "",
            ast::UnresolvedName::Qualified(ast::ModulePath("Foo"), "bar")
        )
    )
}

#[test]
fn name_qualified_upper() {
    assert_eq!(
        parse::name(r#"Foo.Bar"#).unwrap(),
        (
            "",
            ast::UnresolvedName::Qualified(ast::ModulePath("Foo"), "Bar")
        )
    )
}

#[test]
fn unit() {
    assert_eq!(parse::statement(r#"unit = ();"#).unwrap().1, {
        let name = ast::UnresolvedName::Ident("unit");
        Statement::AssignmentWithoutType((
            ast::Lhs::Func { name, args: vec![] },
            ast::Expr::Term(ast::Term::Unit),
        ))
    })
}

#[test]
fn apply_to_unit() {
    assert_eq!(parse::statement(r#"applyToUnit f = f ();"#).unwrap().1, {
        let name = ast::UnresolvedName::Ident("applyToUnit");
        Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name,
                args: vec![ast::Pattern::Bind("f")],
            },
            ast::Expr::App {
                func: Box::new(ast::Expr::Term(ast::Term::Name(
                    ast::UnresolvedName::Ident("f"),
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
            let name = ast::UnresolvedName::Ident("foo");
            Statement::AssignmentWithoutType((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind("x")],
                },
                ast::Expr::Case {
                    expr: Box::new(ast::Expr::Term(ast::Term::Name(
                        ast::UnresolvedName::Ident("x"),
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
