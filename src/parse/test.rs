use std::collections::BTreeMap;

use crate::{ast, parse};

#[test]
fn statement_assign_without_type() {
    // AssignmentWithoutType(Assignment<'file>),
    assert_eq!(
        parse::statement("a = 123;").unwrap().1,
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name: ast::Name::Ident("a".to_string()),
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
                    name: ast::Name::Ident("a".to_string()),
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
            ast::Name::Ident("a".to_string()),
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
            ast::Name::Binop(">>".to_string()),
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
            name: ast::Name::Ident("Foo".to_string()),
            vars: vec![],
            constructors: vec![
                (ast::Name::Ident("Bar".to_string()), vec![]),
                (
                    ast::Name::Ident("Baz".to_string()),
                    vec![ast::TypeTerm::Concrete("Int")]
                ),
            ]
        })
    );
}

#[test]
fn binop_plus() {
    assert_eq!(
        parse::parse(r#"val = 1 + 2;"#).unwrap(),
        parse::parse(r#"val=1+2;"#).unwrap()
    )
}

#[test]
fn unit() {
    assert_eq!(parse::parse(r#"unit = ();"#).unwrap(), {
        let mut definitions: BTreeMap<ast::Name, ast::Definition> = BTreeMap::new();

        let name = ast::Name::Ident("unit".to_string());
        definitions
            .entry(name.clone())
            .or_default()
            .assignments
            .push((
                ast::Lhs::Func { name, args: vec![] },
                ast::Expr::Term(ast::Term::Unit),
            ));

        ast::Module {
            definitions,
            ..ast::Module::default()
        }
    })
}

#[test]
fn apply_to_unit() {
    assert_eq!(parse::parse(r#"applyToUnit f = f ();"#).unwrap(), {
        let mut definitions: BTreeMap<ast::Name, ast::Definition> = BTreeMap::new();

        let name = ast::Name::Ident("applyToUnit".to_string());
        definitions
            .entry(name.clone())
            .or_default()
            .assignments
            .push((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind("f")],
                },
                ast::Expr::App {
                    func: Box::new(ast::Expr::Term(ast::Term::Name(ast::Name::Ident(
                        "f".to_string(),
                    )))),
                    argument: Box::new(ast::Expr::Term(ast::Term::Unit)),
                },
            ));

        ast::Module {
            definitions,
            ..ast::Module::default()
        }
    })
}

#[test]
fn case() {
    assert_eq!(
        parse::parse(
            r#"
                foo x = case x of {
                    1 -> "one";
                    2 -> "two";
                    3 -> "three";
                };
            "#
        )
        .unwrap(),
        {
            let mut definitions: BTreeMap<ast::Name, ast::Definition> = BTreeMap::new();

            let name = ast::Name::Ident("foo".to_string());
            definitions
                .entry(name.clone())
                .or_default()
                .assignments
                .push((
                    ast::Lhs::Func {
                        name: name.clone(),
                        args: vec![ast::Pattern::Bind("x")],
                    },
                    ast::Expr::Case {
                        expr: Box::new(ast::Expr::Term(ast::Term::Name(ast::Name::Ident(
                            "x".to_string(),
                        )))),
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
                ));

            ast::Module {
                definitions,
                ..ast::Module::default()
            }
        }
    )
}
