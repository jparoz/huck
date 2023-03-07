use std::collections::BTreeMap;

use crate::name::{ModulePath, UnresolvedName};
use crate::parse::{self, Error as ParseError};
use crate::precedence::{Associativity, Precedence};
use crate::utils::assert_matches;
use crate::{ast, types};

/// Shorthand to make an `UnresolvedName`.
macro_rules! name {
    ($name:expr) => {
        UnresolvedName::Unqualified($name)
    };
}

/// Shorthand to parse a module into an [`ast::Module`].
macro_rules! module {
    ($src:expr) => {
        parse::parse(concat!("module Test;", $src))
            .and_then(|(path, stats)| ast::Module::from_statements(path, stats))
    };
}

#[test]
fn error_multiple_precs() {
    assert_matches!(
        module!(r#"a ++ b = 123; infixl 3 ++; infixr 4 ++;"#),
        Err(ParseError::MultiplePrecs(..))
    )
}

#[test]
fn error_multiple_type_annotations() {
    assert_matches!(
        module!(r#"foo : Int; foo = 123; foo : Int;"#),
        Err(ParseError::MultipleTypeAnnotations(..))
    )
}

#[test]
fn error_multiple_type_definitions() {
    assert_matches!(
        module!(r#"type Foo = Food; type Foo = Bard;"#),
        Err(ParseError::MultipleTypeDefinitions(..))
    )
}

#[test]
fn error_multiple_type_constructors() {
    assert_matches!(
        module!(r#"type Foo = Foo; type Bar = Foo;"#),
        Err(ParseError::MultipleTypeConstructors(..))
    )
}

#[test]
fn error_multiple_unconditionals() {
    assert_matches!(
        module!(r#"foo x = 123; foo y = 456;"#),
        Err(ParseError::MultipleUnconditionals(..))
    )
}

#[test]
fn error_missing_assignment() {
    assert_matches!(
        module!(r#"foo : Int;"#),
        Err(ParseError::MissingAssignment(..))
    )
}

#[test]
fn error_incorrect_argument_count() {
    assert_matches!(
        module!(r#"foo 1 2 = 3; foo xs = 456;"#),
        Err(ParseError::IncorrectArgumentCount(..))
    )
}

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
        parse::statement(r#"import Foo.Bar (foo, Bar, baz as quux, (++));"#),
        Ok((
            "",
            ast::Statement::Import(
                ModulePath("Foo.Bar"),
                vec![
                    name!("foo").into(),
                    ast::ImportItem::Type {
                        name: name!("Bar"),
                        ident: "Bar",
                        constructors: Vec::new(),
                    },
                    ast::ImportItem::Value {
                        name: name!("baz"),
                        ident: "quux",
                    },
                    ast::ImportItem::Value {
                        name: name!("++"),
                        ident: "++",
                    },
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
                    name: name!("inspect"),
                    type_scheme: ast::TypeScheme {
                        typ: ast::TypeExpr::Arrow(
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Var(name!("a")))),
                            Box::new(ast::TypeExpr::Term(ast::TypeTerm::Concrete(name!(
                                "String"
                            ))))
                        ),
                        vars: vec![name!("a")]
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
                name: name!("a"),
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
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete(name!("Int")))
            },
            (
                ast::Lhs::Func {
                    name: name!("a"),
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
            name!("a"),
            ast::TypeScheme {
                vars: vec![],
                typ: ast::TypeExpr::Term(ast::TypeTerm::Concrete(name!("Int")))
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
            name!(">>"),
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
            name: name!("Foo"),
            vars: types::TypeVarSet::empty(),
            typ: (),
            constructors: BTreeMap::from([
                (
                    name!("Bar"),
                    ast::ConstructorDefinition {
                        name: name!("Bar"),
                        args: vec![],
                        typ: (),
                    }
                ),
                (
                    name!("Baz"),
                    ast::ConstructorDefinition {
                        name: name!("Baz"),
                        args: vec![ast::TypeTerm::Concrete(name!("Int"))],
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
fn binop_backticks() {
    assert_eq!(parse::statement(r#"bar = 4 `foo` 5;"#).unwrap().1, {
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name: name!("bar"),
                args: vec![],
            },
            ast::Expr::Binop {
                operator: name!("foo"),
                lhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("4")))),
                rhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("5")))),
            },
        ))
    })
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
        let name = name!("unit");
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func { name, args: vec![] },
            ast::Expr::Term(ast::Term::Unit),
        ))
    })
}

#[test]
fn apply_to_unit() {
    assert_eq!(parse::statement(r#"applyToUnit f = f ();"#).unwrap().1, {
        let name = name!("applyToUnit");
        ast::Statement::AssignmentWithoutType((
            ast::Lhs::Func {
                name,
                args: vec![ast::Pattern::Bind(name!("f"))],
            },
            ast::Expr::App {
                func: Box::new(ast::Expr::Term(ast::Term::Name(name!("f")))),
                argument: Box::new(ast::Expr::Term(ast::Term::Unit)),
            },
        ))
    })
}

#[test]
fn pattern_int() {
    assert_eq!(parse::pattern("123 ").unwrap().1, ast::Pattern::Int("123"))
}

#[test]
fn pattern_float() {
    assert!(parse::pattern("1.23 ").is_err())
}

#[test]
fn literal_int() {
    assert_eq!(
        parse::expr("123 ").unwrap().1,
        ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("123")))
    )
}

#[test]
fn literal_int_subtract() {
    assert_eq!(
        parse::expr("1-123 ").unwrap().1,
        ast::Expr::Binop {
            operator: name!("-"),
            lhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("1")))),
            rhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int(
                "123"
            )))),
        }
    )
}

#[test]
fn literal_float() {
    assert_eq!(
        parse::expr("1.23 ").unwrap().1,
        ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Float("1.23")))
    )
}

#[test]
fn literal_float_subtract() {
    assert_eq!(
        parse::expr("1.2-3.4 ").unwrap().1,
        ast::Expr::Binop {
            operator: name!("-"),
            lhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Float(
                "1.2"
            )))),
            rhs: Box::new(ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Float(
                "3.4"
            )))),
        }
    )
}

#[test]
fn case_int() {
    assert_eq!(
        parse::statement(
            r#"foo x = case x of {
                    1 -> "one";
                    2 -> "two";
                    3 -> "three";
                    -1 -> "minus one";
                };"#
        )
        .unwrap()
        .1,
        {
            let name = name!("foo");
            ast::Statement::AssignmentWithoutType((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind(name!("x"))],
                },
                ast::Expr::Case {
                    expr: Box::new(ast::Expr::Term(ast::Term::Name(name!("x")))),
                    arms: vec![
                        (
                            ast::Pattern::Int("1"),
                            ast::Expr::Term(ast::Term::String(r#""one""#)),
                        ),
                        (
                            ast::Pattern::Int("2"),
                            ast::Expr::Term(ast::Term::String(r#""two""#)),
                        ),
                        (
                            ast::Pattern::Int("3"),
                            ast::Expr::Term(ast::Term::String(r#""three""#)),
                        ),
                        (
                            ast::Pattern::Int("-1"),
                            ast::Expr::Term(ast::Term::String(r#""minus one""#)),
                        ),
                    ],
                },
            ))
        }
    )
}

#[test]
fn case_maybe() {
    assert_eq!(
        parse::statement(
            r#"foo x = case x of {
                Just n -> n;
                Nothing -> 0;
            };"#
        )
        .unwrap()
        .1,
        {
            let name = name!("foo");
            ast::Statement::AssignmentWithoutType((
                ast::Lhs::Func {
                    name,
                    args: vec![ast::Pattern::Bind(name!("x"))],
                },
                ast::Expr::Case {
                    expr: Box::new(ast::Expr::Term(ast::Term::Name(name!("x")))),
                    arms: vec![
                        (
                            ast::Pattern::Destructure {
                                constructor: name!("Just"),
                                args: vec![ast::Pattern::Bind(name!("n"))],
                            },
                            ast::Expr::Term(ast::Term::Name(name!("n"))),
                        ),
                        (
                            ast::Pattern::UnaryConstructor(name!("Nothing")),
                            ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("0"))),
                        ),
                    ],
                },
            ))
        }
    )
}

#[test]
fn let_in() {
    assert_eq!(parse::expr(r#"let n = 123 in n;"#).unwrap().1, {
        let n = name!("n");
        ast::Expr::Let {
            definitions: BTreeMap::from([(
                n,
                vec![(
                    ast::Lhs::Func {
                        name: n,
                        args: vec![],
                    },
                    ast::Expr::Term(ast::Term::Numeral(ast::Numeral::Int("123"))),
                )],
            )]),
            in_expr: Box::new(ast::Expr::Term(ast::Term::Name(name!("n")))),
        }
    })
}

#[test]
fn empty_definition() {
    let (path, stats) = parse::parse("module Test; foo : Int;").unwrap();
    let module = ast::Module::from_statements(path, stats);
    assert_matches!(module, Err(ParseError::MissingAssignment(name!("foo"))));
}

#[test]
fn comments() {
    assert_eq!(parse::comment("-- Foobar").unwrap().0, "");
    assert_eq!(parse::comment("(* baz (*nested*)*)").unwrap().0, "");
}
