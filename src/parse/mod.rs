use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::u8 as nom_u8;
use nom::character::complete::{anychar, char, hex_digit1, one_of, satisfy};
use nom::combinator::{map, not, opt, peek, recognize, success, value, verify};
use nom::multi::{many0, many0_count, many1, separated_list0, separated_list1};
use nom::number::complete::recognize_float;
use nom::sequence::tuple as nom_tuple;
use nom::sequence::{delimited, preceded, separated_pair, terminated};
use nom::IResult;

use std::collections::HashMap;

use crate::ast::*;

pub mod precedence;
use precedence::{default_precs, ApplyPrecedence, Associativity, Precedence};

#[cfg(test)]
mod test;

pub fn parse(input: &str) -> Result<Module, Error> {
    match preceded(ws(success(())), ws(many0(statement)))(input) {
        Ok((leftover, statements)) => {
            if !leftover.is_empty() {
                return Err(Error::Leftover(leftover.to_string()));
            }

            let mut definitions: HashMap<Name, Definition> = HashMap::new();
            let mut precs = default_precs();

            for stat in statements {
                match stat {
                    Statement::Assignment(Assignment::WithoutType(lhs, expr)) => {
                        definitions
                            .entry(lhs.name().clone())
                            .or_default()
                            .assignments
                            .push((lhs, expr));
                    }

                    Statement::Assignment(Assignment::WithType(ts, lhs, expr)) => {
                        let defn = definitions.entry(lhs.name().clone()).or_default();

                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = defn.explicit_type.replace(ts.clone()) {
                            return Err(Error::MultipleTypes(
                                lhs.name().clone(),
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }

                        defn.assignments.push((lhs, expr));
                    }

                    Statement::TypeAnnotation(name, ts) => {
                        // If there was already an explicit for this name, that's an error.
                        if let Some(previous_ts) = definitions
                            .entry(name.clone())
                            .or_default()
                            .explicit_type
                            .replace(ts.clone())
                        {
                            return Err(Error::MultipleTypes(
                                name,
                                format!("\n    {:?}\n    {:?}", ts, previous_ts),
                            ));
                        }
                    }

                    Statement::Precedence(name, prec) => {
                        precs.insert(name.clone(), prec);
                        // If there was already a precedence for this name, that's an error.
                        if let Some(previous_prec) = definitions
                            .entry(name.clone())
                            .or_default()
                            .precedence
                            .replace(prec)
                        {
                            return Err(Error::MultiplePrecs(name, prec, previous_prec));
                        }
                    }

                    Statement::TypeDeclaration => todo!(),
                }
            }

            // @Cleanup: this comment doesn't make too much sense
            // Now that we've collected all the related statements together,
            // we need to do some checking;
            // first we need to modify the AST to take precedence statements into account.
            for defn in definitions.values_mut() {
                defn.apply(&precs);
            }

            // @Todo: check other things here?

            Ok(Module { definitions })
        }
        Err(nom) => Err(Error::Nom(nom.to_string())),
    }
}

fn statement(input: &str) -> IResult<&str, Statement> {
    alt((
        map(assign, Statement::Assignment),
        map(
            terminated(separated_pair(name, reserved_op(":"), type_scheme), semi),
            |(name, scheme)| Statement::TypeAnnotation(name, scheme),
        ),
        map(prec, |(name, prec)| Statement::Precedence(name, prec)),
    ))(input)
}

fn assign(input: &str) -> IResult<&str, Assignment> {
    terminated(
        alt((
            map(
                nom_tuple((lhs, reserved_op(":"), type_scheme, reserved_op("="), expr)),
                |(lhs, _, ts, _, rhs)| Assignment::WithType(ts, lhs, rhs),
            ),
            map(separated_pair(lhs, reserved_op("="), expr), |(lhs, rhs)| {
                Assignment::WithoutType(lhs, rhs)
            }),
        )),
        semi,
    )(input)
}

fn prec(input: &str) -> IResult<&str, (Name, Precedence)> {
    map(
        terminated(nom_tuple((associativity, ws(nom_u8), operator)), semi),
        |(assoc, prec, op)| (op, Precedence(assoc, prec)),
    )(input)
}

fn associativity(input: &str) -> IResult<&str, Associativity> {
    alt((
        value(Associativity::Left, reserved("infixl")),
        value(Associativity::Right, reserved("infixr")),
        value(Associativity::None, reserved("infix")),
    ))(input)
}

fn lhs(input: &str) -> IResult<&str, Lhs> {
    alt((
        map(nom_tuple((pattern, operator, pattern)), |(a, op, b)| {
            Lhs::Binop { a, op, b }
        }),
        map(nom_tuple((name, many0(pattern))), |(name, args)| {
            Lhs::Func { name, args }
        }),
    ))(input)
}

fn pattern(input: &str) -> IResult<&str, Pattern> {
    alt((
        map(ws(var), Pattern::Bind),
        map(list(pattern), Pattern::List),
        map(tuple(pattern), Pattern::Tuple),
        map(numeral, Pattern::Numeral),
        map(string, Pattern::String),
        map(
            parens(nom_tuple((constructor, many1(pattern)))),
            |(constructor, args)| Pattern::Destructure { constructor, args },
        ),
        map(constructor, Pattern::UnaryConstructor),
        value(Pattern::Unit, unit),
        parens(pattern_binop),
        parens(pattern),
    ))(input)
}

fn pattern_binop(input: &str) -> IResult<&str, Pattern> {
    map(
        nom_tuple((pattern, operator, alt((pattern_binop, pattern)))),
        |(lhs, operator, rhs)| Pattern::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
    )(input)
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((binop, app, let_in, lambda))(input)
}

fn type_scheme(input: &str) -> IResult<&str, TypeScheme> {
    map(
        nom_tuple((
            opt(preceded(
                reserved("forall"),
                terminated(many1(ws(var)), ws(tag("."))),
            )),
            type_expr,
        )),
        |(vars, typ)| {
            // @Todo: check that all the vars are unique

            TypeScheme {
                vars: vars.into_iter().flatten().collect(),
                typ,
            }
        },
    )(input)
}

fn type_expr(input: &str) -> IResult<&str, TypeExpr> {
    alt((
        // @Todo: type-level binops
        // Can possibly just modify the below line to use type_operator instead of reserved_op("->")
        map(
            nom_tuple((type_app, reserved_op("->"), type_expr)),
            |(f, _, x)| TypeExpr::Arrow(Box::new(f), Box::new(x)),
        ),
        type_app,
    ))(input)
}

fn type_app(input: &str) -> IResult<&str, TypeExpr> {
    map(many1(type_term), |ts| {
        ts.into_iter()
            .map(|t| TypeExpr::Term(t))
            .reduce(|a, b| TypeExpr::App(Box::new(a), Box::new(b)))
            .unwrap() // safe unwrap because we're mapping over many1
    })(input)
}

fn type_term(input: &str) -> IResult<&str, TypeTerm> {
    alt((
        map(ws(upper_ident), TypeTerm::Concrete),
        map(ws(var), TypeTerm::Var),
        map(delimited(ws(tag("[")), type_expr, ws(tag("]"))), |t| {
            TypeTerm::List(Box::new(t))
        }),
        value(TypeTerm::Unit, unit),
        map(parens(type_expr), |t| TypeTerm::Parens(Box::new(t))),
        map(tuple(type_expr), TypeTerm::Tuple),
    ))(input)
}

fn binop(input: &str) -> IResult<&str, Expr> {
    map(nom_tuple((app, operator, expr)), |(lhs, operator, rhs)| {
        Expr::Binop {
            operator,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    })(input)
}

fn app(input: &str) -> IResult<&str, Expr> {
    map(many1(term), |ts| {
        ts.into_iter()
            .map(|t| Expr::Term(t))
            .reduce(|a, b| Expr::App {
                func: Box::new(a),
                argument: Box::new(b),
            })
            .unwrap() // safe unwrap because we're mapping over many1
    })(input)
}

fn let_in(input: &str) -> IResult<&str, Expr> {
    map(
        nom_tuple((
            reserved("let"),
            separated_list1(semi, separated_pair(lhs, reserved_op("="), expr)),
            opt(semi),
            reserved("in"),
            expr,
        )),
        |(_, assigns, _, _, in_expr)| {
            let mut local_env = HashMap::new();
            for (lhs, expr) in assigns {
                local_env
                    .entry(lhs.name().clone())
                    .or_insert(Vec::new())
                    .push((lhs, expr));
            }
            Expr::Let {
                definitions: local_env,
                in_expr: Box::new(in_expr),
            }
        },
    )(input)
}

fn lambda(input: &str) -> IResult<&str, Expr> {
    map(
        nom_tuple((reserved_op("\\"), many1(pattern), reserved_op("->"), expr)),
        |(_, args, _, rhs)| Expr::Lambda {
            lhs: Lhs::Lambda { args },
            rhs: Box::new(rhs),
        },
    )(input)
}

fn term(input: &str) -> IResult<&str, Term> {
    alt((
        map(numeral, Term::Numeral),
        map(string, Term::String),
        map(list(expr), Term::List),
        map(name, Term::Name),
        value(Term::Unit, unit),
        map(parens(expr), |e| Term::Parens(Box::new(e))),
        map(tuple(expr), Term::Tuple),
    ))(input)
}

fn var(input: &str) -> IResult<&str, &str> {
    verify(
        recognize(nom_tuple((
            satisfy(is_var_start_char),
            many0(satisfy(is_name_char)),
        ))),
        |s| !is_reserved(s),
    )(input)
}

fn upper_ident(input: &str) -> IResult<&str, &str> {
    recognize(nom_tuple((
        satisfy(char::is_uppercase),
        many0(satisfy(is_name_char)),
    )))(input)
}

fn name(input: &str) -> IResult<&str, Name> {
    ws(alt((
        map(var, |s| Name::Ident(s.to_string())),
        map(upper_ident, |s| Name::Ident(s.to_string())),
        parens(operator),
    )))(input)
}

fn constructor(input: &str) -> IResult<&str, Name> {
    ws(map(upper_ident, |s| Name::Ident(s.to_string())))(input)
}

fn numeral(input: &str) -> IResult<&str, Numeral> {
    map(alt((numeral_positive, parens(numeral_negative))), |s| {
        if s.contains(&['.', 'e', 'E'][..]) {
            Numeral::Float(s)
        } else {
            Numeral::Int(s)
        }
    })(input)
}

fn numeral_string(input: &str) -> IResult<&str, &str> {
    ws(alt((
        recognize(nom_tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
        recognize(nom_tuple((
            alt((tag("0b"), tag("0B"))),
            many1(alt((char('0'), char('1')))),
        ))),
        preceded(not(tag("+")), recognize_float),
    )))(input)
}

fn numeral_positive(input: &str) -> IResult<&str, &str> {
    preceded(not(tag("-")), numeral_string)(input)
}

fn numeral_negative(input: &str) -> IResult<&str, &str> {
    recognize(nom_tuple((tag("-"), numeral_string)))(input)
}

fn string(input: &str) -> IResult<&str, &str> {
    // "hello, world"
    // @Note: includes the quotes
    ws(recognize(delimited(
        char('"'),
        map(
            opt(escaped(is_not("\\\""), '\\', one_of("\\\"'abfnrtv"))),
            |res| res.unwrap_or(""),
        ),
        char('"'),
    )))(input)
}

fn list<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<O>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(
        ws(tag("[")),
        separated_list0(ws(tag(",")), inner),
        ws(tag("]")),
    )
}

fn tuple<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, Vec<O>>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(
        ws(tag("(")),
        separated_list1(ws(tag(",")), inner),
        ws(tag(")")),
    )
}

fn operator(input: &str) -> IResult<&str, Name> {
    map(
        verify(
            ws(recognize(alt((
                value((), many1(operator_char)),
                value((), delimited(char('`'), alt((var, upper_ident)), char('`'))),
            )))),
            |s| !is_reserved(s),
        ),
        |s| Name::Binop(s.to_string()),
    )(input)
}

fn operator_char(input: &str) -> IResult<&str, char> {
    one_of("=+-|!@#$%^&*:.,/~")(input)
}

fn semi(input: &str) -> IResult<&str, &str> {
    ws(tag(";"))(input)
}

fn unit(input: &str) -> IResult<&str, &str> {
    ws(tag("()"))(input)
}

fn comment(input: &str) -> IResult<&str, &str> {
    recognize(nom_tuple((
        tag("(*"),
        many0_count(alt((
            value((), nom_tuple((peek(tag("(*")), comment))),
            value((), nom_tuple((peek(not(tag("*)"))), anychar))),
        ))),
        tag("*)"),
    )))(input)
}

fn ws<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    let space = satisfy(char::is_whitespace);

    let whitespace = many0(alt((value((), comment), value((), space))));

    terminated(inner, whitespace)
}

// @Todo: change to 'static
fn reserved<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str> {
    debug_assert!(is_reserved(s));
    ws(terminated(tag(s), peek(not(satisfy(is_name_char)))))
}

// @Todo: change to 'static
fn reserved_op<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str> {
    debug_assert!(is_reserved(s));
    ws(terminated(tag(s), peek(not(operator_char))))
}

fn parens<'a, F: 'a, O>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O>
where
    F: FnMut(&'a str) -> IResult<&'a str, O>,
{
    delimited(ws(tag("(")), inner, ws(tag(")")))
}

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn is_var_start_char(c: char) -> bool {
    c.is_lowercase() || c == '_'
}

// @Note: In the definition of upper_ident, we assume there are no reserved words beginning with
// an uppercase letter.
// @Todo @Checkme: make sure that this behaves well with custom/overloaded ops
fn is_reserved(word: &str) -> bool {
    match word {
        "module" | "lazy" | "import" | "let" | "in" | "do" | "=" | ":" | "\\" | "->" | "<-"
        | "infix" | "infixl" | "infixr" | "forall" | "=>" | "," | "()" => true,
        _ => false,
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Nom error: {0}")]
    Nom(String),

    #[error("Leftover input: {0}")]
    Leftover(String),

    // @Todo: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple precedence declarations found for `{0}`:\n    {1:?}\n    {2:?}")]
    MultiplePrecs(Name, Precedence, Precedence),

    // @Todo: this shouldn't use Debug printing, but should print the source.
    #[error("Multiple explicit type annotations found for `{0}`:{1}")]
    MultipleTypes(Name, String),
}
