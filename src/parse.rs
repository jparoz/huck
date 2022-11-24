use nom::branch::alt;
use nom::bytes::complete::{escaped, is_not, tag};
use nom::character::complete::{anychar, char, hex_digit1, one_of, satisfy};
use nom::combinator::{map, not, opt, peek, recognize, success, value, verify};
use nom::multi::{many0, many0_count, many1, separated_list0, separated_list1};
use nom::number::complete::recognize_float;
use nom::sequence::{delimited, preceded, separated_pair, terminated, tuple};
use nom::IResult;

use std::collections::HashMap;

use crate::ast::*;

pub fn parse(input: &str) -> Result<Chunk, Error> {
    match preceded(ws(success(())), chunk)(input) {
        Ok((leftover, c)) => {
            if !leftover.is_empty() {
                Err(Error::Leftover(leftover.to_string()))
            } else {
                Ok(c)
            }
        }
        Err(nom) => Err(Error::Nom(nom.to_string())),
    }
}

fn chunk(input: &str) -> IResult<&str, Chunk> {
    let (leftovers, assigns) = ws(many0(assign))(input)?;
    let mut env = HashMap::new();

    for (lhs, expr) in assigns {
        env.entry(lhs.name().clone())
            .or_insert(Vec::new())
            .push((lhs, expr));
    }

    Ok((leftovers, Chunk::new(env)))
}

fn assign(input: &str) -> IResult<&str, Assignment> {
    terminated(separated_pair(lhs, reserved_op("="), expr), semi)(input)
}

fn lhs(input: &str) -> IResult<&str, Lhs> {
    alt((
        map(tuple((pattern, operator, pattern)), |(a, op, b)| {
            Lhs::Binop { a, op, b }
        }),
        map(tuple((name, many0(pattern))), |(name, args)| Lhs::Func {
            name,
            args,
        }),
    ))(input)
}

fn pattern(input: &str) -> IResult<&str, Pattern> {
    alt((
        map(ws(var), Pattern::Bind),
        map(list(pattern), Pattern::List),
        map(numeral, Pattern::Numeral),
        map(string, Pattern::String),
        map(
            parens(tuple((constructor, many1(pattern)))),
            |(constructor, args)| Pattern::Destructure { constructor, args },
        ),
        map(constructor, Pattern::UnaryConstructor),
        parens(pattern_binop),
        parens(pattern),
    ))(input)
}

fn pattern_binop(input: &str) -> IResult<&str, Pattern> {
    map(
        tuple((pattern, operator, alt((pattern_binop, pattern)))),
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

fn binop(input: &str) -> IResult<&str, Expr> {
    map(tuple((app, operator, expr)), |(lhs, operator, rhs)| {
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
        tuple((
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
        tuple((reserved_op("\\"), many1(pattern), reserved_op("->"), expr)),
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
        map(parens(expr), |e| Term::Parens(Box::new(e))),
    ))(input)
}

fn var(input: &str) -> IResult<&str, &str> {
    verify(
        recognize(tuple((
            satisfy(is_var_start_char),
            many0(satisfy(is_name_char)),
        ))),
        |s| !is_reserved(s),
    )(input)
}

fn upper_ident(input: &str) -> IResult<&str, &str> {
    recognize(tuple((
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
        recognize(tuple((alt((tag("0x"), tag("0X"))), hex_digit1))),
        recognize(tuple((
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
    recognize(tuple((tag("-"), numeral_string)))(input)
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

fn comment(input: &str) -> IResult<&str, &str> {
    recognize(tuple((
        tag("(*"),
        many0_count(alt((
            value((), tuple((peek(tag("(*")), comment))),
            value((), tuple((peek(not(tag("*)"))), anychar))),
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

fn reserved<'a>(s: &'a str) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str> {
    debug_assert!(is_reserved(s));
    ws(terminated(tag(s), peek(not(satisfy(is_name_char)))))
}

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
        | "=>" | "," | "()" => true,
        _ => false,
    }
}

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Nom error: {0}")]
    Nom(String),
    #[error("Leftover input: {0}")]
    Leftover(String),
}
