use nom::IResult;
use nom::branch::alt;
use nom::bytes::complete::{tag,take_while,take_while1};
use nom::character::complete::{anychar,digit1};
use nom::combinator::{all_consuming,value,opt,map,cut,peek,verify};
use nom::error::ErrorKind;
use nom::multi::{many0,separated_list};
use nom::sequence::{preceded,delimited,terminated};
use num_bigint::BigUint;
use crate::high_level::ast::*;

#[derive(Debug)]
pub struct ParseError {
    pub pos: HPos
}

impl<'a> nom::error::ParseError<&'a str> for ParseError {
    fn from_error_kind(input: &'a str, _kind: ErrorKind) -> Self {
        ParseError { pos: input.len() }
    }
    fn append(_input: &'a str, _kind: ErrorKind, other: Self) -> Self {
        other
    }
}

fn eof(input: &str) -> IResult<&str, (), ParseError> {
    if input.is_empty() {
        Ok((input,()))
    } else {
        Err(nom::Err::Error(ParseError {pos: input.len() }))
    }
}

/// Zero or more whitespace
fn ws0(input: &str) -> IResult<&str, (), ParseError> {
    value((),take_while(|c|c==' ' || c=='\t' || c=='\r' || c=='\n'))(input)
}
/// Consume whitespace after a word
fn ws1(input: &str) -> IResult<&str, (), ParseError> {
    preceded(word_gap, ws0)(input)
}

fn symbol(sym:&'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move|input| {
        preceded(tag(sym), ws0)(input)
    }
}

fn keyword(kw:&'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move|input| {
        preceded(tag(kw), ws1)(input)
    }
}

fn number(input: &str) -> IResult<&str, BigUint, ParseError> {
    map(terminated(digit1, ws1), |n|BigUint::parse_bytes(n.as_bytes(),10).unwrap())(input)
}

fn is_lower_alphabetic(ch: char) -> bool {
    ch >= 'a' && ch <= 'z'
}
fn is_upper_alphabetic(ch: char) -> bool {
    ch >= 'A' && ch <= 'Z'
}
fn is_alphabetic(ch: char) -> bool {
    is_lower_alphabetic(ch) || is_upper_alphabetic(ch)
}
fn is_digit(ch: char) -> bool {
    ch >= '0' && ch <= '9'
}
fn is_word_char(ch: char) -> bool {
    is_alphabetic(ch) || is_digit(ch) || ch == '_'
}

fn uppercase_char(input: &str) -> IResult<&str, char, ParseError> {
    verify(anychar, |c|is_upper_alphabetic(*c))(input)
}

fn lowercase_char(input: &str) -> IResult<&str, char, ParseError> {
    verify(anychar, |c|is_lower_alphabetic(*c))(input)
}

fn alphabetic_char(input: &str) -> IResult<&str, char, ParseError> {
    verify(anychar, |c|is_alphabetic(*c))(input)
}
fn not_word_char(input: &str) -> IResult<&str, char, ParseError> {
    verify(anychar, |c|!is_word_char(*c))(input)
}
fn word_gap(input: &str) -> IResult<&str, (), ParseError> {
    alt((eof, value((), peek(not_word_char))))(input)
}

/// Don't use this one directly. Use func_name, lemma_name, var_name or const_name
fn word(input: &str) -> IResult<&str, &str, ParseError> {
    terminated(take_while1(is_word_char),ws1)(input)
}

fn func_name(input: &str) -> IResult<&str, &str, ParseError> {
    preceded(peek(alphabetic_char), word)(input)
}

fn lemma_name(input: &str) -> IResult<&str, &str, ParseError> {
    preceded(peek(alphabetic_char), word)(input)
}

/// Lower/uppercase distinguishes vars from consts
fn var_name(input: &str) -> IResult<&str, &str, ParseError> {
    preceded(peek(lowercase_char), word)(input)
}

/// Upper/lowercase distiguishes consts from vars
fn const_name(input: &str) -> IResult<&str, &str, ParseError> {
    preceded(peek(uppercase_char), word)(input)
}

/////////////
//
// Nat exprs
//
/////////////

fn func_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let pos = input.len();
    let (input,name) = func_name(input)?;
    let (input,_) = symbol("(")(input)?;
    let (input,args) = separated_list(symbol(","), expr)(input)?;
    let (input,_) = symbol(")")(input)?;
    Ok((input,HExpr::func(pos, name, args)))
}

fn tight_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let pos = input.len();
    alt((
        not_expr,
        map(number, move|n|HExpr::num(pos, n)),
        func_expr,
        map(const_name, move|c|HExpr::constant(pos, c)),
        map(var_name, move|x|HExpr::var(pos, x)),
        delimited(symbol("("), expr, symbol(")")),
    ))(input)
}

fn not_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let pos = input.len();
    let (input,_) = symbol("~")(input)?;
    let (input,expr) = tight_expr(input)?;
    Ok((input,HExpr::builtin1(pos, HBuiltin::Not, expr)))
}


fn nat_binop(input: &str) -> IResult<&str, HBuiltin, ParseError> {
    alt((
        value(HBuiltin::Add, symbol("+")),
        value(HBuiltin::Mul, symbol("*")),
    ))(input)
}

fn nat_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let (input,a) = tight_expr(input)?;
    let pos = input.len();
    let (input,binop) = opt(nat_binop)(input)?;
    if let Some(binop) = binop {
        let (input,b) = tight_expr(input)?;
        Ok((input,HExpr::builtin2(pos, binop, a, b)))
    } else {
        Ok((input,a))
    }
}

/////////////
//
// Rel exprs
//
/////////////

fn rel_binop(input: &str) -> IResult<&str, HBuiltin, ParseError> {
    value(HBuiltin::Eq, symbol("="))(input)
}

fn rel_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let (input,a) = nat_expr(input)?;
    let pos = input.len();
    let (input,binop) = opt(rel_binop)(input)?;
    if let Some(binop) = binop {
        let (input,b) = nat_expr(input)?;
        Ok((input,HExpr::builtin2(pos, binop, a, b)))
    } else {
        Ok((input,a))
    }
}

/////////////
//
// Quantified exprs
//
/////////////

fn quant(input: &str) -> IResult<&str, HBuiltin, ParseError> {
    alt((
        value(HBuiltin::All, keyword("forall")),
        value(HBuiltin::Exists, keyword("exists")),
    ))(input)
}

fn quant_expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let pos = input.len();
    let (input,q) = quant(input)?;
    let (input,name) = var_name(input)?;
    let (input,_) = symbol(",")(input)?;
    let (input,expr) = expr(input)?;
    Ok((input,HExpr::quant(pos, q, name, expr)))
}

fn bool_expr_inner(input: &str) -> IResult<&str, HExpr, ParseError> {
    alt((
        quant_expr,
        rel_expr,
    ))(input)
}

fn bool_binop(input: &str) -> IResult<&str, HBuiltin, ParseError> {
    alt((
        value(HBuiltin::And, symbol("&")),
        value(HBuiltin::Or, symbol("|")),
        value(HBuiltin::Imp, symbol("->")),
        value(HBuiltin::Iff, symbol("<->")),
    ))(input)
}

fn expr(input: &str) -> IResult<&str, HExpr, ParseError> {
    let (input,a) = bool_expr_inner(input)?;
    let pos = input.len();
    let (input,binop) = opt(bool_binop)(input)?;
    if let Some(binop) = binop {
        let (input,b) = bool_expr_inner(input)?;
        Ok((input,HExpr::builtin2(pos, binop, a, b)))
    } else {
        Ok((input,a))
    }
}

///////////////
//
// Items
//
///////////////

fn list_of_func_names(input: &str) -> IResult<&str, Vec<HFuncName>, ParseError> {
    separated_list(symbol(","), map(func_name, |n|n.to_string()))(input)
}

fn item_def(input: &str) -> IResult<&str, HItem, ParseError> {
    let pos = input.len();
    let (input,_) = keyword("def")(input)?;
    let (input,names) = cut(list_of_func_names)(input)?;
    let (input,rules) = cut(delimited(symbol("{"), separated_list(symbol(";"), expr), symbol("}")))(input)?;
    Ok((input,HItem::Def(HItemDef{
        pos,
        names,
        quants: None,
        rules,
    })))
}

fn claim(input: &str) -> IResult<&str, HStep, ParseError> {
    let pos = input.len();
    let (input,statement) = expr(input)?;
    let (input,_) = cut(symbol(";"))(input)?;
    Ok((input,HStep {
        pos,
        id: None,
        statement: Some(statement),
        intros: None,
        contents: None,
        step_type: HStepType::Claim,
        justification: None,
    }))
}

fn box_type(input: &str) -> IResult<&str, HStepType, ParseError> {
    alt((
        value(HStepType::Given, keyword("given")),
        value(HStepType::Induction, keyword("induction")),
    ))(input)
}

fn intro(input: &str) -> IResult<&str, HIntro, ParseError> {
    alt((
        map(var_name, |n|HIntro::Var(n.to_string())),
        map(expr, |e|HIntro::Stmt(e,None)),
    ))(input)
}

fn box_step(input: &str) -> IResult<&str, HStep, ParseError> {
    let pos = input.len();
    let (input,step_type) = box_type(input)?;
    let (input,intros) = separated_list(symbol(","), intro)(input)?;
    let (input,contents) = list_of_steps(input)?;
    Ok((input,HStep{
        pos,
        id: None,
        statement: None,
        intros: Some(intros),
        contents: Some(contents),
        step_type,
        justification: None,
    }))
}

fn step(input: &str) -> IResult<&str, HStep, ParseError> {
    alt((
        box_step,
        claim,
    ))(input)
}

fn list_of_steps(input: &str) -> IResult<&str, Vec<HStep>, ParseError> {
    delimited(symbol("{"), many0(step), symbol("}"))(input)
}

fn item_lemma(input: &str) -> IResult<&str, HItem, ParseError> {
    let pos = input.len();
    let (input,_) = keyword("lemma")(input)?;
    let (input,name) = lemma_name(input)?;
    let (input,_) = symbol(":")(input)?;
    let (input,statement) = expr(input)?;
    let (input,proof) = list_of_steps(input)?;
    Ok((input,HItem::Lemma(HItemLemma{
        pos,
        name: name.to_string(),
        statement,
        proof
    })))
}

fn item(input: &str) -> IResult<&str, HItem, ParseError> {
    alt((item_def, item_lemma))(input)
}

fn parse_script(input: &str) -> IResult<&str, HScript, ParseError> {
    let (input,_) = ws0(input)?;
    let (input,items) = many0(item)(input)?;
    Ok((input,HScript{items}))
}

pub fn high_level_parse(input: &str) -> Result<HScript, ParseError> {
    match all_consuming(parse_script)(input) {
        Ok((_,script)) => Ok(script),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e),
        Err(nom::Err::Incomplete(_)) => Err(ParseError{pos:0})
    }
}
