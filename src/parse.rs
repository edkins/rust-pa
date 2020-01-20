use nom::IResult;
use nom::branch::alt;
use nom::bytes::complete::{tag,take_while,take_while1};
use nom::character::complete::digit1;
use nom::combinator::{all_consuming,value,opt,map,cut};
use nom::error::ErrorKind;
use nom::multi::{many0,many1,separated_list};
use nom::sequence::{preceded,delimited,terminated};
use crate::{ErrorType,ProcessingError};
use crate::ast::*;

#[derive(Debug)]
pub struct ParseError {
    pos: Pos
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
/// One or more whitespace, or eof
fn ws1(input: &str) -> IResult<&str, (), ParseError> {
    alt((eof, value((),take_while(|c|c==' ' || c=='\t' || c=='\r' || c=='\n'))))(input)
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

fn word(input: &str) -> IResult<&str, &str, ParseError> {
    terminated(take_while1(|c|is_alphanumeric(c) || c == '_'),ws1)(input)
}

fn fail<T>(input: &str) -> IResult<&str, T, ParseError> {
    Err(nom::Err::Failure(ParseError{pos: input.len()}))
}

fn pred_name(input: &str) -> IResult<&str, PredName, ParseError> {
    let (input,w) = word(input)?;
    match PredName::from_str(w) {
        Ok(name) => Ok((input,name)),
        Err(_) => fail(input)
    }
}

fn lemma_name(input: &str) -> IResult<&str, LemmaName, ParseError> {
    let (input,w) = word(input)?;
    match LemmaName::from_str(w) {
        Ok(name) => Ok((input,name)),
        Err(_) => fail(input)
    }
}

fn var_name(input: &str) -> IResult<&str, VarName, ParseError> {
    let (input,w) = word(input)?;
    match VarName::from_str(w) {
        Ok(name) => Ok((input,name)),
        Err(_) => fail(input)
    }
}

fn var_name_list(input: &str) -> IResult<&str, Vec<VarName>, ParseError> {
    many1(var_name)(input)
}

fn stepid(input: &str) -> IResult<&str, StepId, ParseError> {
    let (input,digits) = digit1(input)?;
    let (input,_) = ws1(input)?;
    match digits.parse() {
        Ok(n) => Ok((input,n)),
        Err(_) => fail(input)
    }
}


/////////////
//
// Nat exprs
//
/////////////

fn fn_expr(input: &str) -> IResult<&str, NatExpr, ParseError> {
    let (input,name) = pred_name(input)?;
    let (input,args) = delimited(symbol("("), separated_list(symbol(","), nat_expr), symbol(")"))(input)?;
    Ok((input,NatExpr::UserFunc(name,args)))
}

fn succ_expr(input: &str) -> IResult<&str, NatExpr, ParseError> {
    let (input,_) = keyword("S")(input)?;
    let (input,arg) = delimited(symbol("("), nat_expr, symbol(")"))(input)?;
    Ok((input,NatExpr::Succ(Box::new(arg))))
}

fn var_expr(input: &str) -> IResult<&str, NatExpr, ParseError> {
    let (input,name) = var_name(input)?;
    Ok((input,NatExpr::Var(name)))
}

fn nat_expr_inner(input: &str) -> IResult<&str, NatExpr, ParseError> {
    alt((
        value(NatExpr::Zero, keyword("0")),
        succ_expr,
        fn_expr,
        var_expr,
        delimited(symbol("("), nat_expr, symbol(")")),
    ))(input)
}

#[derive(Clone,Copy,PartialEq,Eq,Debug)]
enum NatBinOp {
    Add,
    Mul,
}

fn nat_binop(input: &str) -> IResult<&str, NatBinOp, ParseError> {
    alt((
        value(NatBinOp::Add, symbol("+")),
        value(NatBinOp::Mul, symbol("*")),
    ))(input)
}

impl NatBinOp {
    fn combine(self,a:NatExpr,b:NatExpr) -> NatExpr {
        match self {
            NatBinOp::Add => NatExpr::Add(Box::new(a),Box::new(b)),
            NatBinOp::Mul => NatExpr::Mul(Box::new(a),Box::new(b)),
        }
    }
}

fn nat_expr(input: &str) -> IResult<&str, NatExpr, ParseError> {
    let (input,a) = nat_expr_inner(input)?;
    let (input,binop) = opt(nat_binop)(input)?;
    if let Some(binop) = binop {
        let (input,b) = nat_expr_inner(input)?;
        Ok((input,binop.combine(a,b)))
    } else {
        Ok((input,a))
    }
}

/////////////
//
// Bool exprs
//
/////////////

fn eq_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,a) = nat_expr(input)?;
    let (input,_) = symbol("=")(input)?;
    let (input,b) = nat_expr(input)?;
    Ok((input,BoolExpr::Eq(Box::new(a), Box::new(b))))
}

fn all_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,_) = keyword("forall")(input)?;
    let (input,name) = var_name(input)?;
    let (input,_) = symbol(",")(input)?;
    let (input,expr) = bool_expr_inner(input)?;
    Ok((input,BoolExpr::All(name,Box::new(expr))))
}

fn exists_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,_) = keyword("exists")(input)?;
    let (input,name) = var_name(input)?;
    let (input,_) = symbol(",")(input)?;
    let (input,expr) = bool_expr_inner(input)?;
    Ok((input,BoolExpr::Exists(name,Box::new(expr))))
}

fn pred_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,name) = pred_name(input)?;
    let (input,args) = delimited(symbol("("),separated_list(symbol(","), nat_expr), symbol(")"))(input)?;
    Ok((input,BoolExpr::UserPred(name,args)))
}

fn not_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,_) = symbol("~")(input)?;
    let (input,expr) = bool_expr_inner_not_eq(input)?; //leave out eq because ~a == b looks like (~a) == b
    Ok((input,BoolExpr::Not(Box::new(expr))))
}

fn bool_expr_inner_not_eq(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    alt((
        value(BoolExpr::False, keyword("false")),
        all_expr,
        exists_expr,
        not_expr,
        pred_expr,
        delimited(symbol("("), bool_expr, symbol(")")),
    ))(input)
}

fn bool_expr_inner(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    alt((
        eq_expr,
        bool_expr_inner_not_eq,
    ))(input)
}

#[derive(Clone,Copy,PartialEq,Eq,Debug)]
enum BoolBinOp {
    And,
    Or,
    Imp,
    Iff,
}

fn bool_binop(input: &str) -> IResult<&str, BoolBinOp, ParseError> {
    alt((
        value(BoolBinOp::And, symbol("&")),
        value(BoolBinOp::Or, symbol("|")),
        value(BoolBinOp::Imp, symbol("->")),
        value(BoolBinOp::Iff, symbol("<->")),
    ))(input)
}

impl BoolBinOp {
    fn combine(self,a:BoolExpr,b:BoolExpr) -> BoolExpr {
        match self {
            BoolBinOp::And => BoolExpr::And(Box::new(a),Box::new(b)),
            BoolBinOp::Or => BoolExpr::Or(Box::new(a),Box::new(b)),
            BoolBinOp::Imp => BoolExpr::Imp(Box::new(a),Box::new(b)),
            BoolBinOp::Iff => BoolExpr::Iff(Box::new(a),Box::new(b)),
        }
    }
}

fn bool_expr(input: &str) -> IResult<&str, BoolExpr, ParseError> {
    let (input,a) = bool_expr_inner(input)?;
    let (input,binop) = opt(bool_binop)(input)?;
    if let Some(binop) = binop {
        let (input,b) = bool_expr_inner(input)?;
        Ok((input,binop.combine(a,b)))
    } else {
        Ok((input,a))
    }
}

///////////////
//
// Justifications
//
///////////////

fn three_steps<F:Fn(StepId,StepId,StepId)->Justification>(f:F, name:&'static str) -> impl Fn(&str) -> IResult<&str, Justification, ParseError> {
    move |input| {
        let (input,_) = keyword(name)(input)?;
        let (input,step_a) = stepid(input)?;
        let (input,step_b) = stepid(input)?;
        let (input,step_c) = stepid(input)?;
        Ok((input,f(step_a,step_b,step_c)))
    }
}

fn two_steps<F:Fn(StepId,StepId)->Justification>(f:F, name:&'static str) -> impl Fn(&str) -> IResult<&str, Justification, ParseError> {
    move |input| {
        let (input,_) = keyword(name)(input)?;
        let (input,step_a) = stepid(input)?;
        let (input,step_b) = stepid(input)?;
        Ok((input,f(step_a,step_b)))
    }
}

fn one_step<F:Fn(StepId)->Justification>(f:F, name:&'static str) -> impl Fn(&str) -> IResult<&str, Justification, ParseError> {
    move |input| {
        let (input,_) = keyword(name)(input)?;
        let (input,step_a) = stepid(input)?;
        Ok((input,f(step_a)))
    }
}

fn justification(input: &str) -> IResult<&str, Justification, ParseError> {
    alt((  // break it up into sub alts because the nom trait isn't defined for this many
        alt((
            preceded(keyword("def"), map(pred_name, Justification::ByDefinition)),
            preceded(keyword("lemma"), map(lemma_name, Justification::Lemma)),
        )),
        alt((
            value(Justification::EqualIntro, keyword("eq_intro")),
            two_steps(Justification::EqualElim, "eq_elim"),
            two_steps(Justification::FalseIntro, "false_intro"),
            one_step(Justification::FalseElim, "false_elim"),
            one_step(Justification::NotIntro, "not_intro"),
            one_step(Justification::DoubleNotElim, "not_not_elim"),
            two_steps(Justification::AndIntro, "and_intro"),
            one_step(Justification::AndElimL, "and_elim_l"),
            one_step(Justification::AndElimR, "and_elim_r"),
            one_step(Justification::OrIntroL, "or_intro_l"),
            one_step(Justification::OrIntroR, "or_intro_r"),
            three_steps(Justification::OrElim, "or_elim"),
            one_step(Justification::ImpIntro, "imp_intro"),
            two_steps(Justification::ImpElim, "imp_elim"),
            two_steps(Justification::IffIntro, "iff_intro"),
            one_step(Justification::IffElimL, "iff_elim_l"),
            one_step(Justification::IffElimR, "iff_elim_r"),
        )),
        alt((
            one_step(Justification::AllIntro, "all_intro"),
            one_step(Justification::AllElim, "all_elim"),
            one_step(Justification::ExistsIntro, "exists_intro"),
            two_steps(Justification::ExistsElim, "exists_elim"),
            one_step(Justification::Rename, "rename"),
        )),
        alt((
            value(Justification::ZeroIsNotSucc, keyword("zero_is_not_succ")),
            value(Justification::SuccInj, keyword("succ_inj")),
            value(Justification::AddZero, keyword("add_zero")),
            value(Justification::AddSucc, keyword("add_succ")),
            value(Justification::MulZero, keyword("mul_zero")),
            value(Justification::MulSucc, keyword("mul_succ")),
            value(Justification::Induction, keyword("induction")),
        ))
    ))(input)
}


///////////////
//
// Items
//
///////////////

fn item_def(input: &str) -> IResult<&str, Item, ParseError> {
    let pos = input.len();
    let (input,_) = keyword("def")(input)?;
    let (input,names) = cut(separated_list(symbol(","), pred_name))(input)?;
    let (input,quants) = cut(opt(preceded(keyword("for"), var_name_list)))(input)?;
    let quants = quants.unwrap_or_else(Vec::new);
    let (input,rules) = cut(delimited(symbol("{"), separated_list(symbol(";"), bool_expr), symbol("}")))(input)?;
    Ok((input,Item::Def(ItemDef{
        pos,
        names,
        quants,
        rules,
    })))
}

fn claim(id: StepId) -> impl Fn(&str) -> IResult<&str, (StepId,Step), ParseError> {
    move |input| {
        let pos = input.len();
        let (input,statement) = bool_expr(input)?;
        let (input,_) = keyword("by")(input)?;
        let (input,justification) = justification(input)?;
        let nextid = id + 1;
        Ok((input,(nextid,Step::Claim(StepClaim{
            id,
            pos,
            statement,
            justification
        }))))
    }
}

fn ebox(id: StepId) -> impl Fn(&str) -> IResult<&str, (StepId,Step), ParseError> {
    move |input| {
        let pos = input.len();
        let (input,_) = keyword("given")(input)?;
        let (input,name) = var_name(input)?;
        let (input,_) = symbol(",")(input)?;
        let (input,hyp) = bool_expr(input)?;
        let (input,(nextid,contents)) = list_of_steps(id, input)?;
        Ok((input,(nextid,Step::EBox(StepEBox{
            id,
            pos,
            name,
            hyp,
            contents
        }))))
    }
}

fn abox(id: StepId) -> impl Fn(&str) -> IResult<&str, (StepId,Step), ParseError> {
    move |input| {
        let pos = input.len();
        let (input,_) = keyword("given")(input)?;
        let (input,name) = var_name(input)?;
        let (input,(nextid,contents)) = list_of_steps(id, input)?;
        Ok((input,(nextid,Step::ABox(StepABox{
            id,
            pos,
            name,
            contents
        }))))
    }
}

fn imp(id: StepId) -> impl Fn(&str) -> IResult<&str, (StepId,Step), ParseError> {
    move |input| {
        let pos = input.len();
        let (input,_) = keyword("given")(input)?;
        let (input,hyp) = bool_expr(input)?;
        let (input,(nextid,contents)) = list_of_steps(id, input)?;
        Ok((input,(nextid,Step::Imp(StepImp{
            id,
            pos,
            hyp,
            contents
        }))))
    }
}

fn step(id: StepId) -> impl Fn(&str) -> IResult<&str, (StepId,Step), ParseError> {
    move|input| {
        alt((
            ebox(id),
            abox(id),
            imp(id),
            claim(id),
        ))(input)
    }
}

fn list_of_steps(mut id: StepId, input: &str) -> IResult<&str, (StepId,Vec<Step>), ParseError> {
    let mut result = vec![];
    let (mut input,_) = symbol("{")(input)?;
    loop {
        match terminated(step(id), symbol(";"))(input) {
            Ok((input2,(id2,step))) => {
                input = input2;
                id = id2;
                result.push(step);
            }
            Err(nom::Err::Error(_)) => break,
            Err(e) => return Err(e)
        }
    }
    let (input,_) = symbol("}")(input)?;
    Ok((input,(id,result)))
}

fn item_lemma(input: &str) -> IResult<&str, Item, ParseError> {
    let pos = input.len();
    let (input,_) = keyword("lemma")(input)?;
    let (input,name) = lemma_name(input)?;
    let (input,_) = symbol(":")(input)?;
    let (input,statement) = bool_expr(input)?;
    let (input,(_,proof)) = list_of_steps(0,input)?;
    Ok((input,Item::Lemma(ItemLemma{
        pos,
        name,
        statement,
        proof
    })))
}

fn item(input: &str) -> IResult<&str, Item, ParseError> {
    alt((item_def, item_lemma))(input)
}

fn parse_script(input: &str) -> IResult<&str, Script, ParseError> {
    let (input,_) = ws0(input)?;
    let (input,items) = many0(item)(input)?;
    Ok((input,Script{items}))
}

pub fn parse(input: &str) -> Result<Script, ProcessingError> {
    match all_consuming(parse_script)(input) {
        Ok((_,script)) => Ok(script),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(ErrorType::Parse.at(e.pos, input)),
        Err(nom::Err::Incomplete(_)) => Err(ErrorType::Unexpected.nowhere())
    }
}
