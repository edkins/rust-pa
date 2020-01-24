use num_traits::identities::Zero;
use crate::high_level::ast::*;
use crate::kernel::ast::*;

#[derive(Debug)]
pub struct TranslationError {
    pub pos: HPos,
    pub typ: ErrorType
}

#[derive(Debug)]
pub enum ErrorType {
    MissingRequiredItem,
    MultipleItems,
    BoolExprIsNotBool,
    BoolExprUnexpected,
    WrongArity,
    FuncWasNotSquashed,
    NumberWasNotSquashed,
    IntrosWereNotSquashed,
    InductionWasNotSquashed,
    NatExprIsNotNat,
    NatExprUnexpected,
    FunctionalVarsNotAllowed,
    QuantUnexpected,
    BadName,
    ContentsShouldBeMissing,
}

impl ErrorType {
    fn at<T>(self, pos: HPos) -> Result<T,TranslationError> {
        Err(TranslationError {
            pos,
            typ: self
        })
    }
    fn m<T>(self, pos: HPos) -> impl FnOnce(T) -> TranslationError {
        move|_| {
            TranslationError {
                pos,
                typ: self
            }
        }
    }
}

/// This does a very straightforward, mechanical translation from HScript to Script.
///
/// It doesn't do any filling in or guesswork. That's left to other passes.
/// Translation errors aren't supposed to happen - the earlier stages are supposed to catch them.
/// But there's no strict guarantee.
///
/// Note also that this doesn't reproduce the functionality of the kernel verifier. Invalid proofs
/// will pass straight through this stage.
pub fn translate(script: &HScript) -> Result<Script,TranslationError> {
    Ok(Script {
        items: script.items.iter().map(item).collect::<Result<_,_>>()?
    })
}

fn the_only<T>(pos: HPos, xs: &[T]) -> Result<&T, TranslationError> {
    if xs.is_empty() {
        ErrorType::MissingRequiredItem.at(pos)
    } else if xs.len() > 1 {
        ErrorType::MultipleItems.at(pos)
    } else {
        Ok(&xs[0])
    }
}

fn req<T>(pos: HPos, x: &Option<T>) -> Result<&T, TranslationError> {
    if let Some(x) = x {
        Ok(x)
    } else {
        ErrorType::MissingRequiredItem.at(pos)
    }
}

fn item(item: &HItem) -> Result<Item, TranslationError> {
    match item {
        HItem::Def(d) => {
            let name = pred_name(d.pos, the_only(d.pos, &d.names)?)?;
            let quants = req(d.pos, &d.quants)?.iter().map(|n|var_name(d.pos,n)).collect::<Result<_,_>>()?;
            let rules = vec![stmt(the_only(d.pos, &d.rules)?)?];
            Ok(Item::Def(ItemDef {
                pos: d.pos,
                name,
                quants,
                rules,
            }))
        }
        HItem::Lemma(lem) => {
            Ok(Item::Lemma(ItemLemma {
                pos: lem.pos,
                name: lemma_name(lem.pos, &lem.name)?,
                statement: stmt(&lem.statement)?,
                proof: steps(&lem.proof)?,
            }))
        }
    }
}

fn steps(steps: &[HStep]) -> Result<Vec<Step>,TranslationError> {
    steps.iter().map(step).collect()
}

fn justification(justification: &HJustification) -> Result<Justification,TranslationError> {
    panic!(); //TODO
}

fn step(step: &HStep) -> Result<Step,TranslationError> {
    let pos = step.pos;
    let id = *req(pos, &step.id)?;
    match step.step_type {
        HStepType::Claim => {
            if step.contents.is_some() {
                return ErrorType::ContentsShouldBeMissing.at(pos);
            }
            Ok(Step::Claim(StepClaim {
                pos,
                id,
                statement: stmt(req(pos, &step.statement)?)?,
                justification: justification(req(pos, &step.justification)?)?
            }))
        }
        HStepType::Induction => ErrorType::InductionWasNotSquashed.at(pos),
        HStepType::Given => {
            let contents = steps(req(pos, &step.contents)?)?;
            let intros = req(pos, &step.intros)?;
            if intros.len() == 2 {
                if let (HIntro::Var(x), HIntro::Stmt(expr,Some(hyp_id))) = (&intros[0], &intros[1]) {
                    return Ok(Step::EBox(StepEBox {
                        pos,
                        id,
                        name: var_name(pos, &x)?,
                        hyp_id: *hyp_id,
                        hyp: stmt(&expr)?,
                        contents,
                    }));
                }
            } else if intros.len() == 1 {
                match &intros[0] {
                    HIntro::Var(x) => {
                        return Ok(Step::ABox(StepABox {
                            pos,
                            id,
                            name: var_name(pos, &x)?,
                            contents,
                        }));
                    }
                    HIntro::Stmt(expr, Some(hyp_id)) => {
                        return Ok(Step::Imp(StepImp {
                            pos,
                            id,
                            hyp_id: *hyp_id,
                            hyp: stmt(&expr)?,
                            contents,
                        }));
                    }
                    _ => {}
                }
            }
            ErrorType::IntrosWereNotSquashed.at(pos)
        }
    }
}

fn nat(expr: &HExpr) -> Result<NatExpr,TranslationError> {
    let pos = expr.pos;
    let args = &expr.args;
    if !expr.typ.maps_to_nat() {
        return ErrorType::NatExprIsNotNat.at(pos);
    }
    match &expr.name {
        HName::UserFunc(_) => ErrorType::FuncWasNotSquashed.at(pos),
        HName::UserVar(name) => {
            if !args.is_empty() {
                return ErrorType::FunctionalVarsNotAllowed.at(pos);
            }
            Ok(NatExpr::Var(var_name(pos,name)?))
        }
        HName::Builtin(b) => {
            if b.arity() != args.len() {
                return ErrorType::WrongArity.at(pos);
            }

            Ok(match b {
                HBuiltin::Succ => NatExpr::Succ(bnat(&args[0])?),
                HBuiltin::Add => NatExpr::Add(bnat(&args[0])?, bnat(&args[1])?),
                HBuiltin::Mul => NatExpr::Mul(bnat(&args[0])?, bnat(&args[1])?),
                _ => return ErrorType::NatExprUnexpected.at(pos)
            })
        }
        HName::Num(n) => {
            if n.is_zero() {
                Ok(NatExpr::Zero)
            } else {
                ErrorType::NumberWasNotSquashed.at(pos)
            }
        }
    }
}

fn stmt(expr: &HExpr) -> Result<BoolExpr,TranslationError> {
    let pos = expr.pos;
    let args = &expr.args;
    if !expr.typ.maps_to_bool() {
        return ErrorType::BoolExprIsNotBool.at(pos);
    }
    match &expr.name {
        HName::UserFunc(name) => {
            let args = args.iter().map(nat).collect::<Result<_,_>>()?;
            Ok(BoolExpr::UserPred(pred_name(pos,name)?, args))
        }
        HName::Builtin(b) => {
            if b.arity() != args.len() {
                return ErrorType::WrongArity.at(pos);
            }

            Ok(match b {
                HBuiltin::Eq => BoolExpr::Eq(bnat(&args[0])?, bnat(&args[1])?),
                HBuiltin::And => BoolExpr::And(bstmt(&args[0])?, bstmt(&args[1])?),
                HBuiltin::Or => BoolExpr::Or(bstmt(&args[0])?, bstmt(&args[1])?),
                HBuiltin::Imp => BoolExpr::Imp(bstmt(&args[0])?, bstmt(&args[1])?),
                HBuiltin::Iff => BoolExpr::Iff(bstmt(&args[0])?, bstmt(&args[1])?),
                HBuiltin::All => BoolExpr::All(quant(&args[0])?, bstmt(&args[1])?),
                HBuiltin::Exists => BoolExpr::Exists(quant(&args[0])?, bstmt(&args[1])?),
                _ => return ErrorType::BoolExprUnexpected.at(pos)
            })
        }
        _ => ErrorType::BoolExprUnexpected.at(pos)
    }
}

fn bnat(expr: &HExpr) -> Result<Box<NatExpr>, TranslationError> {
    Ok(Box::new(nat(expr)?))
}

fn bstmt(expr: &HExpr) -> Result<Box<BoolExpr>, TranslationError> {
    Ok(Box::new(stmt(expr)?))
}

fn quant(expr: &HExpr) -> Result<VarName, TranslationError> {
    let pos = expr.pos;
    let args = &expr.args;
    match &expr.name {
        HName::UserVar(name) => {
            if !args.is_empty() {
                return ErrorType::FunctionalVarsNotAllowed.at(pos);
            }
            var_name(pos,name)
        }
        _ => ErrorType::QuantUnexpected.at(pos)
    }
}

fn pred_name(pos: HPos, name: &str) -> Result<PredName, TranslationError> {
    PredName::from_str(name).map_err(ErrorType::BadName.m(pos))
}

fn var_name(pos: HPos, name: &str) -> Result<VarName, TranslationError> {
    VarName::from_str(name).map_err(ErrorType::BadName.m(pos))
}

fn lemma_name(pos: HPos, name: &str) -> Result<LemmaName, TranslationError> {
    LemmaName::from_str(name).map_err(ErrorType::BadName.m(pos))
}
