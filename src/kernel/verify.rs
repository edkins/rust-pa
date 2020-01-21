use std::collections::HashMap;
use crate::kernel::ast::{Script,Pos,VarName,PredName,BoolExpr,NatExpr,ItemDef,Item,ItemLemma,LemmaName,StepId,Justification,Step};

#[derive(Debug)]
pub struct VerificationError {
    pub pos: Pos,
    pub code: Code
}

#[derive(Debug,Clone,Copy)]
pub enum Code {
    // Errors in definitions
    AlreadyDefined,
    DefMustBeIff,
    DefLhsVarMismatch,
    NoDefinitionRules,
    MultipleDefinitionRules,

    // Errors in boolean expressions
    QuantifiersHaveSameName,
    UsingUndefinedPredicate,
    WrongNumberOfArguments,
    NameBoundTwice,

    // Errors in nat expressions
    NameNotBound,
    UnexpectedHighLevelNatExpr,

    // Errors in proofs
    BoxIsEmpty,
    BoxDoesNotEndWithClaim,
    ProofEndsWithWrongClaim,
    BadStepId,
    ABoxAlreadyBound,
    EBoxAlreadyBound,

    // Errors in justification steps
    ByDefinitionDoesNotExist,   // ByDefinition
    ByDefinitionWrong,
    LemmaDoesNotExist,          // Lemma
    LemmaDoesNotSayThat,
    EqIntroSidesMismatch,       // EqIntro
    EqIntroNotEq,
    EqElimMismatchNat,          // EqElim
    EqElimMismatchBool,
    EqElimNotEq,
    FalseIntroNotContradiction, // FalseIntro
    FalseIntroNotFalse,
    FalseElimNotFalse,          // FalseElim
    NotIntroIsntFalse,          // NotIntro
    NotIntroIsntNot,
    NotIntroWrongNot,
    DoubleNotElimWrong,         // DoubleNotElim
    DoubleNotElimIsnt,
    AndIntroIsnt,               // AndIntro
    AndIntroBadLhs,
    AndIntroBadRhs,
    AndElimLMismatch,           // AndElimL
    AndElimLNotAnd,
    AndElimRMismatch,           // AndElimR
    AndElimRNotAnd,
    OrIntroLMismatch,           // OrIntroL
    OrIntroLNotOr,
    OrIntroRMismatch,           // OrIntroR
    OrIntroRNotOr,
    OrElimNotOr,                // OrElim
    OrElimBadHypL,
    OrElimBadHypR,
    OrElimBadConcL,
    OrElimBadConcR,
    ImpIntroBadHyp,             // ImpIntro
    ImpIntroBadConc,
    ImpIntroNotImp,
    ImpElimBadHyp,              // ImpElim
    ImpElimBadConc,
    ImpElimNotImp,
    IffIntroNotIff,             // IffIntro
    IffIntroNotImpL,
    IffIntroNotImpR,
    IffIntroBadHypL,
    IffIntroBadHypR,
    IffIntroBadConcL,
    IffIntroBadConcR,
    IffElimLNotIff,             // IffElimL
    IffElimLNotImp,
    IffElimLBadHyp,
    IffElimLBadConc,
    IffElimRNotIff,             // IffElimR
    IffElimRNotImp,
    IffElimRBadHyp,
    IffElimRBadConc,
    AllIntroNotForAll,          // AllIntro
    AllIntroWrongName,
    AllIntroWrongConc,
    AllElimNotForAll,           // AllElim
    AllElimBadSubstitution,
    ExistsIntroBadSubstitution, // ExistsIntro
    ExistsIntroNotExists,
    ExistsElimNotExists,        // ExistsElim
    ExistsElimWrongName,
    ExistsElimBadHyp,
    ExistsElimBadConc,
    RenameMismatch,             // Rename
    RenameBoundTwice,
    ZeroIsNotSuccWrong,         // Axioms
    SuccInjWrong,
    AddZeroWrong,
    AddSuccWrong,
    MulZeroWrong,
    InductionMalformed,         // Induction
    InductionWrongVar,
    InductionWrongIndHyp,
    InductionWrongBase,
    InductionWrongIndConc,
}

impl Code {
    fn at<T>(self, pos: Pos) -> Result<T,VerificationError> {
        Err(VerificationError{pos, code:self})
    }
    fn mapat<T>(self, pos: Pos) -> impl Fn(T) -> VerificationError {
        move |_| {
            VerificationError{pos, code:self}
        }
    }
}

struct ProofChecker {
    verified_claims: HashMap<LemmaName,BoolExpr>,
    defined_symbols: HashMap<PredName,usize>,  // store arity of known predicates
    definition_claims: HashMap<PredName,BoolExpr>,
}

impl Default for ProofChecker {
    fn default() -> Self {
        ProofChecker {
            verified_claims: HashMap::new(),
            defined_symbols: HashMap::new(),
            definition_claims: HashMap::new(),
        }
    }
}

fn any_equal<T:Eq+Clone>(xs: &[T]) -> Option<T> {
    for i in 0..xs.len() {
        if xs[i+1..].contains(&xs[i]) {
            return Some(xs[i].clone());
        }
    }
    None
}

impl ProofChecker {
    fn add_def(&mut self, def: &ItemDef) -> Result<(),VerificationError> {
        let name = &def.name;
        if any_equal(&def.quants).is_some() {
            return Code::QuantifiersHaveSameName.at(def.pos);
        }

        if self.defined_symbols.contains_key(name) {
            return Code::AlreadyDefined.at(def.pos);
        }

        if def.rules.is_empty() {
            return Code::NoDefinitionRules.at(def.pos);
        }
        if def.rules.len() > 1 {
            return Code::MultipleDefinitionRules.at(def.pos);
        }

        match &def.rules[0] {
            BoolExpr::Iff(lhs,rhs) => {
                let vars_as_exprs:Vec<NatExpr> = def.quants.iter().map(|v|NatExpr::Var(v.clone())).collect();
                let arity = vars_as_exprs.len();
                let expected_lhs = BoolExpr::UserPred(name.clone(), vars_as_exprs);
                if **lhs != expected_lhs {
                    return Code::DefLhsVarMismatch.at(def.pos);
                }
                self.check_boolexpr(def.pos, &*rhs, &def.quants)?;
                self.defined_symbols.insert(name.clone(), arity);

                let mut claim = def.rules[0].clone();
                for i in 0..def.quants.len() {
                    let var = &def.quants[def.quants.len() - 1 - i];
                    claim = BoolExpr::All(var.clone(), Box::new(claim));
                }
                self.definition_claims.insert(name.clone(), claim);
                Ok(())
            }
            _ => Code::DefMustBeIff.at(def.pos)
        }
    }
    fn check_boolexpr(&self, pos: Pos, expr: &BoolExpr, bound: &[VarName]) -> Result<(),VerificationError> {
        match expr {
            BoolExpr::UserPred(p, xs) => {
                match self.defined_symbols.get(&p) {
                    None => {
                        return Code::UsingUndefinedPredicate.at(pos);
                    }
                    Some(arity) => {
                        if xs.len() != *arity {
                            return Code::WrongNumberOfArguments.at(pos);
                        }
                    }
                }
                for sub_expr in xs {
                    self.check_natexpr(pos, sub_expr, bound)?;
                }
            }
            BoolExpr::Eq(a, b) => {
                self.check_natexpr(pos, &**a, bound)?;
                self.check_natexpr(pos, &**b, bound)?;
            }
            BoolExpr::False => {}
            BoolExpr::Not(p) => {
                self.check_boolexpr(pos, &**p, bound)?;
            }
            BoolExpr::And(p,q) | BoolExpr::Or(p,q) | BoolExpr::Imp(p,q) | BoolExpr::Iff(p,q) => {
                self.check_boolexpr(pos, &**p, bound)?;
                self.check_boolexpr(pos, &**q, bound)?;
            }
            BoolExpr::All(x, p) | BoolExpr::Exists(x, p) => {
                if bound.contains(x) {
                    return Code::NameBoundTwice.at(pos);
                }
                let mut b2 = bound.to_vec();
                b2.push(x.clone());
                self.check_boolexpr(pos, &**p, &b2)?;
            }
        }
        Ok(())
    }

    fn check_natexpr(&self, pos: Pos, expr: &NatExpr, bound: &[VarName]) -> Result<(),VerificationError> {
        match expr {
            NatExpr::Var(x) => {
                if !bound.contains(x) {
                    return Code::NameNotBound.at(pos);
                }
            }
            NatExpr::Zero => {}
            NatExpr::Succ(a) => {
                self.check_natexpr(pos, a, bound)?;
            }
            NatExpr::Add(a,b) | NatExpr::Mul(a,b) => {
                self.check_natexpr(pos, a, bound)?;
                self.check_natexpr(pos, b, bound)?;
            }
        }
        Ok(())
    }

    fn add_lemma(&mut self, lemma: &ItemLemma) -> Result<(),VerificationError> {
        self.check_boolexpr(lemma.pos, &lemma.statement, &[])?;

        let c = self.process_contents(lemma.pos, &lemma.proof, vec![], &[])?;

        if c != lemma.statement {
            return Code::ProofEndsWithWrongClaim.at(lemma.end_pos());
        }
        
        self.verified_claims.insert(lemma.name.clone(), lemma.statement.clone());
        Ok(())
    }

    fn process_contents(&self, pos: Pos, contents: &[Step], mut processed: Vec<ProcessedStep>, bound: &[VarName]) -> Result<BoolExpr,VerificationError> {
        for step in contents {
            let pr = self.process_step(step, &processed, bound)?;
            processed.push(pr);
        }

        if processed.is_empty() {
            return Code::BoxIsEmpty.at(pos);
        }

        let last_step = &processed[processed.len() - 1];
        if let ProcessedStep::Claim(_,c) = last_step {
            Ok(c.clone())
        } else {
            Code::BoxDoesNotEndWithClaim.at(contents[contents.len()-1].pos())
        }
    }

    fn process_step(&self, step: &Step, previous_steps: &[ProcessedStep], bound: &[VarName]) -> Result<ProcessedStep,VerificationError> {
        match step {
            Step::Claim(c) => {
                self.check_boolexpr(c.pos, &c.statement, bound)?;
                self.check_justification(c.pos, &c.statement, &c.justification, previous_steps)?;
                Ok(ProcessedStep::Claim(c.id,c.statement.clone()))
            }
            Step::Imp(b) => {
                self.check_boolexpr(b.pos, &b.hyp, bound)?;
                let mut psteps = previous_steps.to_vec();
                psteps.push(ProcessedStep::Claim(b.hyp_id, b.hyp.clone()));
                let c = self.process_contents(b.pos, &b.contents, psteps, bound)?;
                Ok(ProcessedStep::Imp(b.id, b.hyp.clone(), c))
            }
            Step::ABox(b) => {
                if bound.contains(&b.name) {
                    return Code::ABoxAlreadyBound.at(b.pos);
                }
                let mut b2 = bound.to_vec();
                b2.push(b.name.clone());
                let c = self.process_contents(b.pos, &b.contents, previous_steps.to_vec(), &b2)?;
                Ok(ProcessedStep::ABox(b.id, b.name.clone(), c))
            }
            Step::EBox(b) => {
                if bound.contains(&b.name) {
                    return Code::EBoxAlreadyBound.at(b.pos);
                }
                let mut b2 = bound.to_vec();
                b2.push(b.name.clone());
                self.check_boolexpr(b.pos, &b.hyp, &b2)?;
                let mut psteps = previous_steps.to_vec();
                psteps.push(ProcessedStep::Claim(b.hyp_id, b.hyp.clone()));
                let c = self.process_contents(b.pos, &b.contents, previous_steps.to_vec(), &b2)?;
                self.check_boolexpr(b.end_pos(), &c, bound)?;   // check conclusion doesn't contain bound variable, as this won't work with ExistsElim
                Ok(ProcessedStep::EBox(b.id, b.name.clone(), b.hyp.clone(), c))
            }
        }
    }

    fn check_justification(&self, pos: Pos, statement: &BoolExpr, justification: &Justification, previous_steps: &[ProcessedStep]) -> Result<(),VerificationError> {
        match justification {
            Justification::ByDefinition(pred) => {
                if let Some(actual_statement) = self.definition_claims.get(pred) {
                    if statement != actual_statement {
                        return Code::ByDefinitionWrong.at(pos);
                    }
                } else {
                    return Code::ByDefinitionDoesNotExist.at(pos);
                }
            }
            Justification::Lemma(lemma) => {
                if let Some(actual_statement) = self.verified_claims.get(lemma) {
                    if statement != actual_statement {
                        return Code::LemmaDoesNotSayThat.at(pos);
                    }
                } else {
                    return Code::LemmaDoesNotExist.at(pos);
                }
            }
            Justification::EqualIntro => {
                if let BoolExpr::Eq(lhs,rhs) = statement {
                    if lhs != rhs {
                        return Code::EqIntroSidesMismatch.at(pos);
                    }
                } else {
                    return Code::EqIntroNotEq.at(pos);
                }
            }
            Justification::EqualElim(equality,to_rewrite) => {
                if let BoolExpr::Eq(lhs,rhs) = lookup_claim(pos,previous_steps,*equality)? {
                    let statement_lhs = lookup_claim(pos,previous_steps,*to_rewrite)?;
                    self.check_equal_elim(pos, lhs, rhs, statement_lhs, statement)?;
                } else {
                    return Code::EqElimNotEq.at(pos);
                }
            }
            Justification::FalseIntro(id_p, id_notp) => {
                let p = lookup_claim(pos,previous_steps,*id_p)?;
                if let BoolExpr::Not(p2) = lookup_claim(pos,previous_steps,*id_notp)? {
                    if *p != **p2 {
                        return Code::FalseIntroNotContradiction.at(pos);
                    }
                    if *statement != BoolExpr::False {
                        return Code::FalseIntroNotFalse.at(pos);
                    }
                } else {
                    return Code::FalseIntroNotContradiction.at(pos);
                }
            }
            Justification::FalseElim(id_false) => {
                if let BoolExpr::False = lookup_claim(pos,previous_steps,*id_false)? {
                    // don't need to check statement because it can be anything
                } else {
                    return Code::FalseElimNotFalse.at(pos);
                }
            }
            Justification::NotIntro(id_box) => {
                if let (hyp,BoolExpr::False) = lookup_imp(pos,previous_steps,*id_box)? {
                    if let BoolExpr::Not(s2) = statement {
                        if **s2 != *hyp {
                            return Code::NotIntroWrongNot.at(pos);
                        }
                    } else {
                        return Code::NotIntroIsntNot.at(pos);
                    }
                } else {
                    return Code::NotIntroIsntFalse.at(pos);
                }
            }
            Justification::DoubleNotElim(id_notnot) => {
                if let BoolExpr::Not(notp) = lookup_claim(pos,previous_steps,*id_notnot)? {
                    if let BoolExpr::Not(p) = &**notp {
                        if **p != *statement {
                            return Code::DoubleNotElimWrong.at(pos);
                        }
                    } else {
                        return Code::DoubleNotElimIsnt.at(pos);
                    }
                } else {
                    return Code::DoubleNotElimIsnt.at(pos);
                }
            }
            Justification::AndIntro(id_lhs, id_rhs) => {
                let lhs = lookup_claim(pos,previous_steps,*id_lhs)?;
                let rhs = lookup_claim(pos,previous_steps,*id_rhs)?;
                if let BoolExpr::And(s_lhs, s_rhs) = statement {
                    if **s_lhs != *lhs {
                        return Code::AndIntroBadLhs.at(pos);
                    }
                    if **s_rhs != *rhs {
                        return Code::AndIntroBadRhs.at(pos);
                    }
                } else {
                    return Code::AndIntroIsnt.at(pos);
                }
            }
            Justification::AndElimL(id_and) => {
                if let BoolExpr::And(lhs, _) = lookup_claim(pos,previous_steps,*id_and)? {
                    if **lhs != *statement {
                        return Code::AndElimLMismatch.at(pos);
                    }
                } else {
                    return Code::AndElimLNotAnd.at(pos);
                }
            }
            Justification::AndElimR(id_and) => {
                if let BoolExpr::And(_, rhs) = lookup_claim(pos,previous_steps,*id_and)? {
                    if **rhs != *statement {
                        return Code::AndElimRMismatch.at(pos);
                    }
                } else {
                    return Code::AndElimRNotAnd.at(pos);
                }
            }
            Justification::OrIntroL(id_lhs) => {
                let lhs = lookup_claim(pos,previous_steps,*id_lhs)?;
                if let BoolExpr::Or(s_lhs, _) = statement {
                    if **s_lhs != *lhs {
                        return Code::OrIntroLMismatch.at(pos);
                    }
                } else {
                    return Code::OrIntroLNotOr.at(pos);
                }
            }
            Justification::OrIntroR(id_rhs) => {
                let rhs = lookup_claim(pos,previous_steps,*id_rhs)?;
                if let BoolExpr::Or(_, s_rhs) = statement {
                    if **s_rhs != *rhs {
                        return Code::OrIntroRMismatch.at(pos);
                    }
                } else {
                    return Code::OrIntroRNotOr.at(pos);
                }
            }
            Justification::OrElim(id_or, id_box_l, id_box_r) => {
                if let BoolExpr::Or(lhs, rhs) = lookup_claim(pos,previous_steps,*id_or)? {
                    let (hyp_l, conc_l) = lookup_imp(pos,previous_steps,*id_box_l)?;
                    let (hyp_r, conc_r) = lookup_imp(pos,previous_steps,*id_box_r)?;
                    if *hyp_l != **lhs {
                        return Code::OrElimBadHypL.at(pos);
                    }
                    if *hyp_r != **rhs {
                        return Code::OrElimBadHypR.at(pos);
                    }
                    if conc_l != statement {
                        return Code::OrElimBadConcL.at(pos);
                    }
                    if conc_r != statement {
                        return Code::OrElimBadConcR.at(pos);
                    }
                } else {
                    return Code::OrElimNotOr.at(pos);
                }
            }
            Justification::ImpIntro(id_box) => {
                if let BoolExpr::Imp(s_hyp, s_conc) = statement {
                    let (hyp,conc) = lookup_imp(pos,previous_steps,*id_box)?;
                    if *hyp != **s_hyp {
                        return Code::ImpIntroBadHyp.at(pos);
                    }
                    if *conc != **s_conc {
                        return Code::ImpIntroBadConc.at(pos);
                    }
                } else {
                    return Code::ImpIntroNotImp.at(pos);
                }
            }
            Justification::ImpElim(id_imp, id_hyp) => {
                if let BoolExpr::Imp(imp_hyp, imp_conc) = lookup_claim(pos,previous_steps,*id_imp)? {
                    let hyp = lookup_claim(pos,previous_steps,*id_hyp)?;
                    if *hyp != **imp_hyp {
                        return Code::ImpElimBadHyp.at(pos);
                    }
                    if **imp_conc != *statement {
                        return Code::ImpElimBadConc.at(pos);
                    }
                } else {
                    return Code::ImpElimNotImp.at(pos);
                }
            }
            Justification::IffIntro(id_imp_l, id_imp_r) => {
                if let BoolExpr::Imp(hyp_l, conc_l) = lookup_claim(pos,previous_steps,*id_imp_l)? {
                    if let BoolExpr::Imp(hyp_r, conc_r) = lookup_claim(pos,previous_steps,*id_imp_r)? {
                        if let BoolExpr::Iff(a, b) = statement {
                            if a != hyp_l {
                                return Code::IffIntroBadHypL.at(pos);
                            }
                            if b != conc_l {
                                return Code::IffIntroBadConcL.at(pos);
                            }
                            if a != hyp_r {
                                return Code::IffIntroBadHypR.at(pos);
                            }
                            if b != conc_r {
                                return Code::IffIntroBadConcR.at(pos);
                            }
                        } else {
                            return Code::IffIntroNotIff.at(pos);
                        }
                    } else {
                        return Code::IffIntroNotImpR.at(pos);
                    }
                } else {
                    return Code::IffIntroNotImpL.at(pos);
                }
            }
            Justification::IffElimL(id_iff) => {
                if let BoolExpr::Iff(a,b) = lookup_claim(pos,previous_steps,*id_iff)? {
                    if let BoolExpr::Imp(hyp,conc) = statement {
                        if hyp != a {
                            return Code::IffElimLBadHyp.at(pos);
                        }
                        if conc != b {
                            return Code::IffElimLBadConc.at(pos);
                        }
                    } else {
                        return Code::IffElimLNotImp.at(pos);
                    }
                } else {
                    return Code::IffElimLNotIff.at(pos);
                }
            }
            Justification::IffElimR(id_iff) => {
                if let BoolExpr::Iff(a,b) = lookup_claim(pos,previous_steps,*id_iff)? {
                    if let BoolExpr::Imp(hyp,conc) = statement {
                        if hyp != b {
                            return Code::IffElimRBadHyp.at(pos);
                        }
                        if conc != a {
                            return Code::IffElimRBadConc.at(pos);
                        }
                    } else {
                        return Code::IffElimRNotImp.at(pos);
                    }
                } else {
                    return Code::IffElimRNotIff.at(pos);
                }
            }
            Justification::AllIntro(id_box) => {
                let (name,conc) = lookup_abox(pos,previous_steps,*id_box)?;
                if let BoolExpr::All(s_name, s_conc) = statement {
                    if name != s_name {
                        return Code::AllIntroWrongName.at(pos);  // right now we don't permit renaming in AllIntro
                    }
                    if *conc != **s_conc {
                        return Code::AllIntroWrongConc.at(pos);
                    }
                } else {
                    return Code::AllIntroNotForAll.at(pos);
                }
            }
            Justification::AllElim(id_all) => {
                if let BoolExpr::All(name, conc) = lookup_claim(pos,previous_steps,*id_all)? {
                    let mut subst = None;
                    self.check_substitution(name, conc, statement, &mut subst, &[]).map_err(Code::AllElimBadSubstitution.mapat(pos))?;
                } else {
                    return Code::AllElimNotForAll.at(pos);
                }
            }
            Justification::ExistsIntro(id) => {
                if let BoolExpr::Exists(name, conc) = statement {
                    let p = lookup_claim(pos,previous_steps,*id)?;
                    let mut subst = None;
                    self.check_substitution(name, conc, p, &mut subst, &[]).map_err(Code::ExistsIntroBadSubstitution.mapat(pos))?;
                } else {
                    return Code::ExistsIntroNotExists.at(pos);
                }
            }
            Justification::ExistsElim(id_exists, id_box) => {
                if let BoolExpr::Exists(ex_name, ex_conc) = lookup_claim(pos,previous_steps,*id_exists)? {
                    let (box_name, box_hyp, box_conc) = lookup_ebox(pos,previous_steps,*id_box)?;
                    if box_name != ex_name {
                        return Code::ExistsElimWrongName.at(pos);
                    }
                    if *box_hyp != **ex_conc {
                        return Code::ExistsElimBadHyp.at(pos);
                    }
                    if box_conc != statement {
                        return Code::ExistsElimBadConc.at(pos);
                    }
                } else {
                    return Code::ExistsElimNotExists.at(pos);
                }
            }
            Justification::Rename(id) => {
                let expr = lookup_claim(pos,previous_steps,*id)?;
                self.check_rename(pos,expr,statement,&[])?;
            }
            Justification::ZeroIsNotSucc => {
                let x = VarName::x();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::Not(
                                Box::new(BoolExpr::Eq(
                                        Box::new(NatExpr::Zero),
                                        Box::new(NatExpr::Succ(
                                                Box::new(NatExpr::Var(x))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Code::ZeroIsNotSuccWrong.at(pos);
                }
            }
            Justification::SuccInj => {
                let x = VarName::x();
                let y = VarName::y();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::All(y.clone(),
                                Box::new(BoolExpr::Imp(
                                        Box::new(BoolExpr::Eq(
                                                Box::new(NatExpr::Succ(
                                                        Box::new(NatExpr::Var(x.clone()))
                                                )),
                                                Box::new(NatExpr::Succ(
                                                        Box::new(NatExpr::Var(y.clone()))
                                                ))
                                        )),
                                        Box::new(BoolExpr::Eq(
                                                Box::new(NatExpr::Var(x)),
                                                Box::new(NatExpr::Var(y))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Code::SuccInjWrong.at(pos);
                }
            }
            Justification::AddZero => {
                let x = VarName::x();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::Eq(
                                Box::new(NatExpr::Add(
                                        Box::new(NatExpr::Var(x.clone())),
                                        Box::new(NatExpr::Zero)
                                )),
                                Box::new(NatExpr::Var(x))
                        ))
                );
                if expected != *statement {
                    return Code::AddZeroWrong.at(pos);
                }
            }
            Justification::AddSucc => {
                let x = VarName::x();
                let y = VarName::y();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::All(y.clone(),
                                Box::new(BoolExpr::Eq(
                                        Box::new(NatExpr::Add(
                                                Box::new(NatExpr::Var(x.clone())),
                                                Box::new(NatExpr::Succ(
                                                        Box::new(NatExpr::Var(y.clone()))
                                                ))
                                        )),
                                        Box::new(NatExpr::Succ(
                                                Box::new(NatExpr::Add(
                                                        Box::new(NatExpr::Var(x)),
                                                        Box::new(NatExpr::Var(y))
                                                ))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Code::AddSuccWrong.at(pos);
                }
            }
            Justification::MulZero => {
                let x = VarName::x();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::Eq(
                                Box::new(NatExpr::Mul(
                                        Box::new(NatExpr::Var(x)),
                                        Box::new(NatExpr::Zero)
                                )),
                                Box::new(NatExpr::Zero)
                        ))
                );
                if expected != *statement {
                    return Code::MulZeroWrong.at(pos);
                }
            }
            Justification::MulSucc => {
                let x = VarName::x();
                let y = VarName::y();
                let expected = BoolExpr::All(x.clone(),
                        Box::new(BoolExpr::All(y.clone(),
                                Box::new(BoolExpr::Eq(
                                        Box::new(NatExpr::Mul(
                                                Box::new(NatExpr::Var(x.clone())),
                                                Box::new(NatExpr::Succ(
                                                        Box::new(NatExpr::Var(y.clone()))
                                                ))
                                        )),
                                        Box::new(NatExpr::Add(
                                                Box::new(NatExpr::Mul(
                                                        Box::new(NatExpr::Var(x.clone())),
                                                        Box::new(NatExpr::Var(y))
                                                )),
                                                Box::new(NatExpr::Var(x))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Code::AddSuccWrong.at(pos);
                }
            }
            Justification::Induction => {
                // Pick apart the conclusion to find the relevant statements
                if let BoolExpr::Imp(hyps, concall) = statement {
                    if let BoolExpr::And(h0, all) = &**hyps {
                        if let BoolExpr::All(indvar, imp) = &**all {
                            if let BoolExpr::Imp(hn, hsn) = &**imp {
                                if let BoolExpr::All(concvar,conc) = &**concall {
                                    if indvar != concvar {
                                        return Code::InductionWrongVar.at(pos);
                                    }
                                    if hn != conc {
                                        return Code::InductionWrongIndHyp.at(pos);
                                    }
                                    let mut subst = Some(NatExpr::Zero);
                                    self.check_substitution(indvar, hn, h0, &mut subst, &[]).map_err(Code::InductionWrongBase.mapat(pos))?;
                                    let mut subst = Some(NatExpr::Succ(Box::new(NatExpr::Var(indvar.clone()))));
                                    self.check_substitution(indvar, hn, hsn, &mut subst, &[]).map_err(Code::InductionWrongIndConc.mapat(pos))?;
                                } else {
                                    return Code::InductionMalformed.at(pos);
                                }
                            } else {
                                return Code::InductionMalformed.at(pos);
                            }
                        } else {
                            return Code::InductionMalformed.at(pos);
                        }
                    } else {
                        return Code::InductionMalformed.at(pos);
                    }
                } else {
                    return Code::InductionMalformed.at(pos);
                }
            }
        }
        Ok(())
    }

    /// Check that lhs can be turned into rhs by a consistent renaming of bound variables
    ///
    /// The variables may be renamed differently if they are bound in different places.
    fn check_rename(&self, pos:Pos, lhs:&BoolExpr, rhs:&BoolExpr, bound:&[(VarName,VarName)]) -> Result<(),VerificationError> {
        match (lhs,rhs) {
            (BoolExpr::UserPred(lp,ls), BoolExpr::UserPred(rp,rs)) => {
                if lp != rp || ls.len() != rs.len() {
                    return Code::RenameMismatch.at(pos);
                }

                for i in 0..ls.len() {
                    self.check_rename_nat(pos, &ls[i], &rs[i], bound)?;
                }
            }
            (BoolExpr::Eq(l0,l1), BoolExpr::Eq(r0,r1)) => {
                self.check_rename_nat(pos, l0, r0, bound)?;
                self.check_rename_nat(pos, l1, r1, bound)?;
            }
            (BoolExpr::False, BoolExpr::False) => { /* nothing to check */ }
            (BoolExpr::Not(l), BoolExpr::Not(r)) => {
                self.check_rename(pos, l, r, bound)?;
            }
            (BoolExpr::And(l0,l1), BoolExpr::And(r0,r1)) |
            (BoolExpr::Or(l0,l1),  BoolExpr::Or(r0,r1))  |
            (BoolExpr::Imp(l0,l1), BoolExpr::Imp(r0,r1)) |
            (BoolExpr::Iff(l0,l1), BoolExpr::Iff(r0,r1)) => {
                self.check_rename(pos, l0, r0, bound)?;
                self.check_rename(pos, l1, r1, bound)?;
            }
            (BoolExpr::All(lx,l), BoolExpr::All(rx,r)) => {
                if bound.iter().any(|(ly,ry)| lx==ly || rx==ry) {
                    return Code::RenameBoundTwice.at(pos);  // This error shouldn't happen - should already have been checked
                }
                let mut b2 = bound.to_vec();
                b2.push((lx.clone(), rx.clone()));
                self.check_rename(pos, l, r, &b2)?;
            }
            _ => return Code::RenameMismatch.at(pos)
        }
        Ok(())
    }
    /// Check that lhs can be turned into rhs by the specified renaming of bound variables
    ///
    /// Any variables not occurring in bound are assumed to be floating, and must be the same on
    /// both sides.
    fn check_rename_nat(&self, pos:Pos, lhs:&NatExpr, rhs:&NatExpr, bound:&[(VarName,VarName)]) -> Result<(),VerificationError> {
        match (lhs, rhs) {
            (NatExpr::Var(lx), NatExpr::Var(rx)) => {
                if bound.iter().any(|(ly,ry)| lx==ly && rx==ry) {
                    // this is ok - we expect to rename lx to rx.
                } else if bound.iter().any(|(ly,ry)| lx==ly || rx==ry) || lx != rx {
                    // (1) this is not ok - one of the renaming variables occurs, and is not renamed correctly
                    // (2) Floating variables should not be renamed
                    return Code::RenameMismatch.at(pos);
                }
            }
            (NatExpr::Zero, NatExpr::Zero) => { /* nothing to check */ }
            (NatExpr::Succ(l), NatExpr::Succ(r)) => {
                self.check_rename_nat(pos, l, r, bound)?;
            }
            (NatExpr::Add(l0,l1), NatExpr::Add(r0,r1)) | (NatExpr::Mul(l0,l1), NatExpr::Mul(r0,r1)) => {
                self.check_rename_nat(pos, l0, r0, bound)?;
                self.check_rename_nat(pos, l1, r1, bound)?;
            }
            _ => return Code::RenameMismatch.at(pos)
        }
        Ok(())
    }

    /// Check that all instances of name can be substituted with something, to produce
    /// statement_with_subst.
    ///
    /// It's an error if two occurrences of name get substituted with different things, or if a
    /// bound variable occurs in the substitution.
    /// 
    /// This is used in both AllElim and ExistsIntro.
    /// It is used with an already supplied substitution in Induction.
    fn check_substitution(&self, name: &VarName, statement_with_name:&BoolExpr, statement_with_subst:&BoolExpr, subst:&mut Option<NatExpr>, bound:&[VarName]) -> Result<(),SubstitutionError> {
        match (statement_with_name, statement_with_subst) {
            (BoolExpr::UserPred(lp,ls), BoolExpr::UserPred(rp,rs)) => {
                if lp != rp || ls.len() != rs.len() {
                    return Err(SubstitutionError{});
                }

                for i in 0..ls.len() {
                    self.check_substitution_nat(name, &ls[i], &rs[i], subst, bound)?;
                }
            }
            (BoolExpr::Eq(l0,l1), BoolExpr::Eq(r0,r1)) => {
                self.check_substitution_nat(name, l0, r0, subst, bound)?;
                self.check_substitution_nat(name, l1, r1, subst, bound)?;
            }
            (BoolExpr::False, BoolExpr::False) => { /* nothing to check */ }
            (BoolExpr::Not(l), BoolExpr::Not(r)) => {
                self.check_substitution(name, l, r, subst, bound)?;
            }
            (BoolExpr::And(l0,l1), BoolExpr::And(r0,r1)) |
            (BoolExpr::Or(l0,l1),  BoolExpr::Or(r0,r1))  |
            (BoolExpr::Imp(l0,l1), BoolExpr::Imp(r0,r1)) |
            (BoolExpr::Iff(l0,l1), BoolExpr::Iff(r0,r1)) => {
                self.check_substitution(name, l0, r0, subst, bound)?;
                self.check_substitution(name, l1, r1, subst, bound)?;
            }
            (BoolExpr::All(lx,l), BoolExpr::All(rx,r)) => {
                if lx != rx {
                    return Err(SubstitutionError{});
                }
                if bound.contains(lx) {
                    // This shouldn't happen. We should already have checked for double bound
                    // variables.
                    return Err(SubstitutionError{});
                }
                let mut b2 = bound.to_vec();
                b2.push(lx.clone());
                self.check_substitution(name, l, r, subst, &b2)?;
            }
            _ => return Err(SubstitutionError{})
        }
        Ok(())
    }

    fn check_substitution_nat(&self, name:&VarName, expr_with_name:&NatExpr, expr_with_subst:&NatExpr, subst:&mut Option<NatExpr>, bound:&[VarName]) -> Result<(),SubstitutionError> {
        if let NatExpr::Var(v) = expr_with_name {
            if v == name {
                // The variable must be substituted.
                if let Some(subst_ref) = subst {
                    if subst_ref != expr_with_subst {
                        return Err(SubstitutionError{});
                    }
                } else {
                    self.check_no_occurences_of(expr_with_subst, bound)?;
                    *subst = Some(expr_with_subst.clone());
                }
                return Ok(());
            }
        }

        match (expr_with_name, expr_with_subst) {
            (NatExpr::Var(l), NatExpr::Var(r)) => {
                if l != r {
                    return Err(SubstitutionError{});
                }
            }
            (NatExpr::Zero, NatExpr::Zero) => { /* nothing to check */ }
            (NatExpr::Succ(l), NatExpr::Succ(r)) => {
                self.check_substitution_nat(name, l, r, subst, bound)?;
            }
            (NatExpr::Add(l0,l1), NatExpr::Add(r0,r1)) | (NatExpr::Mul(l0,l1), NatExpr::Mul(r0,r1)) => {
                self.check_substitution_nat(name, l0, r0, subst, bound)?;
                self.check_substitution_nat(name, l1, r1, subst, bound)?;
            }
            _ => return Err(SubstitutionError{})
        }
        Ok(())
    }

    fn check_no_occurences_of(&self, expr:&NatExpr, blacklist:&[VarName]) -> Result<(),SubstitutionError> {
        match expr {
            NatExpr::Var(v) => {
                if blacklist.contains(v) {
                    return Err(SubstitutionError{});
                }
            }
            NatExpr::Zero => { /* nothing to check */ }
            NatExpr::Succ(n) => {
                self.check_no_occurences_of(n, blacklist)?;
            }
            NatExpr::Add(a,b) | NatExpr::Mul(a,b) => {
                self.check_no_occurences_of(a, blacklist)?;
                self.check_no_occurences_of(b, blacklist)?;
            }
        }
        Ok(())
    }

    /// Check that statement_lhs can be rewritten as statement_rhs, using lhs=rhs as a rewrite rule.
    ///
    /// This assumes that the expression has already been validated, so we don't need to check for
    /// bound variables here.
    fn check_equal_elim(&self, pos: Pos, lhs:&NatExpr, rhs:&NatExpr, statement_lhs:&BoolExpr, statement_rhs:&BoolExpr) -> Result<(),VerificationError> {
        if statement_lhs == statement_rhs {
            return Ok(());
        }

        // Otherwise recursively check that statement_rhs can be rewritten as statement_rhs.
        match (statement_lhs, statement_rhs) {
            (BoolExpr::UserPred(lp,ls), BoolExpr::UserPred(rp,rs)) => {
                if lp != rp || ls.len() != rs.len() {
                    return Code::EqElimMismatchBool.at(pos);
                }

                for i in 0..ls.len() {
                    self.check_equal_elim_nat(pos, lhs, rhs, &ls[i], &rs[i])?;
                }
            }
            (BoolExpr::Eq(l0,l1), BoolExpr::Eq(r0,r1)) => {
                self.check_equal_elim_nat(pos, lhs, rhs, l0, r0)?;
                self.check_equal_elim_nat(pos, lhs, rhs, l1, r1)?;
            }
            (BoolExpr::Not(l), BoolExpr::Not(r)) => {
                self.check_equal_elim(pos, lhs, rhs, l, r)?;
            }
            (BoolExpr::And(l0,l1), BoolExpr::And(r0,r1)) |
            (BoolExpr::Or(l0,l1),  BoolExpr::Or(r0,r1))  |
            (BoolExpr::Imp(l0,l1), BoolExpr::Imp(r0,r1)) |
            (BoolExpr::Iff(l0,l1), BoolExpr::Iff(r0,r1)) => {
                self.check_equal_elim(pos, lhs, rhs, l0, r0)?;
                self.check_equal_elim(pos, lhs, rhs, l1, r1)?;
            }
            (BoolExpr::All(lx,l), BoolExpr::All(rx,r)) => {
                if lx != rx {
                    return Code::EqElimMismatchBool.at(pos);
                }
                self.check_equal_elim(pos, lhs, rhs, l, r)?;
            }
            _ => return Code::EqElimMismatchBool.at(pos)
        }

        Ok(())
    }

    /// Check that expr_lhs can be rewritten as expr_rhs, using lhs=rhs as a rewrite rule.
    ///
    /// This assumes that the expression has already been validated, so we don't need to check for
    /// bound variables here.
    fn check_equal_elim_nat(&self, pos: Pos, lhs:&NatExpr, rhs:&NatExpr, expr_lhs:&NatExpr, expr_rhs:&NatExpr) -> Result<(),VerificationError> {
        if expr_lhs == lhs && expr_rhs == rhs {
            // This is ok, because these are the two things we're explicitly being told are equal
            return Ok(());
        }

        if expr_lhs == expr_rhs {
            // This is ok too. They're the same.
            return Ok(());
        }

        // Otherwise recursively check that expr_rhs can be rewritten as expr_rhs.
        match (expr_lhs, expr_rhs) {
            (NatExpr::Succ(l), NatExpr::Succ(r)) => self.check_equal_elim_nat(pos, lhs, rhs, l, r)?,
            (NatExpr::Add(l0,l1), NatExpr::Add(r0,r1)) | (NatExpr::Mul(l0,l1), NatExpr::Mul(r0,r1)) => {
                self.check_equal_elim_nat(pos, lhs, rhs, l0, r0)?;
                self.check_equal_elim_nat(pos, lhs, rhs, l1, r1)?;
            }
            _ => return Code::EqElimMismatchNat.at(pos)
        }

        Ok(())
    }
}

struct SubstitutionError {}

fn lookup_ebox(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<(&VarName,&BoolExpr,&BoolExpr), VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::EBox(step_id, name, hyp, conc) = step {
            if *step_id == id {
                return Ok((name,hyp,conc));
            }
        }
    }
    Code::BadStepId.at(pos)
}

fn lookup_abox(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<(&VarName,&BoolExpr), VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::ABox(step_id, name, conc) = step {
            if *step_id == id {
                return Ok((name,conc));
            }
        }
    }
    Code::BadStepId.at(pos)
}

fn lookup_imp(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<(&BoolExpr,&BoolExpr), VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::Imp(step_id, hyp, conc) = step {
            if *step_id == id {
                return Ok((hyp,conc));
            }
        }
    }
    Code::BadStepId.at(pos)
}

fn lookup_claim(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<&BoolExpr, VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::Claim(step_id, expr) = step {
            if *step_id == id {
                return Ok(expr);
            }
        }
    }
    Code::BadStepId.at(pos)
}

#[derive(Clone,PartialEq,Eq)]
enum ProcessedStep {
    Claim(StepId,BoolExpr),
    Imp(StepId,BoolExpr,BoolExpr),
    ABox(StepId,VarName,BoolExpr),
    EBox(StepId,VarName,BoolExpr,BoolExpr),
}

pub fn verify(script: &Script) -> Result<(),VerificationError> {
    let mut checker = ProofChecker::default();

    for item in &script.items {
        match item {
            Item::Def(def) => {
                checker.add_def(def)?;
            }
            Item::Lemma(lemma) => {
                checker.add_lemma(lemma)?;
            }
        }
    }
    Ok(())
}
