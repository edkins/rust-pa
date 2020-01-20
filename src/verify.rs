use std::collections::HashMap;
use crate::ast::{Script,Pos,VarName,PredName,BoolExpr,NatExpr,ItemDef,Item,ItemLemma,LemmaName,StepId,Justification,Step};

#[derive(Debug)]
pub enum VerificationError {
    // Errors in definitions
    AlreadyDefined(Pos,PredName),
    NotDefiningAnything(Pos),
    CanOnlyDefineOneSymbolAtOnce(Pos,PredName,PredName),
    QuantifiersHaveSameName(Pos,VarName),
    DefMustBeIff(Pos),
    DefLhsMustBe(Pos,BoolExpr),
    NoDefinitionRules(Pos),
    MultipleDefinitionRulles(Pos),

    // Errors in boolean expressions
    UsingUndefinedPredicate(Pos,PredName),
    WrongNumberOfArguments(Pos,PredName,usize/*expected*/,usize/*supplied*/),
    NameBoundTwice(Pos,VarName),

    // Errors in nat expressions
    NameNotBound(Pos,VarName),
    UnexpectedHighLevelNatExpr(Pos,NatExpr),

    // Errors in proofs
    BoxIsEmpty(Pos),
    BoxDoesNotEndWithClaim(Pos),
    ProofEndsWithWrongClaim(Pos, BoolExpr/*proved*/, BoolExpr/*claimed*/),
    BadStepId(Pos,StepId),
    ABoxAlreadyBound(Pos),
    EBoxAlreadyBound(Pos),

    // Errors in justification steps
    NoSuchDefinition(Pos,PredName),  // ByDefinition
    NotDefinedThatWay(Pos,PredName),
    NoSuchLemma(Pos,LemmaName),      // Lemma
    LemmaDoesNotSayThat(Pos,LemmaName),
    LhsNotIdenticalToRhs(Pos),       // EqIntro
    NotIntroducingAnEquality(Pos),
    EqualElimMismatchNat(Pos,NatExpr,NatExpr),   // EqElim
    EqualElimMismatchBool(Pos,BoolExpr,BoolExpr),
    NotEliminatingAnEquality(Pos),
    StatementsDoNotContradict(Pos),  // FalseIntro
    NotIntroducingFalse(Pos),
    WasNotFalse(Pos),                // FalseElim
    DidNotLeadToFalse(Pos),          // NotIntro
    NotIntroducingNot(Pos),
    WrongNot(Pos),
    DoubleNotWrongThing(Pos),        // DoubleNotElim
    NotDoubleNot(Pos),
    NotIntroducingAnd(Pos),          // AndIntro
    AndIntroBadLhs(Pos),
    AndIntroBadRhs(Pos),
    AndElimLMismatch(Pos),           // AndElimL
    AndElimLNotAnd(Pos),
    AndElimRMismatch(Pos),           // AndElimR
    AndElimRNotAnd(Pos),
    OrIntroLMismatch(Pos),           // OrIntroL
    OrIntroLNotOr(Pos),
    OrIntroRMismatch(Pos),           // OrIntroR
    OrIntroRNotOr(Pos),
    OrElimNotOr(Pos),                // OrElim
    OrElimBadHypL(Pos),
    OrElimBadHypR(Pos),
    OrElimBadConcL(Pos),
    OrElimBadConcR(Pos),
    ImpIntroBadHyp(Pos),             // ImpIntro
    ImpIntroBadConc(Pos),
    ImpIntroNotImp(Pos),
    ImpElimBadHyp(Pos),              // ImpElim
    ImpElimBadConc(Pos),
    ImpElimNotImp(Pos),
    IffIntroNotIff(Pos),             // IffIntro
    IffIntroNotImpL(Pos),
    IffIntroNotImpR(Pos),
    IffIntroBadHypL(Pos),
    IffIntroBadHypR(Pos),
    IffIntroBadConcL(Pos),
    IffIntroBadConcR(Pos),
    IffElimLNotIff(Pos),             // IffElimL
    IffElimLNotImp(Pos),
    IffElimLBadHyp(Pos),
    IffElimLBadConc(Pos),
    IffElimRNotIff(Pos),             // IffElimR
    IffElimRNotImp(Pos),
    IffElimRBadHyp(Pos),
    IffElimRBadConc(Pos),
    AllIntroNotForAll(Pos),          // AllIntro
    AllIntroWrongName(Pos),
    AllIntroWrongConc(Pos),
    AllElimNotForAll(Pos),           // AllElim
    AllElimBadSubstitution(Pos),
    ExistsIntroBadSubstitution(Pos), // ExistsIntro
    ExistsIntroNotExists(Pos),
    ExistsElimNotExists(Pos),        // ExistsElim
    ExistsElimWrongName(Pos),
    ExistsElimBadHyp(Pos),
    ExistsElimBadConc(Pos),
    RenameMismatch(Pos),             // Rename
    RenameBoundTwice(Pos),
    ZeroIsNotSuccWrong(Pos),               // Axioms
    SuccInjWrong(Pos),
    AddZeroWrong(Pos),
    AddSuccWrong(Pos),
    MulZeroWrong(Pos),
    InductionMalformed(Pos),         // Induction
    InductionWrongVar(Pos),
    InductionWrongIndHyp(Pos),
    InductionWrongBase(Pos),
    InductionWrongIndConc(Pos),
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
        if def.names.is_empty() {
            return Err(VerificationError::NotDefiningAnything(def.pos));
        }
        if def.names.len() > 1 {
            return Err(VerificationError::CanOnlyDefineOneSymbolAtOnce(def.pos, def.names[0].clone(), def.names[1].clone()));
        }
        let name = &def.names[0];
        if let Some(bad) = any_equal(&def.quants) {
            return Err(VerificationError::QuantifiersHaveSameName(def.pos, bad));
        }

        if self.defined_symbols.contains_key(name) {
            return Err(VerificationError::AlreadyDefined(def.pos, name.clone()));
        }

        if def.rules.is_empty() {
            return Err(VerificationError::NoDefinitionRules(def.pos));
        }
        if def.rules.len() > 1 {
            return Err(VerificationError::MultipleDefinitionRulles(def.pos));
        }

        match &def.rules[0] {
            BoolExpr::Iff(lhs,rhs) => {
                let vars_as_exprs:Vec<NatExpr> = def.quants.iter().map(|v|NatExpr::Var(v.clone())).collect();
                let arity = vars_as_exprs.len();
                let expected_lhs = BoolExpr::UserPred(name.clone(), vars_as_exprs);
                if **lhs != expected_lhs {
                    return Err(VerificationError::DefLhsMustBe(def.pos, expected_lhs));
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
            _ => Err(VerificationError::DefMustBeIff(def.pos))
        }
    }
    fn check_boolexpr(&self, pos: Pos, expr: &BoolExpr, bound: &[VarName]) -> Result<(),VerificationError> {
        match expr {
            BoolExpr::UserPred(p, xs) => {
                match self.defined_symbols.get(&p) {
                    None => {
                        return Err(VerificationError::UsingUndefinedPredicate(pos, p.clone()));
                    }
                    Some(arity) => {
                        if xs.len() != *arity {
                            return Err(VerificationError::WrongNumberOfArguments(pos, p.clone(), *arity, xs.len()));
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
                    return Err(VerificationError::NameBoundTwice(pos, x.clone()));
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
                    return Err(VerificationError::NameNotBound(pos, x.clone()));
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
            _ => return Err(VerificationError::UnexpectedHighLevelNatExpr(pos, expr.clone()))
        }
        Ok(())
    }

    fn add_lemma(&mut self, lemma: &ItemLemma) -> Result<(),VerificationError> {
        self.check_boolexpr(lemma.pos, &lemma.statement, &[])?;

        let c = self.process_contents(lemma.pos, &lemma.proof, vec![], &[])?;

        if c != lemma.statement {
            return Err(VerificationError::ProofEndsWithWrongClaim(lemma.end_pos(), c.clone(), lemma.statement.clone()));
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
            return Err(VerificationError::BoxIsEmpty(pos));
        }

        let last_step = &processed[processed.len() - 1];
        if let ProcessedStep::Claim(_,c) = last_step {
            Ok(c.clone())
        } else {
            Err(VerificationError::BoxDoesNotEndWithClaim(contents[contents.len()-1].pos()))
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
                psteps.push(ProcessedStep::Claim(b.id, b.hyp.clone()));
                let c = self.process_contents(b.pos, &b.contents, psteps, bound)?;
                Ok(ProcessedStep::Imp(b.pos, b.hyp.clone(), c.clone()))
            }
            Step::ABox(b) => {
                if bound.contains(&b.name) {
                    return Err(VerificationError::ABoxAlreadyBound(b.pos));
                }
                let mut b2 = bound.to_vec();
                b2.push(b.name.clone());
                let c = self.process_contents(b.pos, &b.contents, previous_steps.to_vec(), &b2)?;
                Ok(ProcessedStep::ABox(b.id, b.name.clone(), c.clone()))
            }
            Step::EBox(b) => {
                if bound.contains(&b.name) {
                    return Err(VerificationError::EBoxAlreadyBound(b.pos));
                }
                let mut b2 = bound.to_vec();
                b2.push(b.name.clone());
                self.check_boolexpr(b.pos, &b.hyp, &b2)?;
                let mut psteps = previous_steps.to_vec();
                psteps.push(ProcessedStep::Claim(b.pos, b.hyp.clone()));
                let c = self.process_contents(b.pos, &b.contents, previous_steps.to_vec(), &b2)?;
                self.check_boolexpr(b.end_pos(), &c, bound)?;   // check conclusion doesn't contain bound variable, as this won't work with ExistsElim
                Ok(ProcessedStep::EBox(b.id, b.name.clone(), b.hyp.clone(), c.clone()))
            }
        }
    }

    fn check_justification(&self, pos: Pos, statement: &BoolExpr, justification: &Justification, previous_steps: &[ProcessedStep]) -> Result<(),VerificationError> {
        match justification {
            Justification::ByDefinition(pred) => {
                if let Some(actual_statement) = self.definition_claims.get(pred) {
                    if statement != actual_statement {
                        return Err(VerificationError::NotDefinedThatWay(pos, pred.clone()));
                    }
                } else {
                    return Err(VerificationError::NoSuchDefinition(pos, pred.clone()));
                }
            }
            Justification::Lemma(lemma) => {
                if let Some(actual_statement) = self.verified_claims.get(lemma) {
                    if statement != actual_statement {
                        return Err(VerificationError::LemmaDoesNotSayThat(pos, lemma.clone()));
                    }
                } else {
                    return Err(VerificationError::NoSuchLemma(pos, lemma.clone()));
                }
            }
            Justification::EqualIntro => {
                if let BoolExpr::Eq(lhs,rhs) = statement {
                    if lhs != rhs {
                        return Err(VerificationError::LhsNotIdenticalToRhs(pos));
                    }
                } else {
                    return Err(VerificationError::NotIntroducingAnEquality(pos));
                }
            }
            Justification::EqualElim(equality,to_rewrite) => {
                if let BoolExpr::Eq(lhs,rhs) = lookup_claim(pos,previous_steps,*equality)? {
                    let statement_lhs = lookup_claim(pos,previous_steps,*to_rewrite)?;
                    self.check_equal_elim(pos, lhs, rhs, statement_lhs, statement)?;
                } else {
                    return Err(VerificationError::NotEliminatingAnEquality(pos));
                }
            }
            Justification::FalseIntro(id_p, id_notp) => {
                let p = lookup_claim(pos,previous_steps,*id_p)?;
                if let BoolExpr::Not(p2) = lookup_claim(pos,previous_steps,*id_notp)? {
                    if *p != **p2 {
                        return Err(VerificationError::StatementsDoNotContradict(pos));
                    }
                    if *statement != BoolExpr::False {
                        return Err(VerificationError::NotIntroducingFalse(pos));
                    }
                } else {
                    return Err(VerificationError::StatementsDoNotContradict(pos));
                }
            }
            Justification::FalseElim(id_false) => {
                if let BoolExpr::False = lookup_claim(pos,previous_steps,*id_false)? {
                    // don't need to check statement because it can be anything
                } else {
                    return Err(VerificationError::WasNotFalse(pos));
                }
            }
            Justification::NotIntro(id_box) => {
                if let (hyp,BoolExpr::False) = lookup_imp(pos,previous_steps,*id_box)? {
                    if let BoolExpr::Not(s2) = statement {
                        if **s2 != *hyp {
                            return Err(VerificationError::WrongNot(pos));
                        }
                    } else {
                        return Err(VerificationError::NotIntroducingNot(pos));
                    }
                } else {
                    return Err(VerificationError::DidNotLeadToFalse(pos));
                }
            }
            Justification::DoubleNotElim(id_notnot) => {
                if let BoolExpr::Not(notp) = lookup_claim(pos,previous_steps,*id_notnot)? {
                    if let BoolExpr::Not(p) = &**notp {
                        if **p != *statement {
                            return Err(VerificationError::DoubleNotWrongThing(pos));
                        }
                    } else {
                        return Err(VerificationError::NotDoubleNot(pos));
                    }
                } else {
                    return Err(VerificationError::NotDoubleNot(pos));
                }
            }
            Justification::AndIntro(id_lhs, id_rhs) => {
                let lhs = lookup_claim(pos,previous_steps,*id_lhs)?;
                let rhs = lookup_claim(pos,previous_steps,*id_rhs)?;
                if let BoolExpr::And(s_lhs, s_rhs) = statement {
                    if **s_lhs != *lhs {
                        return Err(VerificationError::AndIntroBadLhs(pos));
                    }
                    if **s_rhs != *rhs {
                        return Err(VerificationError::AndIntroBadRhs(pos));
                    }
                } else {
                    return Err(VerificationError::NotIntroducingAnd(pos));
                }
            }
            Justification::AndElimL(id_and) => {
                if let BoolExpr::And(lhs, _) = lookup_claim(pos,previous_steps,*id_and)? {
                    if **lhs != *statement {
                        return Err(VerificationError::AndElimLMismatch(pos));
                    }
                } else {
                    return Err(VerificationError::AndElimLNotAnd(pos));
                }
            }
            Justification::AndElimR(id_and) => {
                if let BoolExpr::And(_, rhs) = lookup_claim(pos,previous_steps,*id_and)? {
                    if **rhs != *statement {
                        return Err(VerificationError::AndElimRMismatch(pos));
                    }
                } else {
                    return Err(VerificationError::AndElimRNotAnd(pos));
                }
            }
            Justification::OrIntroL(id_lhs) => {
                let lhs = lookup_claim(pos,previous_steps,*id_lhs)?;
                if let BoolExpr::Or(s_lhs, _) = statement {
                    if **s_lhs != *lhs {
                        return Err(VerificationError::OrIntroLMismatch(pos));
                    }
                } else {
                    return Err(VerificationError::OrIntroLNotOr(pos));
                }
            }
            Justification::OrIntroR(id_rhs) => {
                let rhs = lookup_claim(pos,previous_steps,*id_rhs)?;
                if let BoolExpr::Or(s_rhs, _) = statement {
                    if **s_rhs != *rhs {
                        return Err(VerificationError::OrIntroRMismatch(pos));
                    }
                } else {
                    return Err(VerificationError::OrIntroRNotOr(pos));
                }
            }
            Justification::OrElim(id_or, id_box_l, id_box_r) => {
                if let BoolExpr::Or(lhs, rhs) = lookup_claim(pos,previous_steps,*id_or)? {
                    let (hyp_l, conc_l) = lookup_imp(pos,previous_steps,*id_box_l)?;
                    let (hyp_r, conc_r) = lookup_imp(pos,previous_steps,*id_box_r)?;
                    if *hyp_l != **lhs {
                        return Err(VerificationError::OrElimBadHypL(pos));
                    }
                    if *hyp_r != **rhs {
                        return Err(VerificationError::OrElimBadHypR(pos));
                    }
                    if conc_l != statement {
                        return Err(VerificationError::OrElimBadConcL(pos));
                    }
                    if conc_r != statement {
                        return Err(VerificationError::OrElimBadConcR(pos));
                    }
                } else {
                    return Err(VerificationError::OrElimNotOr(pos));
                }
            }
            Justification::ImpIntro(id_box) => {
                if let BoolExpr::Imp(s_hyp, s_conc) = statement {
                    let (hyp,conc) = lookup_imp(pos,previous_steps,*id_box)?;
                    if *hyp != **s_hyp {
                        return Err(VerificationError::ImpIntroBadHyp(pos));
                    }
                    if *conc != **s_conc {
                        return Err(VerificationError::ImpIntroBadConc(pos));
                    }
                } else {
                    return Err(VerificationError::ImpIntroNotImp(pos));
                }
            }
            Justification::ImpElim(id_imp, id_hyp) => {
                if let BoolExpr::Imp(imp_hyp, imp_conc) = lookup_claim(pos,previous_steps,*id_imp)? {
                    let hyp = lookup_claim(pos,previous_steps,*id_hyp)?;
                    if *hyp != **imp_hyp {
                        return Err(VerificationError::ImpElimBadHyp(pos));
                    }
                    if **imp_conc != *statement {
                        return Err(VerificationError::ImpElimBadConc(pos));
                    }
                } else {
                    return Err(VerificationError::ImpElimNotImp(pos));
                }
            }
            Justification::IffIntro(id_imp_l, id_imp_r) => {
                if let BoolExpr::Imp(hyp_l, conc_l) = lookup_claim(pos,previous_steps,*id_imp_l)? {
                    if let BoolExpr::Imp(hyp_r, conc_r) = lookup_claim(pos,previous_steps,*id_imp_r)? {
                        if let BoolExpr::Iff(a, b) = statement {
                            if a != hyp_l {
                                return Err(VerificationError::IffIntroBadHypL(pos));
                            }
                            if b != conc_l {
                                return Err(VerificationError::IffIntroBadConcL(pos));
                            }
                            if a != hyp_r {
                                return Err(VerificationError::IffIntroBadHypR(pos));
                            }
                            if b != conc_r {
                                return Err(VerificationError::IffIntroBadConcR(pos));
                            }
                        } else {
                            return Err(VerificationError::IffIntroNotIff(pos));
                        }
                    } else {
                        return Err(VerificationError::IffIntroNotImpR(pos));
                    }
                } else {
                    return Err(VerificationError::IffIntroNotImpL(pos));
                }
            }
            Justification::IffElimL(id_iff) => {
                if let BoolExpr::Iff(a,b) = lookup_claim(pos,previous_steps,*id_iff)? {
                    if let BoolExpr::Imp(hyp,conc) = statement {
                        if hyp != a {
                            return Err(VerificationError::IffElimLBadHyp(pos));
                        }
                        if conc != b {
                            return Err(VerificationError::IffElimLBadConc(pos));
                        }
                    } else {
                        return Err(VerificationError::IffElimLNotImp(pos));
                    }
                } else {
                    return Err(VerificationError::IffElimLNotIff(pos));
                }
            }
            Justification::IffElimR(id_iff) => {
                if let BoolExpr::Iff(a,b) = lookup_claim(pos,previous_steps,*id_iff)? {
                    if let BoolExpr::Imp(hyp,conc) = statement {
                        if hyp != b {
                            return Err(VerificationError::IffElimRBadHyp(pos));
                        }
                        if conc != a {
                            return Err(VerificationError::IffElimRBadConc(pos));
                        }
                    } else {
                        return Err(VerificationError::IffElimRNotImp(pos));
                    }
                } else {
                    return Err(VerificationError::IffElimRNotIff(pos));
                }
            }
            Justification::AllIntro(id_box) => {
                let (name,conc) = lookup_abox(pos,previous_steps,*id_box)?;
                if let BoolExpr::All(s_name, s_conc) = statement {
                    if name != s_name {
                        return Err(VerificationError::AllIntroWrongName(pos));  // right now we don't permit renaming in AllIntro
                    }
                    if *conc != **s_conc {
                        return Err(VerificationError::AllIntroWrongConc(pos));
                    }
                } else {
                    return Err(VerificationError::AllIntroNotForAll(pos));
                }
            }
            Justification::AllElim(id_all) => {
                if let BoolExpr::All(name, conc) = lookup_claim(pos,previous_steps,*id_all)? {
                    let mut subst = None;
                    self.check_substitution(name, conc, statement, &mut subst, &[]).map_err(|_|VerificationError::AllElimBadSubstitution(pos))?;
                } else {
                    return Err(VerificationError::AllElimNotForAll(pos));
                }
            }
            Justification::ExistsIntro(id) => {
                if let BoolExpr::Exists(name, conc) = statement {
                    let p = lookup_claim(pos,previous_steps,*id)?;
                    let mut subst = None;
                    self.check_substitution(name, conc, p, &mut subst, &[]).map_err(|_|VerificationError::ExistsIntroBadSubstitution(pos))?;
                } else {
                    return Err(VerificationError::ExistsIntroNotExists(pos));
                }
            }
            Justification::ExistsElim(id_exists, id_box) => {
                if let BoolExpr::Exists(ex_name, ex_conc) = lookup_claim(pos,previous_steps,*id_exists)? {
                    let (box_name, box_hyp, box_conc) = lookup_ebox(pos,previous_steps,*id_box)?;
                    if box_name != ex_name {
                        return Err(VerificationError::ExistsElimWrongName(pos));
                    }
                    if *box_hyp != **ex_conc {
                        return Err(VerificationError::ExistsElimBadHyp(pos));
                    }
                    if box_conc != statement {
                        return Err(VerificationError::ExistsElimBadConc(pos));
                    }
                } else {
                    return Err(VerificationError::ExistsElimNotExists(pos));
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
                                                Box::new(NatExpr::Var(x.clone()))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Err(VerificationError::ZeroIsNotSuccWrong(pos));
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
                                                Box::new(NatExpr::Var(x.clone())),
                                                Box::new(NatExpr::Var(y.clone()))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Err(VerificationError::SuccInjWrong(pos));
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
                                Box::new(NatExpr::Var(x.clone()))
                        ))
                );
                if expected != *statement {
                    return Err(VerificationError::AddZeroWrong(pos));
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
                                                        Box::new(NatExpr::Var(x.clone())),
                                                        Box::new(NatExpr::Var(y.clone()))
                                                ))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Err(VerificationError::AddSuccWrong(pos));
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
                    return Err(VerificationError::MulZeroWrong(pos));
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
                                                        Box::new(NatExpr::Var(y.clone()))
                                                )),
                                                Box::new(NatExpr::Var(x.clone()))
                                        ))
                                ))
                        ))
                );
                if expected != *statement {
                    return Err(VerificationError::AddSuccWrong(pos));
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
                                        return Err(VerificationError::InductionWrongVar(pos));
                                    }
                                    if hn != conc {
                                        return Err(VerificationError::InductionWrongIndHyp(pos));
                                    }
                                    let mut subst = Some(NatExpr::Zero);
                                    self.check_substitution(indvar, hn, h0, &mut subst, &[]).map_err(|_|VerificationError::InductionWrongBase(pos))?;
                                    let mut subst = Some(NatExpr::Succ(Box::new(NatExpr::Var(indvar.clone()))));
                                    self.check_substitution(indvar, hn, hsn, &mut subst, &[]).map_err(|_|VerificationError::InductionWrongIndConc(pos))?;
                                } else {
                                    return Err(VerificationError::InductionMalformed(pos));
                                }
                            } else {
                                return Err(VerificationError::InductionMalformed(pos));
                            }
                        } else {
                            return Err(VerificationError::InductionMalformed(pos));
                        }
                    } else {
                        return Err(VerificationError::InductionMalformed(pos));
                    }
                } else {
                    return Err(VerificationError::InductionMalformed(pos));
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
                    return Err(VerificationError::RenameMismatch(pos));
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
                    return Err(VerificationError::RenameBoundTwice(pos));  // This error shouldn't happen - should already have been checked
                }
                let mut b2 = bound.to_vec();
                b2.push((lx.clone(), rx.clone()));
                self.check_rename(pos, l, r, &b2)?;
            }
            _ => return Err(VerificationError::RenameMismatch(pos))
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
                } else if bound.iter().any(|(ly,ry)| lx==ly || rx==ry) {
                    // this is not ok - one of the renaming variables occurs, and is not renamed
                    // correctly
                    return Err(VerificationError::RenameMismatch(pos));
                } else if lx != rx {
                    // Floating variables should not be renamed
                    return Err(VerificationError::RenameMismatch(pos));
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
            _ => return Err(VerificationError::RenameMismatch(pos))
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
            _ => return Err(SubstitutionError{})
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
                    return Err(VerificationError::EqualElimMismatchBool(pos, statement_lhs.clone(), statement_rhs.clone()));
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
                    return Err(VerificationError::EqualElimMismatchBool(pos, statement_lhs.clone(), statement_rhs.clone()));
                }
                self.check_equal_elim(pos, lhs, rhs, l, r)?;
            }
            _ => return Err(VerificationError::EqualElimMismatchBool(pos, statement_lhs.clone(), statement_rhs.clone()))
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
            _ => return Err(VerificationError::EqualElimMismatchNat(pos, expr_lhs.clone(), expr_rhs.clone()))
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
    Err(VerificationError::BadStepId(pos,id))
}

fn lookup_abox(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<(&VarName,&BoolExpr), VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::ABox(step_id, name, conc) = step {
            if *step_id == id {
                return Ok((name,conc));
            }
        }
    }
    Err(VerificationError::BadStepId(pos,id))
}

fn lookup_imp(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<(&BoolExpr,&BoolExpr), VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::Imp(step_id, hyp, conc) = step {
            if *step_id == id {
                return Ok((hyp,conc));
            }
        }
    }
    Err(VerificationError::BadStepId(pos,id))
}

fn lookup_claim(pos: Pos, previous_steps: &[ProcessedStep], id: StepId) -> Result<&BoolExpr, VerificationError> {
    for step in previous_steps {
        if let ProcessedStep::Claim(step_id, expr) = step {
            if *step_id == id {
                return Ok(expr);
            }
        }
    }
    Err(VerificationError::BadStepId(pos,id))
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
