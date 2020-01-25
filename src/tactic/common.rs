use std::collections::HashMap;
use crate::high_level::ast::*;

pub struct TacticError {
    pos: HPos,
    code: ErrorCode
}

pub enum ErrorCode {
    DoesNotHaveId,
    DoesNotHaveStatement,
    MalformedQuant,
    NoSuchLemma,
    NoSuchSeq,
    NoValueToSubstitute,
    NotAClaim,
    NotForAll,
    RenameMismatch,
    SubstValueContainsBoundVar,
    VarsCannotBeFunctions,
}

impl ErrorCode {
    pub fn at<T>(self, pos: HPos) -> Result<T,TacticError> {
        Err(TacticError{pos, code:self})
    }
    pub fn err(self, pos: HPos) -> TacticError {
        TacticError{pos, code:self}
    }
}

#[derive(Clone,Copy,Debug)]
pub struct Seq {
    i: usize,
    j: usize,
}

struct BuilderBox {
    bound: Vec<HVarName>,
    steps: Vec<HStep>,
}

pub struct ProofBuilder {
    boxes: Vec<BuilderBox>,
    inserted_axioms: HashMap<HAxiom,Seq>,
    inserted_lemmas: HashMap<HLemmaName,Seq>,
    next_step_id: HStepId,
    lemmas: HashMap<HLemmaName,HExpr>,
}

impl ProofBuilder {
    pub fn new(next_step_id: HStepId, lemmas: HashMap<HLemmaName,HExpr>) -> Self {
        ProofBuilder {
            boxes: vec![BuilderBox{bound:vec![],steps:vec![]}],
            inserted_axioms: HashMap::new(),
            inserted_lemmas: HashMap::new(),
            next_step_id,
            lemmas,
        }
    }

    fn make_step_id(&mut self, step_id: Option<HStepId>) -> HStepId {
        match step_id {
            Some(id) => id,
            None => {
                let id = self.next_step_id;
                self.next_step_id += 1;
                id
            }
        }
    }

    fn add_beginning(&mut self, step: HStep) -> Seq {
        let i = 0;
        let j = self.boxes[i].steps.len();

        self.boxes[i].steps.push(step);

        Seq { i, j }
    }


    fn add_end(&mut self, step: HStep) -> Seq {
        let i = self.boxes.len() - 1;
        let j = self.boxes[i].steps.len();

        self.boxes[i].steps.push(step);

        Seq { i, j }
    }

    fn get(&self, seq: Seq, pos: HPos) -> Result<&HStep,TacticError> {
        if seq.i < self.boxes.len() && seq.j < self.boxes[seq.i].steps.len() {
            Ok(&self.boxes[seq.i].steps[seq.j])
        } else {
            ErrorCode::NoSuchSeq.at(pos)
        }
    }

    fn get_claim(&self, seq: Seq, pos: HPos) -> Result<(HStepId,&HExpr),TacticError> {
        let step = self.get(seq, pos)?;
        if step.step_type == HStepType::Claim {
            if let Some(stmt) = &step.statement {
                if let Some(id) = step.id {
                    Ok((id, stmt))
                } else {
                    ErrorCode::DoesNotHaveId.at(pos)
                }
            } else {
                ErrorCode::DoesNotHaveStatement.at(pos)
            }
        } else {
            ErrorCode::NotAClaim.at(pos)
        }
    }

    pub fn axiom(&mut self, axiom: HAxiom, pos: HPos, step_id: Option<HStepId>) -> Seq {
        match self.inserted_axioms.get(&axiom) {
            Some(seq) => {
                *seq
            }
            None => {
                let id = self.make_step_id(step_id);
                let step = claim(pos, id, axiom.statement(), HJustification::Axiom(axiom.clone()));
                let seq = self.add_beginning(step);
                self.inserted_axioms.insert(axiom, seq);
                seq
            }
        }
    }

    pub fn lemma(&mut self, lemma: HLemmaName, pos: HPos, step_id: Option<HStepId>) -> Result<Seq,TacticError> {
        match self.inserted_lemmas.get(&lemma) {
            Some(seq) => {
                Ok(*seq)
            }
            None => {
                let id = self.make_step_id(step_id);
                let statement = self.lemmas.get(&lemma).ok_or_else(||ErrorCode::NoSuchLemma.err(pos))?.clone();
                let step = claim(pos, id, statement, HJustification::Lemma(lemma.clone()));
                let seq = self.add_beginning(step);
                self.inserted_lemmas.insert(lemma, seq);
                Ok(seq)
            }
        }
    }

    pub fn all_elim(&mut self, all_seq: Seq, subst: Option<HExpr>, pos: HPos, step_id: Option<HStepId>) -> Result<Seq,TacticError> {
        let (all_id, all_stmt) = self.get_claim(all_seq, pos)?;

        if let Some((x, stmt)) = peel_forall(all_stmt) {
            let stmt2 = if let Some(expr) = subst {
                subst_var(stmt, x, &expr)?
            } else {
                // We're given nothing to substitute. This only makes sense if the forall variable
                // doesn't actually occur in the expression body.
                if stmt.contains_var_anywhere(x) {
                    return ErrorCode::NoValueToSubstitute.at(pos);
                }
                stmt.clone()
            };
            let id = self.make_step_id(step_id);
            let step = claim(pos, id, stmt2.clone(), HJustification::Rule(HRule::AllElim, vec![all_id]));
            Ok(self.add_end(step))
        } else {
            ErrorCode::NotForAll.at(pos)
        }
    }

    /// Instead of giving a list of variables to rename, we give the entire renamed statement.
    /// This allows naming different occurrences of a variable differently.
    ///
    /// All variables that are bound by boxes must map to themselves. We're not renaming those.
    pub fn rename(&mut self, prev_seq: Seq, renamed: HExpr, pos: HPos, step_id: Option<HStepId>) -> Result<Seq,TacticError> {
        let (prev_id, prev_stmt) = self.get_claim(prev_seq, pos)?;

        // All variables that are bound by boxes must map to themselves. We're not renaming those.
        let bound = self.boxes[self.boxes.len()-1].bound.iter().map(|x|(x.clone(),x.clone())).collect::<Vec<_>>();
        check_rename(pos, prev_stmt, &renamed, &bound)?;

        let id = self.make_step_id(step_id);
        let step = claim(pos, id, renamed, HJustification::Rule(HRule::Rename, vec![prev_id]));
        Ok(self.add_end(step))
    }
}

fn claim(pos: HPos, id: HStepId, statement: HExpr, justification: HJustification) -> HStep {
    HStep {
        pos,
        id: Some(id),
        statement: Some(statement),
        intros: None,
        contents: None,
        step_type: HStepType::Claim,
        justification: Some(justification),
    }
}

fn peel_forall(e: &HExpr) -> Option<(&HVarName, &HExpr)> {
    if let HName::Builtin(HBuiltin::All) = e.name {
        if e.args.len() == 2 {
            if let HName::UserVar(x) = &e.args[0].name {
                return Some((&x, &e.args[1]))
            }
        }
    }
    None
}

fn subst_var(expr: &HExpr, x: &HVarName, val: &HExpr) -> Result<HExpr, TacticError> {
    if expr.name.is_quant() {
        if expr.args.len() > 0 {
            if let HName::UserVar(y) = &expr.args[0].name {
                if val.contains_var_anywhere(y) && expr.contains_var_anywhere(x) {
                    return ErrorCode::SubstValueContainsBoundVar.at(expr.pos);
                }
            } else {
                return ErrorCode::MalformedQuant.at(expr.pos);
            }
        } else {
            return ErrorCode::MalformedQuant.at(expr.pos);
        }
    }

    if let HName::UserVar(x2) = &expr.name {
        if expr.args.is_empty() {
            if x == x2 {
                return Ok(val.clone());
            }
        } else {
            return ErrorCode::VarsCannotBeFunctions.at(expr.pos);
        }
    }

    let args = expr.args.iter().map(|a| subst_var(a, x, val)).collect::<Result<_,_>>()?;
    Ok(HExpr {
        pos: expr.pos,
        typ: expr.typ.clone(),
        name: expr.name.clone(),
        args
    })
}

/// Check that lhs can be turned into rhs by a consistent renaming of bound variables
///
/// The variables may be renamed differently if they are bound in different places.
fn check_rename(pos:HPos, lhs:&HExpr, rhs:&HExpr, bound:&[(HVarName,HVarName)]) -> Result<(),TacticError> {
    if lhs.args.len() != rhs.args.len() {
        return ErrorCode::RenameMismatch.at(pos);
    }

    for (i,larg) in lhs.args.iter().enumerate() {
        check_rename(pos, larg, &rhs.args[i], bound)?;
    }

    match (&lhs.name, &rhs.name) {
        (HName::UserFunc(lf), HName::UserFunc(rf)) => {
            if lf != rf {
                return ErrorCode::RenameMismatch.at(pos);
            }
        }
        (HName::UserVar(lx), HName::UserVar(rx)) => {
            // Check that lx->rx occurs in the mapping
            // This will fail if we encounter an unexpected free variable,
            // or if it maps to the wrong thing.
            if !bound.iter().any(|(ly,ry)| lx==ly && rx==ry) {
                return ErrorCode::RenameMismatch.at(pos);
            }
        }
        (HName::Builtin(lb), HName::Builtin(rb)) => {
            if lb != rb {
                return ErrorCode::RenameMismatch.at(pos);
            }
        }
        (HName::Num(ln), HName::Num(rn)) => {
            if ln != rn {
                return ErrorCode::RenameMismatch.at(pos);
            }
        }
        _ => return ErrorCode::RenameMismatch.at(pos)
    }
    Ok(())
}

