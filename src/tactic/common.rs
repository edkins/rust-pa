use std::collections::HashMap;
use crate::high_level::ast::{HStep,HStepId,HAxiom,HExpr,HLemmaName,HJustification,HPos,HStepType};

pub struct TacticError {
    pos: HPos,
    code: ErrorCode
}

pub enum ErrorCode {
    NoSuchLemma
}

impl ErrorCode {
    pub fn at<T>(self, pos: HPos) -> Result<T,TacticError> {
        Err(TacticError{pos, code:self})
    }
    pub fn err(self, pos: HPos) -> TacticError {
        TacticError{pos, code:self}
    }
}

#[derive(Clone,Debug)]
pub struct Seq {
    i: usize,
    j: usize,
}

pub struct ProofBuilder {
    boxes: Vec<Vec<HStep>>,
    inserted_axioms: HashMap<HAxiom,Seq>,
    inserted_lemmas: HashMap<HLemmaName,Seq>,
    next_step_id: HStepId,
    lemmas: HashMap<HLemmaName,HExpr>,
}

impl ProofBuilder {
    pub fn new(next_step_id: HStepId, lemmas: HashMap<HLemmaName,HExpr>) -> Self {
        ProofBuilder {
            boxes: vec![vec![]],
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

    fn add(&mut self, step: HStep) -> Seq {
        let i = self.boxes.len() - 1;
        let j = self.boxes[i].len();

        self.boxes[i].push(step);

        Seq { i, j }
    }

    pub fn axiom(&mut self, axiom: HAxiom, pos: HPos, step_id: Option<HStepId>) -> Seq {
        match self.inserted_axioms.get(&axiom) {
            Some(seq) => {
                seq.clone()
            }
            None => {
                let id = self.make_step_id(step_id);
                let step = claim(pos, id, axiom.statement(), HJustification::Axiom(axiom.clone()));
                let seq = self.add(step);
                self.inserted_axioms.insert(axiom, seq.clone());
                seq
            }
        }
    }

    pub fn lemma(&mut self, lemma: HLemmaName, pos: HPos, step_id: Option<HStepId>) -> Result<Seq,TacticError> {
        match self.inserted_lemmas.get(&lemma) {
            Some(seq) => {
                Ok(seq.clone())
            }
            None => {
                let id = self.make_step_id(step_id);
                let statement = self.lemmas.get(&lemma).ok_or_else(||ErrorCode::NoSuchLemma.err(pos))?.clone();
                let step = claim(pos, id, statement, HJustification::Lemma(lemma.clone()));
                let seq = self.add(step);
                self.inserted_lemmas.insert(lemma, seq.clone());
                Ok(seq)
            }
        }
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
