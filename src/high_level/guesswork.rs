use std::collections::HashMap;
use crate::high_level::ast::*;
use crate::high_level::tree_matcher::{TreeMatcher,TreeMatcherSource,TreeMatcherAnswer};

#[derive(Debug)]
pub struct GuessError {
    pub pos: HPos,
    pub code: ErrorCode,
}

#[derive(Debug)]
pub enum ErrorCode {
    CannotCurrentlyMatchStmtIntros,
    CouldNotGuess,
    ClaimHasNoStatement,
    MissingId,
    NoIntrosForBox,
    UnexpectedLemmaNotFound,
    UnexpectedNoId,
    UnexpectedCouldNotPeelForall,
    UnexpectedPeeledWrongVar,
    UnexpectedNoValueToSubstitute,
    UnexpectedMissingStatement,
    UnexpectedMissingId,
    UnexpectedStmtIntro,
}

impl ErrorCode {
    pub fn at<T>(self, pos: HPos) -> Result<T,GuessError> {
        Err(GuessError{pos, code:self})
    }
    pub fn error_at(self, pos: HPos) -> GuessError {
        GuessError{pos, code:self}
    }
}

struct Guesser {
    insert_at_beginning: Vec<HStep>,
    inserted_sources: HashMap<TreeMatcherSource,usize>,
    next_id: HStepId,
    lemmas: HashMap<HLemmaName,HExpr>,
}

impl Guesser {
    fn guess_for_step(&mut self, result: &mut Vec<HStep>, matcher: &TreeMatcher, step: &HStep, processed: &[HExpr]) -> Result<(),GuessError> {
        let pos = step.pos;
        if step.step_type.is_box() {
            let mut p2 = processed.to_vec();
            for intro in step.intros.as_ref().unwrap_or(&vec![]) {
                if let HIntro::Stmt(stmt,_) = intro {
                    p2.push(stmt.clone());
                }
            }
            let contents = self.guess_for_steps(matcher, step.contents.as_ref().unwrap_or(&vec![]), &p2)?;

            result.push(HStep {
                pos,
                id: step.id,
                statement: None,
                intros: step.intros.clone(),
                contents: Some(contents),
                step_type: step.step_type.clone(),
                justification: None,
            });
        } else {
            if let Some(stmt) = &step.statement {
                let matches = matcher.match_expr(stmt);
                if matches.is_empty() {
                    return ErrorCode::CouldNotGuess.at(step.pos);
                }

                let stmt_id = step.id.ok_or_else(||ErrorCode::MissingId.error_at(pos))?;
                self.get_to(pos, stmt_id, result, stmt, &matches[0])?;
            } else {
                return ErrorCode::ClaimHasNoStatement.at(step.pos);
            }
        }
        Ok(())
    }

    fn add_source(&mut self, pos: HPos, source: &TreeMatcherSource) -> Result<usize,GuessError> {
        let stmt;
        let justification;

        if let Some(insert_id) = self.inserted_sources.get(source) {
            return Ok(*insert_id);
        }

        match source {
            TreeMatcherSource::Lemma(lem) => {
                stmt = self.lemmas.get(lem).ok_or_else(||ErrorCode::UnexpectedLemmaNotFound.error_at(pos))?.clone();
                justification = HJustification::Lemma(lem.clone());
            }
            TreeMatcherSource::Axiom(ax) => {
                stmt = ax.statement();
                justification = HJustification::Axiom(ax.clone());
            }
        }
        
        let insert_id = self.insert_at_beginning.len();
        let id = self.gen_id();
        self.insert_at_beginning.push(HStep {
            pos,
            id: Some(id),
            statement: Some(stmt.clone()),
            intros: None,
            contents: None,
            step_type: HStepType::Claim,
            justification: Some(justification),
        });
        self.inserted_sources.insert(source.clone(), insert_id);
        Ok(insert_id)
    }

    fn gen_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn get_to(&mut self, pos: HPos, original_id: HStepId, result: &mut Vec<HStep>, stmt: &HExpr, answer: &TreeMatcherAnswer) -> Result<(),GuessError> {
        let insert_id = self.add_source(stmt.pos, &answer.source)?;
        let mut prev_id = self.insert_at_beginning[insert_id].id.ok_or_else(||ErrorCode::UnexpectedMissingId.error_at(pos))?;
        let mut prev_stmt = self.insert_at_beginning[insert_id].statement.as_ref().ok_or_else(||ErrorCode::UnexpectedMissingStatement.error_at(pos))?.clone();

        // TODO: actual renaming of variables may be necessary. This just copies.
        let id = if answer.intros.is_empty() {original_id} else {self.gen_id()};
        result.push(HStep {
            pos,
            id: Some(id),
            statement: Some(prev_stmt.clone()),
            intros: None,
            contents: None,
            step_type: HStepType::Claim,
            justification: Some(HJustification::Rule(HRule::Rename, vec![prev_id]))
        });
        prev_id = id;

        for (i,intro) in answer.intros.iter().enumerate() {
            match intro {
                HIntro::Var(x) => {
                    if let Some((x2,next_x2)) = peel_forall(&prev_stmt) {
                        if x != x2 {
                            return ErrorCode::UnexpectedPeeledWrongVar.at(pos);
                        }
                        prev_stmt = subst_var(next_x2, x2, answer.vars.get(x))?;
                        let id = if i == answer.intros.len() - 1 {original_id} else {self.gen_id()};
                        result.push(HStep {
                            pos,
                            id: Some(id),
                            statement: Some(prev_stmt.clone()),
                            intros: None,
                            contents: None,
                            step_type: HStepType::Claim,
                            justification: Some(HJustification::Rule(HRule::AllElim, vec![prev_id]))
                        });
                        prev_id = id;
                    } else {
                        return ErrorCode::UnexpectedCouldNotPeelForall.at(pos);
                    }
                }
                HIntro::Stmt(_,_) => {
                    return ErrorCode::UnexpectedStmtIntro.at(pos);
                }
            }
        }

        Ok(())
    }

    fn guess_for_steps(&mut self, matcher: &TreeMatcher, steps: &[HStep], processed: &[HExpr]) -> Result<Vec<HStep>,GuessError> {
        let mut result = vec![];
        let mut p2 = processed.to_vec();
        for step in steps {
            self.guess_for_step(&mut result, matcher, step, &p2)?;
            if let Some(stmt) = &step.statement {
                p2.push(stmt.clone());
            }
        }
        Ok(result)
    }
}

fn subst_var(expr: &HExpr, x: &HVarName, val: Option<&HExpr>) -> Result<HExpr, GuessError> {
    if let HName::UserVar(x2) = &expr.name {
        if x == x2 {
            if let Some(e) = val {
                return Ok(e.clone());
            } else {
                return ErrorCode::UnexpectedNoValueToSubstitute.at(expr.pos);
            }
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

fn step_id_ubound(steps: &[HStep]) -> usize {
    let mut result = 0;
    for step in steps {
        if let Some(step_id) = step.id {
            result = result.max(step_id + 1);
        }
        if let Some(contents) = &step.contents {
            result = result.max(step_id_ubound(contents));
        }
    }
    result
}

fn guess_for_lemma(matcher: &TreeMatcher, lemma: &mut HItemLemma, lemmas: &HashMap<HLemmaName,HExpr>) -> Result<(),GuessError> {
    let mut guesser = Guesser {
        insert_at_beginning: vec![],
        inserted_sources: HashMap::<TreeMatcherSource,_>::new(),
        next_id: step_id_ubound(&lemma.proof),
        lemmas: lemmas.clone()
    };
    let proof2 = guesser.guess_for_steps(matcher, &lemma.proof, &[])?;
    let mut proof = guesser.insert_at_beginning;
    proof.extend_from_slice(&proof2);
    lemma.proof = proof;
    Ok(())
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

fn peel_and_add_payload(matcher: &mut TreeMatcher, source: TreeMatcherSource, stmt: &HExpr) -> Result<(),GuessError> {
    let mut e = stmt;
    let mut intros = vec![];
    loop {
        if let Some((x,e2)) = peel_forall(e) {
            e = e2;
            intros.push(HIntro::Var(x.clone()));
        } else {
            break;
        }
    }

    matcher.add_payload(source, &intros, e)
}

fn add_axiom_payloads(matcher: &mut TreeMatcher) -> Result<(),GuessError> {
    for axiom in &HAxiom::all() {
        peel_and_add_payload(matcher, TreeMatcherSource::Axiom(axiom.clone()), &axiom.statement())?;
    }
    Ok(())
}

pub fn guess_justifications(script: &mut HScript) -> Result<(),GuessError> {
    let mut matcher = TreeMatcher::default();
    let mut lemmas = HashMap::new();
    add_axiom_payloads(&mut matcher)?;
    for item in script.items.iter_mut() {
        if let HItem::Lemma(lemma) = item {
            guess_for_lemma(&mut matcher, lemma, &lemmas)?;
            lemmas.insert(lemma.name.clone(), lemma.statement.clone());
            peel_and_add_payload(&mut matcher, TreeMatcherSource::Lemma(lemma.name.clone()), &lemma.statement)?;
        }
    }
    Ok(())
}
