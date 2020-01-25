use std::collections::{HashMap,VecDeque};
use crate::high_level::ast::{HLemmaName,HExpr,HName,HVarName,HPos,HIntro,HAxiom};
use crate::high_level::guesswork::{GuessError,ErrorCode};

/// This matches expression trees.
///
/// It's designed to match them efficiently, and to allow parts of the expression to be bound to
/// "variables" (typed as either boolean or nat).
///
/// For example, eq_refl would match eq(A, A) where A can be anything.
///
/// Expressions are fed in breadth-first, with the exception that any sub-expression matched by a
/// variable gets omitted from future passes.
///
/// So the matcher eq(A+0,A) would be represented as the following sequence:
/// - on_func eq 
/// - on_func add
/// - push_var A
/// - match_var A
/// - match_var 0
///
/// It would match the expression eq((1+1)+0, 1+1) as follows:
///
/// - on_func eq matches eq(...)
/// - on_func add matches (1+1)+0
/// - push_var A matches 1+1
/// - match_var A matches 1+1
/// - match_var 0 matches 0
pub struct TreeMatcher {
    map: HashMap<MatcherStep, TreeMatcher>,
    payload: Vec<TreeMatcherPayload>,
}

#[derive(PartialEq,Eq,Hash,Clone)]
enum MatcherStep {
    Exact(HName,usize),
    Push,
    Retrieve(usize),
}

impl MatcherStep {
    fn visit_children(&self) -> bool {
        match self {
            MatcherStep::Exact(_,_) => true,
            MatcherStep::Retrieve(_) | MatcherStep::Push => false
        }
    }
}

#[derive(Clone,PartialEq,Eq,Hash)]
pub enum TreeMatcherSource {
    Lemma(HLemmaName),
    Axiom(HAxiom),
}

#[derive(Clone)]
struct TreeMatcherPayload {
    source: TreeMatcherSource,
    intros: Vec<HIntro>,
    vars: HashMap<HVarName,Option<usize>>,
}

#[derive(Clone)]
pub struct TreeMatcherAnswer {
    pub source: TreeMatcherSource,
    pub intros: Vec<HIntro>,
    pub vars: HashMap<HVarName,HExpr>,
}

impl Default for TreeMatcher {
    fn default() -> Self {
        TreeMatcher {
            map: HashMap::new(),
            payload: vec![],
        }
    }
}

#[derive(Clone)]
struct Matching<'a,'b> {
    matcher: &'b TreeMatcher,
    vars: Vec<&'a HExpr>,
    buffer: VecDeque<&'a HExpr>
}

struct Match<'b> {
    next: &'b TreeMatcher,
    push: bool,
    visit_children: bool,
}

impl TreeMatcherPayload {
    fn with_vars<'a>(&self, values: &[&'a HExpr]) -> TreeMatcherAnswer {
        let mut vars = HashMap::new();
        for (k,vopt) in self.vars.iter() {
            if let Some(v) = vopt {
                if *v < values.len() {
                    vars.insert(k.clone(), values[*v].clone());
                }
            }
        }
        TreeMatcherAnswer {
            source: self.source.clone(),
            intros: self.intros.clone(),
            vars
        }
    }
}

impl<'a,'b> Matching<'a,'b> {
    fn get_exact(&self, name: &HName, arity: usize) -> Option<&'b TreeMatcher> {
        self.matcher.map.get(&MatcherStep::Exact(name.clone(), arity))
    }
    fn get_push(&self) -> Option<&'b TreeMatcher> {
        self.matcher.map.get(&MatcherStep::Push)
    }
    // Scanning over a HashMap like this might not be the most efficient
    fn add_retrieves_matching(&self, result: &mut Vec<Match<'b>>, expr: &HExpr) {
        for (i,var) in self.vars.iter().enumerate() {
            if let Some(next) = self.matcher.map.get(&MatcherStep::Retrieve(i)) {
                if expr == *var {
                    result.push(Match{next,push:false,visit_children:false});
                }
            }
        }
    }
    fn get_matches(&self, expr: &HExpr) -> Vec<Match<'b>> {
        let mut result = vec![];
        if let Some(next) = self.get_exact(&expr.name, expr.args.len()) {
            result.push(Match{next,push:false,visit_children:true});
        }
        if let Some(next) = self.get_push() {
            result.push(Match{next,push:true,visit_children:false});
        }
        self.add_retrieves_matching(&mut result, expr);
        result
    }

    fn apply(&mut self, mat: Match<'b>, expr: &'a HExpr) {
        self.matcher = mat.next;
        if mat.push {
            self.vars.push(expr);
        }
        if mat.visit_children {
            for arg in &expr.args {
                self.buffer.push_back(arg);
            }
        }
    }

    fn match_recursive(&mut self, result: &mut Vec<TreeMatcherAnswer>) {
        loop {
            match self.buffer.pop_front() {
                None => {
                    result.extend(self.matcher.payload.iter().map(|p|p.with_vars(&self.vars)));
                }
                Some(expr) => {
                    let mut matches = self.get_matches(expr);

                    if matches.is_empty() {
                        break;
                    } else {
                        for mat in matches.drain(1..) {
                            let mut matching = self.clone();
                            matching.apply(mat, expr);
                            matching.match_recursive(result);
                        }
                        self.apply(matches.remove(0), expr);
                    }
                }
            }
        }
    }
}

impl TreeMatcher {
    pub fn match_expr(&self, e: &HExpr) -> Vec<TreeMatcherAnswer> {
        let mut buffer = VecDeque::new();
        buffer.push_back(e);
        let mut matching = Matching{matcher:self, vars:vec![], buffer};
        let mut result = vec![];
        matching.match_recursive(&mut result);
        result
    }

    fn follow_mut(&mut self, step: &MatcherStep) -> &mut TreeMatcher {
        self.map.entry(step.clone()).or_insert(TreeMatcher::default())
    }

    /// Adds a lemma to this tree, assuming the forall quantifiers have already been unwrapped into
    /// intros.
    ///
    /// Currently can't handle Stmt intros.
    ///
    /// TODO: handle renaming of quantified vars
    pub fn add_payload(&mut self, source: TreeMatcherSource, intros: &[HIntro], stmt: &HExpr) -> Result<(),GuessError> {
        let mut vars = intros_to_set(stmt.pos, intros)?;
        let mut buffer = VecDeque::new();
        buffer.push_back(stmt);
        let mut matcher = self;
        loop {
            if let Some(e) = buffer.pop_front() {
                let mut step = MatcherStep::Exact(e.name.clone(), e.args.len());
                if let HName::UserVar(x) = &e.name {
                    if let Some(nopt) = vars.get(x) {
                        if let Some(n) = nopt {
                            step = MatcherStep::Retrieve(*n);
                        } else {
                            step = MatcherStep::Push;
                            vars.insert(x.clone(), Some(vars.len()));
                        }
                    }
                }

                if step.visit_children() {
                    for arg in &e.args {
                        buffer.push_back(arg);
                    }
                }

                matcher = matcher.follow_mut(&step);
            } else {
                matcher.payload.push(TreeMatcherPayload {
                    source,
                    intros: intros.to_vec(),
                    vars,
                });
                return Ok(());
            }
        }
    }
}

fn intros_to_set(pos: HPos, intros: &[HIntro]) -> Result<HashMap<HVarName,Option<usize>>,GuessError> {
    let mut result = HashMap::new();
    for intro in intros {
        if let HIntro::Var(x) = intro {
            result.insert(x.clone(),None);
        } else {
            return ErrorCode::CannotCurrentlyMatchStmtIntros.at(pos);
        }
    }
    Ok(result)
}
