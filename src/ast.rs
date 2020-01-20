pub struct Script {
    pub items: Vec<Item>
}

pub type Pos = usize;

pub enum Item {
    Def(ItemDef),
    Lemma(ItemLemma),
}

#[derive(Clone,PartialEq,Eq,Hash,Debug)]
pub struct PredName {
    value: String
}

#[derive(Clone,PartialEq,Eq,Hash,Debug)]
pub struct VarName {
    value: String
}

#[derive(Clone,PartialEq,Eq,Hash,Debug)]
pub struct LemmaName {
    value: String
}

pub struct ItemDef {
    pub pos: Pos,
    pub names: Vec<PredName>,
    pub quants: Vec<VarName>,
    pub rules: Vec<BoolExpr>,
}

#[derive(PartialEq,Eq,Clone,Debug)]
pub enum BoolExpr {
    UserPred(PredName, Vec<NatExpr>),
    Eq(Box<NatExpr>, Box<NatExpr>),
    False,
    Not(Box<BoolExpr>),
    And(Box<BoolExpr>,Box<BoolExpr>),
    Or(Box<BoolExpr>,Box<BoolExpr>),
    Imp(Box<BoolExpr>,Box<BoolExpr>),
    Iff(Box<BoolExpr>,Box<BoolExpr>),
    All(VarName, Box<BoolExpr>),
    Exists(VarName, Box<BoolExpr>),
}

#[derive(PartialEq,Eq,Clone,Debug)]
pub enum NatExpr {
    Var(VarName),
    Zero,
    Succ(Box<NatExpr>),
    Add(Box<NatExpr>,Box<NatExpr>),
    Mul(Box<NatExpr>,Box<NatExpr>),
    // Higher-level extensions
    UserFunc(PredName, Vec<NatExpr>),
}

pub struct ItemLemma {
    pub pos: Pos,
    pub name: LemmaName,
    pub statement: BoolExpr,
    pub proof: Vec<Step>
}

pub enum Step {
    Claim(StepClaim),
    Imp(StepImp),
    ABox(StepABox),
    EBox(StepEBox),
}

pub type StepId = usize;

pub struct StepClaim {
    pub id: StepId,
    pub pos: Pos,
    pub statement: BoolExpr,
    pub justification: Justification,
}

pub struct StepImp {
    pub id: StepId,
    pub pos: Pos,
    pub hyp: BoolExpr,
    pub contents: Vec<Step>,
}

pub struct StepABox {
    pub id: StepId,
    pub pos: Pos,
    pub name: VarName,
    pub contents: Vec<Step>,
}

pub struct StepEBox {
    pub id: StepId,
    pub pos: Pos,
    pub name: VarName,
    pub hyp: BoolExpr,
    pub contents: Vec<Step>,
}

#[derive(Clone)]
pub enum Justification {
    // Retrieving previous work
    ByDefinition(PredName),
    Lemma(LemmaName),

    // Logical steps
    EqualIntro,
    EqualElim(StepId/*equality*/,StepId/*statement to rewrite*/), // note not all occurrences of the lhs need to be replaced
    FalseIntro(StepId/*p*/,StepId/*~p*/),
    FalseElim(StepId/*false*/),
    NotIntro(StepId/*box*/),
    DoubleNotElim(StepId/*~~p*/),    // NotElim is the same as FalseIntro
    AndIntro(StepId,StepId),
    AndElimL(StepId),
    AndElimR(StepId),
    OrIntroL(StepId),
    OrIntroR(StepId),
    OrElim(StepId/*or*/,StepId/*box*/,StepId/*box*/),
    ImpIntro(StepId/*box*/),
    ImpElim(StepId/*p->q*/,StepId/*p*/),   // also called Modus Ponens
    IffIntro(StepId/*p->q*/,StepId/*q->p*/),
    IffElimL(StepId),
    IffElimR(StepId),
    AllIntro(StepId/*box*/),
    AllElim(StepId), // it's not specified here what the expression gets replaced with, but it will check that they all get replaced with the same thing
    ExistsIntro(StepId),
    ExistsElim(StepId/*exists*/,StepId/*box*/),
    Rename(StepId),

    // Axioms of PA.
    ZeroIsNotSucc,
    SuccInj,
    AddZero,
    AddSucc,
    MulZero,
    MulSucc,
    Induction,  // this one is the most complicated. The outer forall quantifiers are omitted, and it may contain varaibles that are bound in one of the surrounding boxes rather than in the formula itself.
}

impl Step {
    pub fn pos(&self) -> Pos {
        match self {
            Step::Claim(c) => c.pos,
            Step::Imp(b) => b.pos,
            Step::ABox(b) => b.pos,
            Step::EBox(b) => b.pos,
        }
    }
}

pub struct NameError {}

impl PredName {
    pub fn from_str(string: &str) -> Result<Self, NameError> {
        let mut first = true;
        for ch in string.chars() {
            if first {
                if !is_lower_alphabetic(ch) && !is_upper_alphabetic(ch) {
                    return Err(NameError {});
                }
            } else if !is_lower_alphabetic(ch) && !is_upper_alphabetic(ch) && !is_digit(ch) && ch != '_' {
                return Err(NameError {});
            }
            first = false;
        }
        Ok(PredName{value: string.to_string()})
    }
}

impl LemmaName {
    pub fn from_str(string: &str) -> Result<Self, NameError> {
        let mut first = true;
        for ch in string.chars() {
            if first {
                if !is_lower_alphabetic(ch) && !is_upper_alphabetic(ch) {
                    return Err(NameError {});
                }
            } else if !is_lower_alphabetic(ch) && !is_upper_alphabetic(ch) && !is_digit(ch) && ch != '_' {
                return Err(NameError {});
            }
            first = false;
        }
        Ok(LemmaName{value: string.to_string()})
    }
}

fn is_digit(ch: char) -> bool {
    ch >= '0' && ch <= '9'
}
fn is_lower_alphabetic(ch: char) -> bool {
    ch >= 'a' && ch <= 'z'
}
fn is_upper_alphabetic(ch: char) -> bool {
    ch >= 'A' && ch <= 'Z'
}
pub fn is_alphanumeric(ch: char) -> bool {
    is_digit(ch) || is_lower_alphabetic(ch) || is_upper_alphabetic(ch)
}

impl VarName {
    pub fn from_str(string: &str) -> Result<Self, NameError> {
        let mut first = true;
        for ch in string.chars() {
            if first {
                if !is_lower_alphabetic(ch) {
                    return Err(NameError {});
                }
            } else if !is_lower_alphabetic(ch) && !is_digit(ch) && ch != '_' {
                return Err(NameError {});
            }
            first = false;
        }
        Ok(VarName{value: string.to_string()})
    }
    /// Used in axioms.
    pub fn x() -> Self {
        VarName{value: "x".to_string()}
    }
    pub fn y() -> Self {
        VarName{value: "y".to_string()}
    }
}

impl ItemLemma {
    pub fn end_pos(&self) -> Pos {
        if self.proof.is_empty() {
            return self.pos;
        }
        self.proof[self.proof.len()-1].pos()
    }
}

impl StepEBox {
    pub fn end_pos(&self) -> Pos {
        if self.contents.is_empty() {
            return self.pos;
        }
        self.contents[self.contents.len()-1].pos()
    }
}
