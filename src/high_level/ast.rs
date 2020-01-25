use num_bigint::BigUint;

pub struct HScript {
    pub items: Vec<HItem>
}

pub type HPos = usize;

pub type HFuncName = String;
pub type HVarName = String;
pub type HLemmaName = String;

#[derive(Clone,PartialEq,Eq,Debug,Hash,PartialOrd,Ord)]
pub enum HName {
    UserFunc(HFuncName),
    UserVar(HVarName),
    Builtin(HBuiltin),
    Num(BigUint),
}

#[derive(Clone,PartialEq,Eq,Debug,Hash,PartialOrd,Ord)]
pub enum HBuiltin {
    Eq,
    False,
    Not,
    And,
    Or,
    Imp,
    Iff,
    All,
    Exists,
//    Zero is handled as a BigUint
    Succ,
    Add,
    Mul,
}

#[derive(Clone,Debug)]
pub enum HItem {
    Def(HItemDef),
    Lemma(HItemLemma),
}

#[derive(Clone,Debug)]
pub struct HItemDef {
    pub pos: HPos,
    pub names: Vec<HFuncName>,
    pub quants: Option<Vec<HVarName>>,
    pub rules: Vec<HExpr>,
}

#[derive(Clone,PartialEq,Eq,Debug)]
pub enum HType {
    Nat,
    Bool,
    Unchecked,     // this means the type checker hasn't been run yet
}

#[derive(Clone,Debug)]
pub struct HExpr {
    pub pos: HPos,
    pub typ: HType,
    pub name: HName,
    pub args: Vec<HExpr>,   // for quantifiers, first arg is the quantified variable and is treated specially
}

impl HExpr {
    pub fn num(pos: HPos, n: BigUint) -> Self {
        HExpr {
            pos,
            typ: HType::Unchecked,   // ok, it's probably Nat. But the type checker is a separate pass.
            name: HName::Num(n),
            args: vec![],
        }
    }
    /// This deals with S() and false as special cases
    pub fn func(pos: HPos, name: &str, args: Vec<HExpr>) -> Self {
        let name = if name == "S" {
            HName::Builtin(HBuiltin::Succ)
        } else if name == "false" {
            HName::Builtin(HBuiltin::False)
        } else {
            HName::UserFunc(name.to_string())
        };
        HExpr {
            pos,
            typ: HType::Unchecked,
            name,
            args,
        }
    }
    pub fn constant(pos: HPos, name: &str) -> Self {
        HExpr::func(pos, name, vec![])
    }
    pub fn var(pos: HPos, name: &str) -> Self {
        HExpr {
            pos,
            typ: HType::Unchecked,
            name: HName::UserVar(name.to_string()),
            args: vec![]
        }
    }
    pub fn builtin1(pos: HPos, name: HBuiltin, a: HExpr) -> Self {
        HExpr {
            pos,
            typ: HType::Unchecked,
            name: HName::Builtin(name),
            args: vec![a]
        }
    }
    pub fn builtin2(pos: HPos, name: HBuiltin, a: HExpr, b: HExpr) -> Self {
        HExpr {
            pos,
            typ: HType::Unchecked,
            name: HName::Builtin(name),
            args: vec![a,b]
        }
    }
    pub fn quant(pos: HPos, name: HBuiltin, x: &str, expr: HExpr) -> Self {
        HExpr {
            pos,
            typ: HType::Unchecked,
            name: HName::Builtin(name),
            args: vec![HExpr::var(pos,x),expr]
        }
    }
}

#[derive(Clone,Debug)]
pub struct HItemLemma {
    pub pos: HPos,
    pub name: HLemmaName,
    pub statement: HExpr,
    pub proof: Vec<HStep>
}

#[derive(Clone,Debug)]
pub struct HStep {
    pub pos: HPos,
    pub id: Option<HStepId>,
    pub statement: Option<HExpr>,
    pub intros: Option<Vec<HIntro>>,    // None means no box
    pub contents: Option<Vec<HStep>>,  // None means no box
    pub step_type: HStepType,
    pub justification: Option<HJustification>,   // None means no justification specified. Will be filled in later (or rejected) for claims
}

#[derive(PartialEq,Eq,Clone,Debug)]
pub enum HStepType {
    Claim,
    Given,
    Induction,
}

pub type HStepId = usize;

#[derive(Clone,Debug)]
pub enum HIntro {
    Var(HVarName),
    Stmt(HExpr,Option<HStepId>),
}

#[derive(Clone,Debug)]
pub enum HJustification {
    Axiom(HAxiom),
    Lemma(HLemmaName),
    Rule(HRule, Vec<HStepId>),
}

#[derive(PartialEq,Eq,Clone,Debug)]
pub enum HRule {
    AllElim,
    Rename,
}

#[derive(PartialEq,Eq,Clone,Debug,Hash)]
pub enum HAxiom {
    ZeroIsNotSucc,
    SuccInj,
    AddZero,
    AddSucc,
    MulZero,
    MulSucc,
}

impl std::fmt::Display for HExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.name {
            HName::UserFunc(x) | HName::UserVar(x) => write!(f, "{}", x)?,
            HName::Builtin(b) => write!(f, "{:?}", b)?,
            HName::Num(n) => write!(f, "{}", n)?,
        }
        if !self.args.is_empty() {
            write!(f, "(")?;
            let mut first = true;
            for arg in &self.args {
                if !first {
                    write!(f, ",")?;
                }
                first = false;
                arg.fmt(f)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}
