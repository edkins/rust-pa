use num_traits::Zero;
use crate::high_level::ast::{HBuiltin,HType,HName,HStepType,HAxiom,HExpr,HRule};

#[derive(Clone,Debug)]
pub struct FuncType {
    pub return_type: HType,
    pub args: Vec<HType>,
}

impl HBuiltin {
    pub fn arity(&self) -> usize {
        match self {
            HBuiltin::False => 0,
            HBuiltin::Not | HBuiltin::Succ => 1,
            HBuiltin::Eq | HBuiltin::And | HBuiltin::Or | HBuiltin::Imp | HBuiltin::Iff | HBuiltin::All | HBuiltin::Exists | HBuiltin::Add | HBuiltin::Mul => 2
        }
    }
    pub fn is_quant(&self) -> bool {
        match self {
            HBuiltin::False | HBuiltin::Not | HBuiltin::Succ |
            HBuiltin::Eq | HBuiltin::And | HBuiltin::Or | HBuiltin::Imp | HBuiltin::Iff | HBuiltin::Add | HBuiltin::Mul => false,
            HBuiltin::All | HBuiltin::Exists => true, 
        }
    }
    pub fn func_type(&self) -> FuncType {
        let return_type;
        let args;
        match self {
            HBuiltin::Eq => {
                return_type = HType::Bool;
                args = vec![HType::Nat, HType::Nat];
            }
            HBuiltin::False => {
                return_type = HType::Bool;
                args = vec![];
            }
            HBuiltin::Not => {
                return_type = HType::Bool;
                args = vec![HType::Bool];
            }
            HBuiltin::And | HBuiltin::Or | HBuiltin::Imp | HBuiltin::Iff => {
                return_type = HType::Bool;
                args = vec![HType::Bool,HType::Bool];
            }
            HBuiltin::All | HBuiltin::Exists => {
                return_type = HType::Bool;
                args = vec![HType::Nat,HType::Bool];
            }
            HBuiltin::Succ => {
                return_type = HType::Nat;
                args = vec![HType::Nat];
            }
            HBuiltin::Add | HBuiltin :: Mul => {
                return_type = HType::Nat;
                args = vec![HType::Nat,HType::Nat];
            }
        }
        FuncType{return_type, args}
    }
}

impl HType {
    pub fn maps_to_bool(&self) -> bool {
        match self {
            HType::Bool => true,
            HType::Nat => false,
            HType::Unchecked => false,
        }
    }
    pub fn maps_to_nat(&self) -> bool {
        match self {
            HType::Nat => true,
            HType::Bool => false,
            HType::Unchecked => false,
        }
    }
}

impl HName {
    pub fn is_quant(&self) -> bool {
        match self {
            HName::UserFunc(_) | HName::UserVar(_) | HName::Num(_) => false,
            HName::Builtin(b) => b.is_quant()
        }
    }
}

impl HStepType {
    pub fn is_box(&self) -> bool {
        match self {
            HStepType::Claim => false,
            HStepType::Given | HStepType::Induction => true,
        }
    }
}


impl HAxiom {
    pub fn statement(&self) -> HExpr {
        match self {
            HAxiom::ZeroIsNotSucc =>
                forall(x(),not(eq(zero(),s(x())))),
            HAxiom::SuccInj =>
                forall(x(), forall(y(),
                    imp(eq(s(x()), s(y())), eq(x(), y())))),
            HAxiom::AddZero =>
                forall(x(), eq(add(x(),zero()), x())),
            HAxiom::AddSucc =>
                forall(x(), forall(y(),
                    eq(add(x(),s(y())), s(add(x(),y()))))),
            HAxiom::MulZero =>
                forall(x(), eq(mul(x(),zero()), zero())),
            HAxiom::MulSucc =>
                forall(x(), forall(y(),
                    eq(mul(x(),s(y())), add(mul(x(),y()), x())))),
        }
    }
    pub fn all() -> Vec<Self> {
        vec![HAxiom::ZeroIsNotSucc,
            HAxiom::SuccInj,
            HAxiom::AddZero,
            HAxiom::AddSucc,
            HAxiom::MulZero,
            HAxiom::MulSucc]
    }
}

fn x() -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::UserVar("x".to_string()),
        args: vec![]
    }
}

fn y() -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::UserVar("y".to_string()),
        args: vec![]
    }
}

fn zero() -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::Num(Zero::zero()),
        args: vec![]
    }
}

fn s(n: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::Builtin(HBuiltin::Succ),
        args: vec![n]
    }
}

fn add(m: HExpr, n: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::Builtin(HBuiltin::Add),
        args: vec![m,n]
    }
}

fn mul(m: HExpr, n: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Nat,
        name: HName::Builtin(HBuiltin::Mul),
        args: vec![m,n]
    }
}

fn eq(m: HExpr, n: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Bool,
        name: HName::Builtin(HBuiltin::Eq),
        args: vec![m,n]
    }
}

fn not(p: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Bool,
        name: HName::Builtin(HBuiltin::Not),
        args: vec![p]
    }
}

fn imp(p: HExpr, q: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Bool,
        name: HName::Builtin(HBuiltin::Imp),
        args: vec![p,q]
    }
}

fn forall(x: HExpr, e: HExpr) -> HExpr {
    HExpr {
        pos: 0,
        typ: HType::Bool,
        name: HName::Builtin(HBuiltin::All),
        args: vec![x,e]
    }
}

impl HRule {
    pub fn step_count(&self) -> usize {
        match self {
            HRule::AllElim | HRule::Rename => 1
        }
    }
}

impl HExpr {
    /// Not using == because it's not an exact match. The pos may be different.
    pub fn eq(&self, other: &HExpr) -> bool {
        if self.name != other.name || self.typ != other.typ || self.args.len() != other.args.len() {
            return false;
        }
        for (i,arg) in self.args.iter().enumerate() {
            if !arg.eq(&other.args[i]) {
                return false;
            }
        }
        return true;
    }
}
