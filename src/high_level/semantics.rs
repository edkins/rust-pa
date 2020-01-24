use crate::high_level::ast::{HBuiltin,HType,HName,HStepType};

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

