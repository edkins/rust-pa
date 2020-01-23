use crate::high_level::ast::{HBuiltin,HType,HName};

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
}

impl HType {
    pub fn maps_to_bool(&self) -> bool {
        match self {
            HType::Bool => true,
            HType::Nat => false
        }
    }
    pub fn maps_to_nat(&self) -> bool {
        match self {
            HType::Nat => true,
            HType::Bool => false
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
