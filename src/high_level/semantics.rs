use crate::high_level::ast::{HBuiltin,HType};

impl HBuiltin {
    pub fn arity(&self) -> usize {
        match self {
            HBuiltin::False => 0,
            HBuiltin::Not | HBuiltin::Succ => 1,
            HBuiltin::Eq | HBuiltin::And | HBuiltin::Or | HBuiltin::Imp | HBuiltin::Iff | HBuiltin::All | HBuiltin::Exists | HBuiltin::Add | HBuiltin::Mul => 2
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
