use std::collections::HashMap;
use crate::binary::codes::*;
use crate::binary::deserialize::{DecodingError,ErrorCode};

const ARITY_UNUSED:u8 = 255;

pub struct OpMap {
    arity: HashMap<usize,OpMap>,
}

/// Provides the default OpMap for expressions.
impl Default for OpMap {
    fn default() -> Self {
        let mut result = OpMap {
            arity: HashMap::new()
        };
        for (k,v) in [
            (NOT,1),
            (AND,2),
            (OR,2),
            (IMP,2),
            (IFF,2),
            (EQ,2),
            (FALSE,0),
            (TRUE,0),
            (BOOL,0),
            (NAT,0),
            (PRODUCT,2),
            (FUNC,2),
            (SUCC,1),
            (ADD,2),
            (MUL,2),
        ].iter() {
            result.insert(*k,*v).unwrap();
        }
        for i in UINT_MIN..=UINT_MAX {
            result.insert(i,0).unwrap();
        }
        result
    }
}

impl OpMap {
    fn insert(&mut self, opcode: usize, arity: u8) -> Result<(),ErrorCode> {
        let mut entry = self.entry(&opcode);
        if let Occupied(_) = entry {
            return ErrorCode::OpcodeAlreadyUsed;
        }
        entry.or_insert(arity);
        Ok(())
    }

    fn lookup(input: &[u8]) -> Result<(&[u8],u8),ErrorCode> {
        if input.is_empty() {
            return ErrorCode::UnexpectedEndOfExpression;  // not EOF, because we might not be being given the entire file
        }
    }
}
