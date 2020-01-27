use num_bigint::BigUint;
use std::collections::HashMap;
use crate::binary::codes::*;

/// The binary format
///
/// Unsigned Integers
/// -----------------
///
/// VLQ encoding is used to store unsigned integers. Bytes are stored big-endian, with the top bit
/// set to 1 to indicate more bytes are coming.
///
/// For example:
///
/// | Byte 0   | Byte 1   | Byte 2   |
/// |----------|----------|----------|
/// | 10001111 | 10011001 | 01111000 |
///
/// Ignore the top bits and concatenate them together. This produces 000111100110011111000, or
/// 249080 in decimal.
///
/// Redundant sequences with leading zeros (0x80) are considered invalid.
///
/// In general there is no limit to how big these unsigned integers can be, though speciic
/// implementations may fail if given large integers in certain places.
///
/// Expressions
/// -----------
/// Expressions are written in prefix notation. This was chosen over reverse Polish notation to
/// allow easy depth-first traversal of expression trees. (Depth-first traversal is common in
/// tactics, and it's assumed that lightweight tactics will use the same representation of
/// expressions internally as they use for serialization).
///
/// Expressions therefore start with an opcode. Opcodes are either one of the standard ones listed
/// below, or they are *introduced* before use. The introduction determines how many arguments they
/// have, allowing unambiguous parsing of what follows.
///
/// Commands and the proof stack
/// ----------------------------
/// Expressions are prefixed with a command opcode, for example Claim. Certain commands manipulate
/// the proof stack.
///
/// The proof stack allows universally-quantified variables to enter scope, and hypotheses to be
/// introduced. Things can be defined when the proof stack is nonempty, but when items are popped
/// off the proof stack those definitions will acquire a "forall x" or "P ->" at the front.
///
/// Opcodes and binary data
/// -----------------------
/// Opcodes are encoded as VLQ. Opcodes 2-8 take a second integer.
///
/// Binary data can be encoded, with an 0x01 byte followed by VLQ-encoded length, followed by the
/// binary data itself.
///
/// Definitions
/// -----------
/// Definitions are surprisingly complex, because we want to allow for "underdefined" symbols, that
/// obey certain rules but whose exact value in all circumstances is not known.
///
/// There are two main use cases for underdefined symbols:
/// - partial functions (where e.g. the division by zero case is undefined)
/// - type abstraction, where we want to leave equality undefined between objects of different
/// conceptual types
///
/// A concrete definition must be supplied in all cases though, to prove that we're not introducing
/// contradictory requirements.
///
/// Definitions have the following structure:
///
/// ```text
/// startd
///
/// var x              # push a var corresponding to each arg of the function we're defining
/// def.f "f" mul x x  # The implementation of f(x); this will be hidden later
/// claim lt x f x x   # We can assert miscellaneous facts about f; these will also be hidden
/// popvar
///
/// export eq f 2 4    # This is all people end up seeing - that f maps 2 to 4
///
/// endd
/// ```
///
/// Some opcodes
/// ============
///
/// |Opcode| Name |Args|Operation                                                 |
/// |------|------|----|----------------------------------------------------------|
/// |0     |NULL  |0   |Invalid opcode. Immediately abort processing              |
/// |1;n;xx|binary|0   |Push two nats: the length, and the big-endian data        |
/// |2;n   |error |0   |Error, with error code                                    |
/// |3;n   |intro |2   |Introduce the n thing as the given name/type              |
/// |4;n   |def   |2   |Introduce the n thing as the given name/value             |
/// |5;n   |n     |0   |Big unsigned int                                          |
/// |6;n   |hintcl|0   |Go back n claims and use this as a hint for the next claim|
/// |7;n   |hint  |0   |Hint that we're using logic rule n, defined in a separate table|
/// |8;n   |adv   |0   |Advance n bytes in the source file                        |
/// |9     |var   |1   |Push a variable to the proof stack                        |
/// |10    |popvar|0   |Pop a var off the proof stack                             |
/// |11    |hyp   |1   |Push a hypothesis to the proof stack                      |
/// |12    |pophyp|0   |Pop a hypothesis off the proof stack                      |
/// |13    |claim |1   |Try to prove the given boolean expression                 |
/// |14    |all   |2   |(var,bool) -> bool                                        |
/// |15    |exists|2   |(var,bool) -> bool                                        |
/// |16    |not   |1   |bool->bool                                                |
/// |17    |and   |2   |(bool,bool) -> bool                                       |
/// |18    |or    |2   |(bool,bool) -> bool                                       |
/// |19    |imp   |2   |(bool,bool) -> bool                                       |
/// |20    |iff   |2   |(bool,bool) -> bool                                       |
/// |21    |eq    |2   |(nat,nat) -> bool                                         |
/// |22-95 |      |    |Space for user-defined opcodes                            |
/// |96-127|0-31  |0   |Small unsigned int                                        |
/// |128   |end   |0   |End the script. Proof stack must be empty                 |
/// |129   |enderr|0   |End the script while indicating that errors occurred      |
/// |130   |fatal |0   |End the script early, indicating that processing could not continue|
/// |131   |startd|0   |Start a definition section, which hides everything that isn't exported|
/// |132   |endd  |0   |End a definition section                                  |
/// |133   |export|1   |Prove a bool and export it from the definition section    |
/// |134   |false |0   |The value "false"                                         |
/// |135   |true  |0   |The value "true"                                          |
/// |136   |bool  |0   |The type "bool"                                           |
/// |137   |nat   |0   |The type "nat"                                            |
/// |138   |prod  |2   |(type,type) -> type                                       |
/// |139   |func  |2   |(type,type) -> type                                       |
/// |140   |S     |1   |nat->nat                                                  |
/// |141   |add   |2   |(nat,nat) -> nat                                          |
/// |142   |mul   |2   |(nat,nat) -> nat                                          |
/// |143-255|(reserved)||Reserved. Abort if encountered.                          |
/// |256+  |      |    |Space for user-defined opcodes                            |
pub struct Interaction {
    input: Vec<u8>,
    output: Vec<u8>,
    opcode_args: HashMap<usize,usize>,
    pos: IPos,
}

impl Interaction {
    pub fn new(input: Vec<u8>) -> Self {
        Interaction {
            input,
            output: vec![],
            opcode_args: defaults(),
            pos: IPos { index: 0, remaining_expressions: 0, source_pos: 0 },
        }
    }
    pub fn read_element(&mut self) -> Result<Element,DecodingError> {
        let first = self.read_byte()?;
        if first == 0x80 {
            // binary vector
            let len = self.read_vlq()?;
            let vec = self.read_vec(len)?;
            Ok(Element::Bin(vec))
        } else {
        }
    }

    fn read_vec(&mut self, len:usize) -> Result<Vec<u8>,DecodingError> {
        let mut index2 = self.pos.index.checked_add(len).ok_or_else(||ErrorCode::InternalOverflow.at(self.pos))?;
        if index2 > self.input.len() {
            self.pos.index = self.input.len();
            return ErrorCode::UnexpectedEOF.at(self.pos);
        }
        let result = self.input[self.pos.index..index2].to_vec();
        self.pos.index = index2;
        Ok(result)
    }

    fn read_byte(&mut self) -> Result<u8,DecodingError> {
        if self.pos.index >= self.input.len() {
            return ErrorCode::UnexpectedEOF.at(self.pos);
        }
        let result = self.input[self.pos.index];
        self.pos.index += 1;
        Ok(result)
    }

    fn read_vlq(&mut self) -> Result<usize,DecodingError> {
        let next = self.read_byte()?;
        self.read_rest_of_vlq(next)
    }

    fn read_rest_of_vlq(&mut self, mut next: u8) -> Result<usize,DecodingError> {
        let mut result = 0;
        if next == 0x80 {
            return ErrorCode::InvalidVLQ.at(self.pos);
        }
        loop {
            result |= (next & 0x7f) as usize;
            if (next & 0x80) == 0 {
                break;
            }
            next = self.read_byte()?;
            result = result.checked_shl(7).ok_or_else(||ErrorCode.err(self.pos))?;
        }
        Ok(result)
    }
}

fn defaults() -> HashMap<usize,usize> {
    let mut result:HashMap<usize,usize> = HashMap::new();
    for (k,v) in [
        (ERROR,0),
        (INTRO,2),
        (DEF,2),
        (BIGINT,0),
        (HINTCL,0),
        (HINT,0),
        (ADV,0),
        (VAR,1),
        (POPVAR,0),
        (HYP,0),
        (POPHYP,0),
        (CLAIM,1),
        (ALL,2),
        (EXISTS,2),
        (NOT,1),
        (AND,2),
        (OR,2),
        (IMP,2),
        (IFF,2),
        (EQ,2),
        (END,0),
        (ENDERR,0),
        (FATAL,0),
        (STARTDEF,0),
        (ENDDEF,0),
        (EXPORT,1),
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
        result.insert(*k,*v);
    }
    for i in UINT_MIN..=UINT_MAX {
        result.insert(i,0);
    }
    result
}

pub fn opcode_takes_extra(opcode: usize) -> bool {
    match opcode {
        INTRO | DEF | BIGINT | HINTCL | HINT | ADV => true,
        _ => false
    }
}

pub fn opcode_is_expr(opcode: usize) -> bool {
    match opcode {
        BIGINT | EXPR_MIN..=EXPR_MAX | BIGEXPR_MIN.. => true,
        _ => false
    }
}

pub fn opcode_is_user(opcode: usize) -> bool {
    match opcode {
        USER_MIN..=USER_MAX | BIGUSER_MIN.. => true,
        _ => false
    }
}

pub fn opcode_is_quant(opcode: usize) -> bool {
    match opcode {
        ALL | EXISTS => true,
    }
}

struct OpcodeInfo {
}

type SPos = usize;

#[derive(Clone,Copy)]
struct IPos {
    source_pos: SPos,
    index: usize,
    //remaining_expressions: usize,
}

impl IPos {
    pub fn beginning() -> Self {
        IPos {
            source_pos: 0,
            index: 0
        }
    }

    pub fn backtrack(self, input: &[u8]) -> IPos {
        IPos {
            source_pos: self.source_pos,
            index: self.index - input.len(),
        }
    }

    pub fn advance(self, input: &[u8]) -> IPos {
        IPos {
            source_pos: self.source_pos,
            index: self.index + input.len(),
        }
    }

    pub fn advance_source(self, amount: usize) -> IPos {
        IPos {
            source_pos: self.source_pos + amount,
            index: self.index,
        }
    }
}

pub enum Element {
    Op(usize,usize),
    Extra(usize,usize,usize),
    Num(BigUint),
    Bin(Vec<u8>),
}

pub struct DecodingError {
    pub bpos: usize,
    pub pos: SPos,
    pub code: ErrorCode
}

pub enum ErrorCode {
    InternalOverflow,
    InvalidVLQ,
    MoreElementsToCome,
    NotACommand,
    NotAtAnExpression,
    OpcodeAlreadyUsed,
    StillExpressionsFromPreviousCommand,
    UnexpectedEndOfExpression,
    UnexpectedEOF,
    UnknownOpcode,
}

impl ErrorCode {
    fn at<T>(pos: IPos) -> Result<T,DecodingError> {
        Err(DecodingError{bpos: pos.index, pos: pos.source_pos, code: self})
    }
}
