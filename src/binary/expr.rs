use crate::binary::deserialize::{IPos,DecodingError};
use crate::binary::lowlevel::{Element,read_element};
use crate::binary::opmap::OpMap;

/// Performs a depth-first traversal of an expression.
///
/// Elements can be read one at a time, or entire subexpressions can be parsed and returned as one
/// lump. (The subexpression thing will be less efficient if you then need to dive into the
/// subexpression again, since the internal structure of the subexpression is not recorded).
///
/// Cloning is most useful at the beginning, to allow you to traverse the expression multiple
/// times.
#[derive(Clone)]
pub struct ExprReader<'a> {
    input: &'a[u8],
    pos_at_end: IPos,
    map: &'a OpMap,
    depth: usize,
}

#[derive(Clone,Copy)]
pub enum OpType {
    Bool,
    Nat,
    Bin,
}

#[derive(Clone)]
pub enum FuncType {
    B,
    N,
    B_to_B,
    N_to_N,
    BB_to_B,
    NN_to_B,
    NN_to_N,
    Bin,
    Custom(Vec<OpType>),
}

impl FuncType {
    fn return_type(&self) -> OpType {
        match self {
            B | B_to_B | BB_to_B | NN_to_B => OpType::Bool,
            N | N_to_N | NN_to_N => OpType::Nat,
            Bin => OpType::Bin,
            Custom(ts) => ts[ts.len()-1],
        }
    }

    fn arg_types(&self) -> &[OpType] {
        match self {
            B | N | Bin => &[],
            B_to_B => &[OpType::Bool],
            N_to_N => &[OpType::Nat],
            BB_to_B => &[OpType::Bool,OpType::Bool],
            NN_to_B | NN_to_N => &[OpType::Nat,OpType::Nat],
            Custom(ts) => &ts[..ts.len()-1],
        }
    }
}

#[derive(Clone)]
pub enum ExprElem<'a> {
    OpCode(usize,usize,FuncType),
    All(usize),
    Exists(usize),
    BigNatVLQ(&'a[u8]),
    Bin(&'a[u8]),
}

impl<'a> ExprElem<'a> {
    pub fn arity(&self) -> usize {
        match elem {
            Element::OpCode(_,arity,_) => arity,
            Element::All(_) | Element::Exists(_) => 1,
            Element::BigNatVLQ(_) | Element::Bin(_) => 0,
        }
    }

    pub fn func_type(&self) -> FuncType {
        match elem {
            Element::OpCode(_,_,ft) => ft,
            Element::All(_) | Element::Exists(_) => FuncType::B_to_B,
            Element::BigNatVLQ(_) => FuncType::N,
            Element::Bin(_) => FuncType::Bin,
        }
    }
}

impl<'a> ExprReader<'a> {
    pub fn new(input: &'a[u8], pos: IPos, map: &'a OpMap) -> Self {
        ExprReader {
            input,
            pos_at_end: pos.advance(input),
            map,
            depth: 1
        }
    }

    fn err<T>(code: ErrorCode) -> Result<T,DecodingError> {
        code.at(self.pos())
    }

    fn pos(&self) -> IPos {
        self.pos_at_end.backtrack(self.input)
    }

    fn depth(&self) -> usize {
        self.depth
    }

    fn type_of(&self, elem: Element<'a>) -> Result<OpType,DecodingError> {
        match elem {
            Element::OpCode(op) | self.map.type_of(op),
            Element::BigNatVLQ(_) => Ok(OpType::Nat),
            Element::Bin(_) | Element::Quant(op,ALL) | Element::Quant(op,EXISTS) => Ok(OpType::Binary),
        }
    }

    /// Call this when you're done to make sure the right number of elements have been read
    ///
    /// Consumes the reader and returns the remaining input slice.
    pub fn finish(self) -> Result<&'a[u8], DecodingError> {
        if self.depth != 0 {
            return self.err(ErrorCode::MoreElementsToCome);
        }
        Ok(self.input)
    }

    /// Reads one element in the depth-first traversal, starting from the expression root.
    ///
    /// Will return either an OpCode or a binary slice.
    ///
    /// Will fail if the input is not a valid expression representation, contains an unknown opcode
    /// or if you try to read beyond the end of the expression.
    pub fn read_elem(&mut self) -> Result<Element<'a>, DecodingError> {
        if self.depth == 0 {
            return self.err(ErrorCode::NoMoreElements);
        }
        let (input, op) = read_vlq(self.input).map_err(|e|self.err(e))?;
        self.depth -= 1;
        match op {
            BIN => {
                let (input,len) = read_vlq(input)?;
                let (input,slice) = read_slice(input,len)?;
                self.input = input;
                Ok(ExprElem::Bin(slice))
            }
            BIGINT => {
                let (input,slice) = read_vlq_as_slice(input)?;
                self.input = input;
                Ok(ExprElem::BigNatVLQ(slice))
            }
            ALL => {
                let (input,x) = read_vlq(input)?;
                self.input = input;
                self.depth += 1;
                Ok(ExprElem::All(x))
            }
            EXISTS => {
                let (input,x) = read_vlq(input)?;
                self.input = input;
                self.depth += 1;
                Ok(ExprElem::Exists(x))
            }
            _ => {
                let (arity,typ) = self.map.arity_and_type(op)?;
                self.input = input;
                self.depth += arity;
                Ok(ExprElem::OpCode(op,arity,typ))
            }
        }
        Ok(elem)
    }

    fn consume_until_end(&mut self, initial_depth: usize) -> Result<(), DecodingError> {
        loop {
            if self.depth < initial_depth {
                break;
            }
            let _ = self.read_elem()?;
        }
    }

    pub fn read_expr(&mut self) -> Result<ExprReader<'a>, DecodingError> {
        let initial_depth = self.depth;
        let initial_input = self.input;

        self.consume_until_end(initial_depth)?;

        let len = initial_input.len() - self.input.len();
        Ok(ExprReader {
            input: &initial_input[..len],
            pos_at_end: self.pos(),
            map: self.map,
            depth: 1
        })
    }

    pub fn expect_var(&mut self) -> Result<usize, DecodingError> {
        let initial_depth = self.depth;

        if let Element::OpCode(op) = sel.read_elem()? {
            if self.map.is_var(op)? {
                return op;
            }
        }

        self.consume_until_end(initial_depth)?;
        self.err(ErrorCode::NotAVar)
    }
}
