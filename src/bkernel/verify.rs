use crate::binary::codes::*;
use crate::binary::deserialize::IPos;
use crate::binary::file::FileReader;
use crate::binary::hintcodes::*;

pub fn verify(input: &[u8]) -> Result<(),VerificationError> {
    Verifier::new(input)?.verify_all()?;
    Ok(())
}

struct Verifier<'a> {
    reader: FileReader<'a>,
    proof_stack: Vec<ProofStackItem<'a>>,
}

impl<'a> Verifier<'a> {
    fn new(input &'a[u8]) -> Result<Self,VerificationError> {
        let mut reader = FileReader::new(input)?;
        let mut proof_stack = vec![];

        Ok(Verifier {
            reader,
            proof_stack
        })
    }

    fn err<T>(code: ErrorCode) -> Result<T,VerificationError> {
        code.at(self.reader.pos())
    }
    
    fn verify_all(&mut self) -> Result<(),VerificationError> {
        loop {
            let cmd = self.reader.read_command()?;
            match cmd.op {
                ERROR => {
                    return ErrorCode::Upstream(cmd.extra).at(reader.pos());
                }
                DEF | HINTCL | HINT => {
                    panic!(); //TODO
                }
                INTRO | ADV => {
                    /* nothing to do */
                }
                VAR => {
                    let x = self.reader.expect_var()?;
                    self.proof_stack.push(ProofStackItem::Var(x));
                }
                POPVAR => {
                    if let Some(ProofStackItem::Var(_)) = self.proof_stack.pop() {
                        // ok
                    } else {
                        return ErrorCode::NotVarOnStack.at(reader.pos());
                    }
                }
                HYP => {
                    let stmt = self.read_well_formed_stmt()?;
                    self.proof_stack.push(ProofStackItem::Hyp(stmt));
                }
                POPHYP => {
                    if let Some(ProofStackItem::Hyp(_)) = self.proof_stack.pop() {
                        // ok
                    } else {
                        return ErrorCode::NotHypOnStack.at(reader.pos());
                    }
                }
                CLAIM => {
                    let stmt = self.read_well_formed_stmt()?;
                    self.prove_from_hints(stmt)?;
                }
            }
        }
    }

    fn prove_from_hints(stmt: &mut ExprReader<'a>) -> Result<(),VerificationError> {
        let depth = stmt.depth();
        if let Some(hint_code) = self.hint_code {
            match hint_code {
                HINT_EQUAL_INTRO => {
                    stmt.expect_opcode(EQUALS)?;
                    let lhs = stmt.read_expr()?;
                    stmt.expect_exact(lhs)?;
                }
                HINT_EQUAL_ELIM => {
                    panic!(): //TODO
                }
                HINT_FALSE_INTRO => {
                    let (prev,prev2) = self.hint_stmt2()?;
                    prev2.expect_opcode(NOT)?;
                    prev2.expect_exact(prev)?;
                    prev2.finish()?;
                    prev.finish()?;
                    stmt.expect_opcode(FALSE)?;
                }
                HINT_FALSE_ELIM => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(FALSE)?;
                    prev.finish()?;
                    stmt.read_expr()?;   // can be any valid statement
                }
                HINT_NOTNOT_ELIM => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(NOT)?;
                    prev.expect_opcode(NOT)?;
                    prev.expect_exact(stmt)?;
                    prev.finish()?;
                }
                HINT_AND_INTRO => {
                    let (prev,prev2) = self.hint_stmt2()?;
                    stmt.expect_opcode(AND)?;
                    stmt.expect_exact(prev)?;
                    stmt.expect_exact(prev2)?;
                    prev.finish()?;
                    prev2.finish()?;
                }
                HINT_AND_ELIML => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(AND)?;
                    prev.expect_exact(stmt)?;
                    prev.read_expr()?;   // RHS gets discarded
                    prev.finish()?;
                }
                HINT_AND_ELIMR => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(AND)?;
                    prev.read_expr()?;   // LHS gets discarded
                    prev.expect_exact(stmt)?;
                    prev.finish()?;
                }
                HINT_OR_INTROL => {
                    let prev = self.hint_stmt()?;
                    stmt.expect_opcode(OR)?;
                    stmt.expect_exact(prev)?;
                    stmt.read_expr()?;   // RHS can be any valid statement
                    prev.finish()?;
                }
                HINT_OR_INTROR => {
                    let prev = self.hint_stmt()?;
                    stmt.expect_opcode(OR)?;
                    stmt.read_expr()?;   // LHS can be any valid statement
                    stmt.expect_exact(prev)?;
                    prev.finish()?;
                }
                HINT_OR_ELIM => {
                    let (prev,prev2,prev3) = self.hint_stmt3()?;
                    prev.expect_opcode(OR)?;
                    prev2.expect_opcode(IMP)?;
                    prev3.expect_opcode(IMP)?;
                    expect3(prev, prev2, pre3)?;
                    expect3(stmt, prev2, pre3)?;
                    prev.finish()?;
                    prev2.finish()?;
                    prev3.finish()?;
                }
                HINT_IMP_ELIM => {
                    let (prev,prev2) = self.hint_stmt2()?;
                    prev.expect_opcode(IMP)?;
                    prev.expect_exact(prev2)?;
                    prev.expect_exact(stmt)?;
                    prev.finish()?;
                    prev2.finish()?;
                }
                HINT_IFF_INTRO => {
                    let (prev,prev2) = self.hint_stmt2()?;
                    prev.expect_opcode(IMP)?;
                    prev2.expect_opcode(IMP)?;
                    stmt.expect_opcode(IFF)?;

                    let a = prev2.read_expr()?;
                    expect3(stmt, prev, prev2)?;
                    expect3(stmt, prev, a)?;
                    prev.finish()?;
                    prev2.finish()?;
                }
                HINT_IFF_ELIML => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(IFF)?;
                    stmt.expect_opcode(IMP)?;
                    stmt.expect_exact(prev)?;
                    stmt.expect_exact(prev)?;
                    prev.finish()?;
                }
                HINT_IFF_ELIMR => {
                    let prev = self.hint_stmt()?;
                    prev.expect_opcode(IFF)?;
                    stmt.expect_opcode(IMP)?;
                    let a = prev.read_expr()?;
                    stmt.expect_exact(prev)?;
                    stmt.expect_exact(a)?;
                    prev.finish()?;
                }
                HINT_ALL_ELIM => {
                    let prev = self.hint_stmt()?;
                    let x = prev.expect_forall()?;
                    let mut subst = None;
                    expect_subst(prev, x, &mut subst, stmt)?;
                    prev.finish()?;
                }
            }
        } else {
            self.err(ErrorCode::Unhinted)
        }
        if stmt.depth() != depth - 1 {
            self.err(ErrorCode::DepthMismatch)
        }
    }

    fn has_bound_var(&self, x: usize) -> bool {
        for item in &self.proof_stack {
            if let ProofStackItem::Var(y) = item {
                if x == y {
                    return true;
                }
            }
        }
        return false;
    }

    fn check_well_formed(&mut self, expected_type: OpType, reader: &mut ExprReader<'a>, bindings: &mut Vec<usize>) -> Result<(),VerificationError> {
        let depth = reader.depth();
        let elem = reader.read_elem()?;
        let ft = elem.func_type();
        if ft.return_type() != expected_type {
            return ErrorCode::ExpectedType(expected_type).at(self.reader.pos());
        }

        match elem {
            Element::All(x) | Element::Exists(x) => {
                if self.has_bound_var(x) || bindings.contains(x) {
                    return ErrorCode::DoubleBinding.at(self.reader.pos());
                }
                bindings.push(x);
                self.check_well_formed(OpType::Bool, reader, bindings)?;
                bindings.pop();
            }
            _ => {
                for typ in ft.arg_types().iter().rev() {
                    self.check_well_formed(typ, reader, bindings)?;
                }
            }
        }

        if reader.depth() != depth - 1 {
            return ErrorCode::DepthMismatch.at(self.reader.pos());
        }
        Ok(())
    }

    fn read_well_formed_stmt(&mut self) -> Result<ExprReader<'a>,VerificationError> {
        Ok(self.reader.process_expr(|reader| {
            let clone = reader.clone();
            self.check_well_formed(OpType::Bool, reader, &mut vec![])?;
            Ok(clone)
        })?)
    }
}

fn expect_subst<'a>(before: &mut ExprReader<'a>, x: usize, subst: &mut Option<ExprReader<'a>>, vars_used: &mut HashSet<usize>, after: &mut ExprReader<'a>) -> Result<(),VerificationError> {
    let bdepth = before.depth()?;
    let adepth = after.depth()?;

    let belem = before.read_elem()?;

    if belem.is_op(x) {
        if belem.arity() != 0 {
            return ErrorCode::BadArity.at(before.pos());
        }
        match subst {
            Some(sub) => {
                after.read_exact(sub)?;
            }
            None => {
                *subst = Some(after.read_expr()?);
            }
        }
    } else {
        let aelem = after.read_elem()?;
        if aelem != belem {
            return ErrorCode::SubstMismatch.at(before.pos());
        }
        
        for _ in 0..aelem.arity() {
            expect_subst(before, x, subst, vars_used, after)?;
        }
    }

    if before.depth() != bdepth - 1 || after.depth() != adepth - 1 {
        return ErrorCode::DepthMismatch.at(before.pos());
    }
    Ok(())
}

fn expect3<'a>(x: &mut ExprReader<'a>, y: &mut ExprReader<'a>, z: &mut ExprReader<'a>) -> Result<(),VerificationError> {
    x.clone().expect(y)?;
    x.expect(z)?;
    Ok(())
}

enum ProofStackItem<'a> {
    Var(usize),
    Expr(ExprReader<'a>),
}

pub struct VerificationError {
    pos: IPos,
    code: ErrorCode
}

pub enum ErrorCode {
    Decode(crate::binary::deserialize::ErrorCode),
    ExpectedType(OpType),
    BadArity,
    DepthMismatch,
    NoMoreStack,
    NotHypOnStack,
    NotVarOnStack,
    SubstMismatch,
    Unhinted,
    Upstream(usize),
}

impl ErrorCode {
    fn at<T>(self, pos: IPos) -> Result<T,VerificationError> {
        Err(VerificationError {
            pos,
            code: self,
        }
    }
}
