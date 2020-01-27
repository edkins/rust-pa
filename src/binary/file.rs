use crate::binary::deserialize::{IPos,DecodingError,opcode_takes_extra};
use crate::binary::expr::ExprReader;

pub struct FileReader<'a> {
    input: &'a[u8],
    pos: IPos,
    depth: usize,
}

pub struct Command {
    op: usize,
    extra: usize,
}

impl<'a> FileReader<'a> {
    pub fn new(input: &'a[u8]) -> Result<Self,DecodingError> {
        let pos = IPos::beginning();
        if input.get(..8) != Some(&[b'r',b's',b'P',b'A',1,0,0,0]) {
            return ErrorCode::InvalidMagicNumberOrVersion.at(pos);
        }
        FileReader {
            input: &input[8..],
            pos: pos.advance(&input[..8]),
            depth: 0
        }
    }

    pub fn pos() {
        self.pos
    }

    fn err<T>(&self, code: ErrorCode) -> Result<T,DecodingError> {
        code.at(self.pos)
    }

    fn read_command(&mut self) -> Result<Command, DecodingError> {
        if self.depth != 0 {
            return self.err(ErrorCode::StillExpressionsFromPreviousCommand);
        }

        let (input,op) = read_vlq(input).map_err(|e|self.err(e))?;

        self.depth = self.cmd_depth(op);

        let extra = if opcode_takes_extra(op) {
            read_vlq(input).map_err(|e|self.err(e))?;
        } else {
            0
        };

        if op == ADV {
            self.pos = self.pos.advance_source(extra);
        }

        Ok(Command{op, extra})
    }

    /// Call the given function with the next expression
    ///
    /// The callback pattern is used here because we need to resume where the expression finishes,
    /// and only the ExprReader knows this. (We want to avoid having to scan the expression twice,
    /// for efficiency reasons).
    ///
    /// If the tactic needs to scan the same expression multiple times, it can clone the
    /// ExprReader.
    ///
    /// The supplied function must consume the ExprReader right to the end, unless it returns an
    /// error.
    fn process_expr<T,E,F:FnOnce(&mut ExprReader<'a>) -> Result<T,E>>(&mut self, f: F) -> Result<T, E> {
        if self.depth == 0 {
            return self.err(ErrorCode::NotAtAnExpression);
        }

        self.depth -= 1;

        let mut reader = ExprReader::new(self.input);
        let result = f(&mut reader)?;

        self.input = reader.finish()?;
        Ok(result)
    }

    fn cmd_depth(&self, op: usize) -> Result<usize,DecodingError> {
        Ok(match op {
            ERROR | HINTCL | HINT | ADV | POPVAR | POPHYP | END | ENDERR | FATAL | STARTDEF | ENDDEF => 0,
            VAR | HYP | CLAIM | EXPORT => 1
            INTRO | DEF => 2,
            _ => return self.err(ErrorCode::NotACommand)
        })
    }
}
