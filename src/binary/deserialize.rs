use crate::high_level::ast::*;

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
/// Expressions have a length (in bytes). This length is assumed to be known ahead of time.
///
/// Expressions have a header and either zero, one or two arguments.
///
/// Two-arg expressions
/// ===================
///
/// Two-arg expressions are encoded starting with the length of the first (left) subexpression.
/// This looks a bit like a VLQ, but is one bit short because the top bit indicates that it's this
/// kind of expression. The second part of the header is another VLQ indicating the node type.
///
/// So a short two-arg expression would be encoded as follows:
///
/// 10xxxxxx 0nnnnnnn LLLLLLLL .... RRRRRRRR ....
///
/// where x gives the length (which must be nonzero), and n gives the node type.
///
/// A longer two-arg expression might be encoded as follows:
///
/// 11xxxxxx 1xxxxxxx 0xxxxxxx 1nnnnnnn 0nnnnnnn LLLLLLLLL ........ RRRRRRRR ......
///
/// Note that here, both the LHS-length and the node type are written in extended form, starting
/// with a 1 bit.
///
/// Also note that a special node type exists to join together extra arguments for things that need
/// three or more subexpressions.
///
/// If the LHS-length would exceed the expression length, it's invalid.
///
/// Zero- and one-arg expressions
/// =============================
///
/// These are distinguished from two-sub expressions by the top bit being zero.
///
/// One and zero arg expressions are distinguished from each other by their length. That is, if
/// there's room for an argument, then there's an argument.
///
/// Zero-arg expressions are written like this:
///
/// 00xxxxxx
/// 01xxxxxx 0xxxxxxx
/// 01xxxxxx 1xxxxxxx 0xxxxxxx
///
/// One-arg expressions are written like this:
///
/// 00xxxxxx LLLLLLLL ....
/// 01xxxxxx 0xxxxxxx LLLLLLLL ....
/// 01xxxxxx 1xxxxxxx 0xxxxxxx LLLLLLLL ....
///
/// Raw binary data
/// ===============
///
/// The byte 10000000 leads raw binary data. This does not conflict with the two-arg expression
/// encoding because the LHS expression length must be nonzero. The length of the expression is
/// used to determine the length of the binary data.
///
/// Binary strings that are different lengths but otherwise the same (with leading or trailing
/// zeros) are considered nonequal. Hence, binary data is considered different from unsigned
/// integers (unless there's additional interpretation).
///
/// File structure
/// --------------
/// The file starts with the magic number "rsPA" (0x72735041 in big-endian). It then consists of a
/// version number, the 32-bit big-endian encoded value 1. It then contains an expression, which
/// must be of type Script. Then it ends with the magic number again.
///
/// So a valid file would be:
///
/// 0x72 0x73 0x50 0x41
/// 0x01 0x00 0x00 0x00
/// ...
/// 0x72 0x73 0x50 0x41
///
/// Namespaces
/// ----------
/// The above spec allows one to interpret the structure of a binary blob, but not its
/// interpretation. That is, the "node types" must be mapped to some semantics. This is the job of
/// namespaces.
///
/// There are actually four namespaces:
/// - The zero-arg namespace
/// - The one-arg namespace
/// - The two-arg namespace
/// - The raw binary namespace
///
/// | Namespace | Indexed by      |Builtins?| Constants? |Bindables?|Interp fn?  |
/// |-----------|-----------------|---------|------------|----------|------------|
/// | Zero-arg  | natural numbers | Yes     | Yes        | Yes      |Sub-range   |
/// | One-arg   | natural numbers | Yes     | Yes        | HOL only |No          |
/// | Two-arg   | natural numbers | Yes     | Yes        | HOL only |No          |
/// | Byte vec  | byte vectors    | No      | No         | No       |Entire range|
///
/// You can think of each namespace as a partial function from (natural numbers or byte vectors) to
/// "things". If there's a gap in the partial function then the module is invalid.
///
/// But this partial function is built up of sub-functions, which either map a single item or a
/// range of items to a particular interpretation.
///
/// In the case of builtins and constants, they are mapped one at a time to a particular
/// interpretation. In the case of bindables, a range of them is assigned to be "bindable" but they
/// are then bound individually. In the case of an interpretation function, a function is specified
/// which maps a range to an output range. (For byte vecs, this must be the entire range).
///
/// Types
/// -----
/// Every expression has a type, which can be calculated easily. Advanced type systems are not
/// handled here, and must be handled as an additional layer.
///
/// Each namespace entry specifies the type exactly, with the exception of:
/// - error, which is transparent in its type (any module can wrap any part of an expression in an
/// error node to indicate there was a problem with it)
/// - comma, which is used to provide extra arguments to three-or-more-argument functions. The
/// function itself determines the relevant types.
///
/// The builtin namespace
/// ---------------------
/// The builtin namespaces occupy a contiguous region. The more "useful" ones are given one-byte
/// opcodes, and the less commonly used ones are given two-byte codes. This allows more of the
/// one-byte space to be occupied by user-defined stuff, without conflict.
///
/// Zero-args:
///
/// |Code|Name           |Type     |
/// |----|---------------|---------|
/// |64  |False          |Bool     |
/// |65  |True           |Bool     |
/// |66  |Bool           |Type     |
/// |67  |Nat            |Type     |
/// |66  |Empty_addendum |Addendum |
///
/// One-arg:
/// |Code|Name          |Type     |Arg type |
/// |----|--------------|---------|---------|
/// |62  |Not           |Bool     |Bool     |
/// |63  |S             |Nat      |Nat      |
/// |64  |PA (2-byte)   |Script   |Addendum |
/// |65  |Pop           |Addendum |Addendum |
///
/// Two-args:
///
/// |Code|Name          |Type     |LHS type |RHS type           |
/// |----|--------------|---------|---------|-------------------|
/// |54  |And           |Bool     |Bool     |Bool               |
/// |55  |Or            |Bool     |Bool     |Bool               |
/// |56  |Imp           |Bool     |Bool     |Bool               |
/// |57  |Iff           |Bool     |Bool     |Bool               |
/// |58  |Eq_nat        |Bool     |Nat      |Nat                |
/// |59  |Add           |Nat      |Nat      |Nat                |
/// |60  |Mul           |Nat      |Nat      |Nat                |
/// |61  |All           |Bool     |var.Nat  |Bool               |
/// |62  |Exists        |Bool     |var.Nat  |Bool               |
/// |63  |Comma         |<T,U>    |<T>      |<U>                |
/// |64  |Error         |<T>      |utf-8    |<T>                |
/// |65  |Functype (->) |Type     |Type     |Type               |
/// |66  |Product       |Type     |Type     |Type               |
/// |68  |With_intro    |Addendum |lit.Nat  |utf-8,Type,Addendum|
/// |69  |With_var      |Addendum |lit.Nat  |utf-8,Type,Addendum|
/// |70  |With_axiom    |Addendum |lit.Nat  |Bool,Addendum      |
/// |71  |With_def      |Addendum |lit.Nat  |Bool,Addendum      |
/// |72  |With_lemma    |Addendum |lit.Nat  |Bool,Addendum      |
/// |73  |With_builtin  |Addendum |lit.Nat  |Nat,Nat,Addendum   |
/// |74  |With_smallnat |Addendum |lit.Nat  |Nat,Nat,Addendum   |
/// |75  |With_bignat   |Addendum |lit.Nat  |Nat,Addendum       |
/// |76  |Push_var      |Addendum |lit.Nat  |Addendum           |
/// |77  |Push_hyp      |Addendum |Bool     |Addendum           |
///
/// It might seem to make more sense to have operators that append something to a script, rather
/// than prepending it, since a valid script consists of a shorter valid script with stuff
/// appended. The reason for doing it this way was to allow streaming: the start of a file can be
/// processed, and partial output generated, without knowing how the file will end.
///
/// Let's try again
/// ---------------
///
/// One-byte expressions:
///
/// |Bits       |Args|Header|
/// |-----------|----|------|
/// |xxxxxxxx   |0   |1 byte|
///
/// Two-byte expressions:
///
/// |Bits               |Args|Header |
/// |-------------------|----|-------|
/// |0xxxxxxx yyyyyyyy  |1   |1 byte |
/// |1xxxxxxx xxxxxxxx  |0   |2 bytes|
///
/// Three-byte expressions:
///
/// |Bits                       |Args|Header |
/// |---------------------------|----|-------|
/// |00xxxxxx yyyyyyyy zzzzzzzz |2   |1 byte |
/// |01xxxxxx yyyyyyyy yyyyyyyy |1   |1 byte |
/// |1xxxxxxx 0xxxxxxx yyyyyyyy |1   |2 bytes|
/// |1xxxxxxx 1xxxxxxx xxxxxxxx |0   |3 bytes|
///
/// Four-byte expressions:
///
/// |Bits                               |Args|Header |
/// |-----------------------------------|----|-------|
/// |000xxxxx yyyyyyyy zzzzzzzz zzzzzzzz|2   |1 byte |
/// |001xxxxx yyyyyyyy yyyyyyyy zzzzzzzz|2   |1 byte |
/// |010xxxxx yyyyyyyy yyyyyyyy yyyyyyyy|1   |1 byte |
/// |1xxxxxxx 00xxxxxx yyyyyyyy zzzzzzzz|2   |2 bytes|
/// |1xxxxxxx 01xxxxxx yyyyyyyy yyyyyyyy|1   |2 bytes|
/// |1xxxxxxx 1xxxxxxx 0xxxxxxx yyyyyyyy|1   |3 bytes|
/// |1xxxxxxx 1xxxxxxx 1xxxxxxx 0xxxxxxx|0   |4 bytes|
///
/// That's nice, but let's try again
/// --------------------------------
/// There are two stacks: the expression stack and the proof stack.
///
/// The expression stack allows expressions to be written in reverse-Polish notation: depending on
/// their type, opcodes will pop some number of values off the stack and push a single value.
///
/// The proof stack is separate and may only be manipulated when the expression stack is empty. It
/// allows universally-quantified variables to enter scope, and hypotheses to be introduced. Things
/// can be defined when the proof stack is nonempty, but when items are popped off the proof stack
/// those definitions will acquire a "forall x" or "P ->" at the front.
///
/// Opcodes are encoded as VLQ. Opcodes 1, 2 and 3 take a second integer.
///
/// Binary data can be encoded, with an 0x80 byte followed by VLQ-encoded length, followed by the
/// binary data itself.
///
/// Some opcodes
/// ============
///
/// |Opcode| Name |Operation                                                 |
/// |------|------|----------------------------------------------------------|
/// |0     |NULL  |Invalid opcode. Immediately abort processing.             |
/// |1;n   |Error |Error, with error code.                                   |
/// |2;n   |intro |Pop a utf-8 and a type off the expr stack. Introduce the next thing as that name/type. Cannot redefine control codes|
/// |3;n   |n     |Big unsigned int                                          |
/// |4;n   |hintcl|Go back n claims and use this as a hint for the next claim|
/// |5;n   |hint  |Hint that we're using logic rule n, defined in a separate table|
/// |10    |var   |Pop the final variable off the expr stack. Push it to proof stack|
/// |11    |popvar|Pop a var off the proof stack. Expr stack must be empty  |
/// |12    |hyp   |Pop a bool off the expr stack. Push it to proof stack    |
/// |13    |pophyp|Pop a hyp off the proof stack. Expr stack must be empty  |
/// |14    |claim |Pop the final bool off the expr stack. Fail if not provable|
/// |15    |def   |Pop the final bool off the expr stack and define it to be true. May fail|
/// |16    |adv   |Pop a nat off the expr stack, and advance that many bytes in the source file|
/// |17    |all   |Pop a bool and a variable off the expr stack. Push a bool |
/// |18    |exists|Pop a bool and a variable off the expr stack. Push a bool |
/// |55    |not   |bool->bool                                                |
/// |56    |S     |nat->nat                                                  |
/// |57    |and   |(bool,bool) -> bool                                       |
/// |58    |or    |(bool,bool) -> bool                                       |
/// |59    |imp   |(bool,bool) -> bool                                       |
/// |60    |iff   |(bool,bool) -> bool                                       |
/// |61    |eq    |(nat,nat) -> bool                                         |
/// |62    |add   |(nat,nat) -> nat                                          |
/// |63    |mul   |(nat,nat) -> nat                                          |
/// |64-127|0-64  |Small unsigned ints, until overridden with intro.         |
/// |0x80;n|binary|n indicates length. Push a vector of bytes.               |
/// |128   |End   |Ends the script. Both stacks must be empty.               |
/// |129   |EndErr|Ends the script and states that errors occurred.          |
/// |130   |false |Push false                                                |
/// |131   |true  |Push true                                                 |
/// |132   |Bool  |Push the type "bool"                                      |
/// |133   |Nat   |Push the type "nat"                                       |
/// |134   |Prod  |(type,type) -> type                                       |
/// |135   |Func  |(type,type) -> type                                       |
pub fn deserialize(data: &[u8]) -> HScript {
}

pub struct DecodingError {
    pub bpos: usize,
    pub pos: HPos,
    pub code: ErrorCode
}

pub enum ErrorCode {
    InvalidVLQ,
    LHSTooLong,
}
