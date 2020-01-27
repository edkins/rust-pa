fn read_slice(input: &[u8], len:usize) -> Result<(&[u8],&[u8]), ErrorCode> {
    let input2 = input.get(len..).ok_or(ErrorCode::UnexpectedEndOfExpression)?;
    let slice = &input[..len];
    Ok((input2,slice))
}

fn read_byte(input: &[u8]) -> Result<(&[u8],u8), ErrorCode> {
    if input.is_empty() {
        return ErrorCode::UnexpectedEndOfExpression;
    }
    Ok((&input[1..], input[0]))
}

fn read_vlq_as_slice(input: &[u8]) -> Result<(&[u8],&[u8]), ErrorCode> {
    let mut remainder = input;
    let mut first = true;
    loop {
        if let Some(next) = remainder.get(0) {
            if first && next == 0x80 {
                return ErrorCode::InvalidVLQ;
            }
            first = false;
            remainder = &remainder[1..];
            if (next & 0x80) == 0 {
                break;
            }
        } else {
            return ErrorCode::UnexpectedEndOfExpression;
        }
    }
    Ok((remainder, &input[..input.len() - remainder.len()]))
}

pub fn read_vlq(input: &[u8]) -> Result<(&[u8],usize), ErrorCode> {
    let mut result = 0;
    let (input,next) = self.read_byte(input)?;
    if next == 0x80 {
        return ErrorCode::InvalidVLQ;
    }
    loop {
        result |= (next & 0x7f) as usize;
        if (next & 0x80) == 0 {
            break;
        }
        if input.is_empty() {
            return ErrorCode::UnexpectedEndOfExpression;
        }
        next = input[0];
        input = &input[1..];
        result = result.checked_shl(7).ok_or(ErrorCode::InternalOverflow)?;
    }
    Ok(result)
}
