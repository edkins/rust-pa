use std::fs::read_to_string;
use clap::clap_app;
use crate::parse::{parse,ParseError};
use crate::verify::{verify,VerificationError};

mod ast;
mod parse;
mod verify;

#[derive(Debug)]
enum ProcessingError {
    Verification(VerificationError),
    Parse(ParseError),
    IO(std::io::Error),
}

impl From<std::io::Error> for ProcessingError {
    fn from(e: std::io::Error) -> Self {
        ProcessingError::IO(e)
    }
}

impl From<ParseError> for ProcessingError {
    fn from(e: ParseError) -> Self {
        ProcessingError::Parse(e)
    }
}

impl From<VerificationError> for ProcessingError {
    fn from(e: VerificationError) -> Self {
        ProcessingError::Verification(e)
    }
}

fn main() -> Result<(),ProcessingError> {
    let matches = clap_app!(rust_pa =>
            (version: "0.1")
            (author: "Giles Edkins")
            (@arg INPUT: +required "Input file to validate")
    ).get_matches();

    let filename = matches.value_of("INPUT").unwrap();
    let text = read_to_string(filename)?;
    let script = parse(&text)?;
    verify(&script)?;
    
    Ok(())
}
