use std::fs::{read_dir,read_to_string};
use clap::clap_app;
use crate::ast::Pos;
use crate::parse::parse;
use crate::verify::{verify,Code};

mod ast;
mod parse;
mod verify;

#[derive(Debug)]
pub struct ProcessingError {
    line: String,
    typ: ErrorType,
}

#[derive(Debug)]
pub enum ErrorType {
    Verification(Code),
    Parse,
    IO(std::io::Error),
    TestsFailed(Vec<String>),
    BadFileName,
    Unexpected,
}

impl ErrorType {
    fn nowhere(self) -> ProcessingError {
        ProcessingError {
            line: String::new(),
            typ: self
        }
    }
    fn at(self, pos:Pos, text:&str) -> ProcessingError {
        let linenum = text[..pos].lines().count();
        let lines:Vec<&str> = text.lines().collect();
        let line = if linenum >= lines.len() {
            "EOF".to_string()
        } else {
            format!("{} {}", linenum, lines[linenum])
        };
        ProcessingError{line, typ:self}
    }
}

impl From<std::io::Error> for ProcessingError {
    fn from(e: std::io::Error) -> Self {
        ErrorType::IO(e).nowhere()
    }
}

fn process(filename: &str) -> Result<(),ProcessingError> {
    let text = read_to_string(filename)?;
    let script = parse(&text)?;
    verify(&script).map_err(|e|ErrorType::Verification(e.code).at(e.pos, &text))?;
    Ok(())
}

fn run_tests() -> Result<(),ProcessingError> {
    let mut failures = vec![];
    for entry in read_dir("test/good")? {
        let entry = entry?;
        let path = entry.path();
        let filename = path.to_str().unwrap();
        if !path.file_name().unwrap().to_str().unwrap().starts_with('.') {
            match process(filename) {
                Ok(()) => println!("{:40} PASS", filename),
                Err(e) => {
                    println!("{:40} !!!! {:?}", filename, e);
                    failures.push(filename.to_string());
                }
            }
        }
    }
    for entry in read_dir("test/bad")? {
        let entry = entry?;
        let path = entry.path();
        let filename = path.to_str().unwrap();
        if !path.file_name().unwrap().to_str().unwrap().starts_with('.') {
            match process(filename) {
                Ok(()) => {
                    println!("{:40} !!!!", filename);
                    failures.push(filename.to_string());
                }
                Err(_) => println!("{:40} FAIL as expected", filename)
            }
        }
    }

    if !failures.is_empty() {
        return Err(ErrorType::TestsFailed(failures).nowhere())
    }

    Ok(())
}

fn main() -> Result<(),ProcessingError> {
    let matches = clap_app!(rust_pa =>
            (version: "0.1")
            (author: "Giles Edkins")
            (@arg INPUT: "Input file to validate")
            (@arg TEST: --test "Run tests, expecting test/good to pass and test/bad to fail")
    ).get_matches();

    if matches.is_present("TEST") {
        run_tests()?;
    } else {
        let filename = matches.value_of("INPUT").ok_or_else(||ErrorType::BadFileName.nowhere())?;
        process(filename)?;
    }
    
    Ok(())
}
