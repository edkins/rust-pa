use std::fs::{read_dir,read_to_string};
use clap::clap_app;
use crate::kernel::ast::Pos;
use crate::kernel::parse::parse;
use crate::kernel::verify::{verify,Code};
use crate::high_level::guesswork::guess_justifications;
use crate::high_level::parse::high_level_parse;
use crate::high_level::translate::translate;
use crate::high_level::type_check::type_check;

mod high_level;
mod kernel;
mod tactic;

#[derive(Debug)]
pub struct ProcessingError {
    line: String,
    typ: ErrorType,
}

#[derive(Debug)]
pub enum ErrorType {
    Verification(Code),
    Translation(crate::high_level::translate::ErrorType),
    Guess(crate::high_level::guesswork::ErrorCode),
    TypeCheck(crate::high_level::type_check::ErrorCode),
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
        let mut linenum = text[..text.len() - pos].lines().count();
        let lines:Vec<&str> = text.lines().collect();
        let line = if linenum >= lines.len() {
            "EOF".to_string()
        } else {
            if linenum > 0 {
                linenum -= 1;
            }
            format!("{} {}", linenum + 1, lines[linenum])
        };
        ProcessingError{line, typ:self}
    }
}

impl From<std::io::Error> for ProcessingError {
    fn from(e: std::io::Error) -> Self {
        ErrorType::IO(e).nowhere()
    }
}

impl From<log::SetLoggerError> for ProcessingError {
    fn from(_: log::SetLoggerError) -> Self {
        ErrorType::Unexpected.nowhere()
    }
}

fn process_kernel(filename: &str) -> Result<(),ProcessingError> {
    let text = read_to_string(filename)?;
    let script = parse(&text).map_err(|e|ErrorType::Parse.at(e.pos, &text))?;
    verify(&script).map_err(|e|ErrorType::Verification(e.code).at(e.pos, &text))?;
    Ok(())
}

fn process_high_level(filename: &str) -> Result<(),ProcessingError> {
    let text = read_to_string(filename)?;
    let mut hscript = high_level_parse(&text).map_err(|e|ErrorType::Parse.at(e.pos, &text))?;
    type_check(&mut hscript).map_err(|e|ErrorType::TypeCheck(e.code).at(e.pos, &text))?;
    guess_justifications(&mut hscript).map_err(|e|ErrorType::Guess(e.code).at(e.pos, &text))?;
    let script = translate(&hscript).map_err(|e|ErrorType::Translation(e.typ).at(e.pos, &text))?;
    verify(&script).map_err(|e|ErrorType::Verification(e.code).at(e.pos, &text))?;
    Ok(())
}

fn read_dir_sorted(dir: &str) -> Result<Vec<String>,ProcessingError> {
    let mut result = vec![];
    for entry in read_dir(dir)? {
        let path = entry?.path();
        if !path.file_name().unwrap().to_str().unwrap().starts_with('.') {
            result.push(path.to_str().unwrap().to_string());
        }
    }
    result.sort();
    Ok(result)
}

fn run_tests() -> Result<(),ProcessingError> {
    let mut failures = vec![];
    for filename in &read_dir_sorted("test/kernel_good")? {
        match process_kernel(filename) {
            Ok(()) => println!("{:48} PASS", filename),
            Err(e) => {
                println!("{:48} !!!! {:?}", filename, e);
                failures.push(filename.to_string());
            }
        }
    }
    for filename in &read_dir_sorted("test/kernel_bad")? {
        match process_kernel(filename) {
            Ok(()) => {
                println!("{:48} !!!!", filename);
                failures.push(filename.to_string());
            }
            Err(_) => println!("{:48} FAIL as expected", filename)
        }
    }
    for filename in &read_dir_sorted("test/good")? {
        match process_high_level(filename) {
            Ok(()) => println!("{:48} PASS", filename),
            Err(e) => {
                println!("{:48} !!!! {:?}", filename, e);
                failures.push(filename.to_string());
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
            (@arg TEST: --test "Run tests, expecting test/kernel_good to pass and test/kernel_bad to fail")
            (@arg KERNEL: --kernel "Validate input file in kernel mode, without high-level checking")
            (@arg QUIET: -q "Disables logging output")
            (@arg VERBOSITY: -v +multiple "Set verbosity level of logging")
    ).get_matches();

    stderrlog::new()
        .module(module_path!())
        .quiet(matches.is_present("QUIET"))
        .verbosity(matches.occurrences_of("VERBOSITY") as usize)
        .timestamp(stderrlog::Timestamp::Millisecond)
        .init()?;

    if matches.is_present("TEST") {
        run_tests()?;
    } else {
        let filename = matches.value_of("INPUT").ok_or_else(||ErrorType::BadFileName.nowhere())?;
        if matches.is_present("KERNEL") {
            process_kernel(filename)?;
        } else {
            process_high_level(filename)?;
        }
    }
    
    Ok(())
}
