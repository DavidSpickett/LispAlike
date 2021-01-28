use std::env;
use std::process;
mod ast;
mod debug;
mod exec;
mod tokeniser;
extern crate rand;

use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;
use tokeniser::{padding, SourceError};

// Format a string like:
// (foo 1 2)
//      ^
// This will never panic, just return a string
// describing the read failure. So you can always
// print something.
//
// It will have a newline at the start so you can just
// append it to any existing error.
pub fn get_source_line(err: &SourceError) -> String {
    match err.line_number {
        Some(ln) => {
            let file = File::open(Path::new(&err.filename));

            match file {
                // Return something so we can still print tokens with pseudo files
                Err(_) => format!("<Couldn't open source file {}>", err.filename),
                Ok(file) => {
                    // -1 because lines start at 1 but indexes at 0
                    match BufReader::new(file).lines().nth(ln - 1) {
                        None => format!(
                            "<Couldn't read line {} from source file {}>",
                            ln, err.filename
                        ),
                        Some(line_result) => match line_result {
                            Err(e) => format!(
                                "<Couldnt' read line {} from source file {}: {}>",
                                ln,
                                err.filename,
                                e.to_string()
                            ),
                            // -1 because columns start at 1 but indexes at 0
                            Ok(l) => match err.column_number {
                                Some(cn) => format!("\n{}\n{}^", l, padding(cn - 1)),
                                None => format!("\n{}", l),
                            },
                        },
                    }
                }
            }
        }
        None => String::new(),
    }
}

fn exit_with_error(error: String) -> ! {
    eprintln!("{}", error);
    process::exit(1);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        exit_with_error("Expected exactly 1 argument (the source file name)".to_string());
    }

    match tokeniser::tokenise_file(&args[1]) {
        Err(e) => exit_with_error(format!("{}", e)),
        Ok(ts) => match ast::build(ts) {
            Err(e) => exit_with_error(format!("{}", e)),
            Ok(ast) => match exec::exec(ast) {
                Ok(v) => println!("Return value: {}", v),
                Err(e) => exit_with_error(format!(
                    "{}\n{}{}",
                    ast::format_call_stack(&e.1),
                    e.0,
                    get_source_line(&e.0)
                )),
            },
        },
    };
}
