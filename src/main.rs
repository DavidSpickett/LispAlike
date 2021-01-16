use std::env;
use std::process;
mod ast;
mod debug;
mod exec;
mod tokeniser;
extern crate rand;

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
        Err(e) => exit_with_error(e),
        Ok(ts) => match ast::build(ts) {
            Err(e) => exit_with_error(e),
            Ok(ast) => match exec::exec(ast) {
                Ok(v) => println!("Return value: {}", v),
                Err(e) => exit_with_error(format!("{}\n{}", ast::format_call_stack(&e.1), e.0)),
            },
        },
    };
}
