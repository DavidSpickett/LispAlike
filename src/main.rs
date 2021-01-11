use std::env;
use std::process;
mod tokeniser;
mod ast;
mod exec;
mod debug;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        panic!("Expected exactly 1 argument (the source file name)");
    }

    match exec::exec(ast::build(tokeniser::tokenise_file(&args[1]))) {
        Ok(v) => println!("Return value: {}", v),
        Err(e) => {
            eprintln!("{}\n{}", ast::format_call_stack(&e.1), e.0);
            process::exit(1);
        }
    };
}
