use std::env;
mod tokeniser;
mod ast;
mod exec;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        panic!("Expected exactly 1 argument (the source file name)");
    }

    println!("Return value: {}",
        exec::exec(
            ast::build(
                tokeniser::tokenise_file(&args[1])
            )
        )
    );
}
