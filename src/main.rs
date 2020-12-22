mod tokeniser;
mod ast;
mod exec;

fn main() {
    let filename = "fib.lal";
    let tokens = tokeniser::process_into_tokens(filename,
                       &tokeniser::read_source_file(filename));
    tokens.iter().for_each(|c| println!("{}", c));

    let root_call = ast::build(tokens);
    println!("{}", root_call);

    println!("Return value: {}", exec::exec(root_call));
}
