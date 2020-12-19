mod tokeniser;
mod ast;

fn main() {
    let filename = "fib.lal";
    let tokens = tokeniser::process(filename,
                       &tokeniser::read_source_file(filename));
    //tokens.iter().for_each(|c| println!("{}", c));

    let root_call = ast::build(tokens);
    println!("{}", root_call);
}
