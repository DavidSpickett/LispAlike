mod tokeniser;
mod ast;

fn main() {
    let filename = "fib.lal";
    tokeniser::process(filename,
                       &tokeniser::read_source_file(filename))
                           .iter().for_each(|c| println!("{}", c));
}
