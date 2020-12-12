mod tokeniser;

fn main() {
    let tokens = tokeniser::tokenise("(+ 1 2)");
    tokens.iter().for_each(|c| print!("{}\n", c));
    println!("");
}
