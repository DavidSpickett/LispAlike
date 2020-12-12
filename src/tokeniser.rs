use std::fmt;

#[derive(Debug, PartialEq)]
pub enum TokenType {
     OpenBracket(char, usize, usize),
    CloseBracket(char, usize, usize),
       Character(char, usize, usize),
      Whitespace(char, usize, usize),
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenType::OpenBracket(c, line_number, column_number) => write!(f, "{} at line {} col {}", c, line_number, column_number),
           TokenType::CloseBracket(c, line_number, column_number) => write!(f, "{} at line {} col {}", c, line_number, column_number),
              TokenType::Character(c, line_number, column_number) => write!(f, "{} at line {} col {}", c, line_number, column_number),
             TokenType::Whitespace(c, line_number, column_number) => write!(f, "{} at line {} col {}", c, line_number, column_number),
        }
    }
}

pub fn tokenise(input: &str) -> Vec<TokenType> {
    let mut tokens = Vec::new();

    for (line_number, l) in input.lines().enumerate() {
        for (column_number, c) in l.chars().enumerate() {
            tokens.push(
                match c {
                    // +1s since indexes begin at 0
                    '(' =>  TokenType::OpenBracket(c, line_number+1, column_number+1),
                    ')' => TokenType::CloseBracket(c, line_number+1, column_number+1),
                    ' ' =>   TokenType::Whitespace(c, line_number+1, column_number+1),
                    _   =>    TokenType::Character(c, line_number+1, column_number+1),
                });
        }
    }

    tokens
}

pub fn normalise_whitespace(mut tokens: Vec<TokenType>) -> Vec<TokenType> {
    tokens.dedup_by(|t1, t2| {
        match (t1, t2) {
            (TokenType::Whitespace(_, _, _), TokenType::Whitespace(_, _, _)) => true,
            // The comparison function removes t1 if t1 == t2
            // So this looks for "( ", not " (" as you might think.
            (TokenType::Whitespace(_, _, _), TokenType::OpenBracket(_, _, _)) => true,
            (_, _) => false
        }
    });

    tokens
}

pub fn tokens_to_str(tokens: Vec<TokenType>) -> String {
    tokens.iter().map(|t| match t {
        TokenType::OpenBracket(c, _, _) => c,
        TokenType::CloseBracket(c, _, _) => c,
        TokenType::Character(c, _, _) => c,
        TokenType::Whitespace(c, _, _) => c,
    }).collect()
}

#[cfg(test)]
mod tests {
    use tokeniser::TokenType;
    use tokeniser::tokenise;
    use tokeniser::normalise_whitespace;
    use tokeniser::tokens_to_str;

    #[test]
    fn basic_tokenise() {
        assert_eq!(tokenise("(+ 1 \n\
                             2)"),
        vec![
             TokenType::OpenBracket('(', 1, 1),
               TokenType::Character('+', 1, 2),
              TokenType::Whitespace(' ', 1, 3),
               TokenType::Character('1', 1, 4),
              TokenType::Whitespace(' ', 1, 5),
               TokenType::Character('2', 2, 1),
            TokenType::CloseBracket(')', 2, 2),
            ]);
    }

    #[test]
    fn normalise() {
        // >1 space -> 1 space
        assert_eq!(tokens_to_str(normalise_whitespace(tokenise("  "))), " ");
        // Whitespace after bracket is removed
        assert_eq!(tokens_to_str(normalise_whitespace(tokenise("(  a)"))), "(a)");
        // Whitespace before bracket is removed
        // TODO:??
        //assert_eq!(tokens_to_str(normalise_whitespace(tokenise("(a )"))), "(a)");
    }
}
