use std::fmt;

#[derive(Debug, PartialEq)]
pub enum TokenType {
     OpenBracket(char, usize, usize),
    CloseBracket(char, usize, usize),
       Character(char, usize, usize),
      Whitespace(char, usize, usize),
           Quote(char, usize, usize),
      SpeechMark(char, usize, usize),

      // Post normalisation tokens
      String(String, usize, usize),
      Definition(String, usize, usize),
      Integer(i64, usize, usize),
      Symbol(String, usize, usize),
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenType::OpenBracket(c, line_number, column_number) => write!(f, "OpenBracket {} at line {} col {}", c, line_number, column_number),
           TokenType::CloseBracket(c, line_number, column_number) => write!(f, "CloseBracket {} at line {} col {}", c, line_number, column_number),
              TokenType::Character(c, line_number, column_number) => write!(f, "Character {} at line {} col {}", c, line_number, column_number),
             TokenType::Whitespace(c, line_number, column_number) => write!(f, "Whitespace {} at line {} col {}", c, line_number, column_number),
             TokenType::Quote(c, line_number, column_number) =>      write!(f, "Quote {} at line {} col {}", c, line_number, column_number),
             TokenType::SpeechMark(c, line_number, column_number) => write!(f, "SpeechMark {} at line {} col {}", c, line_number, column_number),
             TokenType::String(s, line_number, column_number) =>     write!(f, "String \"{}\" at line {} col {}", s, line_number, column_number),
             TokenType::Definition(s, line_number, column_number) =>  write!(f, "Definition '{} at line {} col {}", s, line_number, column_number),
             TokenType::Integer(i, line_number, column_number) =>  write!(f, "Integer {} at line {} col {}", i, line_number, column_number),
             TokenType::Symbol(s, line_number, column_number) =>  write!(f, "Symbol {} at line {} col {}", s, line_number, column_number),
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
                    '\'' => TokenType::Quote(c, line_number+1, column_number+1),
                    '"' => TokenType::SpeechMark(c, line_number+1, column_number+1),
                    ' ' =>   TokenType::Whitespace(c, line_number+1, column_number+1),
                    _   =>    TokenType::Character(c, line_number+1, column_number+1),
                });
        }
    }

    tokens
}

fn normalise_strings(tokens: Vec<TokenType>) -> Vec<TokenType> {
    // Convert all tokens within "" to a single string token
    let mut new_tokens = Vec::new();
    let mut current_string: Option<String> = None;
    let mut speech_mark_start : Option<TokenType> = None;
    for t in tokens {
        match speech_mark_start {
            Some(TokenType::SpeechMark(_, line_number, column_number)) => {
                match t {
                    TokenType::SpeechMark(_, _, _) => {
                        let got = current_string.take().unwrap();
                        // Merge into one string token
                        new_tokens.push(TokenType::String(got, line_number, column_number));
                        // Mark starting point as invalid
                        speech_mark_start = None;
                    },
                    _ => match current_string {
                        Some(ref mut s) => {
                            match t {
                                TokenType::OpenBracket(c, _, _)  => s.push(c),
                                TokenType::CloseBracket(c, _, _) => s.push(c),
                                TokenType::Quote(c, _, _)        => s.push(c),
                                TokenType::Character(c, _, _)    => s.push(c),
                                TokenType::SpeechMark(c, _, _)   => s.push(c),
                                TokenType::Whitespace(c, _, _)   => s.push(c),
                                _ => panic!("Unexpected token type! {}", t),
                            }
                        }
                        None => panic!("No string to append to!"),
                    }
                }
            }
            Some(_) => panic!("Speech mark start wasn't a speech mark token!"),
            None => match t {
                TokenType::SpeechMark(_, _, _) => {
                    current_string = Some(String::new());
                    speech_mark_start = Some(t);
                },
                _ => new_tokens.push(t),
            }
        }
    }

    new_tokens
}

fn normalise_whitespace(mut tokens: Vec<TokenType>) -> Vec<TokenType> {
    // Convert all whitespace to single whitespace
    tokens.dedup_by(|t1, t2| {
        match (t1, t2) {
            (TokenType::Whitespace(_, _, _), TokenType::Whitespace(_, _, _)) => true,
            (_, _) => false
        }
    });
    tokens
}

fn normalise_definitions(tokens: Vec<TokenType>) -> Vec<TokenType> {
    // Convert strings after quote into defintions
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut start_quote_char: Option<TokenType> = None;
    let mut current_definition_string: Option<String> = None;

    for t in tokens {
        match start_quote_char {
            Some(TokenType::Quote(_, line_number, column_number)) => {
                match t {
                    TokenType::Character(c, _, _) => {
                        match current_definition_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_definition_string to push to!"),
                        }
                    }
                    // TODO: we're only allowing nested ' in definitions so we don't have
                    // to peek at what the breaking char is
                    TokenType::Quote(c, _, _) => {
                        match current_definition_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_definition_string to push to!"),
                        }
                    }
                    // Anything else finishes the identifier
                    _ => {
                        match current_definition_string {
                            Some(s) => {
                                new_tokens.push(TokenType::Definition(s, line_number, column_number));
                                current_definition_string = None;
                                start_quote_char = None;
                                // Append breaking token as normal
                                new_tokens.push(t);
                            }
                            None => panic!("No current_definition_string to form token with!"),
                        }
                    }
                }
            }
            Some(_) => panic!("start_quote_char isn't a quote char!"),
            None => {
                match t {
                    // Starts a new definition
                    TokenType::Quote(_, _, _) => {
                        start_quote_char = Some(t);
                        current_definition_string = Some(String::new());
                    },
                    _ => new_tokens.push(t),
                }
            }
        }
    }

    new_tokens
}

pub fn normalise_numbers_symbols(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut starting_char: Option<TokenType> = None;
    let mut current_string: Option<String> = None;
    for t in tokens {
        match starting_char {
            Some(TokenType::Character(_, line_number, column_number)) => {
                match t {
                    TokenType::Character(c, _, _) => {
                        match current_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_string to push to!"),
                        }
                    }
                    // Anything else breaks the streak
                    _ => {
                        match current_string {
                            Some(s) => {
                                match s.parse::<i64>() {
                                    Ok(v) => new_tokens.push(TokenType::Integer(v, line_number, column_number)),
                                    // Otherwise assume it's a symbol name
                                    // // TODO: don't allow numbers to start symbol names?
                                    Err(_) => new_tokens.push(TokenType::Symbol(s, line_number, column_number)),
                                }

                                starting_char = None;
                                current_string = None;
                                new_tokens.push(t);
                            },
                            None => panic!("No current_string to attempt to parse!"),
                        }
                    }
                }
            }
            Some(_) => panic!("Starting char wasn't a Character token!"),
            None => {
                match t {
                    TokenType::Character(c, _, _) => {
                        starting_char = Some(t);
                        // Unlike strings etc, symbols start with the first char
                        // For a string we'd ignore the leading/closing ""
                        current_string = Some(String::from(c));
                    }
                    _ => new_tokens.push(t),
                }
            }
        }
    }

    new_tokens
}

pub fn normalise(tokens: Vec<TokenType>) -> Vec<TokenType> {
    normalise_numbers_symbols(
        normalise_definitions(
            normalise_whitespace(
                normalise_strings(tokens)
            )
        )
    )
}

pub fn tokens_to_str(tokens: Vec<TokenType>) -> String {
    tokens.iter().map(|t| match t {
        TokenType::OpenBracket(c, _, _) => String::from(c.clone()),
        TokenType::CloseBracket(c, _, _) => String::from(c.clone()),
        TokenType::Character(c, _, _) => String::from(c.clone()),
        TokenType::Whitespace(c, _, _) => String::from(c.clone()),
        TokenType::Quote(c, _, _) => String::from(c.clone()),
        TokenType::SpeechMark(c, _, _) => String::from(c.clone()),
        TokenType::String(s, _, _) => format!("\"{}\"", s.to_string()),
        TokenType::Definition(s, _, _) => format!("'{}", s.to_string()),
        TokenType::Integer(i, _, _) => format!("{}", i),
        TokenType::Symbol(s, _, _) => s.to_string(),
    }).collect()
}

#[cfg(test)]
mod tests {
    use tokeniser::TokenType;
    use tokeniser::tokenise;
    use tokeniser::normalise;
    use tokeniser::tokens_to_str;

    #[test]
    fn test_tokenise() {
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

        assert_eq!(tokenise("\"'\"'"),
            vec![
                TokenType::SpeechMark('"', 1, 1),
                     TokenType::Quote('\'', 1, 2),
                TokenType::SpeechMark('"', 1, 3),
                     TokenType::Quote('\'', 1, 4),
                ]);
    }

    #[test]
    fn test_normalise() {
        // Any runs of >1 space become just 1 space
        assert_eq!(tokens_to_str(normalise(tokenise("  "))), " ");

        // Runs of characters between "" are made into strings
        // whitespace runs kept when in strings
        assert_eq!(normalise(tokenise("\" a b ()'  c\"")),
                vec![TokenType::String(" a b ()'  c".to_string(), 1, 1)]);

        // Characters after a quote ' are definitions
        // ' is allowed in the definition name
        assert_eq!(normalise(tokenise("('fo'o)")),
                vec![TokenType::OpenBracket('(', 1, 1),
                     TokenType::Definition("fo'o".to_string(), 1, 2),
                     TokenType::CloseBracket(')', 1, 7)]);

        // Non string, non defintions are either symbols or numbers
        assert_eq!(normalise(tokenise("(123 a56)")),
                vec![TokenType::OpenBracket('(', 1, 1),
                     TokenType::Integer(123, 1, 2),
                     TokenType::Whitespace(' ', 1, 5),
                     TokenType::Symbol("a56".to_string(), 1, 6),
                     TokenType::CloseBracket(')', 1, 9)]);
    }
}
