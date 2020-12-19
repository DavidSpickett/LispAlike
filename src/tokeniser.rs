use std::fmt;

#[derive(Debug, PartialEq)]
pub enum TokenType {
     // TODO: &str for th filename
     // Actual character, filename, line number, column number
     OpenBracket(char, String, usize, usize),
    CloseBracket(char, String, usize, usize),
       Character(char, String, usize, usize),
      Whitespace(char, String, usize, usize),
           Quote(char, String, usize, usize),
      SpeechMark(char, String, usize, usize),

      // Post normalisation tokens
          String(String, String, usize, usize),
      Definition(String, String, usize, usize),
         Integer(i64,    String, usize, usize),
          Symbol(String, String, usize, usize),
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenType::OpenBracket(c, fname, ln, cn) => write!(f,  "OpenBracket {} from {} at line {} col {}", c, fname, ln, cn),
           TokenType::CloseBracket(c, fname, ln, cn) => write!(f, "CloseBracket {} from {} at line {} col {}", c, fname, ln, cn),
              TokenType::Character(c, fname, ln, cn) => write!(f,    "Character {} from {} at line {} col {}", c, fname, ln, cn),
             TokenType::Whitespace(c, fname, ln, cn) => write!(f,   "Whitespace {} from {} at line {} col {}", c, fname, ln, cn),
                  TokenType::Quote(c, fname, ln, cn) => write!(f,        "Quote {} from {} at line {} col {}", c, fname, ln, cn),
             TokenType::SpeechMark(c, fname, ln, cn) => write!(f,   "SpeechMark {} from {} at line {} col {}", c, fname, ln, cn),
                 TokenType::String(s, fname, ln, cn) => write!(f,   "String \"{}\" from {} at line {} col {}", s, fname, ln, cn),
             TokenType::Definition(s, fname, ln, cn) => write!(f,  "Definition '{} from {} at line {} col {}", s, fname, ln, cn),
                TokenType::Integer(i, fname, ln, cn) => write!(f,      "Integer {} from {} at line {} col {}", i, fname, ln, cn),
                 TokenType::Symbol(s, fname, ln, cn) => write!(f,       "Symbol {} from {} at line {} col {}", s, fname, ln, cn),
        }
    }
}

pub fn token_to_file_position(token: TokenType) -> (String, usize, usize) {
    match token {
          TokenType::OpenBracket(_, file, ln, cn) => (file, ln, cn),
         TokenType::CloseBracket(_, file, ln, cn) => (file, ln, cn),
            TokenType::Character(_, file, ln, cn) => (file, ln, cn),
           TokenType::Whitespace(_, file, ln, cn) => (file, ln, cn),
                TokenType::Quote(_, file, ln, cn) => (file, ln, cn),
           TokenType::SpeechMark(_, file, ln, cn) => (file, ln, cn),
               TokenType::String(_, file, ln, cn) => (file, ln, cn),
           TokenType::Definition(_, file, ln, cn) => (file, ln, cn),
              TokenType::Integer(_, file, ln, cn) => (file, ln, cn),
               TokenType::Symbol(_, file, ln, cn) => (file, ln, cn),
    }
}

pub fn tokenise(filename: &str, input: &str) -> Vec<TokenType> {
    let mut tokens = Vec::new();

    for (line_number, l) in input.lines().enumerate() {
        for (column_number, c) in l.chars().enumerate() {
            // +1s since indexes begin at 0
            let token_line = line_number+1;
            let token_col = column_number+1;
            tokens.push(
                match c {
                    '('  =>  TokenType::OpenBracket(c, filename.to_string(), token_line, token_col),
                    ')'  => TokenType::CloseBracket(c, filename.to_string(), token_line, token_col),
                    '\'' =>        TokenType::Quote(c, filename.to_string(), token_line, token_col),
                    '"'  =>   TokenType::SpeechMark(c, filename.to_string(), token_line, token_col),
                    ' '  =>   TokenType::Whitespace(c, filename.to_string(), token_line, token_col),
                    _    =>    TokenType::Character(c, filename.to_string(), token_line, token_col),
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
            Some(TokenType::SpeechMark(_, ref filename, line_number, column_number)) => {
                match t {
                    TokenType::SpeechMark(_, _, _, _) => {
                        let got = current_string.take().unwrap();
                        // Merge into one string token
                        new_tokens.push(TokenType::String(got, filename.to_string(), line_number, column_number));
                        // Mark starting point as invalid
                        speech_mark_start = None;
                    },
                    _ => match current_string {
                        Some(ref mut s) => {
                            match t {
                                 TokenType::OpenBracket(c, _, _, _) => s.push(c),
                                TokenType::CloseBracket(c, _, _, _) => s.push(c),
                                       TokenType::Quote(c, _, _, _) => s.push(c),
                                   TokenType::Character(c, _, _, _) => s.push(c),
                                  TokenType::SpeechMark(c, _, _, _) => s.push(c),
                                  TokenType::Whitespace(c, _, _, _) => s.push(c),
                                _ => panic!("Unexpected token type! {}", t),
                            }
                        }
                        None => panic!("No string to append to!"),
                    }
                }
            }
            Some(_) => panic!("Speech mark start wasn't a speech mark token!"),
            None => match t {
                TokenType::SpeechMark(_, _, _, _) => {
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
            (TokenType::Whitespace(_, _, _, _), TokenType::Whitespace(_, _, _, _)) => true,
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
            Some(TokenType::Quote(_, ref filename, line_number, column_number)) => {
                match t {
                    TokenType::Character(c, _, _, _) => {
                        match current_definition_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_definition_string to push to!"),
                        }
                    }
                    // TODO: we're only allowing nested ' in definitions so we don't have
                    // to peek at what the breaking char is
                    TokenType::Quote(c, _, _, _) => {
                        match current_definition_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_definition_string to push to!"),
                        }
                    }
                    // Anything else finishes the identifier
                    _ => {
                        match current_definition_string {
                            Some(s) => {
                                new_tokens.push(TokenType::Definition(s, filename.to_string(), line_number, column_number));
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
                    TokenType::Quote(_, _, _, _) => {
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
            Some(TokenType::Character(_, ref filename, line_number, column_number)) => {
                match t {
                    TokenType::Character(c, _, _, _) => {
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
                                    Ok(v) => new_tokens.push(TokenType::Integer(v, filename.to_string(), line_number, column_number)),
                                    // Otherwise assume it's a symbol name
                                    // // TODO: don't allow numbers to start symbol names?
                                    Err(_) => new_tokens.push(TokenType::Symbol(s, filename.to_string(), line_number, column_number)),
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
                    TokenType::Character(c, _, _, _) => {
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

pub fn normalise_remove_whitespace(mut tokens: Vec<TokenType>) -> Vec<TokenType> {
    tokens.retain(|t| match t {
        TokenType::Whitespace(_, _, _, _) => false,
        _ => true,
    });
    tokens
}

pub fn normalise(tokens: Vec<TokenType>) -> Vec<TokenType> {
    normalise_remove_whitespace(
        normalise_numbers_symbols(
            normalise_definitions(
                normalise_whitespace(
                    normalise_strings(tokens)
                )
            )
        )
    )
}

pub fn tokens_to_str(tokens: Vec<TokenType>) -> String {
    tokens.iter().map(|t| match t {
         TokenType::OpenBracket(c, _, _, _) => String::from(c.clone()),
        TokenType::CloseBracket(c, _, _, _) => String::from(c.clone()),
           TokenType::Character(c, _, _, _) => String::from(c.clone()),
          TokenType::Whitespace(c, _, _, _) => String::from(c.clone()),
               TokenType::Quote(c, _, _, _) => String::from(c.clone()),
          TokenType::SpeechMark(c, _, _, _) => String::from(c.clone()),
              TokenType::String(s, _, _, _) => format!("\"{}\"", s.to_string()),
          TokenType::Definition(s, _, _, _) => format!("'{}", s.to_string()),
             TokenType::Integer(i, _, _, _) => format!("{}", i),
              TokenType::Symbol(s, _, _, _) => s.to_string(),
    }).collect()
}

pub fn process(filename: &str, input: &str) -> Vec<TokenType> {
    normalise(tokenise(filename, input))
}

#[cfg(test)]
mod tests {
    use tokeniser::TokenType;
    use tokeniser::tokenise;
    use tokeniser::process;

    #[test]
    fn test_tokenise() {
        assert_eq!(tokenise("<in>", "(+ 1 \n\
                             2)"),
        vec![
             TokenType::OpenBracket('(', "<in>".to_string(), 1, 1),
               TokenType::Character('+', "<in>".to_string(), 1, 2),
              TokenType::Whitespace(' ', "<in>".to_string(), 1, 3),
               TokenType::Character('1', "<in>".to_string(), 1, 4),
              TokenType::Whitespace(' ', "<in>".to_string(), 1, 5),
               TokenType::Character('2', "<in>".to_string(), 2, 1),
            TokenType::CloseBracket(')', "<in>".to_string(), 2, 2),
            ]);

        assert_eq!(tokenise("<foo>", "\"'\"'"),
            vec![
                TokenType::SpeechMark('"',  "<foo>".to_string(), 1, 1),
                     TokenType::Quote('\'', "<foo>".to_string(), 1, 2),
                TokenType::SpeechMark('"',  "<foo>".to_string(), 1, 3),
                     TokenType::Quote('\'', "<foo>".to_string(), 1, 4),
                ]);
    }

    #[test]
    fn test_normalise() {
        // Runs of characters between "" are made into strings
        // whitespace runs kept when in strings
        assert_eq!(process("<in>", "\" a b ()'  c\""),
                vec![TokenType::String(" a b ()'  c".to_string(), "<in>".to_string(), 1, 1)]);

        // Characters after a quote ' are definitions
        // ' is allowed in the definition name
        assert_eq!(process("<bla>", "('fo'o)"),
                vec![TokenType::OpenBracket('(', "<bla>".to_string(), 1, 1),
                     TokenType::Definition("fo'o".to_string(), "<bla>".to_string(), 1, 2),
                     TokenType::CloseBracket(')', "<bla>".to_string(), 1, 7)]);

        // Non string, non defintions are either symbols or numbers
        assert_eq!(process("<a>", "(123 a56)"),
                vec![TokenType::OpenBracket('(', "<a>".to_string(), 1, 1),
                     TokenType::Integer(123, "<a>".to_string(), 1, 2),
                     // Whitespace is removed as the final stage
                     TokenType::Symbol("a56".to_string(), "<a>".to_string(), 1, 6),
                     TokenType::CloseBracket(')', "<a>".to_string(), 1, 9)]);
    }
}
