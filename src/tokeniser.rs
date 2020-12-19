use std::fmt;
use std::fs;
use std::io::BufReader;
use std::io::BufRead;
use std::error::Error;
use std::fs::File;
use std::path::Path;

//TODO: not the best place for this to live
pub fn read_source_file(filename: &str) -> String {
    fs::read_to_string(filename)
        .expect(&format!("Couldn't open source file {}", filename))
}

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

pub fn token_to_file_position(token: &TokenType) -> (String, usize, usize) {
    match token {
          TokenType::OpenBracket(_, file, ln, cn) |
         TokenType::CloseBracket(_, file, ln, cn) |
            TokenType::Character(_, file, ln, cn) |
           TokenType::Whitespace(_, file, ln, cn) |
                TokenType::Quote(_, file, ln, cn) |
           TokenType::SpeechMark(_, file, ln, cn) |
               TokenType::String(_, file, ln, cn) |
           TokenType::Definition(_, file, ln, cn) |
              TokenType::Integer(_, file, ln, cn) |
               TokenType::Symbol(_, file, ln, cn) => (file.to_string(), *ln, *cn),
    }
}

pub fn get_source_line_from_token(t: &TokenType) -> String {
    let (filename, ln, cn) = token_to_file_position(t);
    let file = match File::open(Path::new(&filename)) {
        Err(why) => panic!("Couldn't open source file {}: {}", filename, Error::to_string(&why)),
        Ok(file) => file,
    };

    // -1 because lines start at 1 but indexes at 0
    match BufReader::new(file).lines().nth(ln-1) {
        None => panic!("Couldn't read line {} from source file {}", ln, filename),
        Some(line_result) => match line_result {
            Err(e) => panic!("Couldnt' read line {} from source file {}: {}", ln, filename, e.to_string()),
            // -1 because columns start at 1 but indexes at 0
            Ok(l) => format!("{}\n{}^", l, std::iter::repeat(" ").take(cn-1).collect::<String>())
        }
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (filename, line, column, type_str, token_str) = match self {
            TokenType::OpenBracket(c, fnm, ln, cn) => (fnm, ln, cn, "OpenBracket",  format!("{}", c)),
           TokenType::CloseBracket(c, fnm, ln, cn) => (fnm, ln, cn, "CloseBracket", format!("{}", c)),
              TokenType::Character(c, fnm, ln, cn) => (fnm, ln, cn, "Character",    format!("{}", c)),
             TokenType::Whitespace(c, fnm, ln, cn) => (fnm, ln, cn, "Whitespace",   format!("{}", c)),
                  TokenType::Quote(c, fnm, ln, cn) => (fnm, ln, cn, "Quote",        format!("{}", c)),
             TokenType::SpeechMark(c, fnm, ln, cn) => (fnm, ln, cn, "SpeechMark",   format!("{}", c)),
                 TokenType::String(s, fnm, ln, cn) => (fnm, ln, cn, "String",       format!("\"{}\"", s)),
             TokenType::Definition(s, fnm, ln, cn) => (fnm, ln, cn, "Definition",   format!("'{}", s)),
                TokenType::Integer(i, fnm, ln, cn) => (fnm, ln, cn, "Integer",      format!("{}", i)),
                 TokenType::Symbol(s, fnm, ln, cn) => (fnm, ln, cn, "Symbol",       s.to_string()),
        };
        write!(f, "{}:{}:{} {} {}\n{}",
            filename, line, column, type_str, token_str,
            get_source_line_from_token(self))
    }
}



pub fn tokenise(filename: &str, input: &str) -> Vec<TokenType> {
    let mut tokens = Vec::new();
    for (ln, l) in input.lines().enumerate() {
        for (cn, c) in l.chars().enumerate() {
            tokens.push(
                match c {
                    '('  => TokenType::OpenBracket,
                    ')'  => TokenType::CloseBracket,
                    '\'' => TokenType::Quote,
                    '"'  => TokenType::SpeechMark,
                    ' '  => TokenType::Whitespace,
                    _    => TokenType::Character,
                // +1s since indexes begin at 0
                }(c, filename.to_string(), ln+1, cn+1));
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
                    TokenType::SpeechMark(..) => {
                        let got = current_string.take().unwrap();
                        // Merge into one string token
                        new_tokens.push(TokenType::String(got, filename.to_string(), line_number, column_number));
                        // Mark starting point as invalid
                        speech_mark_start = None;
                    },
                    _ => match current_string {
                        Some(ref mut s) => {
                            match t {
                                 TokenType::OpenBracket(c, ..) |
                                TokenType::CloseBracket(c, ..) |
                                       TokenType::Quote(c, ..) |
                                   TokenType::Character(c, ..) |
                                  TokenType::SpeechMark(c, ..) |
                                  TokenType::Whitespace(c, ..) => s.push(c),
                                _ => panic!("Unexpected token type! {}", t),
                            }
                        }
                        None => panic!("No string to append to!"),
                    }
                }
            }
            Some(_) => panic!("Speech mark start wasn't a speech mark token!"),
            None => match t {
                TokenType::SpeechMark(..) => {
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
            (TokenType::Whitespace(..), TokenType::Whitespace(..)) => true,
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
                    TokenType::Character(c, ..) => {
                        match current_definition_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_definition_string to push to!"),
                        }
                    }
                    // TODO: we're only allowing nested ' in definitions so we don't have
                    // to peek at what the breaking char is
                    TokenType::Quote(c, ..) => {
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
                    TokenType::Quote(..) => {
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
                    TokenType::Character(c, ..) => {
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
                    TokenType::Character(c, ..) => {
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
    tokens.retain(|t| !matches!(t, TokenType::Whitespace(..)));
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
         TokenType::OpenBracket(c, ..) |
        TokenType::CloseBracket(c, ..) |
           TokenType::Character(c, ..) |
          TokenType::Whitespace(c, ..) |
               TokenType::Quote(c, ..) |
          TokenType::SpeechMark(c, ..) => String::from(*c),
              TokenType::String(s, ..) => format!("\"{}\"", s.to_string()),
          TokenType::Definition(s, ..) => format!("'{}", s.to_string()),
             TokenType::Integer(i, ..) => format!("{}", i),
              TokenType::Symbol(s, ..) => s.to_string(),
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
