use std::fmt;
use std::fs;
use std::io::BufReader;
use std::io::BufRead;
use std::fs::File;
use std::path::Path;

//TODO: not the best place for this to live
pub fn read_source_file(filename: &str) -> String {
    fs::read_to_string(filename)
        .unwrap_or_else(|_| panic!("Couldn't open source file {}", filename))
}

#[derive(Debug, PartialEq)]
pub enum TokenType {
     // TODO: &str for the filename?
     // Actual character, filename, line number, column number
     OpenBracket(char, String, usize, usize),
    CloseBracket(char, String, usize, usize),
       Character(char, String, usize, usize),
      Whitespace(char, String, usize, usize),
         Newline(char, String, usize, usize),
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
              TokenType::Newline(_, file, ln, cn) |
                TokenType::Quote(_, file, ln, cn) |
           TokenType::SpeechMark(_, file, ln, cn) |
               TokenType::String(_, file, ln, cn) |
           TokenType::Definition(_, file, ln, cn) |
              TokenType::Integer(_, file, ln, cn) |
               TokenType::Symbol(_, file, ln, cn) => (file.to_string(), *ln, *cn),
    }
}

pub fn padding(len: usize) -> String {
    std::iter::repeat(" ").take(len).collect::<String>()
}

// Format a string like:
// (foo 1 2)
//      ^
// This will never panic, just return a string
// describing the read failure. So you can always
// print something.
pub fn get_source_line_from_token(t: &TokenType) -> String {
    let (filename, ln, cn) = token_to_file_position(t);
    let file = File::open(Path::new(&filename));

    match file {
        // Return something so we can still print tokens with pseudo files
        Err(_) => format!("<Couldn't open source file {}>", filename),
        Ok(file) => {
            // -1 because lines start at 1 but indexes at 0
            match BufReader::new(file).lines().nth(ln-1) {
                None => format!("<Couldn't read line {} from source file {}>", ln, filename),
                Some(line_result) => match line_result {
                    Err(e) => format!("<Couldnt' read line {} from source file {}: {}>",
                                  ln, filename, e.to_string()),
                    // -1 because columns start at 1 but indexes at 0
                    Ok(l) => format!("{}\n{}^", l, padding(cn-1))
                }
            }
        }
    }
}

pub fn format_token(t: &TokenType) -> String {
    match t {
         TokenType::OpenBracket(c, ..) |
        TokenType::CloseBracket(c, ..) |
           TokenType::Character(c, ..) |
          TokenType::Whitespace(c, ..) |
               TokenType::Quote(c, ..) |
          TokenType::SpeechMark(c, ..) => format!("{}", c),
             // We don't want to print an actual newline
             TokenType::Newline(..)    => "\\n".into(),
              TokenType::Symbol(s, ..) => format!("\"{}\"", s),
             TokenType::Integer(i, ..) => format!("{}", i),
              TokenType::String(s, ..) => format!("\"{}\"", s),
          TokenType::Definition(s, ..) => format!("'{}", s),
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (filename, line, column, type_str, token_str) = match self {
            TokenType::OpenBracket(_, fnm, ln, cn) => (fnm, ln, cn, "OpenBracket",  format_token(self)),
           TokenType::CloseBracket(_, fnm, ln, cn) => (fnm, ln, cn, "CloseBracket", format_token(self)),
              TokenType::Character(_, fnm, ln, cn) => (fnm, ln, cn, "Character",    format_token(self)),
             TokenType::Whitespace(_, fnm, ln, cn) => (fnm, ln, cn, "Whitespace",   format_token(self)),
                TokenType::Newline(_, fnm, ln, cn) => (fnm, ln, cn, "Newline",      format_token(self)),
                  TokenType::Quote(_, fnm, ln, cn) => (fnm, ln, cn, "Quote",        format_token(self)),
             TokenType::SpeechMark(_, fnm, ln, cn) => (fnm, ln, cn, "SpeechMark",   format_token(self)),
                 TokenType::String(_, fnm, ln, cn) => (fnm, ln, cn, "String",       format_token(self)),
             TokenType::Definition(_, fnm, ln, cn) => (fnm, ln, cn, "Definition",   format_token(self)),
                TokenType::Integer(_, fnm, ln, cn) => (fnm, ln, cn, "Integer",      format_token(self)),
                 TokenType::Symbol(_, fnm, ln, cn) => (fnm, ln, cn, "Symbol",       format_token(self)),
        };
        write!(f, "{} {}\n{}",
            type_str, token_str,
            get_source_line_from_token(self))
    }
}

pub fn tokenise(filename: &str, input: &str) -> Vec<TokenType> {
    let mut tokens = Vec::new();
    let mut inside_string = false;
    'lines: for (ln, l) in input.lines().enumerate() {
        for (cn, c) in l.chars().enumerate() {
            tokens.push(
                match c {
                    ' '  => TokenType::Whitespace,
                    '('  => TokenType::OpenBracket,
                    ')'  => TokenType::CloseBracket,
                    '\'' => TokenType::Quote,
                    '"'  => {
                        inside_string ^= true;
                        TokenType::SpeechMark
                    }
                    // Any # outside a string starts a comment
                    '#'  => {
                        if inside_string {
                            TokenType::Character
                        } else {
                            // Ignore the rest of the line
                            continue 'lines;
                        }
                    }
                    _    => TokenType::Character,
                // +1s since indexes begin at 0
                }(c, filename.into(), ln+1, cn+1));
        }
        tokens.push(TokenType::Newline('\n', filename.into(),
            // +1 because lines start at 0
            ln+1,
            // +1 because the line won't include the newline
            l.len()+1));
    }
    tokens
}

// Convert all tokens within "" to a single string token
fn normalise_strings(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens = Vec::new();
    let mut current_string: Option<String> = None;
    let mut speech_mark_start : Option<TokenType> = None;

    for t in tokens {
        match speech_mark_start {
            Some(TokenType::SpeechMark(_, ref filename, ln, cn)) => {
                match t {
                    TokenType::SpeechMark(..) => {
                        let got = current_string.take().unwrap();
                        // Merge into one string token
                        new_tokens.push(TokenType::String(
                            got, filename.to_string(), ln, cn));
                        // Mark starting point as invalid
                        speech_mark_start = None;
                        // Note that we don't make any use of the closing "
                    },
                    _ => match current_string {
                        Some(ref mut s) => {
                            match t {
                                 TokenType::OpenBracket(c, ..) |
                                TokenType::CloseBracket(c, ..) |
                                       TokenType::Quote(c, ..) |
                                   TokenType::Character(c, ..) |
                                  TokenType::SpeechMark(c, ..) |
                                     TokenType::Newline(c, ..) |
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
                // Look for the start of a new string
                TokenType::SpeechMark(..) => {
                    current_string = Some(String::new());
                    speech_mark_start = Some(t);
                    // Note that we don't make any use of the opening "
                },
                _ => new_tokens.push(t),
            }
        }
    }

    new_tokens
}

// Convert any quote followed by a string into a quote token
fn normalise_definitions(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut start_quote_char: Option<TokenType> = None;
    let mut current_definition_string: Option<String> = None;

    for t in tokens {
        match start_quote_char {
            Some(TokenType::Quote(_, ref filename, ln, cn)) => {
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
                                new_tokens.push(TokenType::Definition(
                                    s, filename.to_string(), ln, cn));
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

// Anything that parses as a number becomes an Integer token
// Otherwise we assume it'll be some Symbol at runtime
pub fn normalise_numbers_symbols(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut starting_char: Option<TokenType> = None;
    let mut current_string: Option<String> = None;
    for t in tokens {
        match starting_char {
            Some(TokenType::Character(_, ref filename, ln, cn)) => {
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
                                    Ok(v) => new_tokens.push(TokenType::Integer(
                                                 v, filename.to_string(), ln, cn)),
                                    // Otherwise assume it's a symbol name
                                    // TODO: don't allow numbers to start symbol names?
                                    Err(_) => new_tokens.push(TokenType::Symbol(
                                                  s, filename.to_string(), ln, cn)),
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
                        // Unlike strings etc, symbols include the first char
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
    tokens.retain(|t|
        !matches!(t, TokenType::Whitespace(..) |
                     TokenType::Newline(..)));
    tokens
}

pub fn normalise(tokens: Vec<TokenType>) -> Vec<TokenType> {
    normalise_remove_whitespace(
        normalise_numbers_symbols(
            normalise_definitions(
                normalise_strings(tokens)
            )
        )
    )
}

pub fn process_into_tokens(filename: &str, input: &str) -> Vec<TokenType> {
    normalise(tokenise(filename, input))
}

#[cfg(test)]
mod tests {
    use tokeniser::TokenType;
    use tokeniser::tokenise;
    use tokeniser::process_into_tokens;

    #[test]
    fn test_tokenise() {
        assert_eq!(tokenise("<in>", "(+ 1 \n\
                             2)"),
        vec![
             TokenType::OpenBracket('(',  "<in>".into(), 1, 1),
               TokenType::Character('+',  "<in>".into(), 1, 2),
              TokenType::Whitespace(' ',  "<in>".into(), 1, 3),
               TokenType::Character('1',  "<in>".into(), 1, 4),
              TokenType::Whitespace(' ',  "<in>".into(), 1, 5),
                 TokenType::Newline('\n', "<in>".into(), 1, 6),
               TokenType::Character('2',  "<in>".into(), 2, 1),
            TokenType::CloseBracket(')',  "<in>".into(), 2, 2),
                 TokenType::Newline('\n', "<in>".into(), 2, 3),
            ]);

        assert_eq!(tokenise("<foo>", "\"'\"'"),
            vec![
                TokenType::SpeechMark('"',   "<foo>".into(), 1, 1),
                     TokenType::Quote('\'',  "<foo>".into(), 1, 2),
                TokenType::SpeechMark('"',   "<foo>".into(), 1, 3),
                     TokenType::Quote('\'',  "<foo>".into(), 1, 4),
                    TokenType::Newline('\n', "<foo>".into(), 1, 5),
                ]);
    }

    #[test]
    fn test_tokenise_ignore_comments() {
        // Anything after # is ignored
        assert_eq!(tokenise("<in>", "# This is a comment!"),
            vec![]);

        // Line up to that point is tokenised
        assert_eq!(tokenise("<in>", "(a) # Comment rest of line"),
            vec![
                TokenType::OpenBracket('(', "<in>".into(), 1, 1),
                  TokenType::Character('a', "<in>".into(), 1, 2),
               TokenType::CloseBracket(')', "<in>".into(), 1, 3),
                 TokenType::Whitespace(' ', "<in>".into(), 1, 4),
            ]);

        // # within a string is allowed
        assert_eq!(tokenise("<in>", "(f \"Hash #!\")"),
            vec![
                TokenType::OpenBracket('(',  "<in>".into(), 1, 1),
                  TokenType::Character('f',  "<in>".into(), 1, 2),
                 TokenType::Whitespace(' ',  "<in>".into(), 1, 3),
                 TokenType::SpeechMark('\"', "<in>".into(), 1, 4),
                  TokenType::Character('H',  "<in>".into(), 1, 5),
                  TokenType::Character('a',  "<in>".into(), 1, 6),
                  TokenType::Character('s',  "<in>".into(), 1, 7),
                  TokenType::Character('h',  "<in>".into(), 1, 8),
                 TokenType::Whitespace(' ',  "<in>".into(), 1, 9),
                  TokenType::Character('#',  "<in>".into(), 1, 10),
                  TokenType::Character('!',  "<in>".into(), 1, 11),
                 TokenType::SpeechMark('\"', "<in>".into(), 1, 12),
               TokenType::CloseBracket(')',  "<in>".into(), 1, 13),
                    TokenType::Newline('\n', "<in>".into(), 1, 14),
            ]);

        // # within a string is allowed
        assert_eq!(tokenise("<in>",
"\"foo
bar # abc\""),
            vec![
                TokenType::SpeechMark('\"', "<in>".into(), 1, 1),
                 TokenType::Character('f',  "<in>".into(), 1, 2),
                 TokenType::Character('o',  "<in>".into(), 1, 3),
                 TokenType::Character('o',  "<in>".into(), 1, 4),
                   TokenType::Newline('\n', "<in>".into(), 1, 5),
                 TokenType::Character('b',  "<in>".into(), 2, 1),
                 TokenType::Character('a',  "<in>".into(), 2, 2),
                 TokenType::Character('r',  "<in>".into(), 2, 3),
                TokenType::Whitespace(' ',  "<in>".into(), 2, 4),
                 TokenType::Character('#',  "<in>".into(), 2, 5),
                TokenType::Whitespace(' ',  "<in>".into(), 2, 6),
                 TokenType::Character('a',  "<in>".into(), 2, 7),
                 TokenType::Character('b',  "<in>".into(), 2, 8),
                 TokenType::Character('c',  "<in>".into(), 2, 9),
                TokenType::SpeechMark('\"', "<in>".into(), 2, 10),
                   TokenType::Newline('\n', "<in>".into(), 2, 11),
            ]);
    }

    #[test]
    fn test_normalise() {
        // Runs of characters between "" are made into strings
        // whitespace runs kept when in strings
        assert_eq!(process_into_tokens("<in>", "\" a b ()'  c\""),
                vec![TokenType::String(" a b ()'  c".into(), "<in>".into(), 1, 1)]);

        // Multi line strings are handled
        assert_eq!(process_into_tokens("<in>",
"\"foo
bar\""),
            vec![TokenType::String("foo\nbar".into(), "<in>".into(), 1, 1)]);

        // Characters after a quote ' are definitions
        // ' is allowed in the definition name
        assert_eq!(process_into_tokens("<bla>", "('fo'o)"),
                vec![ TokenType::OpenBracket('(',           "<bla>".into(), 1, 1),
                       TokenType::Definition("fo'o".into(), "<bla>".into(), 1, 2),
                     TokenType::CloseBracket(')',           "<bla>".into(), 1, 7)]);

        // Non string, non defintions are either symbols or numbers
        assert_eq!(process_into_tokens("<a>", "(123 a56)"),
                vec![ TokenType::OpenBracket('(',          "<a>".into(), 1, 1),
                          TokenType::Integer(123,          "<a>".into(), 1, 2),
                           TokenType::Symbol("a56".into(), "<a>".into(), 1, 6),
                     TokenType::CloseBracket(')',          "<a>".into(), 1, 9)]);

        // Whitespace removed
        assert_eq!(process_into_tokens("<a>", "(              )"),
                vec![ TokenType::OpenBracket('(', "<a>".into(),  1, 1),
                     TokenType::CloseBracket(')', "<a>".into(), 1, 16)]);

        // Definitions and symbols are ended by a newline
        assert_eq!(process_into_tokens("<b>", "'foo\nbar\nabc"),
                vec![TokenType::Definition("foo".into(), "<b>".into(), 1, 1),
                         TokenType::Symbol("bar".into(), "<b>".into(), 2, 1),
                         TokenType::Symbol("abc".into(), "<b>".into(), 3, 1),
                ]);
    }
}
