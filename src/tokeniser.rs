use std::fmt;
use std::fs;
use std::io::BufReader;
use std::io::BufRead;
use std::fs::File;
use std::path::Path;

// ! meaning the never type
pub fn panic_with_location(error: &str, filename: &str,
					   start_line: usize, start_col: usize) -> ! {
    panic!("{}:{}:{} {}", filename, start_line, start_col, error)
}

pub fn panic_on_token(error: &str, token: &TokenType) -> ! {
    let (filename, line_number, column_number) = token_to_file_position(token);
    panic_with_location(error, &filename, line_number, column_number);
}

//TODO: not the best place for this to live
pub fn read_source_file(filename: &str) -> String {
    fs::read_to_string(filename)
        .unwrap_or_else(|_| panic!("Couldn't open source file {}", filename))
}

#[derive(Debug, PartialEq)]
pub enum TokenType {
     // TODO: &str for the filename?
     // Actual character, filename, line number, column number
     OpenBracket(String, usize, usize),
    CloseBracket(String, usize, usize),
      Whitespace(String, usize, usize),
         Newline(String, usize, usize),
           Quote(String, usize, usize),
      SpeechMark(String, usize, usize),
       Character(char, String, usize, usize),

      // Post normalisation tokens
          String(String, String, usize, usize),
      Declaration(String, String, usize, usize),
         Integer(i64,    String, usize, usize),
          Symbol(String, String, usize, usize),
}

pub fn token_to_file_position(token: &TokenType) -> (String, usize, usize) {
    match token {
          TokenType::OpenBracket(file, ln, cn)    |
         TokenType::CloseBracket(file, ln, cn)    |
           TokenType::Whitespace(file, ln, cn)    |
              TokenType::Newline(file, ln, cn)    |
                TokenType::Quote(file, ln, cn)    |
           TokenType::SpeechMark(file, ln, cn)    |
            TokenType::Character(_, file, ln, cn) |
               TokenType::String(_, file, ln, cn) |
           TokenType::Declaration(_, file, ln, cn) |
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
            TokenType::OpenBracket(..) => "(".into(),
           TokenType::CloseBracket(..) => ")".into(),
             TokenType::Whitespace(..) => " ".into(),
                  TokenType::Quote(..) => "'".into(),
             TokenType::SpeechMark(..) => "\"".into(),
                // We don't want to print an actual newline
                TokenType::Newline(..) => "\\n".into(),
           TokenType::Character(c, ..) => format!("{}", c),
             TokenType::Integer(i, ..) => format!("{}", i),
              TokenType::Symbol(s, ..) => format!("\"{}\"", s),
              TokenType::String(s, ..) => format!("\"{}\"", s),
          TokenType::Declaration(s, ..) => format!("'{}", s),
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (type_str, token_str) = match self {
            TokenType::OpenBracket(..) => ("OpenBracket",  format_token(self)),
           TokenType::CloseBracket(..) => ("CloseBracket", format_token(self)),
              TokenType::Character(..) => ("Character",    format_token(self)),
             TokenType::Whitespace(..) => ("Whitespace",   format_token(self)),
                TokenType::Newline(..) => ("Newline",      format_token(self)),
                  TokenType::Quote(..) => ("Quote",        format_token(self)),
             TokenType::SpeechMark(..) => ("SpeechMark",   format_token(self)),
                 TokenType::String(..) => ("String",       format_token(self)),
             TokenType::Declaration(..) => ("Declaration",   format_token(self)),
                TokenType::Integer(..) => ("Integer",      format_token(self)),
                 TokenType::Symbol(..) => ("Symbol",       format_token(self)),
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
            // +1s since indexes begin at 0
            let (ln, cn) = (ln+1, cn+1);
            tokens.push(
                match c {
                    ' '  =>   TokenType::Whitespace(filename.into(), ln, cn),
                    '('  =>  TokenType::OpenBracket(filename.into(), ln, cn),
                    ')'  => TokenType::CloseBracket(filename.into(), ln, cn),
                    '\'' =>        TokenType::Quote(filename.into(), ln, cn),
                    '"'  => {
                        inside_string ^= true;
                        TokenType::SpeechMark(filename.into(), ln, cn)
                    }
                    // Any # outside a string starts a comment
                    '#'  => {
                        if inside_string {
                            TokenType::Character(c, filename.into(), ln, cn)
                        } else {
                            // Ignore the rest of the line
                            continue 'lines;
                        }
                    }
                    _    => TokenType::Character(c, filename.into(), ln, cn)
                });
        }
        tokens.push(TokenType::Newline(filename.into(),
            //  because lines start at 1, indexes at 0
            ln+1,
            //  because the line won't include the newline
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
            Some(TokenType::SpeechMark(ref filename, ln, cn)) => {
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
                            s.push(match t {
                                 TokenType::OpenBracket(..)    => '(',
                                TokenType::CloseBracket(..)    => ')',
                                       TokenType::Quote(..)    => '\'',
                                  TokenType::SpeechMark(..)    => '"',
                                     TokenType::Newline(..)    => '\n',
                                  TokenType::Whitespace(..)    => ' ',
                                   TokenType::Character(c, ..) => c,
                                _ => panic!("Unexpected token type! {}", t),
                            })
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
fn normalise_declarations(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut start_quote_char: Option<TokenType> = None;
    let mut current_declaration_string: Option<String> = None;

    for t in tokens {
        match start_quote_char {
            Some(TokenType::Quote(ref filename, ln, cn)) => {
                match t {
                    TokenType::Character(c, ..) => {
                        match current_declaration_string {
                            Some(ref mut s) => s.push(c),
                            None => panic!("No current_declaration_string to push to!"),
                        }
                    }
                    // TODO: we're only allowing nested ' in declarations so we don't have
                    // to peek at what the breaking char is
                    TokenType::Quote(..) => {
                        match current_declaration_string {
                            Some(ref mut s) => s.push('\''),
                            None => panic!("No current_declaration_string to push to!"),
                        }
                    }
                    // Anything else finishes the identifier
                    _ => {
                        match current_declaration_string {
                            Some(s) => {
                                new_tokens.push(TokenType::Declaration(
                                    s, filename.to_string(), ln, cn));
                                current_declaration_string = None;
                                start_quote_char = None;
                                // Append breaking token as normal
                                new_tokens.push(t);
                            }
                            None => panic!("No current_declaration_string to form token with!"),
                        }
                    }
                }
            }
            Some(_) => panic!("start_quote_char isn't a quote char!"),
            None => {
                match t {
                    // Starts a new declaration
                    TokenType::Quote(..) => {
                        start_quote_char = Some(t);
                        current_declaration_string = Some(String::new());
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
fn parse_symbol(start_token: &TokenType, s: &String) -> TokenType {
    let (fname, ln, cn) = token_to_file_position(start_token);

    if s.starts_with("0x") {
        match i64::from_str_radix(s.trim_start_matches("0x"), 16) {
            Ok(v) => TokenType::Integer(v, fname.to_string(), ln, cn),
            Err(_) => panic_on_token(
                &format!("Invalid hex prefix number \"{}\"", s),
                &start_token)
        }
    } else {
        match s.parse::<i64>() {
            Ok(v) => TokenType::Integer(v, fname.to_string(), ln, cn),
            Err(_) => TokenType::Symbol(s.into(), fname.to_string(), ln, cn),
        }
    }
}

fn normalise_numbers_symbols(tokens: Vec<TokenType>) -> Vec<TokenType> {
    let mut new_tokens: Vec<TokenType> = Vec::new();
    let mut starting_char: Option<TokenType> = None;
    let mut current_string = String::new();

    for t in tokens {
        match starting_char {
            Some(ref first_char) => {
                match t {
                    TokenType::Character(c, ..) => current_string.push(c),
                    // Anything else breaks the streak
                    _ => {
                        new_tokens.push(parse_symbol(first_char, &current_string));

                        starting_char = None;
                        current_string.clear();
                        new_tokens.push(t);
                    }
                }
            }
            None => {
                match t {
                    TokenType::Character(c, ..) => {
                        starting_char = Some(t);
                        // Unlike strings etc, symbols include the first char
                        current_string.push(c);
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
            normalise_declarations(
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
    fn basic_tokenise() {
        assert_eq!(tokenise("<in>", "(+ 1 \n\
                             2)"),
        vec![
             TokenType::OpenBracket(      "<in>".into(), 1, 1),
               TokenType::Character('+',  "<in>".into(), 1, 2),
              TokenType::Whitespace(      "<in>".into(), 1, 3),
               TokenType::Character('1',  "<in>".into(), 1, 4),
              TokenType::Whitespace(      "<in>".into(), 1, 5),
                 TokenType::Newline(      "<in>".into(), 1, 6),
               TokenType::Character('2',  "<in>".into(), 2, 1),
            TokenType::CloseBracket(      "<in>".into(), 2, 2),
                 TokenType::Newline(      "<in>".into(), 2, 3),
            ]);

        assert_eq!(tokenise("<foo>", "\"'\"'"),
            vec![
                 TokenType::SpeechMark("<foo>".into(), 1, 1),
                      TokenType::Quote("<foo>".into(), 1, 2),
                 TokenType::SpeechMark("<foo>".into(), 1, 3),
                      TokenType::Quote("<foo>".into(), 1, 4),
                    TokenType::Newline("<foo>".into(), 1, 5),
                ]);
    }

    #[test]
    fn tokenise_ignores_comments() {
        // Anything after # is ignored
        assert_eq!(tokenise("<in>", "# This is a comment!"),
            vec![]);

        // Line up to that point is tokenised
        assert_eq!(tokenise("<in>", "(a) # Comment rest of line"),
            vec![
                TokenType::OpenBracket(     "<in>".into(), 1, 1),
                  TokenType::Character('a', "<in>".into(), 1, 2),
               TokenType::CloseBracket(     "<in>".into(), 1, 3),
                 TokenType::Whitespace(     "<in>".into(), 1, 4),
            ]);

        // # within a string is allowed
        assert_eq!(tokenise("<in>", "(f \"Hash #!\")"),
            vec![
                TokenType::OpenBracket(      "<in>".into(), 1, 1),
                  TokenType::Character('f',  "<in>".into(), 1, 2),
                 TokenType::Whitespace(      "<in>".into(), 1, 3),
                 TokenType::SpeechMark(      "<in>".into(), 1, 4),
                  TokenType::Character('H',  "<in>".into(), 1, 5),
                  TokenType::Character('a',  "<in>".into(), 1, 6),
                  TokenType::Character('s',  "<in>".into(), 1, 7),
                  TokenType::Character('h',  "<in>".into(), 1, 8),
                 TokenType::Whitespace(      "<in>".into(), 1, 9),
                  TokenType::Character('#',  "<in>".into(), 1, 10),
                  TokenType::Character('!',  "<in>".into(), 1, 11),
                 TokenType::SpeechMark(      "<in>".into(), 1, 12),
               TokenType::CloseBracket(      "<in>".into(), 1, 13),
                    TokenType::Newline(      "<in>".into(), 1, 14),
            ]);

        // # within a string is allowed
        assert_eq!(tokenise("<in>",
"\"foo
bar # abc\""),
            vec![
                TokenType::SpeechMark(      "<in>".into(), 1, 1),
                 TokenType::Character('f',  "<in>".into(), 1, 2),
                 TokenType::Character('o',  "<in>".into(), 1, 3),
                 TokenType::Character('o',  "<in>".into(), 1, 4),
                   TokenType::Newline(      "<in>".into(), 1, 5),
                 TokenType::Character('b',  "<in>".into(), 2, 1),
                 TokenType::Character('a',  "<in>".into(), 2, 2),
                 TokenType::Character('r',  "<in>".into(), 2, 3),
                TokenType::Whitespace(      "<in>".into(), 2, 4),
                 TokenType::Character('#',  "<in>".into(), 2, 5),
                TokenType::Whitespace(      "<in>".into(), 2, 6),
                 TokenType::Character('a',  "<in>".into(), 2, 7),
                 TokenType::Character('b',  "<in>".into(), 2, 8),
                 TokenType::Character('c',  "<in>".into(), 2, 9),
                TokenType::SpeechMark(      "<in>".into(), 2, 10),
                   TokenType::Newline(      "<in>".into(), 2, 11),
            ]);
    }

    #[test]
    fn basic_normalise() {
        // Runs of characters between "" are made into strings
        // whitespace runs kept when in strings
        assert_eq!(process_into_tokens("<in>", "\" a b ()'  c\""),
                vec![TokenType::String(" a b ()'  c".into(), "<in>".into(), 1, 1)]);

        // Multi line strings are handled
        assert_eq!(process_into_tokens("<in>",
"\"foo
bar\""),
            vec![TokenType::String("foo\nbar".into(), "<in>".into(), 1, 1)]);

        // Characters after a quote ' are declarations
        // ' is allowed in the declaration name
        assert_eq!(process_into_tokens("<bla>", "('fo'o)"),
                vec![ TokenType::OpenBracket(               "<bla>".into(), 1, 1),
                       TokenType::Declaration("fo'o".into(), "<bla>".into(), 1, 2),
                     TokenType::CloseBracket(               "<bla>".into(), 1, 7)]);

        // Non string, non defintions are either symbols or numbers
        assert_eq!(process_into_tokens("<a>", "(123 a56)"),
                vec![ TokenType::OpenBracket(              "<a>".into(), 1, 1),
                          TokenType::Integer(123,          "<a>".into(), 1, 2),
                           TokenType::Symbol("a56".into(), "<a>".into(), 1, 6),
                     TokenType::CloseBracket(              "<a>".into(), 1, 9)]);

        // Hex numbers are also accepted if prefixed
        assert_eq!(process_into_tokens("<a>", "0xcafe"),
                vec![TokenType::Integer(0xcafe, "<a>".into(), 1, 1)]);

        // Whitespace removed
        assert_eq!(process_into_tokens("<a>", "(              )"),
                vec![ TokenType::OpenBracket("<a>".into(),  1, 1),
                     TokenType::CloseBracket("<a>".into(), 1, 16)]);

        // Declarations and symbols are ended by a newline
        assert_eq!(process_into_tokens("<b>", "'foo\nbar\nabc"),
                vec![TokenType::Declaration("foo".into(), "<b>".into(), 1, 1),
                         TokenType::Symbol("bar".into(), "<b>".into(), 2, 1),
                         TokenType::Symbol("abc".into(), "<b>".into(), 3, 1),
                ]);
    }

    #[test]
    #[should_panic (expected = "<b>:1:1 Invalid hex prefix number \"0xfoobar\"")]
    fn invalid_hex_prefix_num_panics() {
        process_into_tokens("<b>", "0xfoobar");
    }
}
