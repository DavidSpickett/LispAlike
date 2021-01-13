use std::fmt;
use std::fs;
use std::io::BufReader;
use std::io::BufRead;
use std::fs::File;
use std::path::Path;
use std::collections::VecDeque;

pub fn token_err(error: &str, token: &TokenType) -> String {
    let (filename, line_number, column_number) = token_to_file_position(token);
    format!("{}:{}:{} {}", filename, line_number, column_number, error)
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
          TokenType::OpenBracket(file, ln, cn)     |
         TokenType::CloseBracket(file, ln, cn)     |
           TokenType::Whitespace(file, ln, cn)     |
              TokenType::Newline(file, ln, cn)     |
                TokenType::Quote(file, ln, cn)     |
           TokenType::SpeechMark(file, ln, cn)     |
            TokenType::Character(_, file, ln, cn)  |
               TokenType::String(_, file, ln, cn)  |
           TokenType::Declaration(_, file, ln, cn) |
              TokenType::Integer(_, file, ln, cn)  |
               TokenType::Symbol(_, file, ln, cn)  => (file.to_string(), *ln, *cn),
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
            TokenType::OpenBracket(..)  => "(".into(),
           TokenType::CloseBracket(..)  => ")".into(),
             TokenType::Whitespace(..)  => " ".into(),
                  TokenType::Quote(..)  => "'".into(),
             TokenType::SpeechMark(..)  => "\"".into(),
                // We don't want to print an actual newline
                TokenType::Newline(..)  => "\\n".into(),
           TokenType::Character(c, ..)  => format!("{}", c),
             TokenType::Integer(i, ..)  => format!("{}", i),
              TokenType::Symbol(s, ..)  => format!("\"{}\"", s),
              TokenType::String(s, ..)  => format!("\"{}\"", s),
          TokenType::Declaration(s, ..) => format!("'{}", s),
    }
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (type_str, token_str) = match self {
            TokenType::OpenBracket(..)  => ("OpenBracket",  format_token(self)),
           TokenType::CloseBracket(..)  => ("CloseBracket", format_token(self)),
              TokenType::Character(..)  => ("Character",    format_token(self)),
             TokenType::Whitespace(..)  => ("Whitespace",   format_token(self)),
                TokenType::Newline(..)  => ("Newline",      format_token(self)),
                  TokenType::Quote(..)  => ("Quote",        format_token(self)),
             TokenType::SpeechMark(..)  => ("SpeechMark",   format_token(self)),
                 TokenType::String(..)  => ("String",       format_token(self)),
             TokenType::Declaration(..) => ("Declaration",   format_token(self)),
                TokenType::Integer(..)  => ("Integer",      format_token(self)),
                 TokenType::Symbol(..)  => ("Symbol",       format_token(self)),
        };
        write!(f, "{} {}\n{}",
            type_str, token_str,
            get_source_line_from_token(self))
    }
}

pub fn tokenise(filename: &str, input: &str) -> VecDeque<TokenType> {
    let mut tokens = VecDeque::new();
    let mut inside_string = false;
    'lines: for (ln, l) in input.lines().enumerate() {
        for (cn, c) in l.chars().enumerate() {
            // +1s since indexes begin at 0
            let (ln, cn) = (ln+1, cn+1);
            tokens.push_back(
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
        tokens.push_back(TokenType::Newline(filename.into(),
            //  because lines start at 1, indexes at 0
            ln+1,
            //  because the line won't include the newline
            l.len()+1));
    }
    tokens
}

fn token_to_char(token: &TokenType) -> Result<char, String> {
    match token {
         TokenType::OpenBracket(..)    => Ok('('),
        TokenType::CloseBracket(..)    => Ok(')'),
               TokenType::Quote(..)    => Ok('\''),
          TokenType::SpeechMark(..)    => Ok('"'),
             TokenType::Newline(..)    => Ok('\n'),
          TokenType::Whitespace(..)    => Ok(' '),
           TokenType::Character(c, ..) => Ok(*c),
        // Don't expect any post normalise types here
        _ => Err(token_err(&format!("Unexpected token type! {}", token),
                    token))
    }
}

fn generic_normalise(tokens: &mut VecDeque<TokenType>,
                     // So we can print error messages, e.g. "String"
                     token_typename: &str,
                     // Whether to include the first token in the new token
                     // false for something like "foo", where we want foo
                     use_start_token: bool,
                     // Whether to consume the breaking token. Would be true
                     // for a string but for "(foo)" you would want to leave
                     // the closing ) in place so false.
                     consume_end_token: bool,
                     // Function that returns true if the token should break
                     // the current string of tokens for this new token
                     is_end_token: fn(&TokenType) -> bool,
                     // Function that parses the combined string into a
                     // single instance of a token.
                     // Current string, filename, line number, column number
                     parser: fn(&String, String, usize, usize) -> Result<TokenType, String>)
                            -> Result<TokenType, String> {
    // We always consume this token
    let start_token = tokens.pop_front().unwrap();
    // This is the new combined token we're making
    let mut created_token: Option<TokenType> = None;
    let mut current_string = String::new();

    if use_start_token {
        current_string.push(token_to_char(&start_token)?);
    }

    while !tokens.is_empty() {
        let next_token = &tokens[0];

        if is_end_token(next_token) {
            let (fname, ln, cn) = token_to_file_position(&start_token);

            if consume_end_token {
                tokens.pop_front();
            }

            created_token = Some(parser(&current_string, fname, ln, cn)?);
            break;
        } else {
            current_string.push(token_to_char(next_token)?);
            tokens.pop_front();
        }
    }

    match created_token {
        Some(t) => Ok(t),
        // This happens if you for example have "sdfsdf << missing closing "
        None => Err(token_err(
            &format!("Unterminated {} starting here", token_typename), &start_token))
    }
}

// Convert all tokens within "" to a single string token
fn normalise_strings(tokens: &mut VecDeque<TokenType>) -> Result<TokenType, String> {
    generic_normalise(tokens,
                      "String",
                      false, // Discard opening "
                      true,  // Consume closing "
                      |t| { matches!(t, TokenType::SpeechMark(..)) },
                      |s, fname, ln, cn| {
                        let mut final_str = String::new();
                        let mut escaped = false;
                        for chr in s.chars() {
                            if chr == '\\' && !escaped {
                                escaped = true;
                            } else {
                                final_str.push(
                                    if !escaped {
                                        chr
                                    } else {
                                        match chr {
                                            'n' => '\n',
                                            '\\' => '\\',
                                            _ => return Err(format!(
                                                    "Unknown escaped char {} in string \"{}\"", chr, s))
                                        }
                                    }
                                );
                                escaped = false;
                            }
                        }
                        Ok(TokenType::String(final_str, fname, ln, cn))
                      })
}

// Convert any quote followed by a string into a quote token
fn normalise_declarations(tokens: &mut VecDeque<TokenType>) -> Result<TokenType, String> {
    generic_normalise(tokens,
                      "Declaration",
                      false, // Discard opening '
                      false, // Don't consume breaking token
                      |t| { !matches!(t, TokenType::Quote(..) |
                                         TokenType::Character(..)) },
                      |s, fname, ln, cn| {
                        Ok(TokenType::Declaration(s.clone(), fname, ln, cn))
                      })
}

// Anything that parses as a number becomes an Integer token
// Otherwise we assume it'll be some Symbol at runtime
fn parse_symbol(s: &str, fname: &str, ln: usize, cn: usize) -> Result<TokenType, String> {
    if s.starts_with("0x") {
        match i64::from_str_radix(s.trim_start_matches("0x"), 16) {
            Ok(v) => Ok(TokenType::Integer(v, fname.to_string(), ln, cn)),
            Err(_) => Err(token_err(
                &format!("Invalid hex prefix number \"{}\"", s),
                &TokenType::Character('?', fname.to_string(), ln, cn)))
        }
    } else {
        match s.parse::<i64>() {
            Ok(v) => Ok(TokenType::Integer(v, fname.to_string(), ln, cn)),
            Err(_) => Ok(TokenType::Symbol(s.into(), fname.to_string(), ln, cn)),
        }
    }
}

fn normalise_numbers_symbols(tokens: &mut VecDeque<TokenType>) -> Result<TokenType, String> {
    generic_normalise(tokens,
                      "Integer or Symbol",
                      true,  // Keep all chars
                      false, // Don't consume the breaking char
                      |t| { !matches!(t, TokenType::Character(..)) },
                      |s, fname, ln, cn| { parse_symbol(s, &fname, ln, cn) }
                     )
}

pub fn normalise(mut tokens: VecDeque<TokenType>) -> Result<VecDeque<TokenType>, String> {
    let mut new_tokens = VecDeque::new();

    // Until we run out of tokens keep trying to parse larger tokens
    while !tokens.is_empty() {
        let token = &tokens[0];
        let parser: Option<fn (&mut VecDeque<TokenType>) -> Result<TokenType, String>> =
            match token {
                // This defines the priority of the post normalisation tokens
                TokenType::SpeechMark(..) => Some(normalise_strings),
                TokenType::Quote(..)      => Some(normalise_declarations),
                TokenType::Character(..)  => Some(normalise_numbers_symbols),
                _ => None
            };

        match parser {
            Some(p) => new_tokens.push_back(p(&mut tokens)?),
            None => new_tokens.push_back(tokens.pop_front().unwrap())
        }
    }

    // Finally remove whitespace
    new_tokens.retain(|t|
        !matches!(t, TokenType::Whitespace(..) |
                     TokenType::Newline(..)));

    Ok(new_tokens)
}

pub fn process_into_tokens(filename: &str, input: &str) -> Result<VecDeque<TokenType>, String> {
    normalise(tokenise(filename, input))
}

pub fn tokenise_file(filename: &str) -> Result<VecDeque<TokenType>, String> {
    let content = fs::read_to_string(filename);
    match content {
        Err(e) => Err(format!("Couldn't open source file {}, {}", filename, e)),
        Ok(c) => process_into_tokens(filename, &c)
    }
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
    fn normalise_unterminated_string_error() {
        assert_eq!(
            process_into_tokens("<in>", "(+ \"foo\" \"sfsdfsdfsdf"),
            Err("<in>:1:10 Unterminated String starting here".to_string()));
    }

    #[test]
    fn normalise_newline_ends_delcaration() {
        assert_eq!(process_into_tokens("<in>", "(let 'a 1 'b").unwrap(),
            vec![
                TokenType::OpenBracket("<in>".into(), 1, 1),
                TokenType::Symbol("let".into(), "<in>".into(), 1, 2),
                TokenType::Declaration("a".into(), "<in>".into(), 1, 6),
                TokenType::Integer(1, "<in>".into(), 1, 9),
                TokenType::Declaration("b".into(), "<in>".into(), 1, 11),
            ]);
    }

    #[test]
    fn normalise_newline_ends_number_or_symbol() {
        assert_eq!(process_into_tokens("<in>", "(+ foo bar").unwrap(),
            vec![
                TokenType::OpenBracket("<in>".into(), 1, 1),
                TokenType::Symbol("+".into(), "<in>".into(), 1, 2),
                TokenType::Symbol("foo".into(), "<in>".into(), 1, 4),
                TokenType::Symbol("bar".into(), "<in>".into(), 1, 8),
            ]);
    }

    #[test]
    fn basic_normalise() {
        // Runs of characters between "" are made into strings
        // whitespace runs kept when in strings
        assert_eq!(process_into_tokens("<in>", "\" a b ()'  c\"").unwrap(),
                vec![TokenType::String(" a b ()'  c".into(), "<in>".into(), 1, 1)]);

        // Use \n to write newlines
        assert_eq!(process_into_tokens("<in>", "\"a\\nb\"").unwrap(),
                vec![TokenType::String("a\nb".into(), "<in>".into(), 1, 1)]);

        // Use \\ to write literal backslash
        assert_eq!(process_into_tokens("<in>", "\"a\\\\b\"").unwrap(),
                vec![TokenType::String("a\\b".into(), "<in>".into(), 1, 1)]);

        // Multi line strings are handled
        assert_eq!(process_into_tokens("<in>",
"\"foo
bar\"").unwrap(),
            vec![TokenType::String("foo\nbar".into(), "<in>".into(), 1, 1)]);

        // Characters after a quote ' are declarations
        // ' is allowed in the declaration name
        assert_eq!(process_into_tokens("<bla>", "('fo'o)").unwrap(),
                vec![ TokenType::OpenBracket(               "<bla>".into(), 1, 1),
                       TokenType::Declaration("fo'o".into(), "<bla>".into(), 1, 2),
                     TokenType::CloseBracket(               "<bla>".into(), 1, 7)]);

        // Non string, non defintions are either symbols or numbers
        assert_eq!(process_into_tokens("<a>", "(123 a56)").unwrap(),
                vec![ TokenType::OpenBracket(              "<a>".into(), 1, 1),
                          TokenType::Integer(123,          "<a>".into(), 1, 2),
                           TokenType::Symbol("a56".into(), "<a>".into(), 1, 6),
                     TokenType::CloseBracket(              "<a>".into(), 1, 9)]);

        // Hex numbers are also accepted if prefixed
        assert_eq!(process_into_tokens("<a>", "0xcafe").unwrap(),
                vec![TokenType::Integer(0xcafe, "<a>".into(), 1, 1)]);

        // Whitespace removed
        assert_eq!(process_into_tokens("<a>", "(              )").unwrap(),
                vec![ TokenType::OpenBracket("<a>".into(),  1, 1),
                     TokenType::CloseBracket("<a>".into(), 1, 16)]);

        // Declarations and symbols are ended by a newline
        assert_eq!(process_into_tokens("<b>", "'foo\nbar\nabc").unwrap(),
                vec![TokenType::Declaration("foo".into(), "<b>".into(), 1, 1),
                         TokenType::Symbol("bar".into(), "<b>".into(), 2, 1),
                         TokenType::Symbol("abc".into(), "<b>".into(), 3, 1),
                ]);
    }

    #[test]
    fn invalid_hex_prefix_num_error() {
        assert_eq!(process_into_tokens("<b>", "0xfoobar"),
            Err("<b>:1:1 Invalid hex prefix number \"0xfoobar\"".to_string()));
    }
}
