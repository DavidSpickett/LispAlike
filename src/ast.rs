use std::fmt;
use crate::tokeniser;

#[derive(Debug, PartialEq)]
pub enum CallOrToken {
    Token(tokeniser::TokenType),
    // TODO: bad name
    Call(Call),
}

// TODO: calls should include location info (begin and end!)
#[derive(Debug, PartialEq)]
pub struct Call {
    // TODO: can we restrict the type here?
    pub fn_name: tokeniser::TokenType,
    pub arguments: Vec<CallOrToken>,
}

fn padding(len: usize) -> String {
    std::iter::repeat(" ").take(len).collect::<String>()
}

fn format_call(c: &Call, mut indent: usize) -> String {
    let indent_str = padding(indent);
    indent += 4;
    let args_indent = padding(indent);

    format!("\n{}({}{}\n{})",
        indent_str,
        match &c.fn_name {
            tokeniser::TokenType::Symbol(s, ..) => s.to_string(),
            _ => panic!("Call function name wasn't a Symbol!")
        },
        c.arguments.iter().map(|call_or_token|
            match call_or_token {
                CallOrToken::Call(call_arg) => format_call(call_arg, indent),
                CallOrToken::Token(token)   => format!("\n{}{}", args_indent,
                    match token {
                        tokeniser::TokenType::String(s, ..)      => format!("\"{}\"", s),
                        tokeniser::TokenType::Definition(s, ..)  => format!("'{}", s),
                        tokeniser::TokenType::Symbol(s, ..)      => s.to_string(),
                        tokeniser::TokenType::Integer(i, ..)     => format!("{}", i),
                        _ => panic!("Token type should not be found in the AST!")
                    })
            }
        ).collect::<String>(),
        indent_str
    )
}

impl fmt::Display for Call {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format_call(self, 0))
    }
}

// ! meaning the never type
fn panic_with_locaton(error: &str, filename: &str, start_line: usize, start_col: usize) -> ! {
    panic!("{}:{}:{} {}", filename, start_line, start_col, error)
}

fn build_call(tokens: &mut Vec<tokeniser::TokenType>) -> Call {
    // We are garaunteed that the caller found a '('
    let start_bracket = tokens.remove(0);
    let (filename, start_line, start_col) = tokeniser::token_to_file_position(&start_bracket);

    // TODO: we're assuming that fn names aren't calls themselves
    let mut arguments = Vec::new();
    let fn_name = match tokens.first() {
        Some(tokeniser::TokenType::CloseBracket(..)) =>
            panic_with_locaton("Missing function name for call",
                &filename, start_line, start_col),
        // Only allow symbols for function name
        Some(tokeniser::TokenType::Symbol(..)) => {
            // Must do this now before subsequent build_call removes it
            let fn_name_copy = tokens.remove(0);

            loop {
                match tokens.first() {
                    // Finishes a call
                    Some(tokeniser::TokenType::CloseBracket(..)) => {
                        tokens.remove(0);
                        break
                    },
                    // Starts a new call
                    Some(tokeniser::TokenType::OpenBracket(..)) =>
                        arguments.push(CallOrToken::Call(build_call(tokens))),
                    // Any other token is an argument to the current call
                    Some(_) => arguments.push(CallOrToken::Token(tokens.remove(0))),
                    None => panic_with_locaton("EOF trying to build call",
                                &filename, start_line, start_col)
                }
            }

            fn_name_copy
        }
        Some(_) => panic_with_locaton("Function name must be a Symbol for call",
                       &filename, start_line, start_col),
        None => panic_with_locaton("EOF trying to build call",
                    &filename, start_line, start_col),
    };

    Call {fn_name: fn_name, arguments: arguments}
}

pub fn build(mut tokens: Vec<tokeniser::TokenType>) -> Call {
    let mut root_call = Call{
        fn_name: tokeniser::TokenType::Symbol(
            "root".to_string(), "<pseudo>".to_string(), 0, 0),
        arguments: vec![]
    };

    while !tokens.is_empty() {
        root_call.arguments.push(match tokens.first() {
            Some(tokeniser::TokenType::OpenBracket(..)) =>
                CallOrToken::Call(build_call(&mut tokens)),
            Some(_) => panic!("Program must begin with an open bracket!"),
            None => panic!("Empty token list to build AST from!")
        })
    }

    root_call
}

#[cfg(test)]
mod tests {
    use ast::build;
    use ast::Call;
    use ast::CallOrToken;
    use tokeniser;

    #[test]
    fn single_call() {
        assert_eq!(build(tokeniser::process("<in>", "(+ 1 2 \"foo\")")),
        Call {
             fn_name: tokeniser::TokenType::Symbol(
                          "root".to_string(), "<pseudo>".to_string(), 0, 0),
             arguments: vec![
                CallOrToken::Call(Call{
                     fn_name: tokeniser::TokenType::Symbol(
                                  "+".to_string(), "<in>".to_string(), 1, 2),
                     arguments: vec![
                             CallOrToken::Token(tokeniser::TokenType::Integer(
                                 1, "<in>".to_string(), 1, 4)),
                             CallOrToken::Token(tokeniser::TokenType::Integer(
                                 2, "<in>".to_string(), 1, 6)),
                             CallOrToken::Token(tokeniser::TokenType::String(
                                 "foo".to_string(), "<in>".to_string(), 1, 8))
                        ]
                    })
            ]
        });
    }

    #[test]
    fn single_call_multi_line() {
        assert_eq!(build(tokeniser::process("foo.abc", "\
(abc
    (def
        \"a\"
        (ghi)
    )
    99
)")),
            Call {
                fn_name: tokeniser::TokenType::Symbol(
                             "root".to_string(), "<pseudo>".to_string(), 0, 0),
                arguments: vec![
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "abc".to_string(), "foo.abc".to_string(), 1, 2),
                        arguments: vec![
                            CallOrToken::Call(Call {
                                fn_name: tokeniser::TokenType::Symbol(
                                             "def".to_string(), "foo.abc".to_string(), 2, 6),
                                arguments: vec![
                                    CallOrToken::Token(tokeniser::TokenType::String(
                                        "a".to_string(), "foo.abc".to_string(), 3, 9)),
                                    CallOrToken::Call(Call {
                                        fn_name: tokeniser::TokenType::Symbol(
                                                     "ghi".to_string(), "foo.abc".to_string(), 4, 10),
                                        arguments: vec![],
                                    }),
                                ],
                            }),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                99, "foo.abc".to_string(), 6, 5)),
                        ],
                    })
                ]
            }
        );
    }

    #[test]
    fn multi_block() {
        assert_eq!(build(tokeniser::process("<in>", "(foo 1 2)(bar 3 4)")),
            Call {
                fn_name: tokeniser::TokenType::Symbol(
                             "root".to_string(), "<pseudo>".to_string(), 0, 0),
                arguments: vec![
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "foo".to_string(), "<in>".to_string(), 1, 2),
                        arguments: vec![
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                1, "<in>".to_string(), 1, 6)),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                2, "<in>".to_string(), 1, 8))
                        ]
                    }),
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "bar".to_string(), "<in>".to_string(), 1, 11),
                        arguments: vec![
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                3, "<in>".to_string(), 1, 15)),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                4, "<in>".to_string(), 1, 17))
                        ]
                    })
                ]
            }
        );
    }

    #[test]
    #[should_panic (expected = "Program must begin with an open bracket!")]
    fn must_start_with_open_bracket() {
        build(tokeniser::process("bla", "+ 1 2)"));
    }

    #[test]
    #[should_panic (expected = "foo/bar/b.a:1:6 EOF trying to build call")]
    fn missing_closing_bracket_panics_simple() {
        build(tokeniser::process("foo/bar/b.a", "     (+ 1  "));
    }

    #[test]
    #[should_panic (expected = "c.d:1:1 Missing function name for call")]
    fn must_have_fn_name() {
        build(tokeniser::process("c.d", "(     )"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:14 Missing function name for call")]
    fn must_have_fn_name_nested() {
        build(tokeniser::process("a.b", "(food (bla 1 () \"abc\"))"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:1 Function name must be a Symbol for call")]
    fn fn_name_must_be_symbol() {
        build(tokeniser::process("a.b", "(99 123 \"abc\")"));
    }
}
