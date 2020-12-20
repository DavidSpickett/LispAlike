use std::fmt;
use crate::tokeniser;

#[derive(Debug, PartialEq)]
pub enum ASTNode {
        String(String, String, usize, usize),
    Definition(String, String, usize, usize),
       Integer(i64,    String, usize, usize),
        Symbol(String, String, usize, usize),
          // TODO: limit to symbol somehow?
          Call(ASTNode, Vec<ASTNode>),
}

fn format_call(c: &ASTNode, mut indent: usize) -> String {
    let indent_str = tokeniser::padding(indent);
    indent += 4;
    let args_indent = tokeniser::padding(indent);

    format!("\n{}({}{}\n{})",
        indent_str,
        match c {
            ASTNode::Call(fn_name, _) => format!("{}", fn_name),
        },
        match c {
            ASTNode::Call(_, arguments) => arguments.iter().map(|node|
                format!("\n{}{}", args_indent, node))
                .collect::<String>(),
        },
        indent_str
    )
}

impl fmt::Display for ASTNode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ASTNode::Call(..)          => write!(f, "{}", format_call(self, 0)),
            ASTNode::String(s, ..)     => write!(f, "\"{}\"", s),
            ASTNode::Definition(d, ..) => write!(f, "'{}", d),
            ASTNode::Integer(i, ..)    => write!(f, "{}", i),
            ASTNode::Symbol(s, ..)     => write!(f, "{}", s)
        }
    }
}

// ! meaning the never type
fn panic_with_locaton(error: &str, filename: &str, start_line: usize, start_col: usize) -> ! {
    panic!("{}:{}:{} {}", filename, start_line, start_col, error)
}

fn build_call(tokens: &mut Vec<tokeniser::TokenType>) -> ASTNode {
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
                        arguments.push(build_call(tokens)),
                    // Any other token is an argument to the current call
                    Some(_) => {
                        let token = tokens.remove(0);
                        arguments.push(match token {
                            tokeniser::TokenType::String(s, fname, ln, cn) => ASTNode::String(s, fname, ln, cn),
                            tokeniser::TokenType::Definition(s, fname, ln, cn) => ASTNode::Definition(s, fname, ln, cn),
                            tokeniser::TokenType::Integer(i, fname, ln, cn) => ASTNode::Integer(i, fname, ln, cn),
                            tokeniser::TokenType::Symbol(s, fname, ln, cn) => ASTNode::Symbol(s, fname, ln, cn),
                            _ => panic!("Can't put this token into AST! {}", token)
                        })
                    }
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

    ASTNode::Call(fn_name, arguments)
}

pub fn build(mut tokens: Vec<tokeniser::TokenType>) -> ASTNode {
    let mut root_call = ASTNode::Call(
        ASTNode::Symbol(
            "root".to_string(), "<pseudo>".to_string(), 0, 0),
        vec![]
    );

    while !tokens.is_empty() {
        match root_call {
            ASTNode::Call(_, ref mut arguments) => {
                arguments.push(match tokens.first() {
                    Some(tokeniser::TokenType::OpenBracket(..)) => build_call(&mut tokens),
                    Some(_) => panic!("Program must begin with an open bracket!"),
                    None => panic!("Empty token list to build AST from!")
                })
            }
        }
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
        assert_eq!(build(tokeniser::process_into_tokens("<in>", "(+ 1 2 \"foo\")")),
        Call {
             fn_name: tokeniser::TokenType::Symbol(
                          "root".into(), "<pseudo>".into(), 0, 0),
             arguments: vec![
                CallOrToken::Call(Call{
                     fn_name: tokeniser::TokenType::Symbol(
                                  "+".into(), "<in>".into(), 1, 2),
                     arguments: vec![
                             CallOrToken::Token(tokeniser::TokenType::Integer(
                                 1, "<in>".into(), 1, 4)),
                             CallOrToken::Token(tokeniser::TokenType::Integer(
                                 2, "<in>".into(), 1, 6)),
                             CallOrToken::Token(tokeniser::TokenType::String(
                                 "foo".into(), "<in>".into(), 1, 8))
                        ]
                    })
            ]
        });
    }

    #[test]
    fn single_call_multi_line() {
        assert_eq!(build(tokeniser::process_into_tokens("foo.abc", "\
(abc
    (def
        \"a\"
        (ghi)
    )
    99
)")),
            Call {
                fn_name: tokeniser::TokenType::Symbol(
                             "root".into(), "<pseudo>".into(), 0, 0),
                arguments: vec![
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "abc".into(), "foo.abc".into(), 1, 2),
                        arguments: vec![
                            CallOrToken::Call(Call {
                                fn_name: tokeniser::TokenType::Symbol(
                                             "def".into(), "foo.abc".into(), 2, 6),
                                arguments: vec![
                                    CallOrToken::Token(tokeniser::TokenType::String(
                                        "a".into(), "foo.abc".into(), 3, 9)),
                                    CallOrToken::Call(Call {
                                        fn_name: tokeniser::TokenType::Symbol(
                                                     "ghi".into(), "foo.abc".into(), 4, 10),
                                        arguments: vec![],
                                    }),
                                ],
                            }),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                99, "foo.abc".into(), 6, 5)),
                        ],
                    })
                ]
            }
        );
    }

    #[test]
    fn multi_block() {
        assert_eq!(build(tokeniser::process_into_tokens("<in>", "(foo 1 2)(bar 3 4)")),
            Call {
                fn_name: tokeniser::TokenType::Symbol(
                             "root".into(), "<pseudo>".into(), 0, 0),
                arguments: vec![
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "foo".into(), "<in>".into(), 1, 2),
                        arguments: vec![
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                1, "<in>".into(), 1, 6)),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                2, "<in>".into(), 1, 8))
                        ]
                    }),
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol(
                                     "bar".into(), "<in>".into(), 1, 11),
                        arguments: vec![
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                3, "<in>".into(), 1, 15)),
                            CallOrToken::Token(tokeniser::TokenType::Integer(
                                4, "<in>".into(), 1, 17))
                        ]
                    })
                ]
            }
        );
    }

    #[test]
    #[should_panic (expected = "Program must begin with an open bracket!")]
    fn must_start_with_open_bracket() {
        build(tokeniser::process_into_tokens("bla", "+ 1 2)"));
    }

    #[test]
    #[should_panic (expected = "foo/bar/b.a:1:6 EOF trying to build call")]
    fn missing_closing_bracket_panics_simple() {
        build(tokeniser::process_into_tokens("foo/bar/b.a", "     (+ 1  "));
    }

    #[test]
    #[should_panic (expected = "c.d:1:1 Missing function name for call")]
    fn must_have_fn_name() {
        build(tokeniser::process_into_tokens("c.d", "(     )"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:14 Missing function name for call")]
    fn must_have_fn_name_nested() {
        build(tokeniser::process_into_tokens("a.b", "(food (bla 1 () \"abc\"))"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:1 Function name must be a Symbol for call")]
    fn fn_name_must_be_symbol() {
        build(tokeniser::process_into_tokens("a.b", "(99 123 \"abc\")"));
    }
}
