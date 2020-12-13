use crate::tokeniser;

#[derive(Debug, PartialEq)]
pub enum CallOrToken {
    Token(tokeniser::TokenType),
    // TODO: bad name
    Call(Call),
}

#[derive(Debug, PartialEq)]
pub struct Call {
    // TODO: can we restrict the type here?
    pub fn_name: tokeniser::TokenType,
    pub arguments: Vec<CallOrToken>,
}

// TODO: iterator would be easier?
fn build_call(tokens: &mut Vec<tokeniser::TokenType>) -> CallOrToken {
    // We are garaunteed that the caller found a '('
    let start_bracket = tokens.remove(0);
    let (start_line, start_col) = tokeniser::token_to_line_column_number(start_bracket);

    // TODO: better soloution for this init state
    let mut new_call = Call {
        fn_name : tokeniser::TokenType::Symbol("!invalid!".to_string(), 0, 0),
        arguments : Vec::new()
    };

    // TODO: a pop_front Option<T> would be super cool here
    // TODO: we're assuming that fn names aren't calls themselves
    new_call.fn_name = match tokens.first() {
        Some(tokeniser::TokenType::CloseBracket(_, _, _)) =>
            panic!("Missing function name for call starting from line {} column {}!", start_line, start_col),
        // Only allow symbols for function name
        Some(tokeniser::TokenType::Symbol(_, _, _)) => {
            // Must do this now before subsequent build_call remove it
            let fn_name_copy = tokens.remove(0);

            loop {
                match tokens.first() {
                    // Finishes a call
                    Some(tokeniser::TokenType::CloseBracket(_, _, _)) => {
                        tokens.remove(0);
                        break
                    },
                    // Starts a new call
                    Some(tokeniser::TokenType::OpenBracket(_, _, _)) => new_call.arguments.push(build_call(tokens)),
                    Some(_) => new_call.arguments.push(CallOrToken::Token(tokens.remove(0))),
                    None => panic!("EOF trying to build call starting from line {} column {}!", start_line, start_col)
                }
            }

            fn_name_copy
        }
        Some(_) => panic!("Function name must be a Symbol for call starting from line {}, column {}!", start_line, start_col),
        None => panic!("EOF trying to build call starting from line {} column {}!", start_line, start_col),
    };

    CallOrToken::Call(new_call)
}

// Later Vec<Call> with multiple blocks
pub fn build(mut tokens: Vec<tokeniser::TokenType>) -> Call {
    match tokens.first() {
        // Must start with open bracket
        Some(tokeniser::TokenType::OpenBracket(_, _, _)) => {
            match build_call(&mut tokens) {
                CallOrToken::Call(c) => c,
                CallOrToken::Token(_) => {
                    panic!("build ended up with a token not a call?!");
                }
            }
        }
        Some(_) => panic!("Program must begin with an open bracket!"),
        None => panic!("Empty token list to build AST from!")
    }
}

#[cfg(test)]
mod tests {
    use ast::build;
    use ast::Call;
    use ast::CallOrToken;
    use tokeniser;

    #[test]
    fn single_call() {
        assert_eq!(build(tokeniser::process("(+ 1 2 \"foo\")")),
        Call {
             fn_name: tokeniser::TokenType::Symbol("+".to_string(), 1, 2),
             arguments: vec![
                     CallOrToken::Token(tokeniser::TokenType::Integer(1, 1, 4)),
                     CallOrToken::Token(tokeniser::TokenType::Integer(2, 1, 6)),
                     CallOrToken::Token(tokeniser::TokenType::String("foo".to_string(), 1, 8))]});

        assert_eq!(build(tokeniser::process("\
(abc
    (def
        \"a\"
        (ghi)
    )
    99
)")),
            Call {
                fn_name: tokeniser::TokenType::Symbol("abc".to_string(), 1, 2),
                arguments: vec![
                    CallOrToken::Call(Call {
                        fn_name: tokeniser::TokenType::Symbol("def".to_string(), 2, 6),
                        arguments: vec![
                            CallOrToken::Token(tokeniser::TokenType::String("a".to_string(), 3, 9)),
                            CallOrToken::Call(Call {
                                fn_name: tokeniser::TokenType::Symbol("ghi".to_string(), 4, 10),
                                arguments: vec![],
                            }),
                        ],
                    }),
                    CallOrToken::Token(tokeniser::TokenType::Integer(99, 6, 5)),
                ],
            }
        );
    }

    #[test]
    #[should_panic (expected = "Program must begin with an open bracket!")]
    fn must_start_with_open_bracket() {
        build(tokeniser::process("+ 1 2)"));
    }

    #[test]
    #[should_panic (expected = "EOF trying to build call starting from line 1 column 6!")]
    fn missing_closing_bracket_panics_simple() {
        build(tokeniser::process("     (+ 1  "));
    }

    #[test]
    #[should_panic (expected = "Missing function name for call starting from line 1 column 1!")]
    fn must_have_fn_name() {
        build(tokeniser::process("(     )"));
    }

    #[test]
    #[should_panic (expected = "Missing function name for call starting from line 1 column 14!")]
    fn must_have_fn_name_nested() {
        build(tokeniser::process("(food (bla 1 () \"abc\"))"));
    }

    #[test]
    #[should_panic (expected = "Function name must be a Symbol for call starting from line 1, column 1!")]
    fn fn_name_must_be_symbol() {
        build(tokeniser::process("(99 123 \"abc\")"));
    }
}
