use std::fmt;
use crate::tokeniser;

// ! meaning the never type
fn panic_with_location(error: &str, filename: &str, start_line: usize, start_col: usize) -> ! {
    panic!("{}:{}:{} {}", filename, start_line, start_col, error)
}

pub fn panic_on_ast_type(error: &str, ast_type: &ASTType) -> ! {
    let (filename, line_number, column_number) = match ast_type {
            ASTType::String(_, fname, ln, cn) |
        ASTType::Definition(_, fname, ln, cn) |
           ASTType::Integer(_, fname, ln, cn) |
              ASTType::None(fname, ln, cn)    => (fname, *ln, *cn),
           ASTType::Symbol(s) => (&s.filename, s.line_number, s.column_number),
           ASTType::Function(f) => (&f.name.filename, f.name.line_number, f.name.column_number)
    };
    panic_with_location(error, filename, line_number, column_number);
}

fn panic_on_token(error: &str, token: &tokeniser::TokenType) -> ! {
    let (filename, line_number, column_number) = tokeniser::token_to_file_position(token);
    panic_with_location(error, &filename, line_number, column_number);
}

// Format a list of ASTTypes with spaces in between
pub fn format_asttype_list(arguments: &[ASTType]) -> String {
    arguments.iter().map(|a| format!("{}", a)).collect::<Vec<String>>().join(" ")
}

// This represents a user defined function
// (as opposed to the Call type that we build)
// This will enclose a Call amongst other things
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    pub name: Symbol,
    pub call: Call,
    // We use the ASTType here to retain the location info
    // TODO: just use Definition here?
    pub argument_names: Vec<ASTType>
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.name,
            format_asttype_list(&self.argument_names))
    }
}

// Symbol is it's own thing so we can require that call function names are symbols
#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub symbol: String,
    pub filename: String,
    pub line_number: usize,
    pub column_number: usize
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.symbol)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum ASTType {
        String(String, String, usize, usize),
    Definition(String, String, usize, usize),
       Integer(i64,    String, usize, usize),
          None(String, usize, usize),
        Symbol(Symbol),
        Function(Function),
}

impl fmt::Display for ASTType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ASTType::String(s, ..)     => write!(f, "\"{}\"", s),
            ASTType::Definition(d, ..) => write!(f, "'{}", d),
            ASTType::Integer(i, ..)    => write!(f, "{}", i),
            ASTType::Symbol(s, ..)     => write!(f, "{}", s),
            ASTType::Function(n, ..)   => write!(f, "{}", n),
            ASTType::None(..)          => write!(f, "none"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum CallOrType {
    Type(ASTType),
    Call(Call),
}

impl fmt::Display for CallOrType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CallOrType::Call(c) => write!(f, "{}", format_call(c, 0)),
            CallOrType::Type(t) => write!(f, "{}", t)
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Call {
    pub fn_name: Symbol,
    pub arguments: Vec<CallOrType>,
}

fn format_call(c: &Call, mut indent: usize) -> String {
    let indent_str = tokeniser::padding(indent);
    indent += 4;
    let args_indent = tokeniser::padding(indent);

    format!("\n{}({}{}\n{})",
        indent_str,
        format!("{}", c.fn_name),
        c.arguments.iter().map(|arg|
            match arg {
                CallOrType::Call(call_arg) => format!("{}{}", args_indent, format_call(call_arg, indent)),
                CallOrType::Type(type_arg) => format!("\n{}{}", args_indent, type_arg)
            })
            .collect::<String>(),
        indent_str
    )
}

impl fmt::Display for Call {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", format_call(self, 0))
    }
}

// Note that this is always going to return CallOrType::Call
fn build_call(tokens: &mut Vec<tokeniser::TokenType>) -> CallOrType {
    // We are garaunteed that the caller found a '('
    let start_bracket = tokens.remove(0);

    // TODO: we're assuming that fn names aren't calls themselves
    let mut arguments = Vec::new();
    let fn_name = match tokens.first() {
        Some(tokeniser::TokenType::CloseBracket(..)) =>
            panic_on_token("Missing function name for Call", &start_bracket),
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
                            tokeniser::TokenType::String(s, fname, ln, cn) =>
                                CallOrType::Type(ASTType::String(s, fname, ln, cn)),
                            tokeniser::TokenType::Definition(s, fname, ln, cn) =>
                                CallOrType::Type(ASTType::Definition(s, fname, ln, cn)),
                            tokeniser::TokenType::Integer(i, fname, ln, cn) =>
                                CallOrType::Type(ASTType::Integer(i, fname, ln, cn)),
                            tokeniser::TokenType::Symbol(s, fname, ln, cn) =>
                                CallOrType::Type(ASTType::Symbol(Symbol{
                                    symbol: s, filename: fname, line_number: ln, column_number: cn})),
                            _ => panic_on_token(&format!("Can't put {} token into AST!", token), &token)
                        })
                    }
                    None => panic_on_token("Got EOF while trying to build Call", &start_bracket),
                }
            }

            match fn_name_copy {
                tokeniser::TokenType::Symbol(s, fname, ln, cn) => Symbol{
                    symbol: s, filename: fname, line_number: ln, column_number: cn},
                _ => panic_on_token(&format!("fn_name_copy wasn't a Symbol it is {}",
                        fn_name_copy), &fn_name_copy)
            }
        }
        Some(_) => panic_on_token("Function name must be a Symbol for Call", &start_bracket),
        None => panic_on_token("Got EOF while trying to build Call", &start_bracket)
    };

    CallOrType::Call(Call{fn_name, arguments})
}

pub fn build(mut tokens: Vec<tokeniser::TokenType>) -> Call {
    // Programs are wrapped in a virtual (body ...) call
    let mut root_call = Call{
        fn_name: Symbol{
            symbol: "body".to_string(),
            filename: "<pseudo>".to_string(),
            line_number: 0,
            column_number: 0},
        arguments: vec![]
    };

    while !tokens.is_empty() {
        root_call.arguments.push(match tokens.first() {
            Some(tokeniser::TokenType::OpenBracket(..)) => build_call(&mut tokens),
            Some(t) => panic_on_token(&format!("Program must begin with an open bracket, not {}",
                            t), &t),
            None => panic!("Empty token list to build AST from!")
        })
    }

    root_call
}

#[cfg(test)]
mod tests {
    use ast::build;
    use ast::Call;
    use ast::Symbol;
    use ast::CallOrType;
    use ast::ASTType;
    use tokeniser;

    #[test]
    fn build_nothing_returns_root_call() {
        assert_eq!(build(Vec::new()),
            Call {
             fn_name: Symbol{
                          symbol: "body".into(), filename: "<pseudo>".into(),
                          line_number: 0, column_number: 0},
             arguments: Vec::new()
        });
    }

    #[test]
    fn single_call() {
        assert_eq!(build(tokeniser::process_into_tokens("<in>", "(+ 1 2 \"foo\")")),
        Call {
             fn_name: Symbol{
                          symbol: "body".into(), filename: "<pseudo>".into(),
                          line_number: 0, column_number: 0},
             arguments: vec![
                CallOrType::Call(Call{
                     fn_name: Symbol{
                                  symbol: "+".into(), filename: "<in>".into(),
                                  line_number: 1, column_number: 2},
                     arguments: vec![
                             CallOrType::Type(ASTType::Integer(
                                 1, "<in>".into(), 1, 4)),
                             CallOrType::Type(ASTType::Integer(
                                 2, "<in>".into(), 1, 6)),
                             CallOrType::Type(ASTType::String(
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
                fn_name: Symbol{
                             symbol: "body".into(), filename: "<pseudo>".into(),
                             line_number: 0, column_number: 0},
                arguments: vec![
                    CallOrType::Call(Call {
                        fn_name: Symbol{
                                     symbol: "abc".into(), filename: "foo.abc".into(),
                                     line_number: 1, column_number: 2},
                        arguments: vec![
                            CallOrType::Call(Call {
                                fn_name: Symbol{
                                             symbol: "def".into(), filename: "foo.abc".into(),
                                             line_number: 2, column_number: 6},
                                arguments: vec![
                                    CallOrType::Type(ASTType::String(
                                        "a".into(), "foo.abc".into(), 3, 9)),
                                    CallOrType::Call(Call {
                                        fn_name: Symbol{
                                                     symbol: "ghi".into(), filename: "foo.abc".into(),
                                                     line_number: 4, column_number: 10},
                                        arguments: vec![],
                                    }),
                                ],
                            }),
                            CallOrType::Type(ASTType::Integer(
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
                fn_name: Symbol{
                             symbol: "body".into(), filename: "<pseudo>".into(),
                             line_number: 0, column_number: 0},
                arguments: vec![
                    CallOrType::Call(Call {
                        fn_name: Symbol{
                                     symbol: "foo".into(), filename: "<in>".into(),
                                     line_number: 1, column_number: 2},
                        arguments: vec![
                            CallOrType::Type(ASTType::Integer(
                                1, "<in>".into(), 1, 6)),
                            CallOrType::Type(ASTType::Integer(
                                2, "<in>".into(), 1, 8))
                        ]
                    }),
                    CallOrType::Call(Call {
                        fn_name: Symbol{
                                     symbol: "bar".into(), filename: "<in>".into(),
                                     line_number: 1, column_number: 11},
                        arguments: vec![
                            CallOrType::Type(ASTType::Integer(
                                3, "<in>".into(), 1, 15)),
                            CallOrType::Type(ASTType::Integer(
                                4, "<in>".into(), 1, 17))
                        ]
                    })
                ]
            }
        );
    }

    #[test]
    #[should_panic (expected = "bla:1:1 Program must begin with an open bracket, not Symbol \"+\"\n<Couldn't open source file bla>")]
    fn must_start_with_open_bracket() {
        build(tokeniser::process_into_tokens("bla", "+ 1 2)"));
    }

    #[test]
    #[should_panic (expected = "foo/bar/b.a:1:6 Got EOF while trying to build Call")]
    fn missing_closing_bracket_panics_simple() {
        build(tokeniser::process_into_tokens("foo/bar/b.a", "     (+ 1  "));
    }

    #[test]
    #[should_panic (expected = "c.d:1:1 Missing function name for Call")]
    fn call_panics_must_have_fn_name() {
        build(tokeniser::process_into_tokens("c.d", "(     )"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:14 Missing function name for Call")]
    fn call_panics_must_have_fn_name_nested() {
        build(tokeniser::process_into_tokens("a.b", "(food (bla 1 () \"abc\"))"));
    }

    #[test]
    #[should_panic (expected = "a.b:1:1 Got EOF while trying to build Call")]
    fn call_panics_no_fn_name_no_end_bracket() {
        build(tokeniser::process_into_tokens("a.b", "("));
    }

    #[test]
    #[should_panic (expected = "a.b:1:1 Function name must be a Symbol for Call")]
    fn fn_name_must_be_symbol() {
        build(tokeniser::process_into_tokens("a.b", "(99 123 \"abc\")"));
    }
}
