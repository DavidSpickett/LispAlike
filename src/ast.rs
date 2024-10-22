use crate::tokeniser;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt;
use std::rc::Rc;
use tokeniser::SourceError;

// Concrete type so we can require argument names to be declarations
#[derive(Debug, PartialEq, Clone)]
pub struct Declaration {
    pub name: String,
    pub filename: String,
    pub line_number: usize,
    pub column_number: usize,
}

impl fmt::Display for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "'{}", self.name)
    }
}

pub fn format_declaration_list(declarations: &[Declaration]) -> String {
    declarations
        .iter()
        .map(|a| format!("{}", a))
        .collect::<Vec<String>>()
        .join(" ")
}

#[derive(Debug, PartialEq, Clone)]
pub struct BuiltinFunctionWrapper {
    pub name: Symbol,
}

impl fmt::Display for BuiltinFunctionWrapper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(builtin {})", self.name)
    }
}

// This represents a user defined function
// (as opposed to the Call type that we build)
// This will enclose a Call amongst other things
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    // Delcaraton makes more sense here, but it prints with the leading '
    // so just use symbol as a string plus location info.
    pub name: Symbol,
    pub call: Call,
    pub argument_names: Vec<Declaration>,
    // When we capture the scope during a lambda dedfine in a letrec, it isn't complete.
    // So we record a reference to the in progress scope (the Rc).
    // However, Rc doesn't let you modify the thing inside it,
    // so that's what the RefCell is for. We can give out a shared
    // reference to the in progress scope, while still updating it in the letrec handler.
    // Once the letrec finishes, captured_scope will be pointing
    // to the finished scope without needing to be updated.
    //
    // Note: If you did try to update it, manually you'd get into an infinite
    // loop (/immediate error). Imagine this was a copy of the scope.
    // When first defined it would have fn_name -> None, as expected,
    // lambda isn't defined yet.
    // Then we return to the letrec and add this new Function to the scope there.
    // So the scope in letrec has fn_name -> Some(Function) and that Function's
    // captured scope has fn_name -> None.
    //
    // If you were to recursively call this from the letrec scope then,
    // you would get one call, then fail beause the inner scope has
    // fn_name -> None.
    //
    // So you think, I could just put a new copy into the function
    // after the letrec is done. Well ok, let's try that.
    //
    // For each lambda name in the letrec scope let's update the corresponding
    // Function's captured scope to be a copy of the letrec scope.
    //
    // That means letrec scope would have fn_name -> Some(Function) and
    // that function will have a captured_scope of fn_name -> Some(Function).
    // Then *that* inner function will have a captured_scope of fn_name -> None
    // which came from the *original* captured scope.
    //
    // Doing this looks like it works, until you recurse deeply enough
    // and you get unknown function.
    //
    // It is for this reason that we must have the function have a reference
    // to the scope the letrec is creating. It creates a circular reference
    // from outer scope -> Function -> captured_scope (points back to outer scope)
    // -> Function ... etc etc etc
    //
    // This scope is created as shared so that it can live beyond the let/letrec that
    // created it.
    pub captured_scope: Rc<RefCell<Scope>>,
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({} {})",
            self.name,
            format_declaration_list(&self.argument_names)
        )
    }
}

// Symbol is it's own thing so we can require that call function names are symbols
#[derive(Debug, PartialEq, Clone)]
pub struct Symbol {
    pub symbol: String,
    pub filename: String,
    pub line_number: usize,
    pub column_number: usize,
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.symbol)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum ASTType {
    // Value, filename, line number, column number
    String(String, String, usize, usize),
    Integer(i64, String, usize, usize),
    List(Vec<ASTType>, String, usize, usize),
    Bool(bool, String, usize, usize),
    None(String, usize, usize),
    Declaration(Declaration),
    Symbol(Symbol),
    Function(Function),
    BuiltinFunctionWrapper(BuiltinFunctionWrapper),
}

// Option so we can support letrec, where names might be declared but not yet defined
pub type Scope = HashMap<String, Option<ASTType>>;
// Only used by defun so only Function values
pub type FunctionScope = HashMap<String, Function>;

impl fmt::Display for ASTType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ASTType::String(s, ..) => write!(f, "\"{}\"", s),
            ASTType::Declaration(d, ..) => write!(f, "{}", d),
            ASTType::Integer(i, ..) => write!(f, "{}", i),
            ASTType::Symbol(s, ..) => write!(f, "{}", s),
            ASTType::Function(n, ..) => write!(f, "{}", n),
            ASTType::BuiltinFunctionWrapper(n, ..) => write!(f, "{}", n),
            ASTType::Bool(b, ..) => write!(f, "{}", b),
            ASTType::None(..) => write!(f, "none"),
            ASTType::List(l, ..) => write!(f, "[{}]", format_asttype_list(l)),
        }
    }
}

impl SourceError {
    pub fn new_from_asttype(ast_type: &ASTType, msg: String) -> SourceError {
        let (filename, line_number, column_number) = match ast_type {
            ASTType::String(_, fname, ln, cn)
            | ASTType::Integer(_, fname, ln, cn)
            | ASTType::List(_, fname, ln, cn)
            | ASTType::Bool(_, fname, ln, cn)
            | ASTType::None(fname, ln, cn) => (fname, *ln, *cn),
            ASTType::Symbol(s) => (&s.filename, s.line_number, s.column_number),
            ASTType::BuiltinFunctionWrapper(f) => {
                (&f.name.filename, f.name.line_number, f.name.column_number)
            }
            ASTType::Function(f) => (&f.name.filename, f.name.line_number, f.name.column_number),
            ASTType::Declaration(d) => (&d.filename, d.line_number, d.column_number),
        };

        SourceError {
            filename: filename.to_string(),
            line_number: Some(line_number),
            column_number: Some(column_number),
            msg,
        }
    }
}

pub fn ast_type_err(error: &str, ast_type: &ASTType) -> SourceError {
    SourceError::new_from_asttype(ast_type, error.to_string())
}

// Format a list of ASTTypes with spaces in between
pub fn format_asttype_list(arguments: &[ASTType]) -> String {
    arguments
        .iter()
        .map(|a| format!("{}", a))
        .collect::<Vec<String>>()
        .join(" ")
}

pub fn format_asttype_typename_list(arguments: &[ASTType]) -> String {
    arguments
        .iter()
        .map(|a| asttype_typename(a))
        .collect::<Vec<&str>>()
        .join(", ")
}

pub fn asttype_typename(t: &ASTType) -> &str {
    match t {
        ASTType::String(..) => "String",
        ASTType::Declaration(..) => "Declaration",
        ASTType::Integer(..) => "Integer",
        ASTType::List(..) => "List",
        ASTType::Bool(..) => "Bool",
        ASTType::None(..) => "None",
        ASTType::Symbol(_) => "Symbol",
        ASTType::Function(_) => "Function",
        ASTType::BuiltinFunctionWrapper(..) => "BuiltinFunctionWrapper",
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Call {
    pub fn_name: Symbol,
    pub arguments: Vec<CallOrType>,
}

// A record of the callstack for error reporting
pub type CallStack = Vec<Call>;

pub fn format_call_stack(call_stack: &[Call]) -> String {
    // TODO: this needs to detect cycles to handle recursion better
    format!(
        "Traceback (most recent call last):\n{}",
        call_stack
            .iter()
            .map(|c| format!(
                "  {}:{}:{} {}",
                c.fn_name.filename,
                c.fn_name.line_number,
                c.fn_name.column_number,
                c.fn_name.symbol
            ))
            .collect::<Vec<String>>()
            .join("\n")
    )
}

fn format_call(c: &Call, mut indent: usize) -> String {
    let indent_str = tokeniser::padding(indent);
    indent += 4;
    let args_indent = tokeniser::padding(indent);

    format!(
        "\n{}({}{}\n{})",
        indent_str,
        format!("{}", c.fn_name),
        c.arguments
            .iter()
            .map(|arg| match arg {
                CallOrType::Call(call_arg) =>
                    format!("{}{}", args_indent, format_call(call_arg, indent)),
                CallOrType::Type(type_arg) => format!("\n{}{}", args_indent, type_arg),
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

#[derive(Debug, PartialEq, Clone)]
pub enum CallOrType {
    Type(ASTType),
    Call(Call),
}

impl fmt::Display for CallOrType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CallOrType::Call(c) => write!(f, "{}", format_call(c, 0)),
            CallOrType::Type(t) => write!(f, "{}", t),
        }
    }
}

// This is the type exec uses
pub enum Comparison {
    Equal,
    NotEqual,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

impl From<Comparison> for String {
    fn from(c: Comparison) -> String {
        String::from(match c {
            Comparison::Equal => "eq",
            Comparison::NotEqual => "ne",
            Comparison::LessThan => "<",
            Comparison::LessThanOrEqual => "<=",
            Comparison::GreaterThan => ">",
            Comparison::GreaterThanOrEqual => ">=",
        })
    }
}

// These types are used to categorise the comparisons
// (without having to have unreachable _ => panic!:)
// It's a lot of boilerplate but hey it's fun.
enum OrderedComparison {
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
}

enum UnorderedComparison {
    Equal,
    NotEqual,
}

enum ComparisonWithOrder {
    Ordered(OrderedComparison),
    Unordered(UnorderedComparison),
}

impl From<&Comparison> for ComparisonWithOrder {
    fn from(c: &Comparison) -> ComparisonWithOrder {
        match c {
            Comparison::Equal => ComparisonWithOrder::Unordered(UnorderedComparison::Equal),
            Comparison::NotEqual => ComparisonWithOrder::Unordered(UnorderedComparison::NotEqual),
            Comparison::LessThan => ComparisonWithOrder::Ordered(OrderedComparison::LessThan),
            Comparison::LessThanOrEqual => {
                ComparisonWithOrder::Ordered(OrderedComparison::LessThanOrEqual)
            }
            Comparison::GreaterThan => ComparisonWithOrder::Ordered(OrderedComparison::GreaterThan),
            Comparison::GreaterThanOrEqual => {
                ComparisonWithOrder::Ordered(OrderedComparison::GreaterThanOrEqual)
            }
        }
    }
}

pub fn cannot_compare_err(
    function: &ASTType,
    t1: &ASTType,
    t2: &ASTType,
    kind: Comparison,
) -> SourceError {
    ast_type_err(
        &format!(
            "Cannot do {} comparison {} on types {} and {}",
            match kind {
                Comparison::NotEqual | Comparison::Equal => "equality",
                _ => "ordered",
            },
            String::from(kind),
            asttype_typename(t1),
            asttype_typename(t2)
        ),
        function,
    )
}

pub fn compare_asttypes(
    function: &ASTType,
    t1: &ASTType,
    t2: &ASTType,
    kind: Comparison,
) -> Result<bool, SourceError> {
    let spaceship_result = spaceship_compare_asttypes(t1, t2);
    match ComparisonWithOrder::from(&kind) {
        ComparisonWithOrder::Ordered(ordered_kind) => match spaceship_result {
            Some(v) => match ordered_kind {
                OrderedComparison::LessThan => Ok(v == -1),
                OrderedComparison::LessThanOrEqual => Ok(v < 1),
                OrderedComparison::GreaterThan => Ok(v == 1),
                OrderedComparison::GreaterThanOrEqual => Ok(v >= 0),
            },
            None => Err(cannot_compare_err(function, t1, t2, kind)),
        },
        ComparisonWithOrder::Unordered(unordered_kind) => match spaceship_result {
            Some(v) => match unordered_kind {
                UnorderedComparison::Equal => Ok(v == 0),
                UnorderedComparison::NotEqual => Ok(v != 0),
            },
            None => match equality_compare_asttypes(t1, t2) {
                Some(v) => match unordered_kind {
                    UnorderedComparison::Equal => Ok(v),
                    UnorderedComparison::NotEqual => Ok(!v),
                },
                None => Err(cannot_compare_err(function, t1, t2, kind)),
            },
        },
    }
}

fn spaceship_compare_asttypes(t1: &ASTType, t2: &ASTType) -> Option<i64> {
    match (t1, t2) {
        (ASTType::Integer(i1, ..), ASTType::Integer(i2, ..)) => match i1.cmp(i2) {
            std::cmp::Ordering::Greater => Some(1),
            std::cmp::Ordering::Equal => Some(0),
            std::cmp::Ordering::Less => Some(-1),
        },
        (_, _) => None,
    }
}

fn equality_compare_asttypes(t1: &ASTType, t2: &ASTType) -> Option<bool> {
    match (t1, t2) {
        (ASTType::Integer(i1, ..), ASTType::Integer(i2, ..)) => Some(i1 == i2),
        (ASTType::String(s1, ..), ASTType::String(s2, ..)) => Some(s1 == s2),
        (ASTType::None(..), ASTType::None(..)) => Some(true),
        (ASTType::Bool(b1, ..), ASTType::Bool(b2, ..)) => Some(b1 == b2),
        (ASTType::List(l1, ..), ASTType::List(l2, ..)) => {
            if l1.len() != l2.len() {
                Some(false)
            } else {
                let mut result = true;
                for (item1, item2) in l1.iter().zip(l2.iter()) {
                    match equality_compare_asttypes(item1, item2) {
                        Some(v) => {
                            if !v {
                                result = false;
                                // Bail early
                                break;
                            }
                        }
                        None => {
                            // Meaning that a list of different types can be compared but
                            // will always be not equal.
                            result = false;
                            break;
                        }
                    };
                }
                Some(result)
            }
        }
        // Allow anything to be compared against none. For things like if find bla is none etc.
        (ASTType::None(..), _) | (_, ASTType::None(..)) => Some(false),
        (_, _) => None,
    }
}

pub fn ast_type_to_bool(ast_type: &ASTType) -> Result<bool, SourceError> {
    match ast_type {
        ASTType::String(s, ..) => Ok(!s.is_empty()),
        ASTType::Integer(i, ..) => Ok(*i != 0),
        ASTType::List(l, ..) => Ok(!l.is_empty()),
        ASTType::None(..) => Ok(false),
        ASTType::Bool(b, ..) => Ok(*b),
        ASTType::Declaration(..) => {
            Err(ast_type_err("Can't convert Declaration to bool", ast_type))
        }
        ASTType::Symbol(..) => Err(ast_type_err("Can't convert Symbol to bool", ast_type)),
        ASTType::Function(..) => Err(ast_type_err("Can't convert Function to bool", ast_type)),
        ASTType::BuiltinFunctionWrapper(..) => Err(ast_type_err(
            "Can't convert BuiltinFunctionWrapper to bool",
            ast_type,
        )),
    }
}

// Note that this is always going to return CallOrType::Call
fn build_call(tokens: &mut VecDeque<tokeniser::TokenType>) -> Result<CallOrType, SourceError> {
    // We are garaunteed that the caller found a '('
    let start_bracket = tokens.pop_front().unwrap();

    let mut arguments = Vec::new();
    let fn_name = match tokens.front() {
        Some(tokeniser::TokenType::CloseBracket(..)) => {
            return Err(tokeniser::token_err(
                "Missing function name for Call",
                &start_bracket,
            ))
        }
        // Only allow symbols for function name
        Some(tokeniser::TokenType::Symbol(..)) => {
            // Must do this now before subsequent build_call removes it
            let fn_name_copy = tokens.pop_front().unwrap();

            loop {
                match tokens.front() {
                    // Finishes a call
                    Some(tokeniser::TokenType::CloseBracket(..)) => {
                        tokens.pop_front();
                        break;
                    }
                    // Starts a new call
                    Some(tokeniser::TokenType::OpenBracket(..)) => {
                        arguments.push(build_call(tokens)?)
                    }
                    // Any other token is an argument to the current call
                    Some(_) => {
                        let token = tokens.pop_front().unwrap();
                        arguments.push(match token {
                            tokeniser::TokenType::String(s, fname, ln, cn) => {
                                CallOrType::Type(ASTType::String(s, fname, ln, cn))
                            }
                            tokeniser::TokenType::Declaration(s, fname, ln, cn) => {
                                CallOrType::Type(ASTType::Declaration(Declaration {
                                    name: s,
                                    filename: fname,
                                    line_number: ln,
                                    column_number: cn,
                                }))
                            }
                            tokeniser::TokenType::Integer(i, fname, ln, cn) => {
                                CallOrType::Type(ASTType::Integer(i, fname, ln, cn))
                            }
                            tokeniser::TokenType::Symbol(s, fname, ln, cn) => match s.as_str() {
                                "true" => CallOrType::Type(ASTType::Bool(true, fname, ln, cn)),
                                "false" => CallOrType::Type(ASTType::Bool(false, fname, ln, cn)),
                                _ => CallOrType::Type(ASTType::Symbol(Symbol {
                                    symbol: s,
                                    filename: fname,
                                    line_number: ln,
                                    column_number: cn,
                                })),
                            },
                            _ => {
                                return Err(tokeniser::token_err(
                                    &format!("Can't put {} token into AST!", token),
                                    &token,
                                ))
                            }
                        })
                    }
                    None => {
                        return Err(tokeniser::token_err(
                            "Got EOF while trying to build Call, \
                                                             missing closing bracket?",
                            &start_bracket,
                        ))
                    }
                }
            }

            match fn_name_copy {
                tokeniser::TokenType::Symbol(s, fname, ln, cn) => Symbol {
                    symbol: s,
                    filename: fname,
                    line_number: ln,
                    column_number: cn,
                },
                _ => {
                    return Err(tokeniser::token_err(
                        &format!("fn_name_copy wasn't a Symbol it is {}", fn_name_copy),
                        &fn_name_copy,
                    ))
                }
            }
        }
        Some(_) => {
            return Err(tokeniser::token_err(
                "Function name must be a Symbol for Call",
                &start_bracket,
            ))
        }
        None => {
            return Err(tokeniser::token_err(
                "Got EOF while trying to build Call",
                &start_bracket,
            ))
        }
    };

    Ok(CallOrType::Call(Call { fn_name, arguments }))
}

pub fn build(mut tokens: VecDeque<tokeniser::TokenType>) -> Result<Call, SourceError> {
    // Programs are wrapped in a virtual (body ...) call
    let mut root_call = Call {
        fn_name: Symbol {
            symbol: "body".to_string(),
            filename: "<pseudo>".to_string(),
            line_number: 0,
            column_number: 0,
        },
        arguments: vec![],
    };

    while !tokens.is_empty() {
        root_call.arguments.push(match tokens.front() {
            Some(tokeniser::TokenType::OpenBracket(..)) => build_call(&mut tokens)?,
            Some(t) => {
                return Err(tokeniser::token_err(
                    &format!("Program must begin with an open bracket, not {}", t),
                    &t,
                ))
            }
            None => {
                return Err(SourceError::new_from_filename(
                    "FIXME!",
                    "Empty token list to build AST from!".to_string(),
                ))
            }
        })
    }

    Ok(root_call)
}

#[cfg(test)]
mod tests {
    use ast::build;
    use ast::ASTType;
    use ast::Call;
    use ast::CallOrType;
    use ast::Symbol;
    use std::collections::VecDeque;
    use tokeniser;
    use tokeniser::SourceError;

    #[test]
    fn build_nothing_returns_root_call() {
        assert_eq!(
            build(VecDeque::new()).unwrap(),
            Call {
                fn_name: Symbol {
                    symbol: "body".into(),
                    filename: "<pseudo>".into(),
                    line_number: 0,
                    column_number: 0
                },
                arguments: Vec::new()
            }
        );
    }

    #[test]
    fn single_call() {
        assert_eq!(
            build(tokeniser::process_into_tokens("<in>", "(+ 1 2 \"foo\")").unwrap()).unwrap(),
            Call {
                fn_name: Symbol {
                    symbol: "body".into(),
                    filename: "<pseudo>".into(),
                    line_number: 0,
                    column_number: 0
                },
                arguments: vec![CallOrType::Call(Call {
                    fn_name: Symbol {
                        symbol: "+".into(),
                        filename: "<in>".into(),
                        line_number: 1,
                        column_number: 2
                    },
                    arguments: vec![
                        CallOrType::Type(ASTType::Integer(1, "<in>".into(), 1, 4)),
                        CallOrType::Type(ASTType::Integer(2, "<in>".into(), 1, 6)),
                        CallOrType::Type(ASTType::String("foo".into(), "<in>".into(), 1, 8))
                    ]
                })]
            }
        );
    }

    #[test]
    fn single_call_multi_line() {
        assert_eq!(
            build(
                tokeniser::process_into_tokens(
                    "foo.abc",
                    "\
(abc
    (def
        \"a\"
        (ghi)
    )
    99
)"
                )
                .unwrap()
            )
            .unwrap(),
            Call {
                fn_name: Symbol {
                    symbol: "body".into(),
                    filename: "<pseudo>".into(),
                    line_number: 0,
                    column_number: 0
                },
                arguments: vec![CallOrType::Call(Call {
                    fn_name: Symbol {
                        symbol: "abc".into(),
                        filename: "foo.abc".into(),
                        line_number: 1,
                        column_number: 2
                    },
                    arguments: vec![
                        CallOrType::Call(Call {
                            fn_name: Symbol {
                                symbol: "def".into(),
                                filename: "foo.abc".into(),
                                line_number: 2,
                                column_number: 6
                            },
                            arguments: vec![
                                CallOrType::Type(ASTType::String(
                                    "a".into(),
                                    "foo.abc".into(),
                                    3,
                                    9
                                )),
                                CallOrType::Call(Call {
                                    fn_name: Symbol {
                                        symbol: "ghi".into(),
                                        filename: "foo.abc".into(),
                                        line_number: 4,
                                        column_number: 10
                                    },
                                    arguments: vec![],
                                }),
                            ],
                        }),
                        CallOrType::Type(ASTType::Integer(99, "foo.abc".into(), 6, 5)),
                    ],
                })]
            }
        );
    }

    #[test]
    fn multi_block() {
        assert_eq!(
            build(tokeniser::process_into_tokens("<in>", "(foo 1 2)(bar 3 4)").unwrap()).unwrap(),
            Call {
                fn_name: Symbol {
                    symbol: "body".into(),
                    filename: "<pseudo>".into(),
                    line_number: 0,
                    column_number: 0
                },
                arguments: vec![
                    CallOrType::Call(Call {
                        fn_name: Symbol {
                            symbol: "foo".into(),
                            filename: "<in>".into(),
                            line_number: 1,
                            column_number: 2
                        },
                        arguments: vec![
                            CallOrType::Type(ASTType::Integer(1, "<in>".into(), 1, 6)),
                            CallOrType::Type(ASTType::Integer(2, "<in>".into(), 1, 8))
                        ]
                    }),
                    CallOrType::Call(Call {
                        fn_name: Symbol {
                            symbol: "bar".into(),
                            filename: "<in>".into(),
                            line_number: 1,
                            column_number: 11
                        },
                        arguments: vec![
                            CallOrType::Type(ASTType::Integer(3, "<in>".into(), 1, 15)),
                            CallOrType::Type(ASTType::Integer(4, "<in>".into(), 1, 17))
                        ]
                    })
                ]
            }
        );
    }

    #[test]
    fn must_start_with_open_bracket_error() {
        assert_eq!(
            build(tokeniser::process_into_tokens("bla", "+ 1 2)").unwrap()),
            Err(SourceError {
                filename: "bla".into(),
                line_number: Some(1),
                column_number: Some(1),
                msg: "Program must begin with an open bracket, not Symbol \"+\"".to_string(),
            })
        );
    }

    #[test]
    fn missing_closing_bracket_error_simple() {
        assert_eq!(
            build(tokeniser::process_into_tokens("foo/bar/b.a", "     (+ 1  ").unwrap()),
            Err(SourceError {
                filename: "foo/bar/b.a".into(),
                line_number: Some(1),
                column_number: Some(6),
                msg: "Got EOF while trying to build Call, missing closing bracket?".into(),
            })
        );
    }

    #[test]
    fn call_error_must_have_fn_name_error() {
        assert_eq!(
            build(tokeniser::process_into_tokens("c.d", "(     )").unwrap()),
            Err(SourceError {
                filename: "c.d".into(),
                line_number: Some(1),
                column_number: Some(1),
                msg: "Missing function name for Call".to_string()
            })
        );
    }

    #[test]
    fn call_error_must_have_fn_name_nested() {
        assert_eq!(
            build(tokeniser::process_into_tokens("a.b", "(food (bla 1 () \"abc\"))").unwrap()),
            Err(SourceError {
                filename: "a.b".into(),
                line_number: Some(1),
                column_number: Some(14),
                msg: "Missing function name for Call".to_string()
            })
        );
    }

    #[test]
    fn call_error_no_fn_name_no_end_bracket() {
        assert_eq!(
            build(tokeniser::process_into_tokens("a.b", "(").unwrap()),
            Err(SourceError {
                filename: "a.b".into(),
                line_number: Some(1),
                column_number: Some(1),
                msg: "Got EOF while trying to build Call".to_string()
            })
        );
    }

    #[test]
    fn fn_name_must_be_symbol_error() {
        assert_eq!(
            build(tokeniser::process_into_tokens("a.b", "(99 123 \"abc\")").unwrap()),
            Err(SourceError {
                filename: "a.b".into(),
                line_number: Some(1),
                column_number: Some(1),
                msg: "Function name must be a Symbol for Call".to_string()
            })
        );
    }

    #[test]
    fn true_false_become_bool() {
        // Check that true/false in function name position becomes a symbol for a call
        // Anything else converted into ASTType::Bool
        assert_eq!(
            build(tokeniser::process_into_tokens("<in>", "(true true false)").unwrap()).unwrap(),
            Call {
                fn_name: Symbol {
                    symbol: "body".into(),
                    filename: "<pseudo>".into(),
                    line_number: 0,
                    column_number: 0
                },
                arguments: vec![CallOrType::Call(Call {
                    fn_name: Symbol {
                        symbol: "true".into(),
                        filename: "<in>".into(),
                        line_number: 1,
                        column_number: 2
                    },
                    arguments: vec![
                        CallOrType::Type(ASTType::Bool(true, "<in>".into(), 1, 7)),
                        CallOrType::Type(ASTType::Bool(false, "<in>".into(), 1, 12)),
                    ]
                })]
            }
        );
    }
}
