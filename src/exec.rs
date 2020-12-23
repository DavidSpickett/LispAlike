use crate::ast;
use std::collections::HashMap;

type Scope = HashMap<String, ast::ASTType>;
type Executor = fn(Vec<ast::ASTType>) -> ast::ASTType;
type BreadthExecutor = fn(Vec<ast::CallOrType>, Scope)
                        -> (Vec<ast::CallOrType>, Scope);

fn breadth_builtin_let(mut arguments: Vec<ast::CallOrType>, mut local_scope: Scope)
    -> (Vec<ast::CallOrType>, Scope) {
    // Let should have the form:
    // (let <defintion> <value> <defintion2> <value2> ... <call>)
    if arguments.len() < 3 {
        panic!("let requires at least 3 arguments!");
    }

    if (arguments.len() % 2) == 0 {
        // TODO: we're missing location info here, should print types too
        panic!("Wrong number of arguments to len!");
    }

    for pair in arguments.chunks(2) {
        let mut pair = pair.to_vec();

        // Check for the body of the let call
        if pair.len() == 1 {
            break;
        }

        // If the value is the result of a call, resolve it
        if let ast::CallOrType::Call(c) = &pair[1] {
            pair[1] = ast::CallOrType::Type(
                exec_inner(c.clone(), local_scope.clone()));
        };

        // Otherwise we got some definition
        match (&pair[0], &pair[1]) {
            (ast::CallOrType::Type(t1), ast::CallOrType::Type(t2)) =>
                match t1 {
                    ast::ASTType::Definition(def, ..) =>
                        match t2 {
                            // This should have been done by exec_inner
                            ast::ASTType::Symbol(s) =>
                                panic!("Unresolved symbol {} for let pair value!", s),
                            _ => local_scope.insert(def.into(), t2.clone())
                        }
                    _ => panic!("Expected definition type as first of let pair!")
                }
            (_, _) => panic!("Unresolved call in let definition pair!")
        };
    }

    // Remove any name-value arguments
    (arguments.split_off(arguments.len()-2), local_scope)
}

fn builtin_let(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        // TODO: where do we validate the structure of these calls?
        None => panic!("let call must have at least one argument to return!")
    }
}

fn builtin_plus(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    if arguments.is_empty() {
        panic!("Function + requires at least one argument!");
    }

    match arguments[0] {
        // If the first argument is type T, proceed as if the
        // rest are T, otherwise panic
        ast::ASTType::Integer(..) => ast::ASTType::Integer(
            arguments.iter()
                .map(|a| match a {
                        ast::ASTType::Integer(i, ..) => i,
                        // TODO: show specific argument?
                        _ => panic!("Some arguments to + are not integer!")
                })
                .sum(),
                "runtime".into(), 0, 0),
        ast::ASTType::String(..) => ast::ASTType::String(
            arguments.iter()
                .map(|a| match a {
                        ast::ASTType::String(s, ..) => s.to_owned(),
                        // TODO: show specific argument?
                        _ => panic!("Some arguments to + are not string!")
                })
                .collect::<Vec<String>>()
                .concat(),
                "runtime".into(), 0, 0),
        _ => panic!("Cannot + argument of type {:?}!", arguments[0])
    }
}

// TODO: this is basically the (body ) call
fn builtin_dunder_root(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        None => panic!("__root call must have at least one argument to return!")
    }
}

// TODO: test me
fn builtin_print(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // TODO: assuming newline
    println!("{}", arguments.iter().map(|a| format!("{}", a)).collect::<Vec<String>>().join(" "));
    // TODO: void type? (None might be a better name)
    ast::ASTType::Integer(1, "runtime".into(), 0, 0)
}

fn exec_inner(call: ast::Call, local_scope: Scope) -> ast::ASTType {
    // breadth_executor does any breadth first evaluation
    // For example let. (let 'a 1 (print a))
    // This must add "a" to the local scope before we can
    // *depth first* execute the print.
    // This is optional since most calls can just use depth
    // first processing.
    let (breadth_executor, executor):
        (Option<BreadthExecutor>, Executor) =
            match call.fn_name.symbol.as_str() {
            "__root" => (None,                      builtin_dunder_root),
                 "+" => (None,                      builtin_plus),
             "print" => (None,                      builtin_print),
             "let"   => (Some(breadth_builtin_let), builtin_let),
            _ => panic!("Unknown function {}!", call.fn_name.symbol)
    };

    // First resolve all symbols
    let arguments = call.arguments.iter().map(
        |arg| match arg {
            ast::CallOrType::Type(t) => match t {
                ast::ASTType::Symbol(s) =>
                    match local_scope.get(&s.symbol) {
                        Some(t) => ast::CallOrType::Type(t.clone()),
                        None => panic!("{}:{}:{} Symbol {} not found in local scope!",
                                        s.filename, s.line_number, s.column_number, s.symbol)
                    },
                _ => ast::CallOrType::Type(t.clone())
            },
            _ => arg.clone()
        }).collect::<Vec<ast::CallOrType>>();

    // Then do any breadth first evaluations (e.g. let)
    let (arguments, local_scope) = match breadth_executor {
        Some(f) => f(arguments, local_scope),
        None => (arguments, local_scope)
    };

    // Now resolve all Calls in the remaining arguments
    // (this is depth first, as opposed to breadth first as above)
    let arguments = arguments.iter().map(
        |a| match a {
            ast::CallOrType::Call(c) => exec_inner(c.clone(), local_scope.clone()),
            ast::CallOrType::Type(t) => t.clone()
        }).collect::<Vec<ast::ASTType>>();

    // Finally run the current function with all Symbols and Calls resolved
    executor(arguments)
}

// TODO: defun could return a function here
pub fn exec(call: ast::Call) -> ast::ASTType {
    let local_scope = HashMap::new();
    // You would declare global and inital local scope here
    exec_inner(call, local_scope)
}

#[cfg(test)]
mod tests {
    use exec::exec;
    use crate::tokeniser::process_into_tokens;
    use ast::build;
    use ast::ASTType;

    fn exec_program(program: &str) -> ASTType {
        exec(build(process_into_tokens("<in>", program)))
    }

    fn check_program_result(program: &str, expected: ASTType) {
        assert_eq!(exec_program(program), expected);
    }

    #[test]
    fn test_simple_exec() {
        // Simple single call
        check_program_result("(+ 1 2)", ASTType::Integer(3, "runtime".into(), 0, 0));
        // Result is the result of the last block
        check_program_result("(+ 1 2)(+ 9 10)", ASTType::Integer(19, "runtime".into(), 0, 0));
        // We can process nested calls
        check_program_result("(+ (+ 1 (+ 2 3)) 2)", ASTType::Integer(8, "runtime".into(), 0, 0));
    }

    #[test]
    fn test_builtin_plus() {
        // Strings and integers can be added
        check_program_result("(+ 9 10)", ASTType::Integer(19, "runtime".into(), 0, 0));
        check_program_result("(+ \"foo\" \"bar\")", ASTType::String("foobar".into(), "runtime".into(), 0, 0));

        // We can handle any number of arguments
        check_program_result("(+ 9 10 11 12)", ASTType::Integer(42, "runtime".into(), 0, 0));
        check_program_result("(+ \"a\" \"b\" \"c\" \"d\")", ASTType::String("abcd".into(), "runtime".into(), 0, 0));

        // Minimum of 1 argument
        check_program_result("(+ 99)", ASTType::Integer(99, "runtime".into(), 0, 0));
        check_program_result("(+ \"def\")", ASTType::String("def".into(), "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected="Function + requires at least one argument!")]
    fn test_builtin_plus_panics_no_arguments() {
        exec_program("(+)");
    }

    #[test]
    #[should_panic (expected="Some arguments to + are not integer!")]
    fn test_builtin_plus_panics_mismatched_arg_types_integer() {
        exec_program("(+ 1 \"2\")");
    }

    #[test]
    #[should_panic (expected="Some arguments to + are not string!")]
    fn test_builtin_plus_panics_mismatched_arg_types_string() {
        exec_program("(+ \"2\" 1)");
    }

    #[test]
    fn test_builtin_let() {
        // Simple definition is visible in later call
        check_program_result("(let 'a 2 (+ a))",
            ASTType::Integer(2, "runtime".into(), 0, 0));

        // Local scope is inherited from previous call
        check_program_result("(let 'a 2 (+ (+ a) 4))",
            ASTType::Integer(6, "runtime".into(), 0, 0));

        // Symbols are resolved before let is applied
        check_program_result("
            (let 'a 2
                (let 'b a
                    (+ b)
                )
            )",
            ASTType::Integer(2, "runtime".into(), 0, 0));

        // Redefintions shadow earlier values and can change types
        check_program_result("
            (let 'a 2
                (let 'a \"abc\"
                    (+ a)
                )
            )",
            ASTType::String("abc".into(), "runtime".into(), 0, 0));

        // Values that are calls are resolved before putting into scope
        check_program_result("
            (let
                'zzz (+ \"cat\" \"dog\")
                (+ zzz)
            )",
            ASTType::String("catdog".into(), "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "Wrong number of arguments to len!")]
    fn test_let_panics_even_number_of_arguments() {
        exec_program("(let 'a 1 'b 2)");
    }

    #[test]
    #[should_panic (expected = "let requires at least 3 arguments!")]
    fn test_let_panics_too_few_arguments() {
        exec_program("(let 'a)");
    }
}
