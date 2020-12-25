use crate::ast;
use std::collections::HashMap;

type Scope = HashMap<String, ast::ASTType>;
// First argument is either the Symbol for the function name (builtins)
// or an actual Functon (for user defined functions). This carries
// the locaton info for the call.
type Executor = fn(ast::ASTType, Vec<ast::ASTType>) -> ast::ASTType;
// Again first argument is the function/function name being executed
// and lets us use its location info.
type BreadthExecutor = fn(ast::ASTType, Vec<ast::CallOrType>, Scope)
                        -> (Vec<ast::CallOrType>, Scope);

fn breadth_builtin_lambda(function: ast::ASTType, mut arguments: Vec<ast::CallOrType>, local_scope: Scope)
    -> (Vec<ast::CallOrType>, Scope) {
    // Lambda should be of the form:
    // (lambda '<arg1> '<arg2> ... '<argN> <function body)
    // TODO: lambda captures
    let function = match function {
        ast::ASTType::Symbol(s) => s,
        _ => panic!("\"function\" argument to breadth_builtin_lambda should be a Symbol!")
    };

    let new_arguments = vec![
        match arguments.pop() {
            // TODO: location info!
            None => panic!("lambda requires at least one argument! (the function body)"),
            Some(arg) => match arg {
                ast::CallOrType::Call(body) => {
                    ast::CallOrType::Type(ast::ASTType::Function(ast::Function {
                        name: ast::Symbol {
                            symbol: "<lambda>".into(),
                            // We use the locaton of the (lambda ...) start so that later
                            // we can tell the user where the lambda was defined.
                            filename: function.filename.clone(),
                            line_number: function.line_number,
                            column_number: function.column_number
                        },
                        call: body.clone(),
                        argument_names:
                            arguments.iter().map(|param| match param {
                                ast::CallOrType::Call(..) =>
                                    panic!("lambda arguments must be Definitions (not calls)!"),
                                ast::CallOrType::Type(t) => match t {
                                    ast::ASTType::Definition(..) => t.clone(),
                                    _ => panic!("lambda arguments must be Definitions!")
                                }
                            }).collect::<Vec<ast::ASTType>>()
                    }))
                },
                _ => panic!("lambda's last argument must be the body of the function!"),
            }
        }
    ];

    (new_arguments, local_scope)
}

fn builtin_lambda(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Return the function we built earlier
    arguments[0].clone()
}

fn builtin_user_defined_function(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    let function = match function {
        ast::ASTType::Function(f) => f,
        _ => panic!("builtin_user_defined_function argument \"function\" must be an ast::Function!")
    };

    if arguments.len() != function.argument_names.len() {
        panic!("{}:{}:{} Incorrect number of arguments to function {}. Expected {} ({}) got {} ({})",
                                            function.name.filename,      function.name.line_number,
                                            function.name.column_number, function.name.symbol,
                                            function.argument_names.len(),
                                            ast::format_asttype_list(&function.argument_names),
                                            arguments.len(),
                                            ast::format_asttype_list(&arguments));
    }

    // lambdas do not inherit outer scope
    let local_scope: Scope = HashMap::new();

    // TODO: add arguments to the scope

    exec_inner(function.call, local_scope)
}

fn breadth_builtin_let(function: ast::ASTType, mut arguments: Vec<ast::CallOrType>, mut local_scope: Scope)
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

    // If there are multiple Calls as values, we don't want to use
    // the updated symbols for each subsequent call. They must all
    // use the scope *before* any new variables are added/updated.
    let old_local_scope = local_scope.clone();

    for pair in arguments.chunks(2) {
        let mut pair = pair.to_vec();

        // Check for the body of the let call
        if pair.len() == 1 {
            break;
        }

        // If the value is the result of a call, resolve it
        if let ast::CallOrType::Call(c) = &pair[1] {
            pair[1] = ast::CallOrType::Type(
                exec_inner(c.clone(), old_local_scope.clone()));
        };

        // Otherwise we got some definition
        match (&pair[0], &pair[1]) {
            (ast::CallOrType::Type(t1), ast::CallOrType::Type(t2)) =>
                match t1 {
                    // TODO: does this even have to be a definition?
                    // We could delay symbol lookup until breadth executor is done
                    // Then just say that any Symbol in the right place in a let
                    // is an identifier. (let 'a 1 ..) -> (let a 1 ..)
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

fn builtin_let(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        // TODO: where do we validate the structure of these calls?
        None => panic!("let call must have at least one argument to return!")
    }
}

fn builtin_plus(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
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

fn builtin_body(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // body returns the value of the last call in the list of results
    match arguments.last() {
        Some(arg) => arg.clone(),
        None => panic!("body call must have at least one argument to return!")
    }
}

// TODO: test me
fn builtin_print(fucntion: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // TODO: assuming newline
    println!("{}", ast::format_asttype_list(&arguments));
    // TODO: void type? (None might be a better name)
    ast::ASTType::Integer(1, "runtime".into(), 0, 0)
}

fn search_scope(name: &ast::Symbol, local_scope: &Scope) -> Option<ast::ASTType> {
    match local_scope.get(&name.symbol) {
        Some(t) => Some(t.clone()),
        None => None
    }
}

fn exec_inner(call: ast::Call, local_scope: Scope) -> ast::ASTType {
    // breadth_executor does any breadth first evaluation
    // For example let. (let 'a 1 (print a))
    // This must add "a" to the local scope before we can
    // *depth first* execute the print.
    // This is optional since most calls can just use depth
    // first processing.

    // This is passed to the executor so that it can know where
    // the call starts, for error messages.
    let mut function_start = ast::ASTType::Symbol(call.fn_name.clone());
    let (breadth_executor, executor):
        (Option<BreadthExecutor>, Executor) =
            match call.fn_name.symbol.as_str() {
                "body"    => (None,                         builtin_body),
                     "+"  => (None,                         builtin_plus),
                 "print"  => (None,                         builtin_print),
                 "let"    => (Some(breadth_builtin_let),    builtin_let),
                 "lambda" => (Some(breadth_builtin_lambda), builtin_lambda),
                 // If not builtin then it could be user defined
                        _ => match search_scope(&call.fn_name, &local_scope) {
                            // TODO: move into its own function
                            Some(v) => match v {
                                ast::ASTType::Function(f) => {
                                    // Replace the function's name with the name we're calling as
                                    // Which will include the correct location info
                                    function_start = ast::ASTType::Function( ast::Function {
                                            name: ast::Symbol{
                                                // Add the location of the original lambda
                                                // declaration
                                                symbol: format!("\"{}\" (lambda defined at {}:{}:{})",
                                                    call.fn_name.symbol,
                                                    f.name.filename, f.name.line_number,
                                                    f.name.column_number),
                                                filename: call.fn_name.filename.into(),
                                                line_number: call.fn_name.line_number,
                                                column_number: call.fn_name.column_number
                                            },
                                            call: f.call.clone(),
                                            argument_names: f.argument_names.clone()
                                    });
                                    (None, builtin_user_defined_function)
                                },
                                //TODO: panic with location?
                                _ => panic!("{}:{}:{} found \"{}\" in local scope but it is not a function!",
                                            call.fn_name.filename, call.fn_name.line_number,
                                            call.fn_name.column_number, call.fn_name.symbol)
                            },
                            // TODO: panic_with_location
                            None => panic!("{}:{}:{} Unknown function \"{}\"!",
                                            call.fn_name.filename, call.fn_name.line_number,
                                            call.fn_name.column_number, call.fn_name.symbol)
                        }
            };

    // First resolve all symbols
    let arguments = call.arguments.iter().map(
        |arg| match arg {
            ast::CallOrType::Type(t) => match t {
                ast::ASTType::Symbol(s) => match search_scope(&s, &local_scope) {
                    Some(v) => ast::CallOrType::Type(v),
                    None => panic!("{}:{}:{} Symbol {} not found in local scope!",
                                s.filename, s.line_number,
                                s.column_number, s.symbol)
                },
                _ => ast::CallOrType::Type(t.clone())
            },
            _ => arg.clone()
        }).collect::<Vec<ast::CallOrType>>();

    // Then do any breadth first evaluations (e.g. let)
    let (arguments, local_scope) = match breadth_executor {
        Some(f) => f(function_start.clone(), arguments, local_scope),
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
    executor(function_start, arguments)
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
    #[should_panic (expected = "<in>:1:2 Unknown function \"not_a_function\"!")]
    fn test_panics_unknown_function() {
        exec_program("(not_a_function 1 2)");
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

        // Those calls use the scope before any variables are added
        check_program_result("
            (let 'a 1 'b 2
                # If we update \"a\" before the second call then
                # we get b=4 not b=2
                (let 'a (+ a b) 'b (+ a 1)
                    (+ b)
                )
            )",
            ASTType::Integer(2, "runtime".into(), 0, 0));
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

    #[test]
    #[should_panic (expected = "<in>:1:14 Symbol a not found in local scope!")]
    fn test_let_panics_use_symbol_before_define() {
        // You can't reference a symbol until the let has finished
        exec_program("(let 'a 1 'b a (print a))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:12 found \"a\" in local scope but it is not a function!")]
    fn test_panics_function_name_does_not_resolve_to_a_function() {
        exec_program("(let 'a 1 (a 1 2 3))");
    }

    #[test]
    fn test_builtin_lambda() {
        // TODO: lambda capture, needs list type
        check_program_result("
            (let
                'f (lambda 'a 'b (+ a b))
                (f 2 4)
            )",
            ASTType::Integer(6, "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "lambda requires at least one argument! (the function body)")]
    fn test_lambda_panics_no_arguments() {
        exec_program("(lambda)");
    }

    #[test]
    #[should_panic (expected = "lambda's last argument must be the body of the function!")]
    fn test_lambda_panics_body_is_not_a_call() {
        exec_program("(lambda 22)");
    }

    #[test]
    #[should_panic (expected = "lambda arguments must be Definitions (not calls)!")]
    fn test_lambda_panics_argument_name_is_a_call() {
        exec_program("(lambda 'a (+ 1 2) 'c (+a b))");
    }

    #[test]
    // TODO: all of these panic tests should get location info
    #[should_panic (expected = "lambda arguments must be Definitions!")]
    fn test_lambda_panics_argument_name_is_not_a_definition() {
        exec_program("(lambda 'a \"foo\" 'c (+a b))");
    }

    #[test]
    #[should_panic (expected = "<in>:4:18 Incorrect number of arguments to function \"f\" (lambda defined at <in>:3:18). Expected 1 ('a) got 3 (1 \"a\" (<lambda> 'a))")]
    fn test_lambda_panics_wrong_number_of_arguments_too_many() {
        exec_program("
            (let 'f
                (lambda 'a (+ a b))
                (f 1 \"a\" f)
            )");
    }

    #[test]
    #[should_panic (expected = "<in>:3:22 Incorrect number of arguments to function \"foo\" (lambda defined at <in>:2:24). Expected 2 ('a 'b) got 0 ()")]
    fn test_lambda_panics_wrong_number_of_arguments_zero() {
        exec_program("
            (let 'foo (lambda 'a 'b (+ a b))
                    (foo))");
    }
}
