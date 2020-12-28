use crate::ast;
use std::collections::HashMap;
use ast::panic_on_ast_type;

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
    let function = match function {
        ast::ASTType::Symbol(s) => s,
        _ => panic_on_ast_type(
                "\"function\" argument to breadth_builtin_lambda must be a Symbol!",
                &function)
    };

    let new_arguments = vec![
        match arguments.pop() {
            None => panic_on_ast_type(
                        "lambda requires at least one argument (the function body)",
                        &ast::ASTType::Symbol(function)),
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
                        call: body,
                        argument_names:
                            arguments.iter().map(|param| match param {
                                ast::CallOrType::Call(c) =>
                                    ast::panic_on_call(
                                        "lambda arguments must be Declarations (not Call)", &c),
                                ast::CallOrType::Type(t) => match t {
                                    ast::ASTType::Declaration(..) => t.clone(),
                                    _ => panic_on_ast_type("lambda arguments must be Declarations", &t)
                                }
                            }).collect::<Vec<ast::ASTType>>()
                    }))
                },
                _ => panic_on_ast_type("lambda's last argument must be the body of the function",
                        &ast::ASTType::Symbol(function))
            }
        }
    ];

    (new_arguments, local_scope)
}

fn builtin_lambda(_function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Return the function we built earlier
    arguments[0].clone()
}

fn builtin_user_defined_function(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    let function = match function {
        ast::ASTType::Function(f) => f,
        _ => panic_on_ast_type("builtin_user_defined_function argument \
                                \"function\" must be a Function!",
            &function)
    };

    if arguments.len() != function.argument_names.len() {
        panic_on_ast_type(&format!("Incorrect number of arguments to function {}. \
                                    Expected {} ({}) got {} ({})",
                              function.name.symbol,
                              function.argument_names.len(),
                              ast::format_asttype_list(&function.argument_names),
                              arguments.len(),
                              ast::format_asttype_list(&arguments)),
                          &ast::ASTType::Function(function));
    }

    // lambdas do not inherit outer scope
    let mut local_scope: Scope = HashMap::new();

    function.argument_names.iter().zip(arguments.iter()).for_each(|(name, value)| {
        match name {
            // TODO: a concrete Declaration type would help here
            ast::ASTType::Declaration(def, ..) => local_scope.insert(def.clone(), value.clone()),
            _ => panic_on_ast_type("lambda argument name must be a Declaration", &name)
        };
    });

    exec_inner(function.call, local_scope)
}

fn breadth_builtin_let(function: ast::ASTType, mut arguments: Vec<ast::CallOrType>, mut local_scope: Scope)
    -> (Vec<ast::CallOrType>, Scope) {
    // Let should have the form:
    // (let <defintion> <value> <defintion2> <value2> ... <call>)
    if arguments.len() < 3 {
        panic_on_ast_type("let requires at least 3 arguments", &function);
    }

    if (arguments.len() % 2) == 0 {
        panic_on_ast_type("Wrong number of arguments to len. Expected '<name> <value> ... <body>",
            &function);
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

        // Otherwise we got some declaration
        match (&pair[0], &pair[1]) {
            (ast::CallOrType::Type(t1), ast::CallOrType::Type(t2)) =>
                match t1 {
                    // TODO: does this even have to be a declaration?
                    // We could delay symbol lookup until breadth executor is done
                    // Then just say that any Symbol in the right place in a let
                    // is an identifier. (let 'a 1 ..) -> (let a 1 ..)
                    ast::ASTType::Declaration(def, ..) =>
                        match t2 {
                            // This should have been done by exec_inner
                            ast::ASTType::Symbol(s) =>
                                panic_on_ast_type(&format!("Unresolved symbol {} for let pair value", s),
                                    &t2),
                            _ => local_scope.insert(def.into(), t2.clone())
                        }
                    _ => panic_on_ast_type("Expected Declaration as first of let name-value pair", &t1)
                }
            (_, _) => panic!("Unresolved call in let declaration pair!")
        };
    }

    // Remove any name-value arguments
    (arguments.split_off(arguments.len()-2), local_scope)
}

fn builtin_let(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        None => panic_on_ast_type("let call must have at least one argument to return",
                    &function)
    }
}

fn builtin_plus(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    if arguments.is_empty() {
        panic_on_ast_type("+ requires at least one argument", &function);
    }

    if arguments.len() == 1 {
        return arguments[0].clone();
    }

    match arguments[0] {
        // If the first argument is type T, proceed as if the
        // rest are T, otherwise panic
        ast::ASTType::Integer(..) => ast::ASTType::Integer(
            arguments.iter()
                .map(|a| match a {
                        ast::ASTType::Integer(i, ..) => i,
                        _ => panic_on_ast_type(
                                "+ argument is not an Integer (does not match the 1st argument)", &a)
                })
                .sum(),
                "runtime".into(), 0, 0),
        ast::ASTType::String(..) => ast::ASTType::String(
            arguments.iter()
                .map(|a| match a {
                        ast::ASTType::String(s, ..) => s.to_owned(),
                        _ => panic_on_ast_type(
                            "+ argument is not a String (does not match the 1st argument)", &a)
                })
                .collect::<Vec<String>>()
                .concat(),
                "runtime".into(), 0, 0),
        _ => panic_on_ast_type(&format!("Cannot + multiple arguments of types {}",
                arguments.iter().map(|a| ast::asttype_typename(a))
                    .collect::<Vec<&str>>().join(", ")),
                &arguments[0])
    }
}

fn builtin_body(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // body returns the value of the last call in the list of results
    match arguments.last() {
        Some(arg) => arg.clone(),
        None => panic_on_ast_type("body must have at least one argument to return",
            &function)
    }
}

// TODO: test me
fn builtin_print(_function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    println!("{}", ast::format_asttype_list(&arguments));
    ast::ASTType::None("runtime".into(), 0, 0)
}

fn builtin_none(_function: ast::ASTType, _arguments: Vec<ast::ASTType>) -> ast::ASTType {
    ast::ASTType::None("runtime".into(), 0, 0)
}

fn builtin_list(_function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    ast::ASTType::List(arguments, "runtime".into(), 0, 0)
}

fn flatten_argument(argument: ast::ASTType) -> Vec<ast::ASTType> {
    match argument {
        // If it's a list, flatten it and its children into a single list
        ast::ASTType::List(l, ..) => l.into_iter()
                                      .map(flatten_argument)
                                      .flatten()
                                      .collect::<Vec<ast::ASTType>>(),
        _ => vec![argument]
    }
}

fn builtin_flatten(_function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    ast::ASTType::List(arguments
        .into_iter()
        // Produce a list of lists. This will only ever be 1 level deep
        // due to the recursion in flatten_argument.
        .map(flatten_argument)
        .collect::<Vec<Vec<ast::ASTType>>>()
        .into_iter()
        // Then flatten that one level to get a flat list
        .flatten()
        .collect::<Vec<ast::ASTType>>(), "runtime".into(), 0, 0)
}

fn builtin_extend(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    if arguments.len() != 2 {
        panic_on_ast_type("Expected exactly 2 List arguments for extend",
            &function);
    }
    match (arguments[0].clone(), arguments[1].clone()) {
        (ast::ASTType::List(mut l1, ..), ast::ASTType::List(l2, ..)) => {
            l1.extend(l2);
            ast::ASTType::List(l1, "runtime".into(), 0, 0)
        },
        (_, _) => panic_on_ast_type("Both arguments to extend must be List",
                      &function)
    }
}

fn breadth_builtin_if(function: ast::ASTType,
                      mut arguments: Vec<ast::CallOrType>, local_scope: Scope)
    -> (Vec<ast::CallOrType>, Scope) {
    match arguments.len() {
        // condition, true value
        // condition, true value, else value
        2 | 3 => {
            // Evaluate the condition
            let was_true = bool::from(match arguments[0].clone() {
                ast::CallOrType::Call(c) => exec_inner(c, local_scope.clone()),
                ast::CallOrType::Type(t) => t,
            });
            // Always discard the condition argument
            arguments.remove(0);

            // If we were given a true and a false type, pick one
            if arguments.len() == 2 {
                if was_true {
                    arguments.remove(1);
                } else {
                    arguments.remove(0);
                }
            // Otherwise keep the true value if condition was true
            // else return none
            } else if !was_true {
                arguments.remove(0);
                arguments.push(ast::CallOrType::Type(
                    ast::ASTType::None("runtime".into(), 0, 0)));
            }
            // else we leave the true value as the only argument
        }
        _ => panic_on_ast_type("Incorrect number of arguments to if. \
                                Expected <condition> <true value> <false value (optional)>",
                                &function)
    }

    (arguments, local_scope)
}

fn builtin_if(_function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    arguments[0].clone()
}

fn builtin_comparison(function: ast::ASTType, arguments: Vec<ast::ASTType>,
                      compare: ast::Comparison) -> ast::ASTType {
    if arguments.len() != 2 {
        panic_on_ast_type(&format!("Expected exactly 2 arguments to {}",
            String::from(compare)), &function);
    }

    ast::ASTType::Bool(
        ast::compare_asttypes(&function, &arguments[0], &arguments[1], compare),
        "runtime".into(), 0, 0)
}

fn builtin_less_than(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    builtin_comparison(function, arguments, ast::Comparison::LessThan)
}

fn builtin_equal_to(function: ast::ASTType, arguments: Vec<ast::ASTType>) -> ast::ASTType {
    builtin_comparison(function, arguments, ast::Comparison::Equal)
}

fn search_scope(name: &ast::Symbol, local_scope: &Scope) -> Option<ast::ASTType> {
    match local_scope.get(&name.symbol) {
        Some(t) => Some(t.clone()),
        None => None
    }
}

fn find_user_function(call: &ast::Call, local_scope: &Scope)
        -> Option<(ast::ASTType, Option<BreadthExecutor>, Executor)> {
    match search_scope(&call.fn_name, &local_scope) {
        Some(v) => match v {
            ast::ASTType::Function(f) =>
                // Replace the function's name with the name we're calling as
                // Which will include the correct location info
                Some((ast::ASTType::Function( ast::Function {
                        name: ast::Symbol{
                            // Add the location of the original lambda
                            // declaration
                            symbol: format!("\"{}\" (lambda defined at {}:{}:{})",
                                call.fn_name.symbol,
                                f.name.filename, f.name.line_number,
                                f.name.column_number),
                            filename: call.fn_name.filename.clone(),
                            line_number: call.fn_name.line_number,
                            column_number: call.fn_name.column_number
                        },
                        call: f.call.clone(),
                        argument_names: f.argument_names
                    }),
                    None, builtin_user_defined_function)),
            _ => ast::panic_on_call(
                    &format!("Found \"{}\" in local scope but it is not a function",
                    call.fn_name.symbol), &call)
        },
        None => None
    }
}

fn find_builtin_function(call: &ast::Call)
        -> Option<(ast::ASTType, Option<BreadthExecutor>, Executor)> {
    let function_start = ast::ASTType::Symbol(call.fn_name.clone());
    match call.fn_name.symbol.as_str() {
        "body"    => Some((function_start, None,                         builtin_body)),
        "+"       => Some((function_start, None,                         builtin_plus)),
        "print"   => Some((function_start, None,                         builtin_print)),
        "let"     => Some((function_start, Some(breadth_builtin_let),    builtin_let)),
        "lambda"  => Some((function_start, Some(breadth_builtin_lambda), builtin_lambda)),
        "none"    => Some((function_start, None,                         builtin_none)),
        "list"    => Some((function_start, None,                         builtin_list)),
        "if"      => Some((function_start, Some(breadth_builtin_if),     builtin_if)),
        "<"       => Some((function_start, None,                         builtin_less_than)),
        "eq"      => Some((function_start, None,                         builtin_equal_to)),
        "flatten" => Some((function_start, None,                         builtin_flatten)),
        "extend"  => Some((function_start, None,                         builtin_extend)),
        _         => None,
    }
}

fn exec_inner(call: ast::Call, local_scope: Scope) -> ast::ASTType {
    // breadth_executor does any breadth first evaluation
    // For example let. (let 'a 1 (print a))
    // This must add "a" to the local scope before we can
    // *depth first* execute the print.
    // This is optional since most calls can just use depth
    // first processing.
    //
    // function_start is passed to the executor so that it can know where
    // the call starts for error messages.
    let (function_start, breadth_executor, executor) =
        match find_user_function(&call, &local_scope) {
            Some(v) => v,
            None => match find_builtin_function(&call) {
                        Some(v) => v,
                        None => ast::panic_on_call(&format!("Unknown function \"{}\"",
                                    call.fn_name.symbol), &call)
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

pub fn exec(call: ast::Call) -> ast::ASTType {
    let local_scope = HashMap::new();
    exec_inner(call, local_scope)
}

#[cfg(test)]
mod tests {
    use exec::exec;
    use crate::tokeniser::process_into_tokens;
    use ast::build;
    use ast::ASTType;
    use ast::Symbol;
    use ast::Call;
    use ast::Function;
    use ast::CallOrType;

    fn exec_program(program: &str) -> ASTType {
        exec(build(process_into_tokens("<in>", program)))
    }

    fn check_program_result(program: &str, expected: ASTType) {
        assert_eq!(exec_program(program), expected);
    }

    #[test]
    fn simple_exec() {
        // Simple single call
        check_program_result("(+ 1 2)", ASTType::Integer(3, "runtime".into(), 0, 0));
        // Result is the result of the last block
        check_program_result("(+ 1 2)(+ 9 10)", ASTType::Integer(19, "runtime".into(), 0, 0));
        // We can process nested calls
        check_program_result("(+ (+ 1 (+ 2 3)) 2)", ASTType::Integer(8, "runtime".into(), 0, 0));
    }

    #[test]
    fn user_functions_shadow_builtins() {
        check_program_result("
            # The + inside the lambda will be the builtin
            (let '+ (lambda 'x 'y (+ x y 1))
                # The + here is the lambda from above
                # So we get 1 + 2 + 1 = 4
                (+ 1 2)
            )", ASTType::Integer(4, "runtime".into(), 0, 0));

        // You can still name vars the same as a builtin as long
        // as it's not used as a function name in that scope.
        check_program_result("
            # + used as a function name here
            (+ (extend
                 # + made into a variable
                 (let '+ 1
                   # Only used as an argument
                   (list +)
                 )
                 # Once we've left the let, + is the builtin
                 (list 2)
               )
            )",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 5, 26),
                ASTType::Integer(2, "<in>".into(), 10, 24)
            ], "runtime".into(), 0, 0)
        );
    }

    #[test]
    #[should_panic (expected = "<in>:3:18 Found \"+\" in local scope but it is not a function")]
    fn panics_shadowed_builtin_not_a_function() {
        exec_program("
            (let '+ \"foo\"
                (+ 1 2 3)
            )");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Unknown function \"not_a_function\"")]
    fn panics_unknown_function() {
        exec_program("(not_a_function 1 2)");
    }

    #[test]
    fn builtin_body_returns_last_value() {
        check_program_result("(body (+ 1) (+ 2))", ASTType::Integer(2, "<in>".into(), 1, 16));
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 body must have at least one argument to return")]
    fn builtin_body_panics_no_calls() {
        exec_program("(body )");
    }

    #[test]
    fn builtin_plus_basic() {
        // Strings and integers can be added
        check_program_result("(+ 9 10)", ASTType::Integer(19, "runtime".into(), 0, 0));
        check_program_result("(+ \"foo\" \"bar\")", ASTType::String("foobar".into(), "runtime".into(), 0, 0));

        // We can handle any number of arguments
        check_program_result("(+ 9 10 11 12)", ASTType::Integer(42, "runtime".into(), 0, 0));
        check_program_result("(+ \"a\" \"b\" \"c\" \"d\")", ASTType::String("abcd".into(), "runtime".into(), 0, 0));

        // Minimum of 1 argument
        check_program_result("(+ 99)", ASTType::Integer(99, "<in>".into(), 1, 4));
        check_program_result("(+ \"def\")", ASTType::String("def".into(), "<in>".into(), 1, 4));
    }

    #[test]
    #[should_panic (expected="<in>:1:2 + requires at least one argument")]
    fn builtin_plus_panics_no_arguments() {
        exec_program("(+)");
    }

    #[test]
    #[should_panic (expected="<in>:1:4 Cannot + multiple arguments of types Declaration, Declaration")]
    fn builtin_plus_panics_cant_plus_type() {
        exec_program("(+ 'food 'bla)");
    }

    #[test]
    fn builtin_plus_single_argument_any_type_allowed() {
        check_program_result("(+ 'def)", ASTType::Declaration("def".into(), "<in>".into(), 1, 4));
        // Can't + a symbol since it'll be looked up before + runs
        check_program_result("(+ (lambda (+ 1)))",
            ASTType::Function(Function {
                name: Symbol {
                    symbol: "<lambda>".into(), filename: "<in>".into(),
                    line_number: 1, column_number: 5
                },
                call: Call {
                    fn_name: Symbol {
                        symbol: "+".into(), filename: "<in>".into(),
                        line_number: 1, column_number: 13
                    },
                    arguments: vec![
                        CallOrType::Type(ASTType::Integer(1, "<in>".into(), 1, 15))]
                },
                argument_names: vec![],
            })
        );
        check_program_result("(+ (none))", ASTType::None("runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected="<in>:1:6 + argument is not an Integer (does not match the 1st argument)")]
    fn builtin_plus_panics_mismatched_arg_types_integer() {
        exec_program("(+ 1 \"2\")");
    }

    #[test]
    #[should_panic (expected="<in>:1:8 + argument is not a String (does not match the 1st argument)")]
    fn builtin_plus_panics_mismatched_arg_types_string() {
        exec_program("(+ \"2\" 1)");
    }

    #[test]
    fn builtin_let_basic() {
        // Simple declaration is visible in later call
        check_program_result("(let 'a 2 (+ a))",
            ASTType::Integer(2, "<in>".into(), 1, 9));

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
            ASTType::Integer(2, "<in>".into(), 2, 21));

        // Redefintions shadow earlier values and can change types
        check_program_result("
            (let 'a 2
                (let 'a \"abc\"
                    (+ a)
                )
            )",
            ASTType::String("abc".into(), "<in>".into(), 3, 25));

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
    #[should_panic (expected = "<in>:1:4 Wrong number of arguments to len")]
    fn builtin_let_panics_even_number_of_arguments() {
        exec_program("(  let 'a 1 'b 2)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 let requires at least 3 arguments")]
    fn builtin_let_panics_too_few_arguments() {
        exec_program("(let 'a)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:6 Expected Declaration as first of let name-value pair")]
    fn builtin_let_panics_var_name_not_a_declaration() {
        exec_program("(let 22 \"foo\" (+ 99))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:14 Symbol a not found in local scope!")]
    fn builtin_let_panics_use_symbol_before_define() {
        // You can't reference a symbol until the let has finished
        exec_program("(let 'a 1 'b a (print a))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:12 Found \"a\" in local scope but it is not a function")]
    fn panics_function_name_does_not_resolve_to_a_function() {
        exec_program("(let 'a 1 (a 1 2 3))");
    }

    #[test]
    fn builtin_lambda_basic() {
        // Zero or more arguments
        check_program_result("
            (let
                'fn (lambda (+ 1234))
                (fn)
            )",
            ASTType::Integer(1234, "<in>".into(), 3, 32));

        // Scope for calling a lambda is empty but for the argument names
        check_program_result("
            (let
                'f (lambda 'a 'b (+ a b))
                (f 2 4)
            )",
            ASTType::Integer(6, "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "<in>:6:38 Symbol a not found in local scope!")]
    fn builtin_lambda_panics_symbol_from_outer_scope() {
        exec_program("
            # a is in the let's scope
            (let 'a \"foo\"
                 # but is not an argument or captured by the lambda
                 # b is an argument so that's fine
                 'fn (lambda 'b (+ b a))
                (body
                    # This uses the outer scope (the let's scope)
                    (+ a)
                    # This uses a fresh, empty scope
                    (fn 2)
                )
            )");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 lambda requires at least one argument (the function body)")]
    fn builtin_lambda_panics_no_arguments() {
        exec_program("(lambda)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 lambda's last argument must be the body of the function")]
    fn builtin_lambda_panics_body_is_not_a_call() {
        exec_program("(lambda 33 22)");
    }

    #[test]
    #[should_panic (expected = "lambda arguments must be Declarations (not Call)")]
    fn builtin_lambda_panics_argument_name_is_a_call() {
        exec_program("(lambda 'a (+ 1 2) 'c (+a b))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:12 lambda arguments must be Declarations")]
    fn builtin_lambda_panics_argument_name_is_not_a_declaration() {
        exec_program("(lambda 'a \"foo\" 'c (+a b))");
    }

    #[test]
    #[should_panic (expected = "<in>:4:18 Incorrect number of arguments to function \"f\" (lambda defined at <in>:3:18). Expected 1 ('a) got 3 (1 \"a\" (<lambda> 'a))")]
    fn builtin_lambda_panics_wrong_number_of_arguments_too_many() {
        exec_program("
            (let 'f
                (lambda 'a (+ a b))
                (f 1 \"a\" f)
            )");
    }

    #[test]
    #[should_panic (expected = "<in>:3:22 Incorrect number of arguments to function \"foo\" (lambda defined at <in>:2:24). Expected 2 ('a 'b) got 0 ()")]
    fn builtin_lambda_panics_wrong_number_of_arguments_zero() {
        exec_program("
            (let 'foo (lambda 'a 'b (+ a b))
                    (foo))");
    }

    #[test]
    fn builtin_none_basic() {
        // Generates an instance of None
        check_program_result("(none)",
            ASTType::None("runtime".into(), 0, 0));
        // Does so regardless of arguments
        check_program_result("(none 99 \"foo\" 2 1234)",
            ASTType::None("runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_list_basic() {
        // Can be empty
        check_program_result("(list)", ASTType::List(Vec::new(), "runtime".into(), 0, 0));
        // Can hold different types
        check_program_result("(list 1 \"foo\" (+ 9 1))",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 1, 7),
                ASTType::String("foo".into(), "<in>".into(), 1, 9),
                ASTType::Integer(10, "runtime".into(), 0, 0)
            ],
            "runtime".into(), 0, 0));
        // Including other lists
        check_program_result("(list (list (list 1)))",
            ASTType::List(vec![
                ASTType::List(vec![
                    ASTType::List(vec![
                        ASTType::Integer(1, "<in>".into(), 1, 19)
                    ], "runtime".into(), 0, 0)
                ], "runtime".into(), 0, 0)
            ], "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Incorrect number of arguments to if. Expected <condition> <true value> <false value (optional)>")]
    fn builtin_if_not_enough_arguments() {
        exec_program("(if 1)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Incorrect number of arguments to if. Expected <condition> <true value> <false value (optional)>")]
    fn builtin_if_too_many_arguments() {
        exec_program("(if 1 2 3 4)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:5 Can't convert Declaration to bool")]
    fn builtin_if_panics_cant_convert_to_bool() {
        exec_program("(if 'foo 1)");
    }

    #[test]
    fn builtin_if_basics() {
        // Minimum one condition and a true value
        check_program_result("(if 1 2)", ASTType::Integer(2, "<in>".into(), 1, 7));
        // Else is optional
        check_program_result("(if \"\" 99 66)", ASTType::Integer(66, "<in>".into(), 1, 11));
        // Any argument can be another call
        check_program_result("(if (+ 0 1) (+ 1 2) (+ 4 5))", ASTType::Integer(3, "runtime".into(), 0, 0));
        // values can be of different types
        check_program_result("(if 1 \"foo\" (list))", ASTType::String("foo".into(), "<in>".into(), 1, 7));
        // If we don't have an else and the condition is false, return none
        check_program_result("(if (list) (+ 99))", ASTType::None("runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Expected exactly 2 arguments to <")]
    fn builtin_less_than_panics_too_many_arguments() {
        exec_program("(< 1 2 3)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Expected exactly 2 arguments to <")]
    fn builtin_less_than_panics_no_arguments() {
        exec_program("(<)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Cannot do ordered comparison < on types Integer and String")]
    fn builtin_less_than_panics_non_integer_arguments() {
        exec_program("(< 1 \"foo\")");
    }

    #[test]
    fn builtin_less_than_basic() {
        // Only works with 2 integers
        check_program_result("(< 1 2)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(< 9 3)", ASTType::Bool(false, "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Cannot do equality comparison eq on types Function and Function")]
    fn builtin_equal_to_panics_cant_equality_compare_arguments() {
        exec_program("(eq (lambda (list)) (lambda (list)))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Cannot do equality comparison eq on types Function and Integer")]
    fn builtin_equal_to_panics_arguments_different_types() {
        exec_program("(eq (lambda (list)) 1)");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Cannot do equality comparison eq on types None and Integer")]
    fn builtin_equal_to_panics_none_and_other_type() {
        exec_program("(eq (none) 1)");
    }

    #[test]
    fn builtin_equal_to_basic() {
        check_program_result("(eq 1 1)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq 1 2)", ASTType::Bool(false, "runtime".into(), 0, 0));

        check_program_result("(eq \"foo\" \"foo\")", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq \"foo\" \"bar\")", ASTType::Bool(false, "runtime".into(), 0, 0));

        check_program_result("(eq (< 1 2) (< 3 4))", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq (< 1 2) (< 4 3))", ASTType::Bool(false, "runtime".into(), 0, 0));

        check_program_result("(eq (none) (none))", ASTType::Bool(true, "runtime".into(), 0, 0));
        // None doesn't compare to anything else

        check_program_result("(eq (list 1 2 3) (list 1 2 3))",
            ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq (list) (list))",
            ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq (list 6 7 \"g\") (list 6 7 \"f\"))",
            ASTType::Bool(false, "runtime".into(), 0, 0));
        // Even though single items of different types can't be compared,
        // for a list it means not equal.
        check_program_result("(eq (list \"a\") (list 1))",
            ASTType::Bool(false, "runtime".into(), 0, 0));
        // The comparison recurses into nested lists
        check_program_result("(eq (list (list 1 2)) (list (list 1 2)))",
            ASTType::Bool(true, "runtime".into(), 0, 0));
        check_program_result("(eq (list (list 1 (list 2))) (list (list 1 (list 3))))",
            ASTType::Bool(false, "runtime".into(), 0, 0));
        // Lists of different length are not equal
        check_program_result("(eq (list 1) (list 1 2))",
            ASTType::Bool(false, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_flatten() {
        // Always returns a list, even if empty
        check_program_result("(flatten)", ASTType::List(Vec::new(), "runtime".into(), 0, 0));
        // Single items are added into the list
        check_program_result("(flatten 1 2)",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 1, 10),
                ASTType::Integer(2, "<in>".into(), 1, 12),
            ], "runtime".into(), 0, 0));
        // Lists of lists return a flat list of their items
        check_program_result("
            (flatten
                0
                (list
                    (list 1)
                )
                (list
                    2
                    (list
                        (list 3)
                        4
                    )
                )
                5
            )",
            ASTType::List(vec![
                ASTType::Integer(0, "<in>".into(), 3, 17),
                ASTType::Integer(1, "<in>".into(), 5, 27),
                ASTType::Integer(2, "<in>".into(), 8, 21),
                ASTType::Integer(3, "<in>".into(), 10, 31),
                ASTType::Integer(4, "<in>".into(), 11, 25),
                ASTType::Integer(5, "<in>".into(), 14, 17),
            ], "runtime".into(), 0, 0));
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Expected exactly 2 List arguments for extend")]
    fn builtin_extend_panics_too_few_arguments() {
        exec_program("(extend (list))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Expected exactly 2 List arguments for extend")]
    fn builtin_extend_panics_too_many_arguments() {
        exec_program("(extend (list) (list) (list))");
    }

    #[test]
    #[should_panic (expected = "<in>:1:2 Both arguments to extend must be List")]
    fn builtin_extend_panics_argument_not_a_list() {
        exec_program("(extend (list) 1)");
    }

    #[test]
    fn builtin_extend_basic() {
        // Empty list allowed for either
        check_program_result("(extend (list) (list 2))",
            ASTType::List(vec![
                ASTType::Integer(2, "<in>".into(), 1, 22),
            ], "runtime".into(), 0, 0));
        check_program_result("(extend (list 1) (list))",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 1, 15),
            ], "runtime".into(), 0, 0));


        check_program_result("(extend (list 1) (list 2))",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 1, 15),
                ASTType::Integer(2, "<in>".into(), 1, 24),
            ], "runtime".into(), 0, 0));

        // Nested lists are not unpacked in the rhs
        check_program_result("(extend (list 1) (list (list 2)))",
            ASTType::List(vec![
                ASTType::Integer(1, "<in>".into(), 1, 15),
                ASTType::List(vec![
                    ASTType::Integer(2, "<in>".into(), 1, 30),
                ], "runtime".into(), 0, 0),
            ], "runtime".into(), 0, 0));
    }
}
