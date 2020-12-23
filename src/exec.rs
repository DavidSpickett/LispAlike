use crate::ast;

fn breadth_builtin_let(mut arguments: Vec<ast::CallOrType>) -> Vec<ast::CallOrType> {
    // Let must be
    // (let '<name1> <value1> '<name2> <value2> <call>)
    // Where <call> receives the new scope generated
    // Meaning that there is always an odd number of arguments which
    // is at least 3
    // Ignore defs for now
    arguments.split_off(arguments.len()-2)
}

fn depth_builtin_let(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        // TODO: where do we validate the structure of these calls?
        None => panic!("let call must have at least one argument to return!")
    }
}

fn depth_builtin_plus(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    if arguments.len() == 0 {
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
fn depth_builtin_dunder_root(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => arg.clone(),
        None => panic!("__root call must have at least one argument to return!")
    }
}

fn depth_builtin_print(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // TODO: assuming newline
    println!("{}", arguments.iter().map(|a| format!("{}", a)).collect::<Vec<String>>().join(", "));
    // TODO: void type? (None might be a better name)
    ast::ASTType::Integer(1, "runtime".into(), 0, 0)
}

fn exec_inner(call: ast::Call) -> ast::ASTType {
    let (breadth_executor, depth_executor):
        // This does any breadth first processing e.g.
        // (let 'a 1 (print a) must process 'a and 1 first
        // before it dives into (print a)
        // Not all functions have this
        (Option<fn(Vec<ast::CallOrType>) -> Vec<ast::CallOrType>>,
        // Then the depth first executor handles (print a)
         fn(Vec<ast::ASTType>) -> ast::ASTType) =
            match call.fn_name.symbol.as_str() {
            "__root" => (None,                      depth_builtin_dunder_root),
                 "+" => (None,                      depth_builtin_plus),
             "print" => (None,                      depth_builtin_print),
             "let"   => (Some(breadth_builtin_let), depth_builtin_let),
            _ => panic!("Unknown function {}!", call.fn_name.symbol)
    };

    let breadth_processed_args = match breadth_executor {
        // TODO: scope should be passed in here
        Some(f) => f(call.arguments),
        None => call.arguments
    };

    // Now resolve all Calls in its arguments
    let resolved_arguments = breadth_processed_args.iter().map(
        |a| match a {
            ast::CallOrType::Call(c) => exec_inner(c.clone()),
            ast::CallOrType::Type(t) => t.clone()
        }).collect::<Vec<ast::ASTType>>();

    depth_executor(resolved_arguments)
}

// TODO: defun could return a function here
pub fn exec(call: ast::Call) -> ast::ASTType {
    // You would declare global and inital local scope here
    exec_inner(call)
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
}
