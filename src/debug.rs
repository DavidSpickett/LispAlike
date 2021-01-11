use crate::exec;
use crate::ast;
use crate::tokeniser;
use std::io::Write;
use std::io::BufRead;
use std::cell::RefCell;
use std::rc::Rc;

fn do_backtrace_command(_cmd: &str, _local_scope: Rc<RefCell<ast::Scope>>,
                   _global_function_scope: &mut ast::FunctionScope,
                   call_stack: &mut ast::CallStack) -> String {
    let callstack_frames = 10;
    format!("{}{}",
        if call_stack.len() > callstack_frames {
            format!("<backtrace limited, showing {} of {} frames>\n",
             callstack_frames, call_stack.len())
        } else {
            "".to_string()
        },
        ast::format_call_stack(
             if call_stack.len() >= callstack_frames {
                 &call_stack[call_stack.len()-callstack_frames..]
             } else {
                &call_stack
             })
    )
}

fn do_locals_command(_cmd: &str, local_scope: Rc<RefCell<ast::Scope>>,
                   _global_function_scope: &mut ast::FunctionScope,
                   _call_stack: &mut ast::CallStack) -> String {
    // Since hashmaps are not ordered, show variables
    // in alphabetical order.
    let mut names = local_scope.borrow().keys()
                    .map(|n| { n.clone() })
                    .collect::<Vec<String>>();
    names.sort();
    names.iter().map(|n| {
        format!("'{} => {}", n,
            match local_scope.borrow().get(n).unwrap() {
                Some(v) => format!("{}", v),
                None => "<undefined>".to_string()
            })
    }).collect::<Vec<String>>().join("\n")
}

fn do_globals_command(_cmd: &str, _local_scope: Rc<RefCell<ast::Scope>>,
                   global_function_scope: &mut ast::FunctionScope,
                   _call_stack: &mut ast::CallStack) -> String {
    // Again hashmaps aren't ordered
    let mut names = global_function_scope.keys()
                    .map(|n| { n.clone() })
                    .collect::<Vec<String>>();
    names.sort();
    names.iter().map(|n| {
        format!("{} => {}", n,
            global_function_scope.get(n).unwrap())
    }).collect::<Vec<String>>().join("\n")
}

fn do_code_command(_cmd: &str, local_scope: Rc<RefCell<ast::Scope>>,
                   global_function_scope: &mut ast::FunctionScope,
                   call_stack: &mut ast::CallStack) -> String {
    let stdin = std::io::stdin();
    let mut lines = Vec::new();
    println!("Enter your code, end with an empty line:");

    loop {
        let mut line = String::new();
        stdin.lock().read_line(&mut line).expect("Couldn't read from stdin");
        if line == "\n" {
            let result = exec::exec_inner(
                            ast::build(
                                tokeniser::process_into_tokens(
                                    "<in>".into(), &lines.join(""))
                            ),
                            local_scope.clone(), global_function_scope,
                            call_stack);

            return format!("{}", match result {
                Ok(v) => format!("{}", v),
                Err(e) => e
            })
        } else {
            lines.push(line);
        }
    }
}

fn do_unknown_command(cmd: &str, _local_scope: Rc<RefCell<ast::Scope>>,
                    _global_function_scope: &mut ast::FunctionScope,
                    _call_stack: &mut ast::CallStack) -> String {
    format!("Unknown command \"{}\"", cmd)
}

fn do_break_command(cmd: &str, local_scope: Rc<RefCell<ast::Scope>>,
                    global_function_scope: &mut ast::FunctionScope,
                    call_stack: &mut ast::CallStack) -> String {
    (match cmd {
        "b"         |
        "backtrace" => do_backtrace_command,
        "l"         |
        "locals"    => do_locals_command,
        "g"         |
        "globals"   => do_globals_command,
        "code"      => do_code_command,
        _           => do_unknown_command,
    })(cmd, local_scope, global_function_scope, call_stack)
}

pub fn breadth_builtin_break(function: ast::ASTType, arguments: Vec<ast::CallOrType>,
                         local_scope: Rc<RefCell<ast::Scope>>,
                         global_function_scope: &mut ast::FunctionScope,
                         call_stack: &mut ast::CallStack)
        -> Result<(Vec<ast::CallOrType>, Rc<RefCell<ast::Scope>>), String> {
    let mut line = String::new();
    let stdin = std::io::stdin();

    println!("\nbreak called at {}", ast::ast_type_err("", &function));

    loop {
        print!("(lal) ");
        // To get the above to show up
        std::io::stdout().flush().expect("Couldn't flush stdout");

        stdin.lock().read_line(&mut line).expect("Couldn't read from stdin");
        let cmd = line.trim();

        match cmd {
            "c"        |
            "continue" => return Ok((arguments, local_scope)),
            _ => println!("{}", do_break_command(
                    cmd, local_scope.clone(), global_function_scope, call_stack))
        };
        line.clear();
    }
}

#[cfg(test)]
mod tests {
    use crate::ast;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::collections::HashMap;
    use debug::do_break_command;

    #[test]
    fn break_unknown_command() {
        assert_eq!("Unknown command \"abc\"",
            do_break_command(
                "abc",
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut ast::CallStack::new()
            )
        );
    }

    #[test]
    fn break_locals() {
        let mut locals_test_scope = HashMap::new();
        locals_test_scope.insert("foo".to_string(), None);
        locals_test_scope.insert("bar".to_string(),
            Some(ast::ASTType::Integer(99, "runtime".into(), 0, 0)));
        locals_test_scope.insert("ls".to_string(),
            Some(ast::ASTType::List(vec![
                    ast::ASTType::String("abc".into(), "runtime".into(), 0, 0),
                    ast::ASTType::None("runtime".into(), 0, 0),
                ], "runtime".into(), 0, 0))
        );

        // Printed in alphabetical order
        assert_eq!(
            "'bar => 99\n\
             'foo => <undefined>\n\
             'ls => [\"abc\" none]",
            do_break_command(
                "locals",
                Rc::new(RefCell::new(locals_test_scope)),
                &mut ast::FunctionScope::new(),
                &mut ast::CallStack::new()
            )
        );
    }

    fn make_test_call(name: &str) -> ast::Call {
        ast::Call {
            fn_name: ast::Symbol {
                     symbol: name.to_string(), filename: "<in>".into(),
                line_number: 5,            column_number: 39
            },
            arguments: vec![
                ast::CallOrType::Type(ast::ASTType::Symbol(ast::Symbol {
                         symbol: "a".into(), filename: "<in>".into(),
                    line_number: 5,     column_number: 41
                ,})),
                ast::CallOrType::Type(ast::ASTType::Symbol(ast::Symbol {
                    symbol: "b".into(), filename: "<in>".into(),
                    line_number: 5, column_number: 43
                ,}))
            ],
        }
    }

    #[test]
    fn break_globals() {
        let mut test_global_scope = ast::FunctionScope::new();

        let test_function = ast::Function {
            name: ast::Symbol {
                symbol: "<lambda>".into(), filename: "<in>".into(),
                line_number: 5, column_number: 31
            },
            call: make_test_call("foo"),
            argument_names: Vec::new(),
            captured_scope: Rc::new(RefCell::new(ast::Scope::new()))
        };

        test_global_scope.insert("zebra".to_string(), test_function.clone());
        test_global_scope.insert("abcd".to_string(), test_function.clone());

        assert_eq!("abcd => (<lambda> )\n\
                    zebra => (<lambda> )",
            do_break_command(
                "globals",
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut test_global_scope,
                &mut ast::CallStack::new()
            )
        );
    }

    #[test]
    fn break_backtrace() {
        // Empty
        assert_eq!("Traceback (most recent call last):\n",
            do_break_command(
                "backtrace",
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut vec![]
            )
        );

        // < limit
        assert_eq!(
            "Traceback (most recent call last):\n\
          \x20 <in>:5:39 a\n\
          \x20 <in>:5:39 b\n\
          \x20 <in>:5:39 c",
            do_break_command(
                "backtrace",
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut vec![make_test_call("a"), make_test_call("b"), make_test_call("c")]
            )
        );

        // > limit, prints limit note
        assert_eq!(
            "<backtrace limited, showing 10 of 12 frames>\n\
             Traceback (most recent call last):\n\
          \x20 <in>:5:39 c\n\
          \x20 <in>:5:39 d\n\
          \x20 <in>:5:39 e\n\
          \x20 <in>:5:39 f\n\
          \x20 <in>:5:39 g\n\
          \x20 <in>:5:39 h\n\
          \x20 <in>:5:39 i\n\
          \x20 <in>:5:39 j\n\
          \x20 <in>:5:39 k\n\
          \x20 <in>:5:39 l",
            do_break_command(
                "backtrace",
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut vec![
                    make_test_call("a"),
                    make_test_call("b"),
                    make_test_call("c"),
                    make_test_call("d"),
                    make_test_call("e"),
                    make_test_call("f"),
                    make_test_call("g"),
                    make_test_call("h"),
                    make_test_call("i"),
                    make_test_call("j"),
                    make_test_call("k"),
                    make_test_call("l"),
                ]
            )
        );
    }
}
