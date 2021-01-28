use crate::ast;
use crate::exec;
use crate::tokeniser;
use std::io::BufRead;
use std::io::Write;

struct DebugCommand<'a> {
    name: &'a str,
    alias: Option<&'a str>,
    help: &'a str,
    executor: fn(
        cmd: &[&str],
        local_scope: exec::LocalScopeRef,
        global_function_scope: &mut ast::FunctionScope,
        call_stack: &mut ast::CallStack,
    ) -> String,
    // Where none means any number of args
    num_args: Option<usize>,
}

const DEBUG_COMMANDS: [DebugCommand; 7] = [
    DebugCommand {
        name: "backtrace",
        alias: Some("b"),
        help: "print backtrace",
        executor: do_backtrace_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "eval",
        alias: None,
        help: "run typed in code",
        executor: do_eval_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "continue",
        alias: Some("c"),
        help: "resume the program",
        executor: do_continue_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "globals",
        alias: Some("g"),
        help: "print global functions",
        executor: do_globals_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "help",
        alias: Some("h"),
        help: "print command help",
        executor: do_help_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "locals",
        alias: Some("l"),
        help: "print locals",
        executor: do_locals_command,
        num_args: Some(0),
    },
    DebugCommand {
        name: "print",
        alias: Some("p"),
        help: "print an individal symbol. print <name> <name2> ...",
        executor: do_print_command,
        num_args: None,
    },
];

fn do_break_command(
    cmd: &[&str],
    local_scope: exec::LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> String {
    for dc in &DEBUG_COMMANDS {
        if dc.name == cmd[0] || (dc.alias.is_some() && (dc.alias.unwrap() == cmd[0])) {
            if let Some(n) = dc.num_args {
                if (cmd.len() - 1) != n {
                    return format!(
                        "Incorrect number of arguments to {}\nHelp: {}",
                        dc.name, dc.help
                    );
                }
            }
            return (dc.executor)(cmd, local_scope, global_function_scope, call_stack);
        }
    }
    do_unknown_command(cmd, local_scope, global_function_scope, call_stack)
}

fn do_print_command(
    cmd: &[&str],
    local_scope: exec::LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    let mut result = Vec::new();
    for sym_name in &cmd[1..] {
        match exec::resolve_all_symbol_arguments(
            vec![ast::CallOrType::Type(ast::ASTType::Symbol(ast::Symbol {
                symbol: (*sym_name).into(),
                filename: "<in>".into(),
                line_number: 0,
                column_number: 0,
            }))],
            local_scope.clone(),
            global_function_scope,
        ) {
            Ok(v) => match &v[0] {
                ast::CallOrType::Type(t) => result.push(format!("'{} => {}", sym_name, t)),
                // TODO: direct symbol lookup fn?
                ast::CallOrType::Call(_) => return "Got a call from symbol lookup?".to_string(),
            },
            // TODO: fake line:col is still included here
            Err(e) => result.push(e),
        };
    }
    result.join("\n")
}

// Purely here to make the help output easier
// Actual continue done in breadth_builtin_break
fn do_continue_command(
    _cmd: &[&str],
    _local_scope: exec::LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    String::new()
}

fn do_help_command(
    _cmd: &[&str],
    _local_scope: exec::LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    // The continue command doesn't fit the pattern so manually add it
    // to the help.
    let max_name_len = DEBUG_COMMANDS.iter().map(|c| c.name.len()).max().unwrap();

    format!(
        "Commands:\n{}",
        DEBUG_COMMANDS
            .iter()
            .map(|c| {
                format!(
                    "{}{} - {}",
                    format!("{:width$}", c.name, width = max_name_len),
                    match c.alias {
                        Some(a) => format!(" ({})", a),
                        // TODO: bit of a hack to align properly
                        None => "    ".to_string(),
                    },
                    c.help
                )
            })
            .collect::<Vec<String>>()
            .join("\n")
    )
}

fn do_backtrace_command(
    _cmd: &[&str],
    _local_scope: exec::LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> String {
    let callstack_frames = 10;
    format!(
        "{}{}",
        if call_stack.len() > callstack_frames {
            format!(
                "<backtrace limited, showing {} of {} frames>\n",
                callstack_frames,
                call_stack.len()
            )
        } else {
            "".to_string()
        },
        ast::format_call_stack(if call_stack.len() >= callstack_frames {
            &call_stack[call_stack.len() - callstack_frames..]
        } else {
            &call_stack
        })
    )
}

fn do_locals_command(
    _cmd: &[&str],
    local_scope: exec::LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    // Since hashmaps are not ordered, show variables
    // in alphabetical order.
    let mut names = local_scope
        .borrow()
        .keys()
        .cloned()
        .collect::<Vec<String>>();
    names.sort();
    names
        .iter()
        .map(|n| {
            format!(
                "'{} => {}",
                n,
                match local_scope.borrow().get(n).unwrap() {
                    Some(v) => format!("{}", v),
                    None => "<undefined>".to_string(),
                }
            )
        })
        .collect::<Vec<String>>()
        .join("\n")
}

fn do_globals_command(
    _cmd: &[&str],
    _local_scope: exec::LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    // Again hashmaps aren't ordered
    let mut names = global_function_scope
        .keys()
        .cloned()
        .collect::<Vec<String>>();
    names.sort();
    names
        .iter()
        .map(|n| format!("{} => {}", n, global_function_scope.get(n).unwrap()))
        .collect::<Vec<String>>()
        .join("\n")
}

fn do_eval_command(
    _cmd: &[&str],
    local_scope: exec::LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> String {
    let stdin = std::io::stdin();
    let mut lines = Vec::new();
    println!("Enter your code, end with an empty line:");

    loop {
        let mut line = String::new();
        stdin
            .lock()
            .read_line(&mut line)
            .expect("Couldn't read from stdin");
        if line == "\n" {
            return match tokeniser::process_into_tokens("<in>", &lines.join("")) {
                Err(e) => format!("{}", e),
                Ok(ts) => match ast::build(ts) {
                    Err(e) => e,
                    Ok(ast) => {
                        match exec::exec_inner(ast, local_scope, global_function_scope, call_stack)
                        {
                            Ok(v) => format!("{}", v),
                            Err(e) => e,
                        }
                    }
                },
            };
        } else {
            lines.push(line);
        }
    }
}

fn do_unknown_command(
    cmd: &[&str],
    _local_scope: exec::LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> String {
    format!("Unknown command \"{}\"", cmd.join(" "))
}

pub fn breadth_builtin_break(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: exec::LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, exec::LocalScopeRef), String> {
    let mut line = String::new();
    let stdin = std::io::stdin();

    println!("\nbreak called at {}", ast::ast_type_err("", &function));

    loop {
        print!("(lal) ");
        // To get the above to show up
        std::io::stdout().flush().expect("Couldn't flush stdout");

        stdin
            .lock()
            .read_line(&mut line)
            .expect("Couldn't read from stdin");

        let cmd = line
            .split(' ')
            .filter(|p| !p.is_empty() && *p != "\n")
            .map(|p| p.trim())
            .collect::<Vec<&str>>();
        if !cmd.is_empty() {
            let result =
                do_break_command(&cmd, local_scope.clone(), global_function_scope, call_stack);

            match cmd[0] {
                // For continue there is a dummy command that returns nothing
                // but means it shows up in the help.
                "c" | "continue" => return Ok((arguments, local_scope)),
                _ => println!("{}", result),
            };
        }

        line.clear();
    }
}

#[cfg(test)]
mod tests {
    use crate::ast;
    use debug::do_break_command;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    #[test]
    fn break_unknown_command() {
        assert_eq!(
            "Unknown command \"abc\"",
            do_break_command(
                &vec!["abc"],
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut ast::CallStack::new()
            )
        );
    }

    fn test_break_print(cmd: &Vec<&str>, local_scope: ast::Scope, expected: &str) {
        assert_eq!(
            expected,
            do_break_command(
                cmd,
                Rc::new(RefCell::new(local_scope)),
                &mut ast::FunctionScope::new(),
                &mut ast::CallStack::new()
            )
        );
    }

    #[test]
    fn break_print() {
        let mut locals_test_scope = HashMap::new();
        locals_test_scope.insert("foo".to_string(), None);
        locals_test_scope.insert(
            "bar".to_string(),
            Some(ast::ASTType::Integer(99, "runtime".into(), 0, 0)),
        );
        locals_test_scope.insert(
            "ls".to_string(),
            Some(ast::ASTType::List(
                vec![
                    ast::ASTType::String("abc".into(), "runtime".into(), 0, 0),
                    ast::ASTType::None("runtime".into(), 0, 0),
                ],
                "runtime".into(),
                0,
                0,
            )),
        );

        test_break_print(&vec!["print"], locals_test_scope.clone(), "");
        test_break_print(
            &vec!["print", "unknown"],
            locals_test_scope.clone(),
            "<in>:0:0 Symbol unknown not found",
        );
        test_break_print(
            &vec!["print", "bar"],
            locals_test_scope.clone(),
            "'bar => 99",
        );
        test_break_print(
            &vec!["print", "foo", "bar"],
            locals_test_scope.clone(),
            "<in>:0:0 Symbol foo is declared but not defined\n\
             'bar => 99",
        );
    }

    #[test]
    fn break_locals() {
        let mut locals_test_scope = HashMap::new();
        locals_test_scope.insert("foo".to_string(), None);
        locals_test_scope.insert(
            "bar".to_string(),
            Some(ast::ASTType::Integer(99, "runtime".into(), 0, 0)),
        );
        locals_test_scope.insert(
            "ls".to_string(),
            Some(ast::ASTType::List(
                vec![
                    ast::ASTType::String("abc".into(), "runtime".into(), 0, 0),
                    ast::ASTType::None("runtime".into(), 0, 0),
                ],
                "runtime".into(),
                0,
                0,
            )),
        );

        // Printed in alphabetical order
        assert_eq!(
            "'bar => 99\n\
             'foo => <undefined>\n\
             'ls => [\"abc\" none]",
            do_break_command(
                &vec!["locals"],
                Rc::new(RefCell::new(locals_test_scope)),
                &mut ast::FunctionScope::new(),
                &mut ast::CallStack::new()
            )
        );
    }

    fn make_test_call(name: &str) -> ast::Call {
        ast::Call {
            fn_name: ast::Symbol {
                symbol: name.to_string(),
                filename: "<in>".into(),
                line_number: 5,
                column_number: 39,
            },
            arguments: vec![
                ast::CallOrType::Type(ast::ASTType::Symbol(ast::Symbol {
                    symbol: "a".into(),
                    filename: "<in>".into(),
                    line_number: 5,
                    column_number: 41,
                })),
                ast::CallOrType::Type(ast::ASTType::Symbol(ast::Symbol {
                    symbol: "b".into(),
                    filename: "<in>".into(),
                    line_number: 5,
                    column_number: 43,
                })),
            ],
        }
    }

    #[test]
    fn break_globals() {
        let mut test_global_scope = ast::FunctionScope::new();

        let test_function = ast::Function {
            name: ast::Symbol {
                symbol: "<lambda>".into(),
                filename: "<in>".into(),
                line_number: 5,
                column_number: 31,
            },
            call: make_test_call("foo"),
            argument_names: Vec::new(),
            captured_scope: Rc::new(RefCell::new(ast::Scope::new())),
        };

        test_global_scope.insert("zebra".to_string(), test_function.clone());
        test_global_scope.insert("abcd".to_string(), test_function.clone());

        assert_eq!(
            "abcd => (<lambda> )\n\
                    zebra => (<lambda> )",
            do_break_command(
                &vec!["globals"],
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut test_global_scope,
                &mut ast::CallStack::new()
            )
        );
    }

    #[test]
    fn break_backtrace() {
        // Empty
        assert_eq!(
            "Traceback (most recent call last):\n",
            do_break_command(
                &vec!["backtrace"],
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
                &vec!["backtrace"],
                Rc::new(RefCell::new(ast::Scope::new())),
                &mut ast::FunctionScope::new(),
                &mut vec![
                    make_test_call("a"),
                    make_test_call("b"),
                    make_test_call("c")
                ]
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
                &vec!["backtrace"],
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

    fn do_break_command_no_context(cmd: &Vec<&str>) -> String {
        do_break_command(
            cmd,
            Rc::new(RefCell::new(ast::Scope::new())),
            &mut ast::FunctionScope::new(),
            &mut vec![],
        )
    }

    #[test]
    fn break_argument_numbers() {
        assert!(do_break_command_no_context(&vec!["help", "food"])
            .starts_with("Incorrect number of arguments to help\nHelp: print command help"));
        // Alias here just to mix it up
        assert!(do_break_command_no_context(&vec!["c", "abc"])
            .starts_with("Incorrect number of arguments to continue"));
        // Assume the rest follow the pattern
    }

    #[test]
    fn break_help() {
        assert_eq!(
            "Commands:\n\
                    backtrace (b) - print backtrace\n\
                    eval          - run typed in code\n\
                    continue  (c) - resume the program\n\
                    globals   (g) - print global functions\n\
                    help      (h) - print command help\n\
                    locals    (l) - print locals\n\
                    print     (p) - print an individal symbol. print <name> <name2> ...",
            do_break_command_no_context(&vec!["help"])
        );
    }
}
