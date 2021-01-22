use crate::ast;
use crate::debug::breadth_builtin_break;
use crate::tokeniser;
use rand::Rng;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryInto;
use std::rc::Rc;

// First argument is either the Symbol for the function name (builtins)
// or an actual Functon (for user defined functions). This carries
// the locaton info for the call.
// The callstack is used for printing error messages.
type Executor = fn(ast::ASTType, Vec<ast::ASTType>) -> Result<ast::ASTType, String>;
// Again first argument is the function/function name being executed
// and lets us use its location info.
pub type LocalScopeRef = Rc<RefCell<ast::Scope>>;
type BreadthExecutor = fn(
    ast::ASTType,
    Vec<ast::CallOrType>,
    LocalScopeRef,
    &mut ast::FunctionScope,
    &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String>;

fn breadth_builtin_eval(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    let usage = "Expected exactly one String argument to eval";
    if arguments.len() != 1 {
        return Err(ast::ast_type_err(usage, &function));
    }

    let mut arguments =
        resolve_all_symbol_arguments(arguments, local_scope.clone(), global_function_scope)?;

    let arg = match arguments.pop().unwrap() {
        ast::CallOrType::Call(c) => {
            exec_inner(c, local_scope.clone(), global_function_scope, call_stack)?
        }
        ast::CallOrType::Type(t) => t,
    };

    match arg {
        ast::ASTType::String(s1, ..) => Ok((
            vec![ast::CallOrType::Type(exec_inner(
                ast::build(tokeniser::process_into_tokens("<in>", &s1)?)?,
                local_scope.clone(),
                global_function_scope,
                call_stack,
            )?)],
            local_scope,
        )),
        _ => Err(ast::ast_type_err(usage, &function)),
    }
}

fn builtin_eval(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    // Note that we do not eval the code here because we do not have access to the global scope
    Ok(arguments[0].clone())
}

fn breadth_builtin_import(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    let usage = "Expected exactly 1 String argument to import, the filepath";
    if arguments.len() != 1 {
        return Err(ast::ast_type_err(usage, &function));
    }

    let mut arguments =
        resolve_all_symbol_arguments(arguments, local_scope.clone(), global_function_scope)?;

    let filename_arg = match arguments.pop().unwrap() {
        ast::CallOrType::Type(arg) => arg,
        ast::CallOrType::Call(c) => {
            exec_inner(c, local_scope.clone(), global_function_scope, call_stack)?
        }
    };

    Ok((
        vec![match filename_arg {
            ast::ASTType::String(s, ..) => {
                exec_inner(
                    ast::build(tokeniser::tokenise_file(&s)?)?,
                    local_scope.clone(),
                    global_function_scope,
                    call_stack,
                )?;
                // Choosing not to return result of the module here
                ast::CallOrType::Type(ast::ASTType::None("runtime".into(), 0, 0))
            }
            _ => {
                return Err(ast::ast_type_err(
                    "Argument to import must be a String",
                    &function,
                ))
            }
        }],
        local_scope,
    ))
}

fn breadth_builtin_cond(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    if (arguments.len() < 2) || ((arguments.len() % 2) != 0) {
        return Err(ast::ast_type_err(
            "Expected matched condition-value/call pairs for cond call",
            &function,
        ));
    }

    let arguments =
        resolve_all_symbol_arguments(arguments, local_scope.clone(), global_function_scope)?;

    let mut matching_condition_pair = None;
    for pair in arguments.chunks_exact(2) {
        let condition_result = match &pair[0] {
            ast::CallOrType::Call(c) => exec_inner(
                c.clone(),
                local_scope.clone(),
                global_function_scope,
                call_stack,
            )?,
            ast::CallOrType::Type(t) => t.clone(),
        };
        if ast::ast_type_to_bool(&condition_result)? {
            matching_condition_pair = Some(pair);
            break;
        };
    }

    // If nothing returned true, that is an error
    match matching_condition_pair {
        Some(pair) => Ok((vec![pair[1].clone()], local_scope)),
        None => Err(ast::ast_type_err(
            "No condition returned true for cond call",
            &function,
        )),
    }
}

fn builtin_cond(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(arguments[0].clone())
}

fn breadth_builtin_defun(
    function: ast::ASTType,
    mut arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    // TODO: dedupe with lambda

    // defun should be of the form:
    // (defun 'fn_name '<arg1> '<arg2> ... '<argN> <function body)
    if arguments.len() < 2 {
        return Err(ast::ast_type_err(
            "Expected at least two arguments to defun. function name, <arguments>, function body.",
            &function,
        ));
    }

    let new_function_name = match arguments.remove(0) {
        ast::CallOrType::Type(t) => match t {
            ast::ASTType::Declaration(d) => ast::Symbol {
                symbol: d.name,
                filename: d.filename,
                line_number: d.line_number,
                column_number: d.column_number,
            },
            _ => {
                return Err(ast::ast_type_err(
                    "defun function name must be a Declaration",
                    &t,
                ))
            }
        },
        ast::CallOrType::Call(_) => {
            return Err(ast::ast_type_err(
                "defun function name must be a Declaration (not a call)",
                &function,
            ))
        }
    };

    global_function_scope.insert(
        new_function_name.symbol.clone(),
        match arguments.pop() {
            None => {
                return Err(ast::ast_type_err(
                    "defun requires at least one argument (the function body)",
                    &function,
                ))
            }
            Some(arg) => {
                match arg {
                    ast::CallOrType::Call(body) => {
                        ast::Function {
                            name: new_function_name,
                            call: body,
                            argument_names: {
                                let mut params = Vec::new();
                                for param in arguments {
                                    match param {
                                ast::CallOrType::Call(_) =>
                                    return Err(ast::ast_type_err(
                                        "defun function arguments must be Declarations (not Call)",
                                        &function)),
                                ast::CallOrType::Type(t) => match t {
                                    ast::ASTType::Declaration(def) => params.push(def.clone()),
                                    _ => return Err(ast::ast_type_err(
                                            "defun function arguments must be Declarations", &t))
                                }
                            };
                                }
                                params
                            },
                            // defun functions start from an empty scope
                            captured_scope: Rc::new(RefCell::new(HashMap::new())),
                        }
                    }
                    _ => {
                        return Err(ast::ast_type_err(
                            "defun's last argument must be the body of the function",
                            &function,
                        ))
                    }
                }
            }
        },
    );

    Ok((vec![], local_scope))
}

fn builtin_defun(
    _function: ast::ASTType,
    _arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(ast::ASTType::None("runtime".into(), 0, 0))
}

fn breadth_builtin_lambda(
    function: ast::ASTType,
    mut arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    _global_function_scope: &mut ast::FunctionScope,
    _call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    // Lambda should be of the form:
    // (lambda '<arg1> '<arg2> ... '<argN> <function body)
    let function_symbol = match function {
        ast::ASTType::Symbol(ref s) => s,
        _ => {
            return Err(ast::ast_type_err(
                "\"function\" argument to breadth_builtin_lambda must be a Symbol!",
                &function,
            ))
        }
    };

    let new_arguments = vec![match arguments.pop() {
        None => {
            return Err(ast::ast_type_err(
                "lambda requires at least one argument (the function body)",
                &function,
            ))
        }
        Some(arg) => match arg {
            ast::CallOrType::Call(body) => {
                ast::CallOrType::Type(ast::ASTType::Function(ast::Function {
                    name: ast::Symbol {
                        symbol: "<lambda>".into(),
                        // We use the locaton of the (lambda ...) start so that later
                        // we can tell the user where the lambda was defined.
                        filename: function_symbol.filename.clone(),
                        line_number: function_symbol.line_number,
                        column_number: function_symbol.column_number,
                    },
                    call: body,
                    argument_names: {
                        let mut params = Vec::new();
                        for param in arguments {
                            match param {
                                ast::CallOrType::Call(_) => {
                                    return Err(ast::ast_type_err(
                                        "lambda arguments must be Declarations (not Call)",
                                        &function,
                                    ))
                                }
                                ast::CallOrType::Type(t) => match t {
                                    ast::ASTType::Declaration(def) => params.push(def.clone()),
                                    _ => {
                                        return Err(ast::ast_type_err(
                                            "lambda arguments must be Declarations",
                                            &t,
                                        ))
                                    }
                                },
                            };
                        }
                        params
                    },
                    // Lambda's implicitly capture the current scope
                    captured_scope: local_scope.clone(),
                }))
            }
            _ => {
                return Err(ast::ast_type_err(
                    "lambda's last argument must be the body of the function",
                    &function,
                ))
            }
        },
    }];

    Ok((new_arguments, local_scope))
}

fn builtin_lambda(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    // Return the function we built earlier
    Ok(arguments[0].clone())
}

// Note that this the ony executor that gets the gobal function scope
fn builtin_user_defined_function(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<ast::ASTType, String> {
    let function = match function {
        ast::ASTType::Function(f) => f,
        ast::ASTType::BuiltinFunctionWrapper(w) => {
            return exec_inner(
                ast::Call {
                    fn_name: ast::Symbol {
                        // This special prefix means that when it finally does get called,
                        // we won't call anything in the local or global scope that happens
                        // to have shadowed it since we built the wrapper.
                        symbol: format!("__builtin_{}", w.name),
                        filename: w.name.filename,
                        line_number: w.name.line_number,
                        column_number: w.name.column_number,
                    },
                    arguments: arguments
                        .iter()
                        .map(|a| ast::CallOrType::Type(a.clone()))
                        .collect(),
                },
                Rc::new(RefCell::new(ast::Scope::new())),
                global_function_scope,
                call_stack,
            );
        }
        _ => {
            return Err(ast::ast_type_err(
                "builtin_user_defined_function argument \
                                \"function\" must be a Function or BuiltinFunctionWrapper!",
                &function,
            ))
        }
    };

    if arguments.len() != function.argument_names.len() {
        return Err(ast::ast_type_err(
            &format!(
                "Incorrect number of arguments to function {}. \
                                    Expected {} ({}) got {} ({})",
                function.name.symbol,
                function.argument_names.len(),
                ast::format_declaration_list(&function.argument_names),
                arguments.len(),
                ast::format_asttype_list(&arguments)
            ),
            &ast::ASTType::Function(function),
        ));
    }

    // lambdas capture the scope they are defined in (not modifying the original)
    let local_scope = Rc::new(RefCell::new(function.captured_scope.borrow().clone()));

    // Then its arguments can shadow those
    for (name, value) in function.argument_names.iter().zip(arguments.iter()) {
        local_scope
            .borrow_mut()
            .insert(name.name.clone(), Some(value.clone()));
    }

    exec_inner(
        function.call,
        local_scope,
        global_function_scope,
        call_stack,
    )
}

fn check_let_arguments(
    function: &ast::ASTType,
    arguments: &[ast::CallOrType],
    let_kind: &str,
) -> Result<(), String> {
    // Lets should have the form:
    // (<let_kind> <defintion> <value> <defintion2> <value2> ... <call>)
    if arguments.len() < 3 {
        return Err(ast::ast_type_err(
            &format!("{} requires at least 3 arguments", let_kind),
            function,
        ));
    }

    if (arguments.len() % 2) == 0 {
        return Err(ast::ast_type_err(
            &format!(
                "Wrong number of arguments to {}. Expected '<name> <value> ... <body>",
                let_kind
            ),
            function,
        ));
    }

    Ok(())
}

fn breadth_builtin_let(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    check_let_arguments(&function, &arguments, "let")?;

    let mut arguments =
        resolve_all_symbol_arguments(arguments, local_scope.clone(), global_function_scope)?;

    // If there are multiple Calls as values, we don't want to use
    // the updated symbols for each subsequent call. They must all
    // use the scope *before* any new variables are added/updated.
    let new_local_scope = Rc::new(RefCell::new(local_scope.borrow().clone()));

    for pair in arguments.chunks_exact(2) {
        let mut pair = pair.to_vec();

        // If the value is the result of a call, resolve it
        if let ast::CallOrType::Call(c) = &pair[1] {
            pair[1] = ast::CallOrType::Type(exec_inner(
                c.clone(),
                local_scope.clone(),
                global_function_scope,
                call_stack,
            )?);
        };

        // Otherwise we got some declaration
        match (&pair[0], &pair[1]) {
            (ast::CallOrType::Type(t1), ast::CallOrType::Type(t2)) => match t1 {
                ast::ASTType::Declaration(def) => match t2 {
                    // This should have been done by resolve_all_symbol_arguments
                    ast::ASTType::Symbol(s) => {
                        return Err(ast::ast_type_err(
                            &format!("Unresolved symbol {} for let pair value", s),
                            &t2,
                        ))
                    }
                    _ => new_local_scope
                        .borrow_mut()
                        .insert(def.name.clone(), Some(t2.clone())),
                },
                _ => {
                    return Err(ast::ast_type_err(
                        "Expected Declaration as first of let name-value pair",
                        &t1,
                    ))
                }
            },
            (_, _) => {
                return Err(ast::ast_type_err(
                    "Unresolved call in let declaration pair!",
                    &function,
                ))
            }
        };
    }

    // Remove any name-value arguments
    Ok((arguments.split_off(arguments.len() - 1), new_local_scope))
}

fn builtin_let(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    match arguments.last() {
        Some(arg) => Ok(arg.clone()),
        None => Err(ast::ast_type_err(
            "let call must have at least one argument to return",
            &function,
        )),
    }
}

fn breadth_builtin_letrec(
    function: ast::ASTType,
    mut arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    check_let_arguments(&function, &arguments, "letrec")?;

    // Split out names and values so we don't have to match the names again
    let mut name_values = Vec::new();
    // letrec inherits the outer scope but does not modify it
    let local_scope = Rc::new(RefCell::new(local_scope.borrow().clone()));

    // For each name-value
    for pair in arguments.chunks_exact(2) {
        match &pair[0] {
            ast::CallOrType::Call(_) => {
                return Err(ast::ast_type_err(
                    "Unresolved call as letrec declaration",
                    &function,
                ))
            }
            ast::CallOrType::Type(t) => {
                match t {
                    ast::ASTType::Declaration(d) => {
                        // Declare but don't define the new variable
                        local_scope.borrow_mut().insert(d.name.clone(), None);
                        name_values.push((d.name.clone(), pair[1].clone()));
                    }
                    _ => {
                        return Err(ast::ast_type_err(
                            "Expected Declaration as first of letrec name-value pair",
                            &t,
                        ))
                    }
                }
            }
        };
    }

    // Then we define the values in left to right order updating scope as we go
    for pair in &name_values {
        let value = match &pair.1 {
            // If the value is the result of a call, execute it
            ast::CallOrType::Call(c) => exec_inner(
                c.clone(),
                local_scope.clone(),
                global_function_scope,
                call_stack,
            )?,
            ast::CallOrType::Type(t) => match t {
                // If it's a symbol resolve it
                ast::ASTType::Symbol(ref s) => match search_local_scope(&s, &local_scope) {
                    // Was there a name?
                    Some(got_name) =>
                    // Was there a value?
                    {
                        match got_name {
                            Some(v) => v,
                            None => {
                                return Err(ast::ast_type_err(
                                    &format!("Declared but undefined symbol {} in letrec pair", s),
                                    &t,
                                ))
                            }
                        }
                    }
                    None => {
                        return Err(ast::ast_type_err(
                            &format!("Unknown symbol {} in letrec pair", s),
                            &t,
                        ))
                    }
                },
                // Otherwise use the value as is
                _ => t.clone(),
            },
        };

        local_scope.borrow_mut().insert(pair.0.clone(), Some(value));
    }

    // Remove all the name-value arguments
    Ok((arguments.split_off(arguments.len() - 1), local_scope))
}

fn builtin_letrec(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    match arguments.last() {
        Some(arg) => Ok(arg.clone()),
        None => Err(ast::ast_type_err(
            "letrec call must have at least one argument to return",
            &function,
        )),
    }
}

fn builtin_plus(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.is_empty() {
        return Err(ast::ast_type_err(
            "+ requires at least one argument",
            &function,
        ));
    }

    if arguments.len() == 1 {
        return Ok(arguments[0].clone());
    }

    match arguments[0] {
        // If the first argument is type T, proceed as if the
        // rest are T, otherwise error
        ast::ASTType::Integer(..) => {
            let mut total = 0;
            for arg in arguments {
                match arg {
                    ast::ASTType::Integer(i, ..) => total += i,
                    _ => {
                        return Err(ast::ast_type_err(
                            "+ argument is not an Integer (does not match the 1st argument)",
                            &arg,
                        ))
                    }
                };
            }
            Ok(ast::ASTType::Integer(total, "runtime".into(), 0, 0))
        }
        ast::ASTType::String(..) => {
            let mut combined = String::new();
            for arg in arguments {
                match arg {
                    ast::ASTType::String(s, ..) => combined += &s,
                    _ => {
                        return Err(ast::ast_type_err(
                            "+ argument is not a String (does not match the 1st argument)",
                            &arg,
                        ))
                    }
                };
            }
            Ok(ast::ASTType::String(combined, "runtime".into(), 0, 0))
        }
        _ => Err(ast::ast_type_err(
            &format!(
                "Cannot + multiple arguments of types {}",
                ast::format_asttype_typename_list(&arguments)
            ),
            &arguments[0],
        )),
    }
}

fn builtin_minus(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() < 2 {
        return Err(ast::ast_type_err(
            "- requires at least two arguments",
            &function,
        ));
    }

    match arguments[0] {
        // If the first argument is type T, proceed as if the
        // rest are T, otherwise error
        ast::ASTType::Integer(i1, ..) => {
            let mut total = i1;
            for arg in &arguments[1..] {
                match arg {
                    ast::ASTType::Integer(i, ..) => total -= i,
                    _ => return Err(ast::ast_type_err("- argument is not an Integer", &arg)),
                };
            }
            Ok(ast::ASTType::Integer(total, "runtime".into(), 0, 0))
        }
        _ => Err(ast::ast_type_err(
            &format!(
                "Cannot - arguments of types {}",
                ast::format_asttype_typename_list(&arguments)
            ),
            &arguments[0],
        )),
    }
}

fn two_argument_math(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
    operator: fn(i64, i64) -> i64,
) -> Result<ast::ASTType, String> {
    if arguments.len() != 2 {
        return Err(ast::ast_type_err(
            &format!("{} requires exactly two Integer arguments", function),
            &function,
        ));
    }

    match (&arguments[0], &arguments[1]) {
        (ast::ASTType::Integer(i1, ..), ast::ASTType::Integer(i2, ..)) => Ok(
            ast::ASTType::Integer(operator(*i1, *i2), "runtime".into(), 0, 0),
        ),
        (_, _) => Err(ast::ast_type_err(
            &format!(
                "Both arguments to {} must be Integer (got {})",
                function,
                ast::format_asttype_typename_list(&arguments)
            ),
            &function,
        )),
    }
}

fn builtin_mod(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    two_argument_math(function, arguments, |a, b| a % b)
}

fn builtin_div(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    two_argument_math(function, arguments, |a, b| a / b)
}

fn builtin_mul(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    two_argument_math(function, arguments, |a, b| a * b)
}

fn builtin_randint(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    let usage = "Expected either 1 (max) or 2 (min, max) Integer arguments to randint";
    if arguments.len() > 2 {
        return Err(ast::ast_type_err(usage, &function));
    }

    let (min, max) = match arguments.len() {
        // Argument is the maximum
        1 => match &arguments[0] {
            ast::ASTType::Integer(i, ..) => (0, *i),
            _ => return Err(ast::ast_type_err(usage, &function)),
        },
        // Min, max
        2 => match (&arguments[0], &arguments[1]) {
            (ast::ASTType::Integer(i1, ..), ast::ASTType::Integer(i2, ..)) => (*i1, *i2),
            (_, _) => return Err(ast::ast_type_err(usage, &function)),
        },
        0 | _ => return Err(ast::ast_type_err(usage, &function)),
    };

    if min >= max {
        return Err(ast::ast_type_err(
            &format!("randint min ({}) must be < max ({})", min, max),
            &function,
        ));
    }

    Ok(ast::ASTType::Integer(
        rand::thread_rng().gen_range(min..max),
        "runtime".into(),
        0,
        0,
    ))
}

fn builtin_body(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    // body returns the value of the last call in the list of results
    match arguments.last() {
        Some(arg) => Ok(arg.clone()),
        None => Err(ast::ast_type_err(
            "body must have at least one argument to return",
            &function,
        )),
    }
}

// TODO: test me
fn builtin_print(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    println!("{}", ast::format_asttype_list(&arguments));
    Ok(ast::ASTType::None("runtime".into(), 0, 0))
}

fn builtin_none(
    _function: ast::ASTType,
    _arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(ast::ASTType::None("runtime".into(), 0, 0))
}

fn builtin_and(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() < 2 {
        return Err(ast::ast_type_err(
            "Expected at least 2 arguments to and",
            &function,
        ));
    }

    let mut result = true;
    for arg in arguments {
        if !ast::ast_type_to_bool(&arg)? {
            result = false;
            break;
        }
    }
    Ok(ast::ASTType::Bool(result, "runtime".into(), 0, 0))
}

// TODO: generalise logic functions?
fn builtin_or(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() < 2 {
        return Err(ast::ast_type_err(
            "Expected at least 2 arguments to or",
            &function,
        ));
    }

    let mut result = false;
    for arg in arguments {
        result |= ast::ast_type_to_bool(&arg)?;
    }
    Ok(ast::ASTType::Bool(result, "runtime".into(), 0, 0))
}

fn builtin_list(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(ast::ASTType::List(arguments, "runtime".into(), 0, 0))
}

fn builtin_head(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() != 1 {
        return Err(ast::ast_type_err(
            "Expected exactly 1 argument to head",
            &function,
        ));
    }

    let arg = arguments[0].clone();
    match arg {
        ast::ASTType::List(ref l, ..) => match l.len() {
            0 => Err(ast::ast_type_err("Cannot head on an empty List", &arg)),
            _ => Ok(l[0].clone()),
        },
        ast::ASTType::String(ref s, ..) => match s.len() {
            0 => Err(ast::ast_type_err("Cannot head on an empty String", &arg)),
            _ => Ok(ast::ASTType::String(
                String::from(s.chars().next().unwrap()),
                "runtime".into(),
                0,
                0,
            )),
        },
        _ => Err(ast::ast_type_err(
            &format!("Cannot head on type {}", ast::asttype_typename(&arg)),
            &arg,
        )),
    }
}

fn builtin_tail(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() != 1 {
        return Err(ast::ast_type_err(
            "Expected exactly 1 argument to tail",
            &function,
        ));
    }

    let mut arg = arguments[0].clone();
    match arg {
        ast::ASTType::List(ref mut l, ..) => match l.len() {
            0 => Err(ast::ast_type_err("Cannot tail on an empty List", &arg)),
            _ => Ok(ast::ASTType::List(l.split_off(1), "runtime".into(), 0, 0)),
        },
        ast::ASTType::String(ref mut s, ..) => match s.len() {
            0 => Err(ast::ast_type_err("Cannot tail on an empty String", &arg)),
            _ => Ok(ast::ASTType::String(s.split_off(1), "runtime".into(), 0, 0)),
        },
        _ => Err(ast::ast_type_err(
            &format!("Cannot tail on type {}", ast::asttype_typename(&arg)),
            &arg,
        )),
    }
}

fn flatten_argument(argument: ast::ASTType) -> Vec<ast::ASTType> {
    match argument {
        // If it's a list, flatten it and its children into a single list
        ast::ASTType::List(l, ..) => l
            .into_iter()
            .map(flatten_argument)
            .flatten()
            .collect::<Vec<ast::ASTType>>(),
        _ => vec![argument],
    }
}

fn builtin_flatten(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(ast::ASTType::List(
        arguments
            .into_iter()
            // Produce a list of lists. This will only ever be 1 level deep
            // due to the recursion in flatten_argument.
            .map(flatten_argument)
            .collect::<Vec<Vec<ast::ASTType>>>()
            .into_iter()
            // Then flatten that one level to get a flat list
            .flatten()
            .collect::<Vec<ast::ASTType>>(),
        "runtime".into(),
        0,
        0,
    ))
}

fn builtin_extend(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() < 2 {
        return Err(ast::ast_type_err(
            "Expected at least 2 List arguments for extend",
            &function,
        ));
    }

    let types_err = "All arguments to extend must be List, got";
    if let ast::ASTType::List(mut list, ..) = arguments[0].clone() {
        for arg in &arguments[1..] {
            match arg {
                ast::ASTType::List(l, ..) => list.extend(l.clone()),
                _ => {
                    return Err(ast::ast_type_err(
                        &format!("{} {}", types_err, ast::format_asttype_list(&arguments)),
                        &function,
                    ))
                }
            };
        }
        Ok(ast::ASTType::List(list, "runtime".into(), 0, 0))
    } else {
        return Err(ast::ast_type_err(
            &format!("{} {}", types_err, ast::format_asttype_list(&arguments)),
            &function,
        ));
    }
}

fn breadth_builtin_if(
    function: ast::ASTType,
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<(Vec<ast::CallOrType>, LocalScopeRef), String> {
    let mut arguments =
        resolve_all_symbol_arguments(arguments, local_scope.clone(), global_function_scope)?;

    match arguments.len() {
        // condition, true value
        // condition, true value, else value
        2 | 3 => {
            // Evaluate the condition
            let result = match arguments[0].clone() {
                ast::CallOrType::Call(c) => {
                    exec_inner(c, local_scope.clone(), global_function_scope, call_stack)?
                }
                ast::CallOrType::Type(t) => t,
            };
            let was_true = ast::ast_type_to_bool(&result)?;

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
                arguments.push(ast::CallOrType::Type(ast::ASTType::None(
                    "runtime".into(),
                    0,
                    0,
                )));
            }
            // else we leave the true value as the only argument
        }
        _ => {
            return Err(ast::ast_type_err(
                "Incorrect number of arguments to if. \
                                Expected <condition> <true value> <false value (optional)>",
                &function,
            ))
        }
    }

    Ok((arguments, local_scope))
}

fn builtin_if(
    _function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    Ok(arguments[0].clone())
}

fn builtin_comparison(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
    compare: ast::Comparison,
) -> Result<ast::ASTType, String> {
    if arguments.len() != 2 {
        return Err(ast::ast_type_err(
            &format!("Expected exactly 2 arguments to {}", String::from(compare)),
            &function,
        ));
    }

    Ok(ast::ASTType::Bool(
        ast::compare_asttypes(&function, &arguments[0], &arguments[1], compare)?,
        "runtime".into(),
        0,
        0,
    ))
}

fn builtin_less_than(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::LessThan)
}

fn builtin_less_than_or_equal_to(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::LessThanOrEqual)
}

fn builtin_greater_than(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::GreaterThan)
}

fn builtin_greater_than_or_equal_to(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::GreaterThanOrEqual)
}

fn builtin_equal_to(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::Equal)
}

fn builtin_not_equal_to(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    builtin_comparison(function, arguments, ast::Comparison::NotEqual)
}

fn builtin_len(
    function: ast::ASTType,
    arguments: Vec<ast::ASTType>,
) -> Result<ast::ASTType, String> {
    if arguments.len() != 1 {
        return Err(ast::ast_type_err(
            "Expected exactly 1 argument to len",
            &function,
        ));
    }

    let arg = &arguments[0];
    match arg {
        ast::ASTType::List(l, ..) => Ok(ast::ASTType::Integer(
            l.len().try_into().unwrap(),
            "runtime".into(),
            0,
            0,
        )),
        ast::ASTType::String(s, ..) => Ok(ast::ASTType::Integer(
            s.len().try_into().unwrap(),
            "runtime".into(),
            0,
            0,
        )),
        _ => Err(ast::ast_type_err(
            "Argument to len must be List or String",
            arg,
        )),
    }
}

fn search_local_scope(
    name: &ast::Symbol,
    local_scope: &LocalScopeRef,
) -> Option<Option<ast::ASTType>> {
    match local_scope.borrow().get(&name.symbol) {
        // First step tells us the name has been declared
        Some(decl) => match decl {
            // Meaning it has also been defined
            Some(t) => Some(Some(t.clone())),
            // Declared but not defined
            None => Some(None),
        },
        None => None,
    }
}

fn add_origin_to_user_function(
    call_name: &ast::Symbol,
    function: ast::Function,
    fn_kind: &str,
) -> Result<ast::ASTType, String> {
    // Replace the function's name with the name we're calling as.
    // For defun this will be the same as the original name,
    // for lambdas this is the name of the variable we assigned
    // then to.
    // This will give the location that it is called from,
    // and we add the original location in also.
    // (location of the defun/lambda call)
    Ok(ast::ASTType::Function(ast::Function {
        name: ast::Symbol {
            symbol: format!(
                "\"{}\" ({} defined at {}:{}:{})",
                call_name.symbol,
                fn_kind,
                function.name.filename,
                function.name.line_number,
                function.name.column_number
            ),
            filename: call_name.filename.clone(),
            line_number: call_name.line_number,
            column_number: call_name.column_number,
        },
        call: function.call.clone(),
        argument_names: function.argument_names,
        captured_scope: function.captured_scope,
    }))
}

fn find_local_scope_function(
    call: &ast::Call,
    local_scope: LocalScopeRef,
) -> Result<Option<ast::ASTType>, String> {
    let fn_name = ast::ASTType::Symbol(call.fn_name.clone());

    match search_local_scope(&call.fn_name, &local_scope) {
        Some(got_name) => match got_name {
            Some(v) => match v {
                ast::ASTType::Function(f) => Ok(Some(add_origin_to_user_function(
                    &call.fn_name,
                    f,
                    "lambda",
                )?)),
                ast::ASTType::BuiltinFunctionWrapper(_) => Ok(Some(v)),
                _ => Err(ast::ast_type_err(
                    &format!(
                        "Found \"{}\" in local scope but it is not a function",
                        call.fn_name.symbol
                    ),
                    &fn_name,
                )),
            },
            None => Err(ast::ast_type_err(
                &format!(
                    "Function name {} is declared but not defined",
                    call.fn_name.symbol
                ),
                &fn_name,
            )),
        },
        None => Ok(None),
    }
}

fn find_global_scope_function(
    call_name: &ast::Symbol,
    global_function_scope: &ast::FunctionScope,
) -> Result<Option<ast::ASTType>, String> {
    match global_function_scope.get(&call_name.symbol) {
        Some(f) => Ok(Some(add_origin_to_user_function(
            &call_name,
            f.clone(),
            "function",
        )?)),
        None => Ok(None),
    }
}

fn find_builtin_function(
    call_name: &ast::Symbol,
) -> Option<(ast::ASTType, Option<BreadthExecutor>, Executor)> {
    let function_start = ast::ASTType::Symbol(call_name.clone());

    // BuiltinFunctionWrappers have __builtin_ prepended to the symbol name
    // to prevent them being found in the usual function lookups when they
    // are called. They should always resolve to a builtin.
    let fn_name = call_name.symbol.trim_start_matches("__builtin_");
    match fn_name {
        "body" => Some((function_start, None, builtin_body)),
        "+" => Some((function_start, None, builtin_plus)),
        "-" => Some((function_start, None, builtin_minus)),
        "%" => Some((function_start, None, builtin_mod)),
        "/" => Some((function_start, None, builtin_div)),
        "*" => Some((function_start, None, builtin_mul)),
        "print" => Some((function_start, None, builtin_print)),
        "let" => Some((function_start, Some(breadth_builtin_let), builtin_let)),
        "letrec" => Some((function_start, Some(breadth_builtin_letrec), builtin_letrec)),
        "lambda" => Some((function_start, Some(breadth_builtin_lambda), builtin_lambda)),
        "defun" => Some((function_start, Some(breadth_builtin_defun), builtin_defun)),
        "none" => Some((function_start, None, builtin_none)),
        "list" => Some((function_start, None, builtin_list)),
        "if" => Some((function_start, Some(breadth_builtin_if), builtin_if)),
        "cond" => Some((function_start, Some(breadth_builtin_cond), builtin_cond)),
        "<" => Some((function_start, None, builtin_less_than)),
        ">" => Some((function_start, None, builtin_greater_than)),
        ">=" => Some((function_start, None, builtin_greater_than_or_equal_to)),
        "<=" => Some((function_start, None, builtin_less_than_or_equal_to)),
        "eq" => Some((function_start, None, builtin_equal_to)),
        "neq" => Some((function_start, None, builtin_not_equal_to)),
        "flatten" => Some((function_start, None, builtin_flatten)),
        "extend" => Some((function_start, None, builtin_extend)),
        "import" => Some((function_start, Some(breadth_builtin_import), builtin_none)),
        "head" => Some((function_start, None, builtin_head)),
        "tail" => Some((function_start, None, builtin_tail)),
        "len" => Some((function_start, None, builtin_len)),
        "and" => Some((function_start, None, builtin_and)),
        "or" => Some((function_start, None, builtin_or)),
        "break" => Some((function_start, Some(breadth_builtin_break), builtin_none)),
        "eval" => Some((function_start, Some(breadth_builtin_eval), builtin_eval)),
        "randint" => Some((function_start, None, builtin_randint)),
        _ => None,
    }
}

pub fn resolve_all_symbol_arguments(
    arguments: Vec<ast::CallOrType>,
    local_scope: LocalScopeRef,
    global_function_scope: &ast::FunctionScope,
) -> Result<Vec<ast::CallOrType>, String> {
    let mut new_arguments = Vec::new();
    for arg in arguments {
        match arg {
            ast::CallOrType::Type(t) => match t {
                ast::ASTType::Symbol(ref s) => match search_local_scope(s, &local_scope) {
                    Some(got_name) => match got_name {
                        Some(v) => new_arguments.push(ast::CallOrType::Type(v)),
                        None => {
                            return Err(ast::ast_type_err(
                                &format!("Symbol {} is declared but not defined", s.symbol),
                                &t,
                            ))
                        }
                    },
                    None => match find_global_scope_function(s, global_function_scope)? {
                        Some(f) => new_arguments.push(ast::CallOrType::Type(f)),
                        None => match find_builtin_function(s) {
                            Some(_) => new_arguments.push(ast::CallOrType::Type(
                                ast::ASTType::BuiltinFunctionWrapper(ast::BuiltinFunctionWrapper {
                                    name: s.clone(),
                                }),
                            )),
                            None => {
                                return Err(ast::ast_type_err(
                                    &format!("Symbol {} not found", s.symbol),
                                    &t,
                                ))
                            }
                        },
                    },
                },
                _ => new_arguments.push(ast::CallOrType::Type(t.clone())),
            },
            _ => new_arguments.push(arg.clone()),
        };
    }
    Ok(new_arguments)
}

pub fn exec_inner(
    call: ast::Call,
    local_scope: LocalScopeRef,
    global_function_scope: &mut ast::FunctionScope,
    call_stack: &mut ast::CallStack,
) -> Result<ast::ASTType, String> {
    call_stack.push(call.clone());

    // breadth_executor does any breadth first evaluation
    // For example let. (let 'a 1 (print a))
    // This must add "a" to the local scope before we can
    // *depth first* execute the print.
    // This is optional since most calls can just use depth
    // first processing.
    //
    // function_start is passed to the executor so that it can know where
    // the call starts for error messages.

    // The only executor that needs the global function scope is builtin_user_defined
    // So we jump through some hoops to check for that first, meaning we don't
    // have to pass the global scope to every single executor.
    // (note that most breadth executors execute calls, so they need the global scope)
    let mut function_start = match find_local_scope_function(&call, local_scope.clone())? {
        Some(f) => Some(f),
        None => match find_global_scope_function(&call.fn_name, global_function_scope)? {
            Some(f) => Some(f),
            None => None,
        },
    };

    let mut breadth_executor = None;
    let mut executor = None;

    // If we didn't find a user defined function
    if function_start.is_none() {
        let got = match find_builtin_function(&call.fn_name) {
            Some(v) => v,
            None => {
                return Err(ast::ast_type_err(
                    &format!("Unknown function \"{}\"", call.fn_name.symbol),
                    &ast::ASTType::Symbol(call.fn_name),
                ))
            }
        };
        function_start = Some(got.0);
        // This is already an Option
        breadth_executor = got.1;
        executor = Some(got.2);
    }

    let function_start = function_start.unwrap();

    // Anything that does breadth first must choose when to evaluate symbols
    let (arguments, local_scope) = match breadth_executor {
        Some(f) => f(
            function_start.clone(),
            call.arguments,
            local_scope,
            global_function_scope,
            call_stack,
        )?,
        // Anything else we just do it all now
        None => (
            resolve_all_symbol_arguments(
                call.arguments,
                local_scope.clone(),
                global_function_scope,
            )?,
            local_scope,
        ),
    };

    // Now resolve all Calls in the remaining arguments
    // (this is depth first, as opposed to breadth first as above)
    let mut resolved_calls_arguments = Vec::new();
    for arg in arguments {
        match arg {
            ast::CallOrType::Call(c) => resolved_calls_arguments.push(exec_inner(
                c.clone(),
                local_scope.clone(),
                global_function_scope,
                call_stack,
            )?),
            ast::CallOrType::Type(t) => resolved_calls_arguments.push(t.clone()),
        };
    }

    // Finally run the current function with all Symbols and Calls resolved
    let result = match executor {
        Some(e) => e(function_start, resolved_calls_arguments)?,
        None => builtin_user_defined_function(
            function_start,
            resolved_calls_arguments,
            global_function_scope,
            call_stack,
        )?,
    };
    // Now we know it worked we can remove this call level
    call_stack.pop();
    Ok(result)
}

pub fn exec(call: ast::Call) -> Result<ast::ASTType, (String, ast::CallStack)> {
    let local_scope: LocalScopeRef = Rc::new(RefCell::new(HashMap::new()));
    let mut global_function_scope: ast::FunctionScope = HashMap::new();
    let mut call_stack = Vec::new();
    match exec_inner(
        call,
        local_scope,
        &mut global_function_scope,
        &mut call_stack,
    ) {
        Ok(t) => Ok(t),
        Err(e) => Err((e, call_stack)),
    }
}

#[cfg(test)]
mod tests {
    use crate::tokeniser::process_into_tokens;
    use ast::build;
    use ast::ASTType;
    use ast::Call;
    use ast::CallOrType;
    use ast::Declaration;
    use ast::Function;
    use ast::Symbol;
    use exec::exec;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;

    fn run_program(program: &str) -> Result<ASTType, String> {
        match exec(build(process_into_tokens("<in>", program)?)?) {
            Ok(v) => Ok(v),
            // Ignore callstack
            Err(e) => Err(e.0),
        }
    }

    fn check_error(program: &str, error: &str) {
        assert_eq!(run_program(program), Err(error.to_string()));
    }

    fn check_result(program: &str, expected: ASTType) {
        assert_eq!(run_program(program), Ok(expected));
    }

    #[test]
    fn simple_exec() {
        // Simple single call
        check_result("(+ 1 2)", ASTType::Integer(3, "runtime".into(), 0, 0));
        // Result is the result of the last block
        check_result(
            "(+ 1 2)(+ 9 10)",
            ASTType::Integer(19, "runtime".into(), 0, 0),
        );
        // We can process nested calls
        check_result(
            "(+ (+ 1 (+ 2 3)) 2)",
            ASTType::Integer(8, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn user_functions_shadow_builtins() {
        check_result(
            "
            # The + inside the lambda will be the builtin
            (let '+ (lambda 'x 'y (+ x y 1))
                # The + here is the lambda from above
                # So we get 1 + 2 + 1 = 4
                (+ 1 2)
            )",
            ASTType::Integer(4, "runtime".into(), 0, 0),
        );

        // You can still name vars the same as a builtin as long
        // as it's not used as a function name in that scope.
        check_result(
            "
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
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 5, 26),
                    ASTType::Integer(2, "<in>".into(), 10, 24),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn errors_shadowed_builtin_not_a_function() {
        check_error(
            "(let '+ \"foo\"
               (+ 1 2 3)
             )",
            "<in>:2:17 Found \"+\" in local scope but it is not a function",
        );
    }

    #[test]
    fn errors_unknown_function() {
        check_error(
            "(not_a_function 1 2)",
            "<in>:1:2 Unknown function \"not_a_function\"",
        );
    }

    #[test]
    fn builtin_body_returns_last_value() {
        check_result(
            "(body (+ 1) (+ 2))",
            ASTType::Integer(2, "<in>".into(), 1, 16),
        );
    }

    #[test]
    fn builtin_body_errors_no_calls() {
        check_error(
            "(body )",
            "<in>:1:2 body must have at least one argument to return",
        );
    }

    #[test]
    fn builtin_plus_basic() {
        // Strings and integers can be added
        check_result("(+ 9 10)", ASTType::Integer(19, "runtime".into(), 0, 0));
        check_result(
            "(+ \"foo\" \"bar\")",
            ASTType::String("foobar".into(), "runtime".into(), 0, 0),
        );

        // We can handle any number of arguments
        check_result(
            "(+ 9 10 11 12)",
            ASTType::Integer(42, "runtime".into(), 0, 0),
        );
        check_result(
            "(+ \"a\" \"b\" \"c\" \"d\")",
            ASTType::String("abcd".into(), "runtime".into(), 0, 0),
        );

        // Minimum of 1 argument
        check_result("(+ 99)", ASTType::Integer(99, "<in>".into(), 1, 4));
        check_result(
            "(+ \"def\")",
            ASTType::String("def".into(), "<in>".into(), 1, 4),
        );
    }

    #[test]
    fn builtin_plus_errors() {
        check_error("(+)", "<in>:1:2 + requires at least one argument");
        check_error(
            "(+ 'food 'bla)",
            "<in>:1:4 Cannot + multiple arguments of types Declaration, Declaration",
        );
        check_error(
            "(+ 1 \"2\")",
            "<in>:1:6 + argument is not an Integer (does not match the 1st argument)",
        );
        check_error(
            "(+ \"2\" 1)",
            "<in>:1:8 + argument is not a String (does not match the 1st argument)",
        );
    }

    #[test]
    fn builtin_plus_single_argument_any_type_allowed() {
        check_result(
            "(+ 'def)",
            ASTType::Declaration(Declaration {
                name: "def".into(),
                filename: "<in>".into(),
                line_number: 1,
                column_number: 4,
            }),
        );
        // Can't + a symbol since it'll be looked up before + runs
        check_result(
            "(+ (lambda (+ 1)))",
            ASTType::Function(Function {
                name: Symbol {
                    symbol: "<lambda>".into(),
                    filename: "<in>".into(),
                    line_number: 1,
                    column_number: 5,
                },
                call: Call {
                    fn_name: Symbol {
                        symbol: "+".into(),
                        filename: "<in>".into(),
                        line_number: 1,
                        column_number: 13,
                    },
                    arguments: vec![CallOrType::Type(ASTType::Integer(1, "<in>".into(), 1, 15))],
                },
                argument_names: vec![],
                captured_scope: Rc::new(RefCell::new(HashMap::new())),
            }),
        );
        check_result("(+ (none))", ASTType::None("runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_let_basic() {
        // Simple declaration is visible in later call
        check_result("(let 'a 2 (+ a))", ASTType::Integer(2, "<in>".into(), 1, 9));

        // Local scope is inherited from previous call
        check_result(
            "(let 'a 2 (+ (+ a) 4))",
            ASTType::Integer(6, "runtime".into(), 0, 0),
        );

        // Symbols are resolved before let is applied
        check_result(
            "
            (let 'a 2
                (let 'b a
                    (+ b)
                )
            )",
            ASTType::Integer(2, "<in>".into(), 2, 21),
        );

        // Redefintions shadow earlier values and can change types
        check_result(
            "
            (let 'a 2
                (list
                    (let 'a \"abc\"
                        (+ a)
                    )
                    (+ a)
                )
            )",
            ASTType::List(
                vec![
                    ASTType::String("abc".into(), "<in>".into(), 4, 29),
                    ASTType::Integer(2, "<in>".into(), 2, 21),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Values that are calls are resolved before putting into scope
        check_result(
            "
            (let
                'zzz (+ \"cat\" \"dog\")
                (+ zzz)
            )",
            ASTType::String("catdog".into(), "runtime".into(), 0, 0),
        );

        // Those calls use the scope before any variables are added
        check_result(
            "
            (let 'a 1 'b 2
                # If we update \"a\" before the second call then
                # we get b=4 not b=2
                (let 'a (+ a b) 'b (+ a 1)
                    (+ b)
                )
            )",
            ASTType::Integer(2, "runtime".into(), 0, 0),
        );

        // Calls used as values are executed once and only once
        // I had an off by one here where the last value call would
        // be left in the arguments after breadth processing.
        check_result(
            "
            (let 'c 1
                (let 'c 2
                     # This value call must be last
                     'v (cond
                              # First time through it sees c =1
                              (eq c 1) 99
                              # If we're off by one it'll see c=2 and error
                              true     (+ error_here)
                        )
                    (+ v)
                )
            )",
            ASTType::Integer(99, "<in>".into(), 7, 40),
        );
    }

    #[test]
    fn builtin_let_errors() {
        check_error(
            "(  let 'a 1 'b 2)",
            "<in>:1:4 Wrong number of arguments to let. Expected \'<name> <value> ... <body>",
        );
        check_error("(let 'a)", "<in>:1:2 let requires at least 3 arguments");
        check_error(
            "(let 22 \"foo\" (+ 99))",
            "<in>:1:6 Expected Declaration as first of let name-value pair",
        );

        // You can't reference a symbol until the let has finished
        // Error is symbol not found, unlike letrec which adds names up front
        check_error("(let 'a 1 'b a (print a))", "<in>:1:14 Symbol a not found");
    }

    #[test]
    fn builtin_letrec_basic() {
        // Since we're using refcell and all that, check we don't leak into outer scopes
        check_result(
            "
            (letrec 'a 1
                (list
                    (letrec 'a 2
                        (+ a)
                    )
                    (+ a)
                )
            )",
            ASTType::List(
                vec![
                    ASTType::Integer(2, "<in>".into(), 4, 32),
                    ASTType::Integer(1, "<in>".into(), 2, 24),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Let rec adds all names first then values as they are evaluated
        check_result(
            "(letrec 'a 1 'b a (+ b))",
            ASTType::Integer(1, "<in>".into(), 1, 12),
        );

        // This scope extends into calls to generate values
        // and the values are in the body as normal
        check_result(
            "(letrec 'a 2 'b (+ 9 a) (+ b a))",
            ASTType::Integer(13, "runtime".into(), 0, 0),
        );

        // lambdas capture the final scope even if they weren't the last
        // thing to be declared
        check_result(
            "
            (letrec 'x (+ 2 5)
                    'fn (lambda (+ x y))
                    'y (+ 1 2)
                    (fn)
            )",
            ASTType::Integer(10, "runtime".into(), 0, 0),
        );

        // Just like plain let, the lambda capture happens before the body
        // runs. So new definitions do not update the value.
        check_result(
            "
            (letrec 'fn (lambda 'x (+ x y)) 'y 99
                (let 'y 0
                    (fn 1)
                )
            )",
            ASTType::Integer(100, "runtime".into(), 0, 0),
        );

        // The main point of letrec is to allow recursive lambdas
        check_result(
            "
            (letrec
                'fn (lambda 'x
                        (if (< x 4)
                            (extend (list x)
                                    (fn (+ x 1))
                            )
                            (list x)
                        )
                    )
                'start 0
                (fn start)
            )",
            ASTType::List(
                vec![
                    ASTType::Integer(0, "<in>".into(), 11, 24),
                    ASTType::Integer(1, "runtime".into(), 0, 0),
                    ASTType::Integer(2, "runtime".into(), 0, 0),
                    ASTType::Integer(3, "runtime".into(), 0, 0),
                    ASTType::Integer(4, "runtime".into(), 0, 0),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // This includes mutual recursion
        check_result(
            "
            (letrec
                'f1 (lambda 'x
                        (if (< x 4)
                          (extend
                            (list \"f1\") (f2 (+ x 1))
                          )
                          (list \"f1 finished!\")
                        )
                    )
                'f2 (lambda 'x
                        (if (< x 2)
                          (extend
                            (list \"f2\") (f1 (+ x 1))
                          )
                          (list \"f2 finished!\")
                        )
                    )
                (f1 0)
            )",
            ASTType::List(
                vec![
                    ASTType::String("f1".into(), "<in>".into(), 6, 35),
                    ASTType::String("f2".into(), "<in>".into(), 14, 35),
                    ASTType::String("f1".into(), "<in>".into(), 6, 35),
                    ASTType::String("f2 finished!".into(), "<in>".into(), 16, 33),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Values that are calls are executed only once
        // Had an issue where the last call would be run twice
        // due to an off by one.
        check_result(
            "
            (defun 'foo (+ true))
            (letrec 'b
              (body
                (if (foo)
                  # First time through we redefine foo and return
                  # a normal value.
                  (body
                    (defun 'foo (+ false))
                    (+ 99)
                  )
                  # If we call it a second time we get an error
                  (+ unknown_symbol)
                )
              )
              (+ b)
            )",
            ASTType::Integer(99, "<in>".into(), 10, 24),
        );
    }

    #[test]
    fn builtin_letrec_errors() {
        // b references a before it has a value
        check_error(
            "(letrec 'b a 'a 1 (+ a b))",
            "<in>:1:12 Declared but undefined symbol a in letrec pair",
        );
        check_error(
            "(  letrec 'a 1 'b 2)",
            "<in>:1:4 Wrong number of arguments to letrec. Expected \'<name> <value> ... <body>",
        );
        check_error(
            "(letrec 'a)",
            "<in>:1:2 letrec requires at least 3 arguments",
        );
        check_error(
            "(letrec 22 \"foo\" (+ 99))",
            "<in>:1:9 Expected Declaration as first of letrec name-value pair",
        );
    }

    #[test]
    fn errors_function_declared_but_not_defined() {
        check_error(
            "
            (letrec
              'a (fn 2)
              'fn (lambda 'x
                    (+ x 99)
                  )
              (fn 1)
            )",
            "<in>:3:19 Function name fn is declared but not defined",
        );
    }

    #[test]
    fn errors_function_name_does_not_resolve_to_a_function() {
        check_error(
            "(let 'a 1 (a 1 2 3))",
            "<in>:1:12 Found \"a\" in local scope but it is not a function",
        );
    }

    #[test]
    fn builtin_lambda_basic() {
        // Zero or more arguments
        check_result(
            "
            (let
                'fn (lambda (+ 1234))
                (fn)
            )",
            ASTType::Integer(1234, "<in>".into(), 3, 32),
        );

        // lambdas capture the scope they are defined in
        // this is a copy so futher declarations don't change values
        check_result(
            "
            (let 'a 4
                (let
                    # a is captured here
                    'f (lambda 'b (+ a b))
                    # This a is a new a, so the lambda still sees 4
                    (let 'a 9
                        (f 2)
                    )
                )
            )",
            ASTType::Integer(6, "runtime".into(), 0, 0),
        );

        // Here the lambda should capture a and b but not c
        let mut expected_captured_scope = HashMap::new();
        expected_captured_scope.insert(
            "a".to_string(),
            Some(ASTType::Integer(1, "<in>".into(), 2, 21)),
        );
        expected_captured_scope.insert(
            "b".to_string(),
            Some(ASTType::Integer(2, "<in>".into(), 3, 25)),
        );
        let expected_captured_scope_rc = Rc::new(RefCell::new(expected_captured_scope));

        check_result(
            "
            (let 'a 1
                (let 'b 2
                    (let 'c 3
                         'fn (lambda (+ a b))
                        (+ fn)
                    )
                )
            )
            ",
            ASTType::Function(Function {
                name: Symbol {
                    symbol: "<lambda>".into(),
                    filename: "<in>".into(),
                    line_number: 5,
                    column_number: 31,
                },
                call: Call {
                    fn_name: Symbol {
                        symbol: "+".into(),
                        filename: "<in>".into(),
                        line_number: 5,
                        column_number: 39,
                    },
                    arguments: vec![
                        CallOrType::Type(ASTType::Symbol(Symbol {
                            symbol: "a".into(),
                            filename: "<in>".into(),
                            line_number: 5,
                            column_number: 41,
                        })),
                        CallOrType::Type(ASTType::Symbol(Symbol {
                            symbol: "b".into(),
                            filename: "<in>".into(),
                            line_number: 5,
                            column_number: 43,
                        })),
                    ],
                },
                argument_names: Vec::new(),
                captured_scope: expected_captured_scope_rc,
            }),
        );

        // Argument names shadow captured scope
        check_result(
            "
            (let 'a 4 'b 5
                (let
                    # a and b captured here
                    'f (lambda 'b (+ a b))
                    (list
                        # b shadowed so a=4, b=3
                        (f 3)
                        # This uses a=4, b=5
                        (+ a b)
                    )
                )
            )",
            ASTType::List(
                vec![
                    ASTType::Integer(7, "runtime".into(), 0, 0),
                    ASTType::Integer(9, "runtime".into(), 0, 0),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Captured scopes live as long as the lambda, not the life of the original scope
        check_result(
            "
        (let 'outer_fn
            (letrec 'a 1
                 'fn (lambda (+ a))
                 (+ fn)
            )
            (outer_fn)
        )",
            ASTType::Integer(1, "<in>".into(), 3, 24),
        );
    }

    #[test]
    fn builtin_lambda_errors() {
        // Error because lambda references a symbol that wasn't in scope yet
        check_error(
            "
            # a is in the let's scope
            (let 'a \"foo\"
                 # But it is not available when the lambda is defined
                 'fn (lambda 'b (+ b a))
                 (body
                     # Now a is defined so this works
                     (+ a)
                     # But this does not since it's captured scope
                     # didn't include a
                     (fn 2)
                 )
            )",
            "<in>:5:38 Symbol a not found",
        );

        check_error(
            "(lambda)",
            "<in>:1:2 lambda requires at least one argument (the function body)",
        );
        check_error(
            "(lambda 33 22)",
            "<in>:1:2 lambda's last argument must be the body of the function",
        );
        check_error(
            "(lambda 'a (+ 1 2) 'c (+a b))",
            "<in>:1:2 lambda arguments must be Declarations (not Call)",
        );
        check_error(
            "(lambda 'a \"foo\" 'c (+a b))",
            "<in>:1:12 lambda arguments must be Declarations",
        );

        check_error(
            "
            (let 'f
                (lambda 'a (+ a b))
                (f 1 \"a\" f)
            )",
            "<in>:4:18 Incorrect number of arguments to function \"f\" \
             (lambda defined at <in>:3:18). Expected 1 ('a) got 3 (1 \"a\" (<lambda> 'a))",
        );

        // Specific test for zero arguments
        check_error(
            "
            (let 'foo (lambda 'a 'b (+ a b))
                    (foo))",
            "<in>:3:22 Incorrect number of arguments to function \"foo\" \
             (lambda defined at <in>:2:24). Expected 2 ('a 'b) got 0 ()",
        );
    }

    #[test]
    fn builtin_none_basic() {
        // Generates an instance of None
        check_result("(none)", ASTType::None("runtime".into(), 0, 0));
        // Does so regardless of arguments
        check_result(
            "(none 99 \"foo\" 2 1234)",
            ASTType::None("runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_list_basic() {
        // Can be empty
        check_result("(list)", ASTType::List(Vec::new(), "runtime".into(), 0, 0));
        // Can hold different types
        check_result(
            "(list 1 \"foo\" (+ 9 1))",
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 1, 7),
                    ASTType::String("foo".into(), "<in>".into(), 1, 9),
                    ASTType::Integer(10, "runtime".into(), 0, 0),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
        // Including other lists
        check_result(
            "(list (list (list 1)))",
            ASTType::List(
                vec![ASTType::List(
                    vec![ASTType::List(
                        vec![ASTType::Integer(1, "<in>".into(), 1, 19)],
                        "runtime".into(),
                        0,
                        0,
                    )],
                    "runtime".into(),
                    0,
                    0,
                )],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn builtin_if_errors() {
        check_error("(if 1)",
            "<in>:1:2 Incorrect number of arguments to if. Expected <condition> <true value> <false value (optional)>");
        check_error("(if 1 2 3 4)",
            "<in>:1:2 Incorrect number of arguments to if. Expected <condition> <true value> <false value (optional)>");
        check_error("(if 'foo 1)", "<in>:1:5 Can't convert Declaration to bool");
    }

    #[test]
    fn builtin_if_basics() {
        // Minimum one condition and a true value
        check_result("(if 1 2)", ASTType::Integer(2, "<in>".into(), 1, 7));
        // Else is optional
        check_result(
            "(if \"\" 99 66)",
            ASTType::Integer(66, "<in>".into(), 1, 11),
        );
        // Any argument can be another call
        check_result(
            "(if (+ 0 1) (+ 1 2) (+ 4 5))",
            ASTType::Integer(3, "runtime".into(), 0, 0),
        );
        // values can be of different types
        check_result(
            "(if 1 \"foo\" (list))",
            ASTType::String("foo".into(), "<in>".into(), 1, 7),
        );
        // If we don't have an else and the condition is false, return none
        check_result("(if (list) (+ 99))", ASTType::None("runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_less_than_errors() {
        check_error("(< 1 2 3)", "<in>:1:2 Expected exactly 2 arguments to <");
        check_error("(<)", "<in>:1:2 Expected exactly 2 arguments to <");
        check_error(
            "(< 1 \"foo\")",
            "<in>:1:2 Cannot do ordered comparison < on types Integer and String",
        );
    }

    #[test]
    fn builtin_less_than_basic() {
        // Only works with 2 integers
        check_result("(< 1 2)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_result("(< 9 3)", ASTType::Bool(false, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_less_than_or_equal_to_errors() {
        check_error("(<= 1 2 3)", "<in>:1:2 Expected exactly 2 arguments to <=");
        check_error("(<=)", "<in>:1:2 Expected exactly 2 arguments to <=");
        check_error(
            "(<= 1 \"foo\")",
            "<in>:1:2 Cannot do ordered comparison <= on types Integer and String",
        );
    }

    #[test]
    fn builtin_less_than_or_equal_to_basic() {
        // Only works with 2 integers
        check_result("(<= 1 2)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_result("(<= 2 2)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_result("(<= 3 2)", ASTType::Bool(false, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_equal_to_errors() {
        check_error(
            "(eq (lambda (list)) (lambda (list)))",
            "<in>:1:2 Cannot do equality comparison eq on types Function and Function",
        );
        check_error(
            "(eq (lambda (list)) 1)",
            "<in>:1:2 Cannot do equality comparison eq on types Function and Integer",
        );
    }

    #[test]
    fn builtin_equal_to_basic() {
        check_result("(eq 1 1)", ASTType::Bool(true, "runtime".into(), 0, 0));
        check_result("(eq 1 2)", ASTType::Bool(false, "runtime".into(), 0, 0));

        check_result(
            "(eq \"foo\" \"foo\")",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq \"foo\" \"bar\")",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );

        check_result(
            "(eq (< 1 2) (< 3 4))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq (< 1 2) (< 4 3))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );

        check_result(
            "(eq (none) (none))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        // Any other type compared to none is not equal
        check_result(
            "(eq 1 (none))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq (none) (list \"foo\"))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );

        check_result(
            "(eq (list 1 2 3) (list 1 2 3))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq (list) (list))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq (list 6 7 \"g\") (list 6 7 \"f\"))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        // Even though single items of different types can't be compared,
        // for a list it means not equal.
        check_result(
            "(eq (list \"a\") (list 1))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        // The comparison recurses into nested lists
        check_result(
            "(eq (list (list 1 2)) (list (list 1 2)))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(eq (list (list 1 (list 2))) (list (list 1 (list 3))))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        // Lists of different length are not equal
        check_result(
            "(eq (list 1) (list 1 2))",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_not_equal_to_basic() {
        check_result(
            "(neq 1 (none))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result("(neq 1 1)", ASTType::Bool(false, "runtime".into(), 0, 0));
        check_result(
            "(neq (list 1) (list 1 2))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_flatten() {
        // Always returns a list, even if empty
        check_result(
            "(flatten)",
            ASTType::List(Vec::new(), "runtime".into(), 0, 0),
        );
        // Single items are added into the list
        check_result(
            "(flatten 1 2)",
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 1, 10),
                    ASTType::Integer(2, "<in>".into(), 1, 12),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
        // Lists of lists return a flat list of their items
        check_result(
            "
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
            ASTType::List(
                vec![
                    ASTType::Integer(0, "<in>".into(), 3, 17),
                    ASTType::Integer(1, "<in>".into(), 5, 27),
                    ASTType::Integer(2, "<in>".into(), 8, 21),
                    ASTType::Integer(3, "<in>".into(), 10, 31),
                    ASTType::Integer(4, "<in>".into(), 11, 25),
                    ASTType::Integer(5, "<in>".into(), 14, 17),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn builtin_extend_errors() {
        check_error(
            "(extend (list))",
            "<in>:1:2 Expected at least 2 List arguments for extend",
        );
        check_error(
            "(extend (list) 1)",
            "<in>:1:2 All arguments to extend must be List, got [] 1",
        );
    }

    #[test]
    fn builtin_extend_basic() {
        // Empty list allowed for either
        check_result(
            "(extend (list) (list 2))",
            ASTType::List(
                vec![ASTType::Integer(2, "<in>".into(), 1, 22)],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Handles one list being empty
        check_result(
            "(extend (list 1) (list))",
            ASTType::List(
                vec![ASTType::Integer(1, "<in>".into(), 1, 15)],
                "runtime".into(),
                0,
                0,
            ),
        );

        check_result(
            "(extend (list 1) (list 2))",
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 1, 15),
                    ASTType::Integer(2, "<in>".into(), 1, 24),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Nested lists are not unpacked in the rhs
        check_result(
            "(extend (list 1) (list (list 2)))",
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 1, 15),
                    ASTType::List(
                        vec![ASTType::Integer(2, "<in>".into(), 1, 30)],
                        "runtime".into(),
                        0,
                        0,
                    ),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // Can handle > 2 lists
        check_result(
            "(extend (list 1) (list 2) (list 3))",
            ASTType::List(
                vec![
                    ASTType::Integer(1, "<in>".into(), 1, 15),
                    ASTType::Integer(2, "<in>".into(), 1, 24),
                    ASTType::Integer(3, "<in>".into(), 1, 33),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn builtin_cond_errors() {
        check_error(
            "(cond)",
            "<in>:1:2 Expected matched condition-value/call pairs for cond call",
        );
        check_error(
            "(cond 1)",
            "<in>:1:2 Expected matched condition-value/call pairs for cond call",
        );
        check_error(
            "(cond 1 2 3)",
            "<in>:1:2 Expected matched condition-value/call pairs for cond call",
        );
        check_error(
            "
            (cond
                0      (+ 1)
                false  (+ 2)
                (list) (+ 3)
                \"\"   (+ 4)
                (none) (+ 5)
            )",
            "<in>:2:14 No condition returned true for cond call",
        );
    }

    #[test]
    fn builtin_cond_basic() {
        // First true condition is executed
        check_result(
            "
            (cond true  (+ 1)
                  false 2)",
            ASTType::Integer(1, "<in>".into(), 2, 28),
        );

        // Conditions can be calls, first true wins
        check_result(
            "
            (cond (+ false)    (+ 1)
                  (+ 1)        (+ 2)
                  (+ \"foo\")  (+ 3)
            )",
            ASTType::Integer(2, "<in>".into(), 3, 35),
        );

        // Conditions can be symbols
        check_result(
            "
            (let 'a false 'b true 'c 99
                (cond a c
                      b (+ c 1)
                )
            )",
            ASTType::Integer(100, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_mod_basic() {
        check_result("(% 9 4)", ASTType::Integer(1, "runtime".into(), 0, 0));
        check_result("(% 6 2)", ASTType::Integer(0, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_mod_errors() {
        check_error("(%)", "<in>:1:2 % requires exactly two Integer arguments");
        check_error(
            "(% \"abc\" \"foo\")",
            "<in>:1:2 Both arguments to % must be Integer (got String, String)",
        );
        check_error(
            "(% 1 \"2\")",
            "<in>:1:2 Both arguments to % must be Integer (got Integer, String)",
        );
    }

    #[test]
    fn builtin_div_basic() {
        check_result("(/ 9 4)", ASTType::Integer(2, "runtime".into(), 0, 0));
        check_result("(/ 6 2)", ASTType::Integer(3, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_div_errors() {
        check_error("(/)", "<in>:1:2 / requires exactly two Integer arguments");
        check_error(
            "(/ \"abc\" \"foo\")",
            "<in>:1:2 Both arguments to / must be Integer (got String, String)",
        );
        check_error(
            "(/ 1 \"2\")",
            "<in>:1:2 Both arguments to / must be Integer (got Integer, String)",
        );
    }

    #[test]
    fn builtin_mul_basic() {
        check_result("(* 9 4)", ASTType::Integer(36, "runtime".into(), 0, 0));
        check_result("(* 6 -1)", ASTType::Integer(-6, "runtime".into(), 0, 0));
    }

    #[test]
    fn builtin_mul_errors() {
        check_error("(*)", "<in>:1:2 * requires exactly two Integer arguments");
        check_error(
            "(* \"abc\" \"foo\")",
            "<in>:1:2 Both arguments to * must be Integer (got String, String)",
        );
        check_error(
            "(* 1 \"2\")",
            "<in>:1:2 Both arguments to * must be Integer (got Integer, String)",
        );
    }

    #[test]
    fn builtin_defun_errors() {
        check_error("(defun)",
            "<in>:1:2 Expected at least two arguments to defun. function name, <arguments>, function body.");
        check_error(
            "(defun 1 (+ 2))",
            "<in>:1:8 defun function name must be a Declaration",
        );
        check_error(
            "(defun (+ \"foo\") 'a (+ 1))",
            "<in>:1:2 defun function name must be a Declaration (not a call)",
        );
        check_error(
            "(defun 'f 'a 1 (+ 1))",
            "<in>:1:14 defun function arguments must be Declarations",
        );
        check_error(
            "(defun 'f 'a (+ 123) (+ 1))",
            "<in>:1:2 defun function arguments must be Declarations (not Call)",
        );
        check_error(
            "(defun 'f 22)",
            "<in>:1:2 defun's last argument must be the body of the function",
        );
        check_error(
            "
            (defun 'f 'x 'y (+ x y))
            (f 4 5)
            (f 1 2 3)",
            "<in>:4:14 Incorrect number of arguments to function \"f\" \
             (function defined at <in>:2:20). Expected 2 (\'x \'y) got 3 (1 2 3)",
        );
    }

    #[test]
    fn builtin_defun_basic() {
        // Returns none
        check_result("(defun 'f 'x (+ x))", ASTType::None("runtime".into(), 0, 0));

        // Function is added to global function scope with the name given
        // (so is visible across blocks)
        check_result(
            "
            (defun 'f 'x (+ x))
            (f 2)",
            ASTType::Integer(2, "<in>".into(), 3, 16),
        );

        // Defined functions shadow builtins
        check_result(
            "
            (defun '+ 'x 'y (list x y))
            (+ 2 3)",
            ASTType::List(
                vec![
                    ASTType::Integer(2, "<in>".into(), 3, 16),
                    ASTType::Integer(3, "<in>".into(), 3, 18),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );

        // lambdas in local scope shadow defined functions
        check_result(
            "
            (defun '+ 'x (list 1))
            (let '+ (lambda 'x 'y (list 2))
                (+ 3 4)
            )",
            ASTType::List(
                vec![ASTType::Integer(2, "<in>".into(), 3, 41)],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn builtin_import_errors() {
        check_error(
            "(import)",
            "<in>:1:2 Expected exactly 1 String argument to import, the filepath",
        );
        check_error(
            "(import \"foo\" \"bar\")",
            "<in>:1:2 Expected exactly 1 String argument to import, the filepath",
        );
        check_error(
            "(import 99)",
            "<in>:1:2 Argument to import must be a String",
        );
        check_error(
            "(import (list 99))",
            "<in>:1:2 Argument to import must be a String",
        );
    }

    #[test]
    fn builtin_import_resolves_symbols() {
        check_error(
            "(let 'p \"_not_a_file_\" (import p))",
            "Couldn't open source file _not_a_file_, No such file or directory (os error 2)",
        );
    }

    #[test]
    fn builtin_head_errors() {
        check_error("(head)", "<in>:1:2 Expected exactly 1 argument to head");
        check_error(
            "(head (list) (list))",
            "<in>:1:2 Expected exactly 1 argument to head",
        );
        check_error("(head 1)", "<in>:1:7 Cannot head on type Integer");
        check_error("(head (list))", "runtime:0:0 Cannot head on an empty List");
        check_error("(head \"\")", "<in>:1:7 Cannot head on an empty String");
    }

    #[test]
    fn builtin_head_basic() {
        check_result(
            "(head (list 1 2 3))",
            ASTType::Integer(1, "<in>".into(), 1, 13),
        );
        check_result(
            "(head \"foo\")",
            ASTType::String("f".into(), "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_tail_errors() {
        check_error("(tail)", "<in>:1:2 Expected exactly 1 argument to tail");
        check_error(
            "(tail (list) (list))",
            "<in>:1:2 Expected exactly 1 argument to tail",
        );
        check_error("(tail 1)", "<in>:1:7 Cannot tail on type Integer");
        check_error("(tail (list))", "runtime:0:0 Cannot tail on an empty List");
        check_error("(tail \"\")", "<in>:1:7 Cannot tail on an empty String");
    }

    #[test]
    fn builtin_tail_basic() {
        check_result(
            "(tail (list 1 2 3))",
            ASTType::List(
                vec![
                    ASTType::Integer(2, "<in>".into(), 1, 15),
                    ASTType::Integer(3, "<in>".into(), 1, 17),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
        check_result(
            "(tail \"foo\")",
            ASTType::String("oo".into(), "runtime".into(), 0, 0),
        );

        // Tail when length is 1 should give an empty result
        check_result(
            "(tail (list 1))",
            ASTType::List(vec![], "runtime".into(), 0, 0),
        );
        check_result(
            "(tail \"f\")",
            ASTType::String("".into(), "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_len_errors() {
        check_error("(len)", "<in>:1:2 Expected exactly 1 argument to len");
        check_error("(len 1 2 3)", "<in>:1:2 Expected exactly 1 argument to len");
        check_error("(len 1)", "<in>:1:6 Argument to len must be List or String");
    }

    #[test]
    fn builtin_len_basic() {
        check_result("(len (list))", ASTType::Integer(0, "runtime".into(), 0, 0));
        check_result("(len \"\")", ASTType::Integer(0, "runtime".into(), 0, 0));
        check_result(
            "(len (list 1 2 3 ))",
            ASTType::Integer(3, "runtime".into(), 0, 0),
        );
        check_result(
            "(len \"food\")",
            ASTType::Integer(4, "runtime".into(), 0, 0),
        );
        check_result(
            "(len (list (list 1) (list 2)))",
            ASTType::Integer(2, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_and_errors() {
        check_error("(and)", "<in>:1:2 Expected at least 2 arguments to and");
        check_error(
            "(and true)",
            "<in>:1:2 Expected at least 2 arguments to and",
        );
    }

    #[test]
    fn builtin_and_basic() {
        check_result(
            "(and true true)",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(and false true)",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        check_result(
            "(and false false)",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        check_result(
            "(and true false)",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );

        check_result(
            "(and 1 \"foo\" (list 3))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(and (list 0) 0 \"?\")",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_or_errors() {
        check_error("(or)", "<in>:1:2 Expected at least 2 arguments to or");
        check_error("(or true)", "<in>:1:2 Expected at least 2 arguments to or");
    }

    #[test]
    fn builtin_or_basic() {
        check_result(
            "(or true true)",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(or false true)",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(or false false)",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
        check_result(
            "(or true false)",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );

        check_result(
            "(or 1 \"foo\" (list 3))",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(or (list 0) 0 \"?\")",
            ASTType::Bool(true, "runtime".into(), 0, 0),
        );
        check_result(
            "(or (list) 0 \"\")",
            ASTType::Bool(false, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_minus_errors() {
        check_error("(-)", "<in>:1:2 - requires at least two arguments");
        check_error("(- true)", "<in>:1:2 - requires at least two arguments");
        check_error(
            "(- true false)",
            "<in>:1:4 Cannot - arguments of types Bool, Bool",
        );
        check_error(
            "(- 1 2 true false)",
            "<in>:1:8 - argument is not an Integer",
        );
    }

    #[test]
    fn builtin_minus_basic() {
        check_result("(- 1 3)", ASTType::Integer(-2, "runtime".into(), 0, 0));
        check_result("(- 7 5)", ASTType::Integer(2, "runtime".into(), 0, 0));
        check_result("(- 7 6 5)", ASTType::Integer(-4, "runtime".into(), 0, 0));
    }

    #[test]
    fn globally_defined_functions_are_part_of_symbol_lookup() {
        check_result(
            "
            (defun 'foo (+ 1))
            (defun 'callfn 'fn (fn))
            (callfn foo)",
            ASTType::Integer(1, "<in>".into(), 2, 28),
        );

        // They have a lower priority than local scope variables
        check_result(
            "
            (defun 'foo (+ 1))
            (list
                (let 'foo (lambda (+ 2))
                    # Returns 2
                    (foo)
                )
                # Returns 1
                (foo)
            )",
            ASTType::List(
                vec![
                    ASTType::Integer(2, "<in>".into(), 4, 38),
                    ASTType::Integer(1, "<in>".into(), 2, 28),
                ],
                "runtime".into(),
                0,
                0,
            ),
        );
    }

    #[test]
    fn builtins_included_in_sybmol_lookup() {
        // No arguments
        check_result(
            "
            (defun 'callfn 'fn (fn))
            (callfn list)",
            ASTType::List(vec![], "runtime".into(), 0, 0),
        );

        //With arguments
        check_result(
            "
            (defun 'callfn 'fn 'x 'y (fn x y))
            (callfn + 9 1)",
            ASTType::Integer(10, "runtime".into(), 0, 0),
        );

        // The builtin chosen is frozen at lookup time so shadowing doesn't change it
        // First, with a let...
        check_result(
            "
            (defun 'callfn 'fn 'x 'y (fn x y))
            # Symbol tied to the builtin plus here
            (let 'builtin_plus +
                # Then we shadow + in scopes
                (let '+ (lambda 'x 'y (+ x y 10))
                    # But this is unaffected and returns 10, not 20
                    (callfn builtin_plus 9 1)
                )
            )",
            ASTType::Integer(10, "runtime".into(), 0, 0),
        );

        // Then with a defun...
        check_result(
            "
            (defun 'callfn 'fn 'x 'y (fn x y))
            # Symbol tied to the builtin plus here
            (let 'builtin_plus +
                (body
                    # Shadowing + in the global function scope here
                    (defun '+ 'x 'y (- x y))
                    # This shouldn't change and return 10 not 8
                    (callfn builtin_plus 9 1)
                )
            )",
            ASTType::Integer(10, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_eval_errors() {
        check_error(
            "(eval)",
            "<in>:1:2 Expected exactly one String argument to eval",
        );
        check_error(
            "(eval \"a\" \"b\")",
            "<in>:1:2 Expected exactly one String argument to eval",
        );
        check_error(
            "(eval (list))",
            "<in>:1:2 Expected exactly one String argument to eval",
        );
    }

    #[test]
    fn builtin_eval_basic() {
        // Direct string
        check_result(
            "(eval \"(+ 2 2)\")",
            ASTType::Integer(4, "runtime".into(), 0, 0),
        );

        // Can be result of a call
        check_result(
            "(eval (+ \"(+ \" \"3 \" \"5\" \")\"))",
            ASTType::Integer(8, "runtime".into(), 0, 0),
        );

        // Resolves symbols on its own
        check_result(
            "(let 'p \"(+ 1 1)\" (eval p))",
            ASTType::Integer(2, "runtime".into(), 0, 0),
        );

        // Can define global functions for later
        check_result(
            "
            (eval \"(defun 'foo 'a (+ a a))\")
            (foo 50)",
            ASTType::Integer(100, "runtime".into(), 0, 0),
        );
    }

    #[test]
    fn builtin_randint_errors() {
        // No args
        check_error(
            "(randint)",
            "<in>:1:2 Expected either 1 (max) or 2 (min, max) Integer arguments to randint",
        );
        // Too many args
        check_error(
            "(randint 1 2 3)",
            "<in>:1:2 Expected either 1 (max) or 2 (min, max) Integer arguments to randint",
        );
        // Single arg is not int
        check_error(
            "(randint (list))",
            "<in>:1:2 Expected either 1 (max) or 2 (min, max) Integer arguments to randint",
        );
        // Two args, one not int
        check_error(
            "(randint (list) 1)",
            "<in>:1:2 Expected either 1 (max) or 2 (min, max) Integer arguments to randint",
        );
        // Reverse of above
        check_error(
            "(randint 1 (list))",
            "<in>:1:2 Expected either 1 (max) or 2 (min, max) Integer arguments to randint",
        );
        // min >= max
        check_error(
            "(randint 9 6)",
            "<in>:1:2 randint min (9) must be < max (6)",
        );
    }

    fn test_randint(prog: &str, min: i64, max: i64) {
        // This is more of a smoke test given that random is, well, random
        for _n in 1..100 {
            let result = run_program(prog).unwrap();
            match result {
                ASTType::Integer(i, ..) => {
                    assert!(i >= min);
                    assert!(i < max);
                }
                _ => assert!(false, "Expected Integer from randint!"),
            };
        }
    }

    #[test]
    fn builtin_randint_basic() {
        test_randint("(randint 10)", 0, 10);
        test_randint("(randint 10 20)", 10, 20);
        test_randint("(randint -20 20)", -20, 20);
    }
}
