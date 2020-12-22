use crate::ast;
use std::collections::HashMap;

// This is call or type so a symbol can be a function
// or a variable.
#[derive(Clone)]
struct Scope(HashMap<String, ast::CallOrType>);

// MAybe we want an ast type for resolved/made functions
// instead of switching from call or type all the time.
// Try forgetting scopes alltogether and just get that working.

fn builtin_plus(arguments: Vec<ast::CallOrType>) -> ast::ASTType {
    // Assuming two arguments for now
    if arguments.len() != 2 {
        panic!("Function + requires exactly two arguments!");
    }
    match (&arguments[0], &arguments[1]) {
        (ast::CallOrType::Type(t1), ast::CallOrType::Type(t2)) => match (t1, t2) {
            (ast::ASTType::Integer(i1, ..), ast::ASTType::Integer(i2, ..)) =>
                ast::ASTType::Integer(i1+i2, "runtime?".into(), 0, 0),
            (_, _) => panic!("Cannot + these argument types!")
        },
        (_, _) => panic!("Unresolved calls in + arguments!")
    }
}

fn builtin__root(arguments: Vec<ast::CallOrType>) -> ast::ASTType {
    // Result of a program is the result of the last block/call
    match arguments.last() {
        Some(arg) => match arg {
            // TODO: this doesn't check all the args
            ast::CallOrType::Call(_) => panic!("unresolved call in __root arguments!"),
            ast::CallOrType::Type(t) => t.clone()
        }
        None => panic!("__root call must have at least one argument to return!")
    }
}

fn exec_inner(call: ast::Call,
              global_scope: &mut Scope,
              local_scope: Scope)
    -> ast::ASTType {

    let function = match local_scope.0.get(&call.fn_name.symbol) {
        Some(f) => f,
        None => match global_scope.0.get(&call.fn_name.symbol) {
                    Some(f) => match f {
                        ast::CallOrType::Type(t) => panic!(
                            "Symbol \"{}\" does not resolve to a Call, it is {}",
                            call.fn_name.symbol, t),
                        ast::CallOrType::Call(_) => f
                    }
                    None =>
                        ast::panic_with_location(
                            &format!("No function found with name {}",
                                &call.fn_name.symbol),
                                &call.fn_name.filename,
                                call.fn_name.line_number,
                                call.fn_name.column_number)
                }
    };

    // Now resolve all Calls in its arguments
    // TODO: handle things that do breadth first evaluation
    let mut resolved_arguments = Vec::new();
    for call_or_type in call.arguments {
        resolved_arguments.push(match call_or_type {
            ast::CallOrType::Call(c) =>
                ast::CallOrType::Type(exec_inner(c, global_scope, local_scope.clone())),
            _ => call_or_type
        });
    }

    // Then run the actual function
    //executor(resolved_arguments, global_scope, local_scope.clone())

    // TODO: return result
    ast::ASTType::Integer(1, "sdfsdf".into(), 0, 0)
}

// TODO: defun could return a function here
pub fn exec(call: ast::Call) -> ast::ASTType {
    let mut global_scope = Scope(HashMap::new());

    exec_inner(call, &mut global_scope, Scope(HashMap::new()))
}
