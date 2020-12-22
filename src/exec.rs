use crate::ast;

// Next step is to add local variables (not functions yet)
// implement (let 'a 1 (print a)) etc.
// By adding "breadth" functions to each builtin
// that can run before we depth evaluate
// and will modify the argument list for the call
// (well, return a new copy more likely)

fn builtin_plus(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // Assuming two arguments for now
    if arguments.len() != 2 {
        panic!("Function + requires exactly two arguments!");
    }
    match (&arguments[0], &arguments[1]) {
        (ast::ASTType::Integer(i1, ..), ast::ASTType::Integer(i2, ..)) =>
            ast::ASTType::Integer(i1+i2,
                "runtime?".into(), 0, 0),
        (ast::ASTType::String(s1, ..), ast::ASTType::String(s2, ..)) =>
            ast::ASTType::String(s1.to_owned()+s2,
                "runtime?".into(), 0, 0),
        (_, _) => panic!("Cannot + these argument types! {:?}", arguments)
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

fn builtin_print(arguments: Vec<ast::ASTType>) -> ast::ASTType {
    // TODO: assuming newline
    println!("{}", arguments.iter().map(|a| format!("{}", a)).collect::<Vec<String>>().join(", "));
    // TODO: void type? (None might be a better name)
    ast::ASTType::Integer(1, "runtime".into(), 0, 0)
}

fn exec_inner(call: ast::Call) -> ast::ASTType {
    let executor: fn(Vec<ast::ASTType>) -> ast::ASTType = match call.fn_name.symbol.as_str() {
        "__root" => builtin_dunder_root,
             "+" => builtin_plus,
         "print" => builtin_print,
        _ => panic!("Unknown function {}!", call.fn_name.symbol)
    };

    // Now resolve all Calls in its arguments
    // TODO: we're assuming depth first is fine here (not fine for let, etc)
    let mut resolved_arguments = Vec::new();
    for call_or_type in call.arguments {
        resolved_arguments.push(match call_or_type {
            ast::CallOrType::Call(c) => exec_inner(c),
            ast::CallOrType::Type(t) => t
        });
    }

    executor(resolved_arguments)
}

// TODO: defun could return a function here
pub fn exec(call: ast::Call) -> ast::ASTType {
    // You would declare global and inital local scope here
    exec_inner(call)
}
