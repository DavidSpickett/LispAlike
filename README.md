# RLispALike

RLispALike is an interpreter for a Lisp dialect (LispALike)
that mostly cribs from Scheme and Common Lisp.

```
(letrec
  'limit 100
  'fib (lambda 'x 'y
     (let 'n (+ x y)
       (if (< n limit)
          (extend
            (list n)
            (fib y n)
          )
          (list n)
       )
     )
   )
 (fib 0 1)
)
```

You can find more examples [here](examples/). There is also a [standard library](lib/lib.lal) written
in LispALike, with useful functions not provided by the interpreter.

RLispALike is a Rust rewrite and expansion of my Python project [LispALike](https://github.com/DavidSpickett/LispALike).

## Usage

To run a program:
```
$ cargo run examples/fibonacci.lal
```

To test the interpreter:
```
$ cargo test
```

To test an example/all examples:
```
$ cargo run --bin tester examples/fibonacci.lal
$ cargo run --bin tester examples/*
```

The tester looks for source lines beginning with "## " and checks the rest
of the line against the output of the program.

## Language Details

### Comments

Comments start with a # and the rest of the line is ignored.
(unless the # is within a string)
```
# This is a comment
# This is the second line of a block comment
(+ "# This is not a comment")
```

### Scoping

There are 3 scopes at any one time. They are,
in order of lowest priority to highest:
* builtin functions (those defined by the interpreter)
* global user defined functions (defined with `defun`)
* the current local scope (which contains functions or data)

Meaning that a `defun` function can shadow a builtin,
which can then be shadowed by a `let` lambda and so on.

The first two are always visible, but can be shadowed.
The last one changes as you move through the code.

The local scope behaves as follows. Each time you `let/letrec`
we take a copy of the current local scope and add the new names
to that. The outer scope is not modified.
```
(let 'a 1 'b 2
  # a=1 b=2
  (let 'c 2 'a 2
    # a=2 b=2 c=2
  )
  # a=1 b=2
)
```

Note that the `a` in the second let is a completely new variable.
So you can change the type if you wish.

When you call a function the local scope depends on how it was
defined. For `defun` you get a fresh scope. (but remember that global
functions and builtins are still visible)
```
(defun 'fn 'x 'y
  # scope contains x and y
  # I can still call the builtin + here as well
  (+ x y)
)
```

lambdas on the other hand, capture a copy of the scope they were declared in.
```
(let 'a 1
  # a=1
  (let
    # Captures a=1
    'fn (lambda 'x (+ x a))
    # Will see x=2 a=1
    (fn 2)
  )
)
```

Note that this captured scope is a copy and therefore doesn't modify the
original and can also live beyond the scope the lambda was defined in.
(useful if you write a function that returns another function)

This captured scope can also include other lambdas. If you use a `letrec`
you can even reference the name of the current lambda to do recursion.

### Types

The interpreter recognises some set types, some of which
you can use directly, some are only returned by functions
at runtime.

#### String

Anything between "".
```
(print "Hello
World!")
"Hello
World!"
```

#### Integer

Any decimal number.
```
(print (+ -1 1))
0
```

#### List

Returned by the list function. Can contain any combination of types.
```
(list 1 "foo" (list 2 3))
```

#### Bool

`true` or `false`.
```
(cond (eq foo 1) "foo"
      (true)     "bar")
```
#### None

Produced by the `(none)` function, returned by some functions.
Similair in use to Python's None type.

#### Declaration

Anything after a quote `'` character. Used for variable names
and function parameter names.
```
(let 'foo 1 (+ foo))
```

#### Symbol

Anything that isn't a Declaration or a string. This represents
a name that will be looked up at runtime.
```
(let 'foo # is a Delcaration
     1
  (+ foo # is a Symbol
  )
)
```

#### Function

This represents user defined functions, either by `lambda` or
`defun`. However only `lambda` returns a Function object,
`defun` simply adds it to the global scope.
```
(let 'f # f will have type Function
  (lambda 'x (+ x))
)
```

### Type comparison

The interpreter supports ordered (e.g. >) or unordered (e.g ==)
comparison between types. You will get errors telling you if a
comparison is not allowed.

Generally this is logical stuff but there's a few situations worth
noting:
* You can compare anything to none and get false. Useful for stuff like
  if find returns none then do etc.
* When comparing lists, different length and different types means
  they are not equal. (where if you tried to compare element by element
  you would get an error for mismatching types)

### Implicit bool conversion

Borrowing from Python, types have rules as to how they convert to bool
implicitly. So you can say:
```
(let 'a "food"
   (if a (print "Y")
         (print "N")
   )
)
"Y"
```

These follow the usual rules, empty list or string is false, integer 0
is false, etc. See the [AST](src/ast.rs) for the full lists.

### Program stucture

Programs are wrapped in an implicit `body` call and the result
of this call is what the interpreter prints when the program
finishes.

A `body` call returns the result of the last argument to it.
```
(body # Implciitly added by the interpreter
(+ 0)
(+ 1)
) # Added by the interpreter

Return value: 1
```

### Importing other files

You can import other files using `import` with the path.
This path is relative to the current working dir where you run
the program.

See [examples/import.lal](examples/import.lal) for a minimal
example.

You do not get the return value of the script imported.
So the main use case is to `defun` some functions for the global
scope, as the standard library does.
