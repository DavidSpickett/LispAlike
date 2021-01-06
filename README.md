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
