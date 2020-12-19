mod tokeniser;
mod ast;

fn main() {
    tokeniser::process("<in>", "
(defun 'fib 'x 'y
  (let 'n (+ x y)
    (body
      (print n)
      (if (< n 100)
        (fib y n)
      )
    )
  )
)

(print 0)
(print 1)
(print \"hello world!\")
(fib 0 1)").iter().for_each(|c| print!("{}\n", c));
    println!("");
}
