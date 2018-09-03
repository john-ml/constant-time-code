# Verification & synthesis of constant-time code in Rosette

Cryptographic algorithms whose timings are dependent upon
private information are vulnerable to a side channel attack where
an attacker uses correlational analyses of execution times in response
to different queries in order to extract information. Since manually
writing programs that are constant-time with respect to hidden information
is difficult and error-prone, it's important to have software that performs
automatic verification of constant-time code.

This repository contains an implementation,
using the [Rosette](https://github.com/emina/rosette) language,
of an interpreter for a simple imperative programming language and functions
capable of 1) verifying that programs written in this language are constant-time
with respect to private input variables and 2) filling holes of a program
sketch such that the resulting program is both functionally equivalent to a
"specification" program (which may not necessarily be constant-time) and
itself constant-time with respect to private input variables.

## A simple imperative language

The grammar of the language is given below.
An arithmetic expression `aexp` can be an integer literal, a variable (which can be annotated
as a hole to be completed or as private), an application of an arithmetic operator `+` `-` or `*`, or
a conditional expression.
A boolean expression `bexp` can be a literal `#t` or `#f` or a comparison of two arithmetic expressions.
A statement `stmt` can be a variable assignment, an assertion, or a while loop.
Finally, a program is a statement or sequence of statements.

```bnf
alit ::= -?[0-9]+
avar ::= [a-zA-Z0-9]+

aexp ::= <alit>
       | <avar>
       | (hole <avar>)
       | (private <avar>)
       | (+ <aexp> <aexp>)
       | (- <aexp> <aexp>)
       | (* <aexp> <aexp>)

bexp ::= #t
       | #f
       | (= <aexp> <aexp>)
       | (< <aexp> <aexp>)

stmt ::= (set! <avar> <aexp>)
       | (assert <bexp>)
       | (if <bexp> <prgm> <prgm>)
       | (while <bexp> <prgm>)

prgm ::= <stmt>
       | (program <stmt> ...)
``` 

For example, the following program computes the factorial of some private variable `n` in a public variable `result`:
```racket
(program
  (set! k (private n))
  (set! result 1)
  (while (< 0 k)
    (program
      (set! k (- k 1))
      (set! result (* result k)))))
```

## Conversion to Rosette code

In order to run programs written in this language, we use Racket macros to expand
them into executable Rosette code. Since the language is written using s-expressions
and most of the operator names (`+`, `*`, `=`, `set!`, etc.) are identical to their Rosette
counterparts, the expansion leaves most expressions unchanged, with just a few exceptions:
`(program expr ...)` is replaced by `(begin 0 expr ...)`, `while` loops are unrolled to a
fixed depth of 20, all variable names are declared at the top of the expanded program
using `define-symbolic`, and the entire expanded program is enclosed in a `let`-expression
to avoid polluting the surrounding scope with local variable declarations.

For example, the factorial example above yields the following Rosette code when expanded:
```racket
(let ()
  (begin 0
    ; declare variables
    (define-symbolic k integer?)
    (define-symbolic n integer?)
    (define-symbolic result integer?)

    ; main program
    (set! k n)
    (set! result 1)

    ; unrolled loop
    (begin 0
      (if (< 0 k) ; iteration 1
        (begin 0
          (begin 0 ; loop body
            (set! k (- k 1)
            (set! result (* result k))))
          (if (< 0 k) ; iteration 2
            (begin 0
              (begin 0 ; loop body
                (set! k (- k 1)
                (set! result (* result k))))
              ; 17 more iterations ...
                (if (< 0 k) ; iteration 20
                  (begin 0
                    (begin 0 ; loop body
                      (set! k (- k 1)
                      (set! result (* result k))))
                    (assert (not (< 0 k)))) ; fail for iterations > 20 (unroll depth was too low)
                  (begin 0)))
              ; 17 more else clauses ...
            (begin 0)))
        (begin 0))
      (begin 0))))
```

To track the execution time of a program, the expansion process also generates code to increment
a counter variable whenever a statement is evaluated.
The `bench` function, shown below, is used to compute the amount by which to increment the
counter variable for any arithmetic expression or `set!` statement.
For simplicity, we assume that each `+`, `-`, `*`, `=`, `<`, and `set!` operation takes the same
amount of time, incrementing the counter variable by 1.
```racket
(define (bench expr)
  (match expr
    ; assume +, <, *, and set! all take 1 counter tick
    [`(+ ,a ,b)    (+ 1 (bench a) (bench b))]
    [`(- ,a ,b)    (+ 1 (bench a) (bench b))]
    [`(< ,a ,b)    (+ 1 (bench a) (bench b))]
    [`(* ,a ,b)    (+ 1 (bench a) (bench b))]
    [`(= ,a ,b)    (+ 1 (bench a) (bench b))]
    [`(set! ,a ,b) (+ 1 (bench b))]
    [_             0]))
```

The function `emit-counter-code` takes a program written in our simple imperative language and
transforms it into evaluable Rosette code that additionally maintains a counter variable throughout its execution.
The result of this expansion and addition of a counter variable `k1` is shown below for the factorial program.
```racket
(let ()
  (begin 0
    ; declare variables
    (define-symbolic k integer?)
    (define-symbolic result integer?)
    (define-symbolic n integer?)

    ; initialize counter variable
    (define-symbolic k1 integer?)
    (set! k1 0)

    ; main program
    (begin 0
      ; initialize loop index `k` and accumulator variable `result`
      (begin
        (set! k1 (+ k1 1)) ; `set!` takes 1 tick
        (set! k n))
      (begin
        (set! k1 (+ k1 1))
        (set! result 1))

      ; main loop
      (if (begin (set! k1 (+ k1 1)) (< 0 k))
        (begin 0
          ; loop body
          (begin 0
            (begin
              (set! k1 (+ k1 2)) ; `-` and `set!` both take 1 tick, so `set! k (- k 1)` takes 2
              (set! k (- k 1)))
            (begin
              (set! k1 (+ k1 2))
              (set! result (* result k))))
          ; 18 more iterations ... 
            ; iteration 20
            (if (begin (set! k1 (+ k1 1)) (< 0 k))
              (begin 0
                ; loop body
                (begin 0
                  (begin
                    (set! k1 (+ k1 2))
                    (set! k (- k 1)))
                  (begin
                    (set! k1 (+ k1 2))
                    (set! result (* result k))))
                (assert (not (< 0 k)))) ; fail for > 20 iterations (unroll depth was too low)
              (begin 0)))
          ; 18 more else clauses ...
        (begin 0)))))
```

## Verification

Constant-time verification is implemented using a cross product construction from Almeida et. al.<sup>[1](#references)</sup>.  
Let `P` represent a fully macro-expanded program, complete with a counter variable to track execution time.
The cross-product construction reduces the problem of checking that the original program runs in constant-time with respect to
private variables to verification of a product program `Q`, which simulates the execution of two copies of `P`.
The structure of `Q` is as follows for the product construction implemented in this repository (where `P'` is a copy of the
original program `P` with all variables renamed to avoid conflicts, and `c`, `c'` are the counter variables of `P` and `P'`
respectively):
```
for each non-private variable v in P corresponding to v' in P', (assume (= v v'))
P
P'
(assert (= c c'))
```

The final assertion only fails if there exist differing initial values for the private variables of `P` that result in different
final values for the counter variables `c` and `c'`--in other words, if the execution time of `P` depends on the values of its
private variables. As an example, here's a simple program which computes the sum of two variables `x` and `y` only if a
private variable `z` is zero:
```racket
(program
  (if (= (private z) 0)
    (set! w (+ x y))
    (set! w x))
```

The product construction for this program, generated by the `product` macro, yields
```racket
(let ()
  (begin 0
    ; declare variables (P)
    (define-symbolic z integer?)
    (define-symbolic w integer?)
    (define-symbolic x integer?)
    (define-symbolic y integer?)

    ; declare variables (P')
    (define-symbolic z6 integer?)
    (define-symbolic w7 integer?)
    (define-symbolic x8 integer?)
    (define-symbolic y9 integer?)

    ; initialize counter (P)
    (define-symbolic z10 integer?)
    (set! z10 0)

    ; initialize counter (P')
    (define-symbolic z615 integer?)
    (set! z615 0)

    ; assume public variables are equal
    (set! w w7)
    (set! x x8)
    (set! y y9)

    ; main program (P)
    (begin 0
      (begin
        (set! z10 (+ z10 1))
        (if (begin (set! z10 (+ z10 1)) (= z 0))
          (begin
            (set! z10 (+ z10 2))
            (set! w (+ x y)))
          (begin
            (set! z10 (+ z10 1))
            (set! w x)))))

    ; main program (P')
    (begin 0
      (begin
        (set! z615 (+ z615 1))
        (if (begin (set! z615 (+ z615 1)) (= z6 0))
          (begin
            (set! z615 (+ z615 2))
            (set! w7 (+ x8 y9)))
          (begin
            (set! z615 (+ z615 1))
            (set! w7 x8)))))

    ; assert counter variables are equal
    (assert (= z10 z615))))
```

The product program is just Rosette code, so it can be easily verified using Rosette's `verify`:
```racket
(verify
  (product
    (program
      (if (= (private z) 0)
        (set! w (+ x y))
        (set! w x)))))
```

Since this program is not constant-time with respect to the private variable `z` (it performs an extra addition operation if `z` is zero),
Rosette's verifier finds a counterexample to the assertion made in the product program--the model returned by `verify` asserts that the program will have different execution times depending on whether `z` is initialized to 0 or -1.
```racket
(model
 [n 0]
 [z 0]
 [z110 -1])
```
(`z` and `z110` correspond to the private variable `z` in `P` and `P'`, respectively.)

On the other hand, if we replace `x` in the else clause with `(+ x 0)`, the program will be constant time with respect to `z`, and
`verify` will be unable to find a counterexample:
```racket
(verify
  (product
    (program
      (if (= (private z) 0)
        (set! w (+ x y))
        (set! w (+ x 0))))))
; ==> (unsat)
```

## Sketch completion

The `complete-sketch` macro produces, given a sketch and a specification program, a Rosette `synthesize` query
that tries to fill holes using integer constants or other variables present in the sketch in such a way that
the resulting completed program runs in constant time with respect to its private variables and is functionally
equivalent to the specification program.
The structure of the `synthesize` query is approximately as follows:
```racket
(synthesize
  #:forall (list ,@(append (variables-of left) (variables-of right) (variables-of spec)))
  #:guarantee
    (begin
      ,(self-product left right #t)
      ,(assert-functionally-equivalent left spec)))))))
```
where `left` and `right` are two copies of the sketch and `spec` is the specification program.

For instance, this call to `complete-sketch`
```racket
(complete-sketch
  (program
    (if (= (private z) 0)
      (set! w (+ x y))
      (set! w (+ x (hole a)))))
  (program
    (if (= (private z) 0)
      (set! w (+ x y))
      (set! w x))))
```
generates the following `synthesize` query:
```racket
(let ()
  (begin 0
    ; declare variables (P)
    (define-symbolic z integer?)
    (define-symbolic w integer?)
    (define-symbolic x integer?)
    (define-symbolic y integer?)

    ; initialize counter (P)
    (define-symbolic z24 integer?)
    (set! z24 0)

    ; declare variables (P')
    (define-symbolic z8 integer?)
    (define-symbolic w9 integer?)
    (define-symbolic x10 integer?)
    (define-symbolic y11 integer?)

    ; initialize counter (P')
    (define-symbolic z835 integer?)
    (set! z835 0)

    ; initialize holes
    (define a (basic z w x y 1))

    ; declare variables (spec)
    (define-symbolic z12 integer?)
    (define-symbolic w13 integer?)
    (define-symbolic x14 integer?)
    (define-symbolic y15 integer?)

    ; synthesize query
    (synthesize
      #:forall (list z w x y z8 w9 x10 y11 z12 w13 x14 y15)
      #:guarantee
        (begin
          ; assume public vars are equal
          (set! w w9)
          (set! x x10)
          (set! y y11)

          ; main program (P)
          (begin 0
            (begin
              (set! z24 (+ z24 1))
              (if (begin (set! z24 (+ z24 1)) (= z 0))
                (begin
                  (set! z24 (+ z24 2))
                  (set! w (+ x y)))
                (begin
                  (set! z24 (+ z24 2))
                  (set! w (+ x a))))))

          ; main program (P')
          (begin 0
            (begin
              (set! z835 (+ z835 1))
              (if (begin (set! z835 (+ z835 1)) (= z8 0))
                (begin
                  (set! z835 (+ z835 2))
                  (set! w9 (+ x10 y11)))
                (begin
                  (set! z835 (+ z835 2))
                  (set! w9 (+ x10 a))))))

          ; counter variables must be equal (assert that completed sketch is constant time)
          (assert (= z24 z835))

          ; assert functional equivalence
          (begin
            ; assume same initial state
            (set! z z12)
            (set! w w13)
            (set! x x14)
            (set! y y15)

            ; run completed sketch
            (begin 0
              (if (= z 0)
                (set! w (+ x y))
                (set! w (+ x a))))

            ; run spec
            (begin 0
              (if (= z12 0)
                (set! w13 (+ x14 y15))
                (set! w13 x14)))

            ; assert same final state
            (assert (= z z12))
            (assert (= w w13))
            (assert (= x x14))
            (assert (= y y15)))))))
```

The above `synthesize` query produces the following model, which correctly fills in the integer constant 0 in place of
`(hole a)` in the original sketch:
```racket
(model
 [n -11]
 [0$choose:loopfree:287:10$basic:#f:#f:#f #t])
```

## Future work

At present, it's only possible to use integer constants or variables in holes, since a more complex expression would
need to be embellished with code that maintains the counter variable properly--therefore, some macro expansion would have to
occur at runtime in order to synthesize more complicated expressions.
Additionally, the resulting models produced by Rosette are somewhat decipherable for the examples presented above, but
in general are not very easy to understand. The results of `synthesize` are especially cryptic, since they are
intended to be passed to `print-forms`, which produces a pretty-printed completed sketch.
However, since the "sketches" given to `synthesize` in our case have already undergone several layers of macro expansion
in order to incorporate a counter variable, a product program, and code to check for functional equivalence to some
specification, the completed programs returned by `print-forms` would be far removed from the original sketches.
Thus, a natural next step might be to develop a function that reverses the macro-expansion, allowing for recovery of
a program written in our imperative language.

Such a function would also be useful in developing a tool for automatic repair of programs that are not constant-time
with respect to their private variables. Rosette's `debug` module has the ability to extract an "unsolvable kernel"
from a `verify` query, which can then be used to generate potential sketches for completion. With the ability to
recover a program in our toy language from the macro-expanded Rosette code, it may be possible to determine which
expressions in the original program correspond to the unsolvable kernel of a macro-expanded verify query, which would
allow us to automatically generate a completable sketch.

## References

**1.** J. B. Almeida, M. Barbosa, G. Barthe, F. Dupressoir, and M. Emmi. Verifying constant-time implementations. In USENIX, pages 53–70. USENIX Association, 2016.
