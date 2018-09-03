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
with respect to private input variables and 2) completing a partially filled program
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
Finally, a program is a sequence of statements.

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
       | (if <bexp> <aexp> <aexp>)

bexp ::= #t
       | #f
       | (= <aexp> <aexp>)
       | (< <aexp> <aexp>)

stmt ::= (set! <avar> <aexp>)
       | (assert <bexp>)
       | (while <bexp> <prgm>)

prgm ::= (program <stmt> ...)
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

For example, the while-loop in the factorial example above, when unrolled and expanded, yields
the following Rosette code:
```racket
(let ()
  (begin 0
    ; declare variables
    (define-symbolic k integer?)
    (define-symbolic n integer?)
    (define-symbolic result integer?)

    ; the unrolled loop
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
              ...
                (if (< 0 k) ; iteration 20
                  (begin 0
                    (begin 0 ; loop body
                      (set! k (- k 1)
                      (set! result (* result k))))
                    (assert (not (< 0 k)))) ; fail for iterations > 20 (unroll depth was too low)
                  (begin 0)))
              ...
            (begin 0)))
        (begin 0))
      (begin 0))))
```

To track the execution time of a program, the expansion process also generates code to initialize
and maintain a counter variable that gets incremented whenever a statement or conditional expression is evaluated.
The `bench` function, shown below, is used to compute the amount by which to increment the
counter variable for any arithmetic expression that does not contain conditionals.
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
          ... 
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
          ...
        (begin 0)))))
```

## Verification

Constant-time verification is implemented using a cross product construction from Almeida et. al.<sup>[1](#references)</sup>.  
Let `P` represent a fully macro-expanded program, complete with a counter variable to track execution time.
The cross-product construction reduces the problem of checking that `P` runs in constant-time with respect to private variables to
verification of a product program `Q`, which simulates the execution of two copies of `P`. The structure of `Q` is as follows
for the product construction implemented in this repository (where `P'` is a copy of the original program `P` with all variables renamed to avoid conflicts, and `c`, `c'` are the counter variables of `P` and `P'` respectively):
```
for each non-private variable v in P corresponding to v' in P', (assume (= v v'))
P
P'
(assert (= c c'))
```

These assertions only fail if there exist differing initial values for the private variables of `P` that result in different `c`s--
that is, if the execution time of `P` depends on the values of its private variables.

As an example, here's a simple program which computes the sum of two variables `x` and `y` only if a private variable `z` is zero:
```racket
(program
  (if (= (private z) 0)
    (+ x y)
    x))
```

The product construction for this program yields
```racket
(let ()
  (begin 0
    ; declare variables (P)
    (define-symbolic z integer?)
    (define-symbolic x integer?)
    (define-symbolic y integer?)
    
    ; declare variables (P')
    (define-symbolic z5 integer?)
    (define-symbolic x6 integer?)
    (define-symbolic y7 integer?)
    
    ; initialize counter (P)
    (define-symbolic z8 integer?)
    (set! z8 0)
    
    ; initialize counter (P')
    (define-symbolic z512 integer?)
    (set! z512 0)
    
    ; assume public variables are equal
    (set! x x6)
    (set! y y7)
    
    ; main program (P)
    (begin 0
      (begin
        (set! z8 (+ z8 1))
        (if (begin (set! z8 (+ z8 1)) (= z 0))
          (begin
            (set! z8 (+ z8 1))
            (+ x y))
          x)))
    
    ; main program (P')
    (begin 0
      (begin
        (set! z512 (+ z512 1))
        (if (begin (set! z512 (+ z512 1)) (= z5 0))
          (begin
            (set! z512 (+ z512 1))
            (+ x6 y7))
          x6)))
    
    ; assert counter variables are equal
    (assert (= z8 z512))))
```

  how verifier is used to check for constant time (give examples)

## Sketch completion

sketch completion
  how holes are implemented
  how synthesizer is used to complete sketches of faulty programs

## Directions for future work

  "undo" macroexpansion (useful for pretty printing the completed sketches)
  repair (use rosette to isolate an "unsolvable kernel", then use "undo expansion" to create holes in original program)

## References

**1.** J. B. Almeida, M. Barbosa, G. Barthe, F. Dupressoir, and M. Emmi. Verifying constant-time implementations. In USENIX, pages 53–70. USENIX Association, 2016.