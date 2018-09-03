#lang rosette

(require rosette/lib/synthax)

; helper macros
(begin-for-syntax

  ; return whether an symbol is a valid variable (avoid recognizing holes like ?? as variables)
  (define (variable? v)
    (and
      ; numbers can't be variables
      (not (number? v))

      ; if variable is a symbol or identifier, check that its name is alphanumerics only
      (if (or (symbol? v) (identifier? v))
        (let ([sym (if (identifier? v) (syntax-e v) v)])
          (andmap (lambda (c) (or (char-alphabetic? c) (char-numeric? c))) (string->list (symbol->string sym))))
        #f)))

  ; helper for variables-of. union of two sets of variables (represented by lists of symbols)
  (define (merge a b)
    (append a (filter (lambda (x) (not (member x a))) b)))

  ; extract a list of variables used in an expression
  ; if publics, extract public variables (variables without any annotation)
  ; if privates, extract private variables (annotated variables, which look like (private variable-name))
  ; if holes, extract holes (annotated variables, which look like (hole hole-name))
  (define (variables-of expr [publics #t] [privates #t] [holes #f])
    (match expr
      [`(+ ,a ,b)        (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(- ,a ,b)        (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(< ,a ,b)        (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(* ,a ,b)        (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(= ,a ,b)        (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(set! ,a ,b)     (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(hole ,a)        (if holes (list a) (list))]
      [`(if ,a ,b ,c)    (merge (merge
                                   (variables-of a publics privates holes)
                                   (variables-of b publics privates holes))
                                   (variables-of c publics privates holes))]
      [`(assert ,a)      (variables-of a publics privates holes)]
      [`(program ,a ...) (foldl merge (list)
                            (map (lambda (b) (variables-of b publics privates holes)) a))]
      [`(while ,a ,b)    (merge (variables-of a publics privates holes) (variables-of b publics privates holes))]
      [`(private ,a)     (if (and (variable? a) privates) (list a) (list))]
      [a                 (if (and (variable? a) publics) (list a) (list))]))

  ; extract a list of variables annotated as public
  (define (publics-of expr)
    (variables-of expr #t #f))

  ; extract a list of variables annotated as private
  (define (privates-of expr)
    (variables-of expr #f #t))

  ; extract a list of identifiers annotated as holes
  (define (holes-of expr)
    (variables-of expr #f #f #t))

  ; given a toy language expression (not including if-then-else or while)
  ; return a Rosette expression that computes the number of "counter ticks" needed to evaluate it
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

  ; rename all variables in a toy language expression given rename pairings
  ; pairs are a list of (list original-name new-name)
  (define (rename-with expr pairs)
    (match expr
      [`(+ ,a ,b)        `(+ ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(- ,a ,b)        `(- ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(< ,a ,b)        `(< ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(* ,a ,b)        `(* ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(= ,a ,b)        `(= ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(set! ,a ,b)     `(set! ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(hole ,a) expr]
      [`(if ,a ,b ,c)    `(if ,(rename-with a pairs)
                             ,(rename-with b pairs)
                             ,(rename-with c pairs))]
      [`(assert ,a)      `(assert ,(rename-with a pairs))]
      [`(program ,a ...) `(program ,@(map (lambda (b) (rename-with b pairs)) a))]
      [`(while ,a ,b)    `(while ,(rename-with a pairs) ,(rename-with b pairs))]
      [`(private ,a)     `(private ,(rename-with a pairs))]
      [a                 (let ([search-result (filter (lambda (p) (eq? a (first p))) pairs)])
                                                 (if (not (empty? search-result))
                                                   (second (first search-result))
                                                   a))]))

  ; return a copy of a toy language expression with all variables renamed
  ; new variable names do not conflict with old ones
  (define (rename expr [extra-vars (list)])
    (define variable-names (append extra-vars (variables-of expr)))
    (define new-names (generate-temporaries variable-names))
    (define pairs (map list variable-names new-names))
    (rename-with expr pairs))

  ; given a loop condition and body, unroll to unroll-depth
  ; place an assert at maximum depth that, when evaluated, signals that unroll-depth was too small
  (define (unroll pred body [unroll-depth 20])
    (if (= 0 unroll-depth)
      `(assert (not ,pred))
      `(if ,pred (program ,body ,(unroll pred body (- unroll-depth 1))) (program))))

  ; remove private and hole annotations
  (define (strip-annotations expr)
    (match expr
      [`(= ,a ,b)        `(= ,(strip-annotations a) ,(strip-annotations b))]
      [`(+ ,a ,b)        `(+ ,(strip-annotations a) ,(strip-annotations b))]
      [`(- ,a ,b)        `(- ,(strip-annotations a) ,(strip-annotations b))]
      [`(< ,a ,b)        `(< ,(strip-annotations a) ,(strip-annotations b))]
      [`(* ,a ,b)        `(* ,(strip-annotations a) ,(strip-annotations b))]
      [`(set! ,a ,b)     `(set! ,(strip-annotations a) ,(strip-annotations b))]
      [`(hole ,a) a]
      [`(if ,a ,b ,c)    `(if ,(strip-annotations a)
                              ,(strip-annotations b)
                              ,(strip-annotations c))]
      [`(assert ,a)      `(assert ,(strip-annotations a))]
      [`(program ,a ...) `(program ,@(map strip-annotations a))]
      [`(while ,a ,b)    `(while ,(strip-annotations a) ,(strip-annotations b))]
      [`(private ,a)     (strip-annotations a)]
      [a                 a]))

  ; convert toy language to normal racket 
  (define (to-racket expr)
    (define (go expr)
      (match expr
        [`(= ,a ,b)        `(= ,(go a) ,(go b))]
        [`(+ ,a ,b)        `(+ ,(go a) ,(go b))]
        [`(- ,a ,b)        `(- ,(go a) ,(go b))]
        [`(< ,a ,b)        `(< ,(go a) ,(go b))]
        [`(not ,a ,b)      `(not ,(go a))]
        [`(* ,a ,b)        `(* ,(go a) ,(go b))]
        [`(set! ,a ,b)     `(set! ,(go a) ,(go b))]
        [`(if ,a ,b ,c)    `(if ,(go a)
                              ,(go b)
                              ,(go c))]
        [`(assert ,a)      `(assert ,(go a))]
        [`(program ,a ...) `(begin 0 ,@(map go a))]
        [`(while ,a ,b)    (go (unroll a b))]
        [a                 a]))
    (go (strip-annotations expr)))

  ; given a name for a counter variable,
  ; return a function that, given a toy language expression,
  ;   adds proper counter manipulation code
  ;   converts the toy language syntax to evaluable Rosette exprs
  (define (emit-counter-code counter-name)
    (define (emit expr)
      (match expr
        [`(if ,a ,b ,c)    `(begin
                              (set! ,counter-name (+ ,counter-name ,(bench a)))
                              (if ,(emit a) ,(emit b) ,(emit c)))]
        [`(program ,a ...) `(begin 0 ,@(map emit a))]
        [`(while ,a ,b)    (emit (unroll a b))]
        [_                 (let ([cost (bench expr)])
                             (if (= 0 cost)
                               expr
                               `(begin (set! ,counter-name (+ ,counter-name ,cost)) ,expr)))]))
    (lambda (expr) (emit (strip-annotations expr))))

  ; given a toy language expression, return 4 values:
  ;   Rosstte expression initializing the counter variable
  ;   Rosette expression initializing all variables
  ;   Rosette expression initializing all holes
  ;   Rosette expression + expressions to maintain the counter variable
  ; ensures that counter variable does not conflict with any variable used in the toy language expression
  (define (add-counts expr [extra-vars (list)] [grammar-depth 1])
    ; the counter name must differ from all variable/hole names
    (define counter-name (first (generate-temporaries (append (variables-of expr) (holes-of expr) extra-vars (list 'a)))))

    (values
      ; code to initialize the counter variable
      (list `(define-symbolic ,counter-name integer?)
           `(set! ,counter-name 0))

      ; code to initialize variables
      (map (lambda (name) `(define-symbolic ,name integer?)) (variables-of expr))

      ; code to initialize holes
      (map
        ; (lambda (name) `(define ,name (??)))
        (lambda (name) `(define ,name (basic ,@(variables-of expr) ,grammar-depth)))
        (holes-of expr))

      ; toy language expression translated into Rosette that also increments counter variable
      ((emit-counter-code counter-name) expr)))

  ; given a toy language expression and a renamed copy,
  ; construct a product program to verify constant-time execution
  (define (self-product left right [no-init #f])
    ; translate the original into executable Rosette code
    (define-values (left-counter-init left-inits left-hole-inits left-counted) (add-counts left))
    (define left-counter (cadar left-counter-init))

    ; translate the copy into executable Rosette code
    (define-values (right-counter-init right-inits _ right-counted) (add-counts right (list left-counter)))
    (define right-counter (cadar right-counter-init))

    ; return Rosette expression to execute one translated program after the other with identical public inputs,
    ; and assert that counter variables of both programs are equal
    (append
      (list 'let ' ())
      (list (append
             (list 'begin 0)
             (if no-init
               (list)
               (append left-inits left-hole-inits right-inits))
             left-counter-init
             right-counter-init
             (map (lambda (a b) `(set! ,a ,b)) (publics-of left) (publics-of right))
             (list left-counted)
             (list right-counted)
             (list `(assert (= ,left-counter ,right-counter)))))))

  ; assert two expressions, one with holes and one without, are functionally equiv
  ; assumes no naming conflicts between the two and that all vars are initialized
  (define (assert-functionally-equivalent left spec)
    `(begin
      ,@(map (lambda (a b) `(set! ,a ,b)) (variables-of left) (variables-of spec))
      ,(to-racket left)
      ,(to-racket spec)
      ,@(map (lambda (a b) `(assert (= ,a ,b))) (variables-of left) (variables-of spec)))))

; macro to convert toy language to Rosette with code to increment a counter variable
(define-syntax (program stx)
  (define-values (counter-init inits hole-inits counted) (add-counts (syntax->datum stx)))
  (datum->syntax stx
    (append
      (list 'let ' ())
      ; (list 'quote)
      (list (append
              (list 'begin 0)
              inits
              hole-inits
              counter-init
              (list counted))))))

; macro to convert toy language to Rosette + self product
(define-syntax (product stx)
  (define left (cadr (syntax->datum stx)))
  ; datum->syntax stx
  ;   `(quote (pair ,(unroll `(= x 0) `(program (set! x + x 1) (set! y + y 3)))
  ;                 ,((emit-counter-code 'a) (unroll `(= x 0) `(program (set! x + x 1) (set! y + y 3))))))
  (define right (rename left))
  (datum->syntax stx (self-product left right)))

; macro to return bindings for a functionally equivalent constant-time program
(define-syntax (complete-sketch stx)
  (define left (cadr (syntax->datum stx)))
  (define right (rename left))
  (define spec (rename (caddr (syntax->datum stx))
                  (append (variables-of left) (variables-of right))))
  (define-values (left-counter-init left-inits left-hole-inits left-counted) (add-counts left))
  (define-values (_ spec-inits __ ___) (add-counts spec))
  (define-values (right-counter-init right-inits ____ right-counted) (add-counts right))
  (datum->syntax stx
    `(let ()
          (begin 0
            ,@left-inits
            ,@right-inits
            ,@left-hole-inits
            ,@spec-inits
            (synthesize
              #:forall (list ,@(append (variables-of left) (variables-of right) (variables-of spec)))
              #:guarantee
                ,(begin
                   (self-product left right #t)
                   (assert-functionally-equivalent left spec)))))))

; the grammar of the language
(define-synthax (basic a ... depth)
  #:base (choose 0 1 2 3 a ...)
  #:else (choose
           0 1 2 3 a ...
           ((choose + < * =) (basic a ... (- depth 1)) (basic a ... (- depth 1)))))
           ; (set! (choose a ...) (basic a ... - depth 1))
           ; (if (basic a ... - depth 1) (basic a ... - depth 1) (basic a ... - depth 1))
           ; (program (basic a ... - depth 1))

; -------------------------------- examples --------------------------------------

; factorial program
(program
  (set! k (private n))
  (set! result 1)
  (while (< 0 k) (program
    (set! k (- k 1))
    (set! result (* result k)))))

; runs in constant time wrt z, so the verifier returns unsat
(verify
  (product
    (program
      (if (= (private z) 0)
        (+ x y)
        (+ x 0)))))

; does not run in constant time wrt z, so the verifier returns a counterexample
(verify
  (product
    (program
      (if (= (private z) 0)
        (+ x y)
        x))))

; does not run in constant time wrt n, so the verifier returns a counterexample
(verify
  (product
    (program
      (set! k (private n))
      (set! result 1)
      (while (< 0 k) (program
        (set! k (- k 1))
        (set! result (* result k)))))))

; synthesize an expression when there are multiple if statements
(complete-sketch
  (program
    (set! c 4)
    (if (= 0 (* (hole a) (private z)))
      (set! c 3)
      (set! c 5))
    (if (= 0 (* (hole b) (private z2)))
      (set! c 3)
      (set! c 5)))
  (program
    (set! c 4)
    (if (= 0 (* 0 (private z)))
      (set! c 3)
      (set! c 5))
    (if (= 0 (* 0 (private z2)))
      (set! c 3)
      (set! c 5))))

; synthesize an expression in a loop bound
(complete-sketch
  (program
    (set! x 1)
    (set! i 1)
    (while (< x (* (private y) (hole c)))
      (program
        (set! x (* x i))
        (set! i (+ i 1))))
    x)
  (program
    (set! x 1)
    (set! i 1)
    (while (< x (* (private y) 1))
      (program
        (set! x (* x i))
        (set! i (+ i 1))))
    x))
