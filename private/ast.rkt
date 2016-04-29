#lang racket/base

;; Basic datatypes for Kodkod.

;; "Everyting" in the file is exported.
;; Hopefully that's clear from the syntax.
;; If not, all provides come from the `define-ADT` macro.

(provide
  define-ADT

  format-kk:formula
  kk:formula-bvs
  kk:formula-fvs

  kk:expr-bvs
  kk:expr-fvs

  (struct-out kk:varDecl)
  kk:varDecl*-bvs
  kk:varDecl*-fvs

  (struct-out kk:relBound)
  format-kk:relBound
  kk:relBound*-bvs
  kk:relBound-fvs

  (struct-out kk:problem)
  format-kk:problem

  Universe
  kk:universe
  format-kk:universe
  assert-universe-contains?
  universe-contains?
  universe-size

  Bool
)

(require
  kodkod/private/parameters
  kodkod/private/predicates
  racket/match
  racket/set
  (for-syntax racket/base syntax/parse racket/syntax))

;; =============================================================================
;; --- Syntax

(define-syntax (define-ADT stx)
  (syntax-parse stx
   [(_ T:id [t*:id field-stx*] ...)
    #:with (t-def* ...)
      (for/list ([t (in-list (syntax-e #'(t* ...)))]
                 [field-stx (in-list (syntax-e #'(field-stx* ...)))])
        (syntax-parse field-stx
         #:datum-literals (:)
         [((name*:id (~optional :) ctc*) ...)
          #:with t t
          (syntax/loc stx
            (begin (struct t T (name* ...) #:transparent)
                   (provide (contract-out (struct (t T) ((name* ctc*) ...))))))]))
    #:with match-T-id
      (format-id stx "match-~a" (syntax-e #'T))
    #:with T?-id
      (format-id stx "~a?" (syntax-e #'T))
    #:with match-T-def
      (quasisyntax/loc stx
        (lambda (stx)
          (syntax-parse stx
           [(_ tgt [(tag*:id e** (... ...)) e* (... ...)] (... ...))
            ;; -- Check for duplicate / missing cases
            (let* ([tag-list (for/list ([tag (in-list (syntax-e #'(tag* (... ...))))]) (syntax-e tag))])
              (for ([t-stx (in-list (syntax-e #'(t* ...)))])
                (let* ([t (syntax-e t-stx)]
                       [m (memq t tag-list)])
                  (if m
                    (when (memq t (cdr m))
                      (raise-user-error
                        (syntax->src stx)
                        "Duplicate case for constructor '~a'" t))
                    (raise-user-error
                      (syntax->src stx)
                      "Missing case for constructor '~a'" t)))))
            ;; -- Desugar to a normal match, except a little type-aware
            (syntax/loc stx
              (if (T?-id tgt)
                (match tgt
                  [(tag* e** (... ...)) e* (... ...)]
                  (... ...)
                  [else (raise-user-error '#,(syntax-e #'match-T-id) "Reached absurd case for value ~a" tgt)])
                (raise-user-error '#,(syntax-e #'match-T-id) "Expected ~a, got ~a" '#,(syntax-e #'T?-id) tgt)))])))
    (syntax/loc stx
      (begin
        (struct T () #:transparent)
        (provide (contract-out (struct T ())))
        t-def* ...
        (define-syntax match-T-id match-T-def)
        (provide match-T-id)))]))

(define-for-syntax (syntax->src stx)
  (string->symbol (format "~a:~a:~a" (syntax-source stx) (syntax-line stx) (syntax-column stx))))

;; -----------------------------------------------------------------------------
;; formulas

(define-ADT kk:formula
  (f:no ( ;; Empty formula
    [e : kk:expr?]))
  (f:lone ( ;; At most one
    [e : kk:expr?]))
  (f:one ( ;; Exactly one
    [e : kk:expr?]))
  (f:some ( ;; Non-empty
    [e : kk:expr?]))
  (f:subset ( ;; Subseteq
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (f:equal (
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (f:neg (
    [f : kk:formula?]))
  (f:wedge (
    [f0 : kk:formula?]
    [f1 : kk:formula?]))
  (f:vee (
    [f0 : kk:formula?]
    [f1 : kk:formula?]))
  (f:implies (
    [f0 : kk:formula?]
    [f1 : kk:formula?]))
  (f:iff (
    [f0 : kk:formula?]
    [f1 : kk:formula?]))
  (f:forall (
    [v* : kk:varDecl*?]
    [f : kk:formula?]))
  (f:exists (
    [v* : kk:varDecl*?]
    [f : kk:formula?])))

(define MultiplicityFormula
  (U f:no? f:some? f:one? f:lone?))

(define ComparisonFormula
  (U f:subset? f:equal?))

(define (format-kk:formula f)
  (format "~a\n~a" f (*PRINT-INDENT*)))

;; -----------------------------------------------------------------------------

(define-ADT kk:expr
  (e:var (
    [v : Symbol]))
  (e:transpose ( ;; `
    [e : kk:expr?]))
  (e:closure ( ;; ^
    [e : kk:expr?]))
  (e:refl ( ;; *
    [e : kk:expr?]))
  (e:union ( ;; +
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (e:intersection ( ;; &
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (e:difference  ( ;; -
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (e:join ( ;; .
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (e:product ( ;; ->
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  ;(e:override ( ;; ++ TODO))
  (e:if/else (
    [f : kk:formula?]
    [e0 : kk:expr?]
    [e1 : kk:expr?]))
  (e:comprehension (
    [v* : kk:varDecl?]
    [f : kk:formula?])))

;; -----------------------------------------------------------------------------
;; varDecl

(define (write-kk:varDecl vd port mode)
  (fprintf port "[~a : ~a]" (kk:varDecl-v vd) (kk:varDecl-e vd)))

;; (v : e)
(struct kk:varDecl (v e)
  #:methods gen:custom-write
  [(define write-proc write-kk:varDecl)])

(define kk:varDecl*?
  (Listof kk:varDecl?))

;; =============================================================================
;; --- Free Variables (fvs)

(define (kk:varDecl*-fvs vd*)
  (for/fold ([acc (set)])
            ([vd (in-list vd*)])
    (set-union acc (kk:expr-fvs (kk:varDecl-e vd)))))

(define (kk:formula-fvs f)
  (match-kk:formula f
   [(f:no e)
    (kk:expr-fvs e)]
   [(f:lone e)
    (kk:expr-fvs e)]
   [(f:one e)
    (kk:expr-fvs e)]
   [(f:some e)
    (kk:expr-fvs e)]
   [(f:subset e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(f:equal e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(f:neg f)
    (kk:formula-fvs f)]
   [(f:wedge f0 f1)
    (set-union (kk:formula-fvs f0) (kk:formula-fvs f1))]
   [(f:vee f0 f1)
    (set-union (kk:formula-fvs f0) (kk:formula-fvs f1))]
   [(f:implies f0 f1)
    (set-union (kk:formula-fvs f0) (kk:formula-fvs f1))]
   [(f:iff f0 f1)
    (set-union (kk:formula-fvs f0) (kk:formula-fvs f1))]
   [(f:forall v* f)
    (set-union
      (kk:varDecl*-fvs v*)
      (set-subtract (kk:formula-fvs f) (kk:varDecl*-bvs v*)))]
   [(f:exists v* f)
    (set-union
      (kk:varDecl*-fvs v*)
      (set-subtract (kk:formula-fvs f) (kk:varDecl*-bvs v*)))]))

(define (kk:expr-fvs e)
  (match-kk:expr e
   [(e:var v)
    (set v)]
   [(e:transpose e)
    (kk:expr-fvs e)]
   [(e:closure e)
    (kk:expr-fvs e)]
   [(e:refl e)
    (kk:expr-fvs e)]
   [(e:union e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:intersection e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:difference e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:join e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:product e0 e1)
    (set-union (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:if/else f e0 e1)
    (set-union (kk:formula-fvs f) (kk:expr-fvs e0) (kk:expr-fvs e1))]
   [(e:comprehension v* f)
    (set-union
      (kk:varDecl*-fvs v*)
      (set-subtract (kk:formula-fvs f) (kk:varDecl*-bvs v*)))]))


;; -----------------------------------------------------------------------------
;; --- Bound Variables (bvs)

(define (kk:varDecl*-bvs vd*)
  (for/set ([vd (in-list vd*)])
    (kk:varDecl-v vd)))

;; Build a set of bound variables on the way DOWN,
;;  return the set only when finding a variable in `v`.
;; Otherwise return the empty set.
(define (kk:formula-bvs f [bvs (set)] #:over v*)
  (let loop ([f f]  [bvs bvs])
    (match-kk:formula f
     [(f:no e)
      (kk:expr-bvs e bvs #:over v*)]
     [(f:lone e)
      (kk:expr-bvs e bvs #:over v*)]
     [(f:one e)
      (kk:expr-bvs e bvs #:over v*)]
     [(f:some e)
      (kk:expr-bvs e bvs #:over v*)]
     [(f:subset e0 e1)
      (set-union ;; Losing path precision, but whatever
        (kk:expr-bvs e0 bvs #:over v*)
        (kk:expr-bvs e1 bvs #:over v*))]
     [(f:equal e0 e1)
      (set-union
        (kk:expr-bvs e0 bvs #:over v*)
        (kk:expr-bvs e1 bvs #:over v*))]
     [(f:neg f)
      (loop f bvs)]
     [(f:wedge f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(f:vee f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(f:implies f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(f:iff f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(f:forall v* f)
      (loop f (set-union bvs (kk:varDecl*-bvs v*)))]
     [(f:exists v* f)
      (loop f (set-union bvs (kk:varDecl*-bvs v*)))])))

(define (kk:expr-bvs e bvs #:over v*)
  (let loop ([e e]  [bvs bvs])
    (match-kk:expr e
     [(e:var v)
      (if (set-member? v* v)
        bvs
        (set))]
     [(e:transpose e)
      (loop e bvs #:over v*)]
     [(e:closure e)
      (loop e bvs #:over v*)]
     [(e:refl e)
      (loop e bvs #:over v*)]
     [(e:union e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:intersection e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:difference e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:join e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:product e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:if/else f e0 e1)
      (set-union
        (kk:formula-fvs f bvs #:over v*)
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:comprehension v* f)
      (apply set-union
        (kk:formula-fvs f bvs #:over v*)
        (for/list ([vd (in-list v*)])
          (loop (kk:varDecl-e vd) bvs)))])))

;; -----------------------------------------------------------------------------

(define Universe (Setof Symbol))

(define (kk:universe sym*)
  (list->set sym*))

(define (assert-universe-contains? U a)
  (unless (universe-contains? U a)
    (raise-user-error 'unbound-var "Unbound variable '~a' in universe '~a'" a U)))

(define (universe-contains? U a)
  (set-member? U a))

(define (universe-size U)
  (set-count U))

;(define (universe-index U a)
;  (for/first ([u (in-vector U)]
;              [i (in-naturals)]
;              #:when (atom=? a u))
;    i))

;(define universe-size
;  vector-length)

(define (format-kk:universe u)
  u)

;; -----------------------------------------------------------------------------

(struct kk:relBound (
  id      ;; Symbol
  arity   ;; Natural
  lo*     ;; Constant
  hi*     ;; Constant
) #:transparent
)

(define (make-kk:relBound id lo* hi*)
  (if (and (null? lo*) (null? hi*))
    (kk:relBound id 0 lo* hi*)
    (let ([arity (if (null? lo*) (length (car hi*)) (length (car lo*)))])
      (kk:relBound id arity lo* hi*))))

(define (kk:relBound-fvs rb)
  (set-union
    (constant-fvs (kk:relBound-lo* rb))
    (constant-fvs (kk:relBound-hi* rb))))

(define (kk:relBound*-bvs rb*)
  (for/fold ([acc (set)])
            ([rb (in-list rb*)])
    (set-add acc (kk:relBound-id rb))))

(define (format-kk:relBound rb)
  (format "[~a :~a ~a ~a]\n~a"
    (kk:relBound-id rb)
    (kk:relBound-arity rb)
    (kk:relBound-lo* rb)
    (kk:relBound-hi* rb)
    (*PRINT-INDENT*)))

;; kodkod = problem
(struct kk:problem (
  universe ;; (Vectorof Symbol)
  bound*   ;; (Listof Bound)
  formula* ;; (Listof Formula)
) #:transparent )

(define (format-kk:problem kk)
  (format "(problem\n  U = ~a\n  B = ~a\n  F = ~a\n)"
    (format-kk:universe (kk:problem-universe kk))
    (map format-kk:relBound (kk:problem-bound* kk))
    (map format-kk:formula (kk:problem-formula* kk))))

;; -----------------------------------------------------------------------------
;; (define-type Constant (Setof Tuple))

(define (tuple=? x* y*)
  (let ([x*-nil (null? x*)]
        [y*-nil (null? y*)])
    (cond
     [(and x*-nil y*-nil)
      #t]
     [(or x*-nil y*-nil)
      #f]
     [else
      (and (atom=? (car x*) (car y*))
           (tuple=? (cdr x*) (cdr y*)))])))

(define atom=?
  eq?)

(define (make-constant . tuple*)
  ;; TODO all inputs must be lists of same length
  (list->set tuple*))

(define (constant-fvs c)
  (for*/set ([a* (in-set c)]
             [a (in-list a*)])
    a))

(define (constant-arity c)
  (if (set-empty? c)
    0
    (length (set-first c))))

;; -----------------------------------------------------------------------------
;; --- Booleans

(define-ADT kk:bool
  (b:zero ())
  (b:one ())
  (b:var ([v : Symbol]))
  (b:neg ([b : kk:bool?]))
  (b:and ([b0 : kk:bool?] [b1 : kk:bool?]))
  (b:or  ([b0 : kk:bool?] [b1 : kk:bool?]))
  (b:if/else ([b0 : kk:bool?] [b1 : kk:bool?] [b2 : kk:bool?]))
)
(define Bool kk:bool?)

;; -----------------------------------------------------------------------------
;; --- Parsing

;; -- TODO make print/parse macro?
;;     track precedence by vertical position?

;; =============================================================================
(define-namespace-anchor anchor)
(module+ test
  (require rackunit)

  (test-case "match-formula"
    (parameterize ([current-namespace (namespace-anchor->namespace anchor)])
      (check-exn #rx"Missing case for constructor 'f:lone'"
        (lambda () (compile '(match-kk:formula f [(f:no e) #f]))))
      (check-exn #rx"Duplicate case for constructor 'f:no'"
        (lambda () (compile '(match-kk:formula f [(f:no e) #t] [(f:no e) #f]))))))

  ;; TODO lots more tests
)

