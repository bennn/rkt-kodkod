#lang racket/base

;; Basic datatypes for Kodkod.

;; "Everyting" in the file is exported.
;; Hopefully that's clear from the syntax.
;; If not, all provides come from the `define-ADT` macro.

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
           [(_ tgt [(tag*:id e** (... ...)) e*] (... ...))
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
                  [(tag* e** (... ...)) e*]
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

(define-ADT formula
  (f:no ( ;; Empty formula
    [e : expr?]))
  (f:lone ( ;; At most one
    [e : expr?]))
  (f:one ( ;; Exactly one
    [e : expr?]))
  (f:some ( ;; Non-empty
    [e : expr?]))
  (f:subset ( ;; Subseteq
    [e0 : expr?]
    [e1 : expr?]))
  (f:equal (
    [e0 : expr?]
    [e1 : expr?]))
  (f:neg (
    [f : formula?]))
  (f:wedge (
    [f0 : formula?]
    [f1 : formula?]))
  (f:vee (
    [f0 : formula?]
    [f1 : formula?]))
  (f:implies (
    [f0 : formula?]
    [f1 : formula?]))
  (f:iff (
    [f0 : formula?]
    [f1 : formula?]))
  (f:forall (
    [v* : varDecl?]
    [f : formula?]))
  (f:exists (
    [v* : varDecl?]
    [f : formula?])))

(define (format-formula f)
  (format "~a\n~a" f (*PRINT-INDENT*)))

;; -----------------------------------------------------------------------------

(define-ADT expr
  (e:var (
    [v : Symbol]))
  (e:transpose ( ;; `
    [e : expr?]))
  (e:closure ( ;; ^
    [e : expr?]))
  (e:refl ( ;; *
    [e : expr?]))
  (e:union (
    [e0 : expr?]
    [e1 : expr?]))
  (e:intersection (
    [e0 : expr?]
    [e1 : expr?]))
  (e:difference  (
    [e0 : expr?]
    [e1 : expr?]))
  (e:join (
    [e0 : expr?]
    [e1 : expr?]))
  (e:product (
    [e0 : expr?]
    [e1 : expr?]))
  (e:if/else (
    [f : formula?]
    [e0 : expr?]
    [e1 : expr?]))
  (e:comprehension (
    [v* : varDecl?]
    [f : formula?])))

;; -----------------------------------------------------------------------------
;; varDecl

(define (write-varDecl vd port mode)
  (fprintf port "[~a : ~a]" (varDecl-v vd) (varDecl-e vd)))

;; (v : e)
(struct varDecl (v e)
  #:methods gen:custom-write
  [(define write-proc write-varDecl)])

;; -----------------------------------------------------------------------------
;; --- booleans

(define-ADT bool
  (b:zero ())   ;; 0 (constant)
  (b:one ())    ;; 1 (constant)
  (b:var ([v : Symbol]))   ;; identifier
  (b:neg ([b : bool?]))
  (b:and ([b0 : bool?] [b1 : bool?]))
  (b:or ([b0 : bool?] [b1 : bool?]))
  (b:if/else ([b0 : bool?] [b1 : bool?] [b2 : bool?])))

(define-syntax-rule (big-bor for-clause for-body)
  (for/fold ([acc (bzero)])
            for-clause
    (bor acc for-body)))

(define-syntax-rule (big-band for-clause for-body)
  (for/fold ([acc (bone)])
            for-clause
    (band acc for-body)))

;(define (b-simplify b)
;  'TODO)

;; =============================================================================
;; --- Free Variables (fvs)

(define (varDecl*-fvs vd*)
  (for/fold ([acc (set)])
            ([vd (in-list vd*)])
    (set-union acc (expr-fvs (varDecl-e vd)))))

(define (formula-fvs f)
  (match-formula f
   [(f:no e)
    (expr-fvs e)]
   [(f:lone e)
    (expr-fvs e)]
   [(f:one e)
    (expr-fvs e)]
   [(f:some e)
    (expr-fvs e)]
   [(f:subset e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(f:equal e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(f:neg f)
    (formula-fvs f)]
   [(f:wedge f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(f:vee f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(f:implies f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(f:iff f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(f:forall v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]
   [(f:exists v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]))

(define (expr-fvs e)
  (match-expr e
   [(e:var v)
    (set v)]
   [(e:transpose e)
    (expr-fvs e)]
   [(e:closure e)
    (expr-fvs e)]
   [(e:refl e)
    (expr-fvs e)]
   [(e:union e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(e:intersection e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(e:difference e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(e:join e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(e:product e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(e:if/else f e0 e1)
    (set-union (formula-fvs f) (expr-fvs e0) (expr-fvs e1))]
   [(e:comprehension v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]))


;; -----------------------------------------------------------------------------
;; --- Bound Variables (bvs)

(define (varDecl*-bvs vd*)
  (for/set ([vd (in-list vd*)])
    (varDecl-v vd)))

;; Build a set of bound variables on the way DOWN,
;;  return the set only when finding a variable in `v`.
;; Otherwise return the empty set.
(define (formula-bvs f [bvs (set)] #:over v*)
  (let loop ([f f]  [bvs bvs])
    (match-formula f
     [(f:no e)
      (expr-bvs e bvs #:over v*)]
     [(f:lone e)
      (expr-bvs e bvs #:over v*)]
     [(f:one e)
      (expr-bvs e bvs #:over v*)]
     [(f:some e)
      (expr-bvs e bvs #:over v*)]
     [(f:subset e0 e1)
      (set-union ;; Losing path precision, but whatever
        (expr-bvs e0 bvs #:over v*)
        (expr-bvs e1 bvs #:over v*))]
     [(f:equal e0 e1)
      (set-union
        (expr-bvs e0 bvs #:over v*)
        (expr-bvs e1 bvs #:over v*))]
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
      (loop f (set-union bvs (varDecl*-bvs v*)))]
     [(f:exists v* f)
      (loop f (set-union bvs (varDecl*-bvs v*)))])))

(define (expr-bvs e bvs #:over v*)
  (let loop ([e e]  [bvs bvs])
    (match-expr e
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
        (formula-fvs f bvs #:over v*)
        (loop e0 bvs)
        (loop e1 bvs))]
     [(e:comprehension v* f)
      (apply set-union
        (formula-fvs f bvs #:over v*)
        (for/list ([vd (in-list v*)])
          (loop (varDecl-e vd) bvs)))])))

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
        (lambda () (compile '(match-formula f [(f:no e) #f]))))
      (check-exn #rx"Duplicate case for constructor 'f:no'"
        (lambda () (compile '(match-formula f [(f:no e) #t] [(f:no e) #f]))))))
)

