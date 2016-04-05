#lang racket/base
(module+ test (require rackunit))

;; TODO
;; - stop ignoring syntax information?
;; - compile forall/exists to lambdas, re-use Racket's identifier management
;; - atoms in tuples must be ordered by universe
;; - what is the SAT solver format?
;; - how to open a pipe to solver?
;; - exit-early bitmatrix optimizations (instead of iterating over whole space)

;; Emina TODO
;; - better bitvector arithmetic
;; - better inductive definitions
;; - special handling for simple fragments of input language
;; - heuristics for good variable / constraint ordering

;; TYPO
;; - Fig2-3 : missing ∙ × definitions
;;          : TE(if ...) needs to define m_q

(provide
  read-problem
  ;; (-> Any Problem)

  lint-problem
  ;; (-> Problem Void)

  format-problem
  ;; (-> Problem String)
  ;; Pretty printing

 #;(contract-out
  make-problem


  (make-universe
   (-> (listof symbol?) universe/c))


  (make-relBound
   (->i (id symbol?)
        (lo* (listof (listof symbol?)))
        (hi* (listof (listof symbol?)))
        #:pre (arity=? lo* hi*)
        var/c))

  (make-constant
   (->i () () #:rest [atom** (set/c (listof symbol?))]
        #:pre (arity=? atom**)
        constant/c))

))

(require
  kodkod/private/predicates
  kodkod/private/exceptions

  racket/match
  racket/set
  (for-syntax racket/base syntax/parse)
  syntax/parse

  (only-in racket/list drop-right cartesian-product)
)

;; =============================================================================
;; === Parameters

(define *PRINT-INDENT* (make-parameter (make-string 6 #\space)))

;; =============================================================================
;; === STRUCTS

;; kodkod = problem
(struct problem (
  universe ;; (Vectorof Symbol)
  bound*   ;; (Listof Bound)
  formula* ;; (Listof Formula)
) #:transparent )

(define (format-problem kk)
  (format "(problem\n  U = ~a\n  B = ~a\n  F = ~a\n)"
    (format-universe (problem-universe kk))
    (map format-relBound (problem-bound* kk))
    (map format-formula (problem-formula* kk))))

;; -----------------------------------------------------------------------------
;; (define-type Universe (Vectorof Symbol))

(define (make-universe sym*)
  (for/vector ([x sym*])
    x))

(define (universe-contains? U a)
  (for/or ([u (in-vector U)])
    (atom=? a u)))

(define (universe-index U a)
  (for/first ([u (in-vector U)]
              [i (in-naturals)]
              #:when (atom=? a u))
    i))

(define universe-size
  vector-length)

(define (format-universe u)
  u)

;; -----------------------------------------------------------------------------

(struct relBound (
  id      ;; Symbol
  arity   ;; Natural
  lo*     ;; Constant
  hi*     ;; Constant
) #:transparent
)

(define (make-relBound id lo* hi*)
  (if (and (null? lo*) (null? hi*))
    (relBound id 0 lo* hi*)
    (let ([arity (if (null? lo*) (length (car hi*)) (length (car lo*)))])
      (relBound id arity lo* hi*))))

(define (relBound-fvs rb)
  (set-union
    (constant-fvs (relBound-lo* rb))
    (constant-fvs (relBound-hi* rb))))

(define (relBound*-bvs rb*)
  (for/fold ([acc (set)])
            ([rb (in-list rb*)])
    (set-add acc (relBound-id rb))))

(define (format-relBound rb)
  (format "[~a :~a ~a ~a]\n~a"
    (relBound-id rb)
    (relBound-arity rb)
    (relBound-lo* rb)
    (relBound-hi* rb)
    (*PRINT-INDENT*)))

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
;; formulas

(struct formula () #:transparent)

(define-syntax-rule (define-formula* [id e] ...)
  (begin (struct id formula e #:transparent) ...))

(define-formula*
  (no (e))           ;; Empty
  (lone (e))         ;; at most one
  (one (e))          ;; exactly one
  (some (e))         ;; non-empty
  (subset (e0 e1))   ;; subseteq
  (equal (e0 e1))
  (neg (f))
  (wedge (f0 f1))
  (vee (f0 f1))
  (implies (f0 f1))
  (iff (f0 f1))
  (forall (v* f))
  (exists (v* f)))

(define (format-formula f)
  (format "~a\n~a" f (*PRINT-INDENT*)))

;; -----------------------------------------------------------------------------

(struct expr () #:transparent)

(define-syntax-rule (define-expr* [id e] ...)
  (begin (struct id expr e #:transparent) ...))

(define-expr*
  (var (v))
  (transpose (e))        ;; ~
  (closure (e))          ;; ^
  (refl (e))             ;; *
  (union (e0 e1))        ;; \cup
  (intersection (e0 e1)) ;; \cap
  (difference  (e0 e1))  ;; \setminus
  (join  (e0 e1))        ;; .
  (product (e0 e1))      ;; \rightarrow
  (if/else (f e0 e1))    ;; f ? e1 : e2
  (comprehension (v* f)))     ;; { v* | f }

(define (formula-fvs f)
  (match f
   [(no e)
    (expr-fvs e)]
   [(lone e)
    (expr-fvs e)]
   [(one e)
    (expr-fvs e)]
   [(some e)
    (expr-fvs e)]
   [(subset e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(equal e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(neg f)
    (formula-fvs f)]
   [(wedge f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(vee f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(implies f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(iff f0 f1)
    (set-union (formula-fvs f0) (formula-fvs f1))]
   [(forall v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]
   [(exists v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]))

(define (expr-fvs e)
  (match e
   [(? var? (app var-v v)) ;; ha ha
    (set v)]
   [(transpose e)
    (expr-fvs e)]
   [(closure e)
    (expr-fvs e)]
   [(refl e)
    (expr-fvs e)]
   [(union e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(intersection e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(difference e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(join e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(product e0 e1)
    (set-union (expr-fvs e0) (expr-fvs e1))]
   [(if/else f e0 e1)
    (set-union (formula-fvs f) (expr-fvs e0) (expr-fvs e1))]
   [(comprehension v* f)
    (set-union
      (varDecl*-fvs v*)
      (set-subtract (formula-fvs f) (varDecl*-bvs v*)))]))

;; Build a set of bound variables on the way DOWN,
;;  return the set only when finding a variable in `v`.
;; Otherwise return the empty set.
(define (formula-bvs f [bvs (set)] #:over v*)
  (let loop ([f f]  [bvs bvs])
    (match f
     [(no e)
      (expr-bvs e bvs #:over v*)]
     [(lone e)
      (expr-bvs e bvs #:over v*)]
     [(one e)
      (expr-bvs e bvs #:over v*)]
     [(some e)
      (expr-bvs e bvs #:over v*)]
     [(subset e0 e1)
      (set-union ;; Losing path precision, but whatever
        (expr-bvs e0 bvs #:over v*)
        (expr-bvs e1 bvs #:over v*))]
     [(equal e0 e1)
      (set-union
        (expr-bvs e0 bvs #:over v*)
        (expr-bvs e1 bvs #:over v*))]
     [(neg f)
      (loop f bvs)]
     [(wedge f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(vee f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(implies f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(iff f0 f1)
      (set-union
        (loop f0 bvs)
        (loop f1 bvs))]
     [(forall v* f)
      (loop f (set-union bvs (varDecl*-bvs v*)))]
     [(exists v* f)
      (loop f (set-union bvs (varDecl*-bvs v*)))])))

(define (expr-bvs e bvs #:over v*)
  (let loop ([e e]  [bvs bvs])
    (match e
     [(var v)
      (if (set-member? v* v)
        bvs
        (set))]
     [(transpose e)
      (loop e bvs #:over v*)]
     [(closure e)
      (loop e bvs #:over v*)]
     [(refl e)
      (loop e bvs #:over v*)]
     [(union e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(intersection e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(join e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(product e0 e1)
      (set-union
        (loop e0 bvs)
        (loop e1 bvs))]
     [(if/else f e0 e1)
      (set-union
        (formula-fvs f bvs #:over v*)
        (loop e0 bvs)
        (loop e1 bvs))]
     [(comprehension v* f)
      (apply set-union
        (formula-fvs f bvs #:over v*)
        (for/list ([vd (in-list v*)])
          (loop (varDecl-e vd) bvs)))])))

;; -----------------------------------------------------------------------------
;; varDecl

(define (write-varDecl vd port mode)
  (fprintf port "[~a : ~a]" (varDecl-v vd) (varDecl-e vd)))

;; (v : e)
(struct varDecl (v e)
  #:methods gen:custom-write
  [(define write-proc write-varDecl)])

(define (varDecl*-fvs vd*)
  (for/fold ([acc (set)])
            ([vd (in-list vd*)])
    (set-union acc (expr-fvs (varDecl-e vd)))))

(define (varDecl*-bvs vd*)
  (for/set ([vd (in-list vd*)])
    (varDecl-v vd)))

;; -----------------------------------------------------------------------------
;; Bindings

;; (define-type Binding (HashTable Symbol Constant))

(define (env-init)
  (hasheq))

(define (env-lookup b v)
  (hash-ref b v (lambda () (raise-user-error 'lookup))))

(define (env-update b v s)
  (hash-set b v s))

(define ⊕ ;; \oplus
  env-update)

;; -----------------------------------------------------------------------------
;; --- Semantics
;; Currently unused. What am I supposed to do with this?

;; Kinda tempting to do this as a syntax-parse, but we don't want
;;  to keep using syntactic representations. Think efficiency.

;; (: P (-> Problem Binding Boolean))
(define (P p b)
  ;; Ignores atoms
  (and
    (for/and ([r (in-list (problem-bound* p))])
      (R r b))
    (for/and ([f (in-list (problem-formula* p))])
      (F f b))))

;; (: R (-> relBound Binding Boolean))
(define (R r b)
  (let ([bv (env-lookup b (relBound-id r))])
    (and
      (subset? (relBound-lo* r) bv)
      (subset? bv (relBound-hi* r)))))

;; (: F (-> Formula Binding Boolean))
(define (F f b)
  (match f
   [(no p)
    (null? (E p b))]
   [(lone p)
    (let ([r (E p b)])
      (or (null? p)
          (null? (cdr p))))]
   [(one p)
    ;; = length 1
    (let ([r (E p b)])
      (and (not (null? r))
           (null? (cdr r))))]
   [(some p)
    (not (null? (E p b)))]
   [(subset p q)
    (subset? (E p b) (E q b))]
   [(equal p q)
    (set-equal? (E p b) (E q b))]
   [(neg f)
    (not (F f b))]
   [(wedge f g)
    (and (F f b) (F g b))]
   [(vee f g)
    (or (F f b) (F g b))]
   [(implies f g)
    (if (F f b) (F g b) #t)]
   [(iff f g)
    (not (xor (F f b) (F g b)))]
   [(forall vd* f)
    (or
     (null? vd*)
     (let* ([vd (car vd*)]
            [vd* (cdr vd*)]
            [v (varDecl-v vd)]
            [e (varDecl-e vd)])
       (for/and ([s (in-list (E e b))])
         (F (forall vd* f) (env-update b v s)))))]
   [(exists vd* f)
    (and
     (not (null? vd*))
     (let* ([vd (car vd*)]
            [vd* (cdr vd*)]
            [v (varDecl-v vd)]
            [e (varDecl-e vd)])
       (for/or ([s (in-list (E e b))])
         (F (exists vd* f) (env-update b v s)))))]))

;; (: E (-> Expr Binding Constant))
(define (E e b)
  (match e
   [(var v)
    (env-lookup b v)]
   [(transpose e)
    (map reverse (E e b))]
   [(closure e)
    (transitive-closure (E e b))]
   [(refl e)
    ;; TODO what is p_1 ?
    (set-add
     (E (closure e) b)
     (make-constant (list e e)))]
   [(union p q)
    (set-union (E p b) (E q b))]
   [(intersection p q)
    (set-intersect (E p b) (E q b))]
   [(difference p q)
    (set-subtract (E p b) (E q b))]
   [(join p q)
    (for*/set ([p* (in-set (E p b))]
               [q* (in-set (E q b))])
      (append (drop-right p* 1) (cdr q*)))]
   [(product p q)
    (for*/set ([p* (in-set (E p b))]
               [q* (in-set (E q b))])
      (append p* q*))]
   [(if/else f p q)
    (if (F f b) (E p b) (E q b))]
   [(comprehension vd* f)
    (define-values (s**-rev b+)
      (for/fold ([s** '()]
                 [b b])
                ([vd (in-list vd*)])
        (let* ([v (varDecl-v vd)]
               [e (varDecl-e vd)]
               [s* (E e b)])
          (values (cons s* s**) (⊕ b v s*)))))
    (for/set ([x (cartesian-product (reverse s**-rev))])
      x)]))

;; =============================================================================
;; === Set operations

;; For now, just handle pairs
;; ??? are all the output tuples the same length?
;; (-> (Setof (Listof Atom)) (Setof (Listof Atom)))
(define (transitive-closure p1+p2*)
  ;; Find all paths from all p1's in the list of pairs
  (not-implemented))

(define (xor a b)
  (or (and a (not b))
      (and (not a) b)))

(define (eq?* x*)
  (or (null? x*)
      (let ([x (car x*)])
        (for/and ([y (in-list (cdr x*))])
          (eq? x y)))))

;; =============================================================================
;; === Parsing

(define (relBound# stx)
  (syntax-parse stx
   [(v:id {(lo*-stx:id ...) ...} {(hi*-stx:id ...) ...})
    (define lo* (syntax->datum #'((lo*-stx ...) ...)))
    (define hi* (syntax->datum #'((hi*-stx ...) ...)))
    (define arity (arity=? lo* hi*))
    (relBound (syntax-e #'v) arity lo* hi*)]
   [_ #f]))

(define (formula# stx)
  (syntax-parse stx
   #:datum-literals (no lone one some ⊆ = ¬ ∨ ∧ ⇒ ⇔ ∀ : ∃ ∣)
   [(no e)
    (let ([e (expr# #'e)])
      (and e (no e)))]
   [(lone e)
    (let ([e (expr# #'e)])
      (and e (lone e)))]
   [(one e)
    (let ([e (expr# #'e)])
      (and e (one e)))]
   [(some e)
    (let ([e (expr# #'e)])
      (and e (some e)))]
   [(~or (⊆ e0 e1) (e0 ⊆ e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (subset e0 e1)))]
   [(~or (= e0 e1) (e0 = e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (equal e0 e1)))]
   [(¬ f)
    (let ([f (formula# #'f)])
      (and f (neg f)))]
   [(~or (∧ f0 f1) (f0 ∧ f1))
    (let ([f0 (formula# #'f0)]
          [f1 (formula# #'f1)])
      (and f0 f1 (wedge f0 f1)))]
   [(~or (∨ f0 f1) (f0 ∨ f1))
    (let ([f0 (formula# #'f0)]
          [f1 (formula# #'f1)])
      (and f0 f1 (vee f0 f1)))]
   [(~or (⇒ f0 f1) (f0 ⇒ f1))
    (let ([f0 (formula# #'f0)]
          [f1 (formula# #'f1)])
      (and f0 f1 (implies f0 f1)))]
   [(~or (⇔ f0 f1) (f0 ⇔ f1))
    (let ([f0 (formula# #'f0)]
          [f1 (formula# #'f1)])
      (and f0 f1 (iff f0 f1)))]
   [(∀ v* (~optional ∣) f)
    (let ([v* (varDecls# #'v*)]
          [f (formula# #'f)])
      (and v* f (forall v* f)))]
   [(∃ v* (~optional ∣) f)
    (let ([v* (varDecls# #'v*)]
          [f (formula# #'f)])
      (and v* f (exists v* f)))]
   [_ #f]))

(define (expr# stx)
  (syntax-parse stx
   #:datum-literals (~ ^ * ∪ ∩ ∖ ∙ → ? : ∣)
   [x:id
    (var (syntax-e #'x))]
   [(~ e)
    (let ([e (expr# #'e)])
      (and e (transpose e)))]
   [(^ e)
    (let ([e (expr# #'e)])
      (and e (closure e)))]
   [(* e)
    (let ([e (expr# #'e)])
      (and e (refl e)))]
   [(~or (∪ e0 e1) (e0 ∪ e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (union e0 e1)))]
   [(~or (∩ e0 e1) (e0 ∩ e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (intersection e0 e1)))]
   [(~or (∖ e0 e1) (e0 ∖ e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (difference e0 e1)))]
   [(~or (∙ e0 e1) (e0 ∙ e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (join e0 e1)))]
   [(~or (→ e0 e1) (e0 → e1))
    (let ([e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and e0 e1 (product e0 e1)))]
   [(f ? e0 : e1)
    (let ([f (formula# #'f)]
          [e0 (expr# #'e0)]
          [e1 (expr# #'e1)])
      (and f e0 e1 (if/else f e0 e1)))]
   [(v* ∣ f)
    (let ([v* (varDecls# #'v*)]
          [f (formula# #'f)])
      (and v* f (comprehension v* f)))]
   [_ #f]))

(define (varDecls# stx)
  (syntax-parse stx
   #:datum-literals (:)
   [((v**:id ... : e*) ...)
    (for/fold ([acc '()])
              ([v* (in-list (syntax-e #'((v** ...) ...)))]
               [e (in-list (syntax-e #'(e* ...)))])
      (and acc
        (let ([e+ (expr# e)])
          (and e+
            (let ([v+ (for/list ([v (in-list (syntax-e v*))]) (varDecl (syntax-e v) e+))])
              (append v+ acc))))))]
   [_ #f]))

;; (-> Input-Port Problem)
(define (input-port->problem [source-path #f] [in-port (current-input-port)])
  (define U  (box #f))
  (define B* (box '()))
  (define F* (box '()))
  (let loop ()
    (let ([stx (read in-port)])
      (if (eof-object? stx)
        (void)
        (begin
         (syntax-parse #`#,stx ;; IDK why, but `read-syntax` alone just hangs
          #:datum-literals (universe var fuck)
          [(universe x*:id ...)
           ;; It always feels bad throwing away lexical information
           (set-box! U (make-universe (syntax->datum #'(x* ...))))]
          [(var e* ...)
           (set-box!/parse B* relBound# (syntax-e #'(e* ...)) #:src source-path)]
          [(formula e* ...)
           (set-box!/parse F* formula# (syntax-e #'(e* ...)) #:src source-path)]
          [_
           (parse-warning source-path stx)])
         (loop)))))
  (cond
   [(not (unbox U))
    (parse-error source-path "Failed to parse universe of atoms")]
   [else
    (problem (unbox U) (reverse (unbox B*)) (reverse (unbox F*)))]))

(define (set-box!/parse bx parse# e* #:src source-path)
  (set-box! bx
    (let loop ([e* e*])
      (cond
       [(null? e*)
        (unbox bx)]
       [(parse# (car e*))
        => (lambda (rb) (cons rb (loop (cdr e*))))]
       [else
        (parse-warning source-path (syntax->datum (car e*)))
        (loop (cdr e*))]))))

(define (read-problem [src-path #f] [any (current-input-port)])
  (cond
   [(path-string? any)
    (path-string->problem any)]
   [(input-port? any)
    (input-port->problem src-path any)]
   [else
    (parse-error 'read-problem "Cannot read from source '~a'" any)]))

(define (path-string->problem ps)
  (with-input-from-file ps
    (lambda ()
      (input-port->problem ps))))

;; =============================================================================
;; === Linting / Typechecking

;; TODO need to give source locations in error messages

(require
  (only-in levenshtein string-levenshtein))

(define *EDIT-DISTANCE* (make-parameter 2))

;; (-> Symbol (Setof Symbol) (U #f Symbol))
(define (suggest-var v U)
  (define v-str (symbol->string v))
  (define dist (*EDIT-DISTANCE*))
  (for/first ([u (in-set U)]
              #:when (<= (string-levenshtein v-str (symbol->string u)) dist))
    u))

;; (-> (U #f Symbol) String)
(define (format-suggestion u)
  (if u
    (format " Maybe you meant '~a'?" u)
    ""))

(define-syntax-rule (unbound-variable-error U v)
  (raise-user-error 'kodkod:lint "Variable '~a' is unbound in environment ~a.~a"
    v U (format-suggestion (suggest-var v U))))

(define (lint-problem kk)
  ;; TODO
  ;; - no unbound variables
  ;; -  .;...
  (lint-variables kk)
  (void))

(define (lint-variables kk)
  (define U (problem-universe kk))
  (for ([rb (in-list (problem-bound* kk))])
    (for ([v (in-set (relBound-fvs rb))])
      (unless (set-member? U v)
        (unbound-variable-error U v))))
  (define U+V (set-union U (relBound*-bvs (problem-bound* kk))))
  (for ([f (in-list (problem-formula* kk))])
    (for ([v (in-set (formula-fvs f))])
      (unless (set-member? U+V v)
        (unbound-variable-error (set-union U+V (formula-bvs f #:over (set v))) v))))
  (void))

;; =============================================================================
;; === Bits / Booleans

(struct bool () #:transparent)

(define-syntax-rule (define-bool* [id e] ...)
  (begin (struct id bool e #:transparent) ...))

;; TODO unwrap these?
(define-bool*
  (bzero ())   ;; 0 (constant)
  (bone ())    ;; 1 (constant)
  (bvar (v))   ;; identifier
  (bneg (b))
  (band (b0 b1))
  (bor (b0 b1))
  (bif/else (b0 b1 b2)))

(define-syntax-rule (big-bor for-clause for-body)
  (for/fold ([acc (bzero)])
            for-clause
    (bor acc for-body)))

(define-syntax-rule (big-band for-clause for-body)
  (for/fold ([acc (bone)])
            for-clause
    (band acc for-body)))

(define (b-simplify b)
  'TODO)

;;; =============================================================================
;;; === Bit Matrix
;(require kodkod/private/sparse-sequence)
;
;;; Model relations as matrices of boolean values
;;;
;;; TODO best representation?
;;; - math/matrix (ha ha)
;;; - bitvector library
;;; - integer representation (native bitstrings)
;;; - vector library (track trivial bounds?)
;;; - function
;;; - USE EMINA'S FOR NOW
;
;;; Square, boolean matrix.
;;; Indices are FLAT integers.
;(struct bit-matrix (
;  unsafe-num-columns     ;; Natural
;  unsafe-num-dimensions  ;; Natural
;  cell* ;; (Instance sparse-sequence<%>) ; legal to `instance` an interface?
;) #:transparent )
;
;(define-syntax-rule (mask-null v)
;  (or v (bzero)))
;
;;;; M
;;;; First arg = integer, s raised to the d
;;;; 2nd arg = (idx -> bool) function
;;(define (procedure->bit-matrix cols dim f)
;;  (unless (procedure? f)
;;    ;; TODO use contract
;;    (raise-user-error 'bit-matrix "Can only make matrix from procedures"))
;;  ;; Cache needs abstraction, not sure how to implement now.
;;  ;; What is a matrix anyway? Just a function ?
;;  (bit-matrix cols dim f))
;;
;;(define (tuple->bit-matrix cols dim x*)
;;  (define (ref y*)
;;    (if (tuple=? x* y*)
;;      (bone)
;;      (bzero)))
;;  (procedure->bit-matrix cols dim ref))
;
;(define (bit-matrix-and M . M*)
;  (bit-matrix-map M
;    (lambda (i)
;      (band (bit-matrix-ref M i)
;        (big-band ([m (in-list M*)])
;          (bit-matrix-ref m i))))))
;
;;(define (bit-matrix-choice b M0 M1)
;;  'todo)
;
;(define (bit-matrix-closure M)
;  ;; nope don't udnerstand dimensions
;  (raise-user-error 'closure "not implemented"))
;
;(define (bit-matrix-cross M . M*)
;  ;; TODO error if (null? M*)
;  (match-define (bit-matrix cols dims cell*) M)
;  (bit-matrix cols dims
;    (for/fold ([acc (new tree-sequence%)])
;              ([M2 (in-list M*)])
;      (for ([i (in-dense-index* M)])
;        (define offset (* dims i))
;        (for ([i2 (in-dense-index* M2)])
;          (send acc put (+ offset i2)
;                        (band (bit-matrix-ref M i)
;                              (bit-matrix-ref M2 i2)))))
;      acc)))
;
;;; Set of all indices in M
;;; ⦇ ⦈
;;; Return all non-#f indices
;(define (bit-matrix-dense-index* M)
;  (send (bit-matrix-cell* M) indices))
;
;(define-syntax-rule (in-dense-index* M)
;  (in-list (bit-matrix-dense-index* M)))
;
;;; Not sure what's easier for refs, later
;;; (-> Bit-Matrix (Sequenceof Natural))
;(define (bit-matrix-index* M)
;  '())
;
;(define-syntax-rule (in-index* M)
;  (in-list (bit-matrix-index* M)))
;
;;; Return number of non-#f entries.
;;; (-> BitMatrix Natural)
;(define (bit-matrix-density M)
;  (send (bit-matrix-cell* M) get-size))
;
;(define (bit-matrix-difference M . M*)
;  (bit-matrix-map M
;    (lambda (i)
;      (band (bit-matrix-ref M i)
;        (big-band ([m (in-list M*)])
;          (bneg (bit-matrix-ref m i)))))))
;
;(define (bit-matrix-dot M . M*)
;  (match-define (bit-matrix cols dims cell*) M)
;  ;; TODO I don't even "see" what to do here
;  (raise-user-error 'dot "Not implemented"))
;  ;(bit-matrix cols dims
;  ;  (for/fold ([acc (new tree-sequence%)])
;  ;            ([M2 (in-list M*)])
;  ;    (for ([i (in-dense-index* M)])
;  ;      (define rowHead (* (modulo i b) c))
;  ;      (define rowTail 
;  ;    acc
;
;(define (bit-matrix-equal M . M*)
;  (match-define (bit-matrix cols dims cell*) M)
;  (for/and ([M2 (in-list M*)])
;    (match-define (bit-matrix cols2 dims2 cell2*) M2)
;    (and
;      (= cols cols2)
;      (= dims dims2)
;      (sparse-sequence=? cell* cell2*))))
;
;;;; Return formula that at least one value in M is non-#f
;;(define (bit-matrix-lone M)
;;  'todo)
;
;;; Technically, mapi
;;; (-> Bit-Matrix (-> Index* Bool) Bit-Matrix)
;(define (bit-matrix-map M f)
;  (match-define (bit-matrix cols dims cell*) M)
;  (bit-matrix cols dims
;    (for/fold ([acc (new tree-sequence%)])
;              ([i* (in-index* M)])
;      (send acc put i* (f i*)))))
;
;;(define (bit-matrix-none M)
;;  'todo)
;
;(define (bit-matrix-not M)
;  (bit-matrix-map M (lambda (i*) (bneg (bit-matrix-ref M i*)))))
;
;;(define (bit-matrix-one M)
;;  'todo)
;
;(define (bit-matrix-or M . M*)
;  ;; TODO could shrink this def
;  (bit-matrix-map M
;    (lambda (i*)
;      (bor
;        (bit-matrix-ref M i*)
;        (big-bor ([m (in-list M*)])
;          (bit-matrix-ref m i*))))))
;
;;(define (bit-matrix-override M0 M1)
;;  'todo)
;
;(define (bit-matrix-ref M i)
;  (mask-null (send (bit-matrix-cell* M) ref i)))
;
;(define (bit-matrix-set M i v)
;  (send (bit-matrix-cell* M) put i v))
;
;;(define (bit-matrix-some M)
;;  'todo)
;
;(define (bit-matrix-subset M0 M1)
;  (big-band ([i (in-dense-index* M0)])
;    (bor
;      (bneg (bit-matrix-ref M0 i))
;      (bit-matrix-ref M1 i))))
;
;(define (bit-matrix-transpose M)
;  'todo) ;; Depends on representation
;
;;;; --- TODO ---
;;
;;(define (bit-matrix-size M)
;;  (expt (bit-matrix-s M)
;;        (bit-matrix-d M)))
;;
;;(define bit-matrix-s
;;  bit-matrix-unsafe-num-columns)
;;
;;(define bit-matrix-d
;;  bit-matrix-unsafe-num-dimensions)
;;
;;; =============================================================================
;;; === Problem -> Matrix Translation
;
;(define (translate-problem kk)
;  (define u (problem-universe kk))
;  (define rb* (problem-bound* kk))
;  (define f* (problem-formula* kk))
;  (when (null? f*)
;    (raise-user-error 'translate-problem "Cannot translate problem with no formulas"))
;  (translate-formula
;    (for/fold ([acc (car f*)]
;               [f (in-list (cdr f*))])
;      (wedge acc f))
;    (for/fold ([env (env-init)])
;              ([rb (in-list rb*)])
;      (env-update env (relBound-id rb) (translate-relBound rb u)))))
;
;(define (translate-relBound rb u)
;  (make-bit-matrix
;    (expt (length u) (relBound-arity rb))
;    (lambda (a*)
;      (unless (= (length a*) (relBound-arity rb))
;        (raise-user-error 'matrix "Expected ~a elements, got ~a" arity a*))
;      (let ([a* (if (atom?* a*) a* (index->atom* a*))])
;        (cond
;         [(set-member? (relBound-lo* rb) a*)
;          (bone)]
;         [(set-member? (relBound-hi* rb) a*)
;          (translate-tuple (relBound-id rb) a*)]
;         [else
;          (bzero)])))))
;
;;; TODO would be simpler if variables were not symbolic
;;;  and I could re-use racket's booleans
;(define (translate-formula f env)
;  (match f
;   [(no p)
;    (bneg (translate-formula (some p)) env)]
;   [(lone p)
;    (bor (translate-formula (no p) env)
;         (translate-formula (one p) env))]
;   [(one p)
;    (let ([m (translate-expr p env)])
;      (big-bor ([x* (in-indexes m)])
;        (band (bit-matrix-ref m x*)
;              (big-band ([y* (in-indexes m)]
;                         #:when (not (tuple=? x* y*)))
;                (bneg (bit-matrix-ref m y*)))))))]
;   [(some p)
;    (let ([m (translate-expr p env)])
;      (big-bor ([x* (in-indexes m)])
;        (bit-matrix-ref m x*)))]
;   [(subset e0 e1)
;    (let ([m (bor (bneg (translate-expr p e))
;                  (translate-expr q e))])
;      (big-band ([x* (in-indexes m)])
;        (bit-matrix-ref m x*)))]
;   [(equal e0 e1)
;    (band (translate-formula (subset e0 e1) env)
;          (translate-formula (subset e1 e0) env))]
;   [(neg f)
;    (bneg (translate-formula f env))]
;   [(wedge f0 f1)
;    (band (translate-formula f0 env)
;          (translate-formula f1 env))]
;   [(vee f0 f1)
;    (bor (translate-formula f0 env)
;         (translate-formula f1 env))]
;   [(implies f0 f1)
;    (bor (bneg (translate-formula f0 env))
;         (translate-formula f1 env))]
;   [(iff f0 f1)
;    (let ([r0 (translate-formula f0 env)]
;          [r1 (translate-formula f1 env)])
;      (bor (band r0 r1)
;           (band (bneg r0) (bneg r1))))]
;   [(forall (cons (varDecl v e) vd*) f)
;    (let ([m (translate-expr e env)])
;      (big-band ([x* (in-indexes m)])
;        (bor (bneg (bit-matrix-ref m x*))
;             (translate-formula
;               (forall vd* f)
;               (⊕ env v (tuple->bit-matrix (bit-matrix-size m) x*))))))]
;   [(forall vd* e)
;    (raise-user-error 'translate-formula "Need at least one variable bound in ~a\n" vd*)]
;   [(exists (cons (varDecl v e) vd*) f)
;    (let ([m (translate-expr e env)])
;      (big-bor ([x* (in-indexes m)])
;        (band (bit-matrix-ref m x*)
;              (translate-formula
;                (forall vd* f)
;                (⊕ env v (tuple->bit-matrix (bit-matrix-size m) x*))))))]
;   [(exists vd* f)
;    (raise-user-error 'translate-formula "Need at least one variable bound in ~a\n" vd*)]
;))
;
;(define (translate-expr expr env)
;  (match expr
;   [(var v)
;    (env-lookup env v)]
;   [(transpose e)
;    (bit-matrix-transpose (E e b))]
;   [(closure p)
;    (define m (translate-expr p env))
;    (define s (bit-matrix-s m))
;    (define (sq x i)
;      (if (= i s)
;        x
;        (let ([y (sq x (* i 2))])
;          ;; TODO real formula is `y \/ y * y`
;          ;; boolean join? defined on matrices?
;          (band (bor y y) y))))
;    (sq m 1)]
;   [(refl e)
;    (define m (translate-expr p e))
;    (define size (bit-matrix-size m))
;    (define (ref a*)
;      (if (eq?* a*)
;        (bone)
;        (bzero)))
;    (bor m (bit-matrix size ref))]
;   [(union p q)
;    (bor (translate-expr p env)
;         (translate-expr q env))]
;   [(intersection p q)
;    (band (translate-expr p env)
;          (translate-expr q env))]
;   [(difference p q)
;    (band (translate-expr p env)
;          (bneg (translate-expr q env)))]
;   [(join p q)
;    (bjoin (translate-expr p env)
;           (translate-expr q env))]
;   [(product p q)
;    (bproduct (translate-expr p env)
;              (translate-expr q env))]
;   [(if/else f p q)
;    (define mp (translate-expr p env))
;    (define mq (translate-expr q env))
;    (define (ref x*)
;      (bif/else (translate-formula f env)
;                (bit-matrix-ref mp)
;                (bit-matrix-ref mq)))
;    (procedure->bit-matrix (bit-matrix-s mp) (bit-matrix-d mp) ref)]
;   [(comprehension (cons (varDecl v e) vd*) f)
;    (define m1 (translate-expr e env))
;    (define s (bit-matrix-s m1))
;    (define d (bit-matrix-d m1))
;    (define n (+ 1 (length vd*)))
;    (procedure->bit-matrix s d
;      (lambda (i*)
;        (unless (= (length i*) n)
;          (raise-user-error 'translate-expr:comprehension "Expected ~a-tuple, got ~a" n i*))
;        (define-values (env+ acc)
;          (for/fold ([env+ (⊕ env v (tuple->bit-matrix s d (car i*)))]
;                     [acc (bit-matrix-ref m1 (car i*))])
;                    ([i (in-list (cdr i*))]
;                     [vd (in-list vd*)])
;            (match-define (varDecl v e) vd)
;            (define m (translate-expr e env+))
;            (values (⊕ env+ v (tuple->bit-matrix s d i))
;                    (band m acc))))
;        (band acc (translate-formula f env+)))))]
;   [(comprehension vd* f)
;    (raise-user-error 'translate-expr "Need varDecl in ~aν" expr)]))
;
;;; V(v, a*) = boolVar
;(define (translate-tuple v a*)
;  (raise-user-error 'translate-tuple "not implemented"))
;
;;; =============================================================================
;;; === Compact Boolean Circuit
;
;(struct circuit (
;  V ;; (Setof vertex)
;  E ;; (Setof (Pairof vertex vertex))
;  d ;; TODO
;) #:transparent )
;
;(struct vertex () #:transparent)
;
;(struct operator vertex () #:transparent)
;(struct leaf vertex () #:transparent)
;
;(define-syntax-rule (define-operator* [id e] ...)
;  (begin (struct id operator e #:transparent) ...))
;(define-syntax-rule (define-leaf* [id e] ...)
;  (begin (struct id leaf e #:transparent) ...))
;
;(define-operator*
;  [vand (v*)] ;; (Setof vertex)
;  [vor (v*)] ;; (Setof vertex)
;  [vnot (v)] ;; vertex
;  [vif/else (v0 v1 v2)] ;; vertex vertex vertex
;)
;
;(define-leaf*
;  [vvar (v)] ;; TODO
;  [vtrue ()]
;  [vfalse ()])
;
;;; -----------------------------------------------------------------------------
;
;;; Sec 2.4
;(define *SHARING-DEPTH* (make-parameter 3))
;
;;; Total ordering on vertices
;(define (vertex<? v0 v1)
;  ;; TODO
;  #f)
;
;;; Two operator nodes of the same type must have different children
;;; (??? NO vertex can be simplified to another by applying equivalences from Table 2.1)
;(define (operator=? v0 v1)
;  ;; TODO
;  #f)
;
;;; No binary vertex can be transformed to another by applying associativity
;;;  to d-reachable descendants
;
;(define (operator-vertex* cbc)
;  (for/set ([v (in-set (circuit-V cbc))]
;            #:when (operator? v))
;    v))
;
;(define (leaf-vertex* cbc)
;  (for/set ([v (in-set (circuit-V cbc))]
;            #:when (leaf? v))
;    v))
;
;;; Convert a boolean circuit to a compact boolean circuit
;(define (compactify circ #:depth [d (*SHARING-DEPTH*)]) ;;TODO pick a default
;  (not-implemented))
;
;
;(module+ test
;  ;; Figure 2-7
;
;  (let ([sample-circuit
;         (vand
;           (vor
;             (vor
;               (vand (vvar 'x) (vand (vvar 'y) (vvar 'z)))
;               (vnot (vand (vvar 'w) (vvar 'v)))))
;           (vor
;             (vand (vvar 'w) (vvar 'v))
;             (vnot (vand (vvar 'x) (vvar 'y) (vvar 'z)))))]
;        [d1 ;; CBC, d=1
;         (let ([vx (vvar 'x)]
;               [vy (vvar 'y)]
;               [vz (vvar 'z)]
;               [va (vand (vvar 'v) (vvar 'w))])
;           (vand
;             (vor
;               (vnot va)
;               (vand vx (vand vy vz)))
;             (vor
;               va
;               (vnot (vand vx vy vz)))))]
;        [d2 ;; CBC, d=2
;         (let ([vxyz (vand (vvar 'x) (vvar 'y) (vvar 'z))]
;               [vvw (vand (vvar 'v) (vvar 'w))])
;           (vand
;             (vor vxyz (vnot vvw))
;             (vor vvw (vnot vxyz))))])
;    (check-equal?
;      (compactify sample-circuit #:depth 1)
;      d1)
;    (check-equal?
;      (compactify sample-circuit #:depth 2)
;      d2))
;
;  (let* ([va (vand (vvar 'a) (vvar 'c))]
;         [in
;          (vand
;           (vand
;            (vvar 'd)
;            (vand (vvar 'a) (vvar 'c)))
;           (vand
;            (vvar 'b)
;            (vand (vvar 'a) (vvar 'c))))]
;         [out
;          (vand
;           (vand
;            (vvar 'd)
;            va)
;           (vand
;            (vvar 'b)
;            va))])
;    (check-equal? (compactify in) out))
;
;)
;
;;; =============================================================================
;;; === Greedy Base Partitioning
;
;(define (gbp U C)
;  ;; Condition: C ⊆ U
;  (for/fold ([S (set U)])
;            ([c (in-set X)])
;    (partition c S)))
;
;;; bg: we're all imperative->functional in here
;(define (partition c S)
;  (define k (constant-arity c))
;  (define c-first (for/set ([a* (in-set c)]) (car a*)))
;  (define S+
;    (for/fold ([S+ S])
;              ([s (in-set S)]
;              #:when (and (not (subset? s c-first))
;                          (not (set-empty? (set-intersect s c-first)))))
;      (set-union (set-remove S+ s)
;                 (set (set-intersect s c-first))
;                 (set (set-subtract  s c-first)))))
;  (if (> k 1)
;    (let-values ([(S C)
;           (for ([s (in-set S+)]
;                 #:when (not (set-empty? (set-intersect s c-first))))
;             (let loop ([s s]
;                        [S (set-subtract S+ s)]
;                        [C (set)])
;               (if (set-empty? s)
;                 (values S C)
;                 (let* ([x (set-first s)])
;                        [x-rest (for/set ([a* (in-set c)]) (cdr a*))]
;                        [x-part (for/set ([a (in-set s)]
;                                          #:when (equal? x-rest
;                                                         (for/set ([a* (in-set c)]
;                                                                   #:when (eq? (car a*) a))
;                                                           (cdr a*))))
;                                  a)]
;                        [s (set-subtract s x-part)]
;                        [S (set-union S (set x-part))]
;                        [C (set-union C (set x-rest))])
;                   (loop s S C))))})
;      (for/fold ([S S])
;                ([c (in-set C)])
;        (paritition c S)))
;    S+))
;
;(module+ test
;  ;; Figure 3-5
;  (check-equal?
;    (gbp '(d0 d1 f0 f1 f2) (set (set '(f0) '(f1) '(f2))))
;    (set (set 'd0) (set 'd1) (set 'f0 f1 f2)))
;)

;; =============================================================================
;; === Problem -> SAT

(define-syntax-rule (unbound-atom kk a)
  (raise-user-error 'kodkod "Invalid atom '~a', universe is ~a" a (problem-universe kk)))

(define (atom->index kk a)
  (or (for/first ([u (in-list (problem-universe kk))]
                  [i (in-naturals)]
                  #:when (eq? a u))
        i)
      (unbound-atom kk a)))

(define (atom->index* kk a*)
  (for/list ([a (in-list a*)])
    (atom->index kk a)))

(define (index->atom kk i)
  (or (for/first ([u (in-list (problem-universe kk))]
                  [j (in-naturals)]
                  #:when (= i j))
        u)
      (unbound-atom kk i)))

(define (index->atom* kk i*)
  (for/list ([i (in-list i*)])
    (index->atom kk i)))

;; Convert a problem spec. to SAT
(define (problem->sat kk)
  ;; kodkod->bool
  ;; symmetry-break
  ;; bool->cnf
  ;; model/bool->model/kodkod
  (void))

;; Turn a relational formula to boolean logic
(define (problem->bool kk)
  (void))

;; Transform boolean formula to conjunctive normal form
(define (bool->cnf bool)
  (void))

;; Convert boolean model to a model of the original problem
;; TODO is a model different from a formula?
(define (bool->kodkod bool)
  (void))

;; =============================================================================
;; === SAT Solvers

(require racket/class)

(define *SOLVER-TIMEOUT* (make-parameter 300)) ;; Seconds

(define solver%
  (class* object% (printable<%>)
    (super-new)
    (init-field
     id ;; String
    )
    (field
     [num-clauses 0] ;; Natural
     [num-vars    0] ;; Natural
     [solver     #f] ;; 
     [val*       #f] ;; (U #f (Vectorof TODO)), assign vars to values
    )

    ;; -------------------------------------------------------------------------
    ;; --- printable<%> interface

    (define/public (custom-print port depth)
      (send this custom-display port))

    (define/public (custom-write port)
      (send this custom-display port))

    (define/public (custom-display port)
      (fprintf port "#<solver:~a>" (get-field id this)))

    ;; -----------------------------------------------------------------------------
    ;; ---

    ;; TODO n>=0
    (define/public (add-variables n)
      (set-field! num-vars this (+ n (get-field num-vars this))))

    ;; (-> (Sequenceof Natural) Boolean)
    (define/public (add-clause c)
      'todo)

    (define/public (get-clauses)
      (get-field num-clauses this))

    (define/public (get-variables)
      (get-field num-vars this))

    ;; TODO 0 <= i < this.vars
    (define/public (get-value i)
      (unless (< i (send this get-variables))
        (raise-user-error 'solver "Unbound variable ~a in solver ~a" i this))
      (let ([v* (get-field val* this)])
        (and v*
          (vector-ref v* i))))

    (define/public (solve)
      ;; Open a subprocess, wait until timeout, kill if necessary
      'TODO)

    ;; Frees the memory used by this solver.
    ;; Gross!
    (define/public (free)
      'TODO)
))

;; -----------------------------------------------------------------------------

(define glucose%
  (class solver%
    (super-new)

    ; TODO
))

;; =============================================================================
;; === Minimal Core Extraction (Ch. 4)

;; Recycling Core Extraction
;; Useful for identifying
;; - over-constraints (eliminate good)
;; - weak properties (allow bad)
;; - low analysis bounds
(define (rce)
  (void))
