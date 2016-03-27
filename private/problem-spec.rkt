#lang racket/base

;; TODO
;; - stop ignoring syntax information?
;; - compile forall/exists to lambdas, re-use Racket's identifier management
;; - atoms in tuples must be ordered by universe


(provide
  read-problem
  ;; (-> Any Problem)

  lint-problem
  ;; (-> Problem Void)


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

  (only-in racket/list drop-right)
)

;; =============================================================================
;; === STRUCTS

;; kodkod = problem
(struct problem (
  universe ;; (Listof Symbol)
  bound*   ;; (Listof Bound)
  formula* ;; (Listof Formula)
) #:transparent )

;; -----------------------------------------------------------------------------
;; universe = listof symbol = listof atom

(define (make-universe sym*)
  sym*)

;; -----------------------------------------------------------------------------

;; TODO
;; - give vars explicit arity? can just infer from the inputs
;; - can lo* / hi* be empty?

(struct relBound (
  id  ;; Symbol
  arity ;; Natural
  lo* ;; Constant
  hi* ;; Constant
) #:transparent
)

(define (make-relBound id lo* hi*)
  ;; TODO check that all elements of lo* and hi* have the same length.
  ;; length can be anything, but needs to be uniform
  (when (null? lo*)
    (internal-error 'make-relBound "Bad argument 'lo*' = ~a\n" lo*))
  (relBound id (length (car lo*)) lo* hi*))

;; -----------------------------------------------------------------------------

;; TODO ignores the conditions from { tuple+ } | {}+
;; (define-type Constant (Setof Tuple))

(define (make-constant . tuple*)
  (list->set tuple*))

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

;; -----------------------------------------------------------------------------

(struct expr () #:transparent)

(define-syntax-rule (define-expr* [id e] ...)
  (begin (struct id expr e #:transparent) ...))

(define-expr*
  (var (v))
  (transpose (e))        ;; ~
  (closure (e))          ;; ^
  (refl (e))             ;; *
  (union (e1 e2))        ;; \cup
  (intersection (e1 e2)) ;; \cap
  (difference  (e1 e2))  ;; \setminus
  (join  (e1 e2))        ;; .
  (product (e1 e2))      ;; \rightarrow
  (if/else (f e1 e2))    ;; f ? e1 : e2
  (comprehension (v* f)))     ;; { v* | f }

;; -----------------------------------------------------------------------------
;; varDecls = (Listof (Pairof Var Expr))

;; (v : e)
(struct varDecl (v e))


;; -----------------------------------------------------------------------------
;; Bindings

;; (define-type Binding (HashTable Symbol Constant))

(define (lookup b v)
  (hash-ref b v (lambda () (raise-user-error 'lookup))))

(define (update b v s)
  (hash-set b v s))

(define ⊕ update) ;; \oplus

;; -----------------------------------------------------------------------------
;; ---

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
  (let ([bv (lookup b (relBound-id r))])
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
         (F (forall vd* f) (update b v s)))))]
   [(exists vd* f)
    (and
     (not (null? vd*))
     (let* ([vd (car vd*)]
            [vd* (cdr vd*)]
            [v (varDecl-v vd)]
            [e (varDecl-e vd)])
       (for/or ([s (in-list (E e b))])
         (F (exists vd* f) (update b v s)))))]))

;; (: E (-> Expr Binding Constant))
(define (E e b)
  (match e
   [(var v)
    (lookup b v)]
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
    (for/set ([x (in-product (reverse s**-rev) 2)])
      x)))

;; =============================================================================
;; === Set operations

(define (in-product x* n)
  (unless (= n 2)
    (raise-user-error 'in-product "Not implemented unless n=2"))
  (cartesian-product x*))

;; For now, just handle pairs
;; ??? are all the output tuples the same length?
;; (-> (Setof (Listof Atom)) (Setof (Listof Atom)))
(define (transitive-closure p1+p2*)
  ;; Find all paths from all p1's in the list of pairs
  (not-implemented))

(define (xor a b)
  (or (and a (not b))
      (and (not a) b)))

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
    (define e (expr# #'e))
    (and e (no e))]
   [(lone e)
    (define e (expr# #'e))
    (and e (lone e))]
   [(one e)
    (define e (expr# #'e))
    (and e (one e))]
   [(some e)
    (define e (expr# #'e))
    (and e (some e))]
   [(~or (⊆ e0 e1) (e0 ⊆ e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (subset e0 e1))]
   [(~or (= e0 e1) (e0 = e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (equal e0 e1))]
   [(¬ f)
    (let ([f (formula# #'f)])
      (and f (neg f)))]
   [(~or (∧ f0 f1) (f0 ∧ f1))
    (define f0 (formula# #'f0))
    (define f1 (formula# #'f1))
    (and f0 f1 (wedge f0 f1))]
   [(~or (∨ f0 f1) (f0 ∨ f1))
    (define f0 (formula# #'f0))
    (define f1 (formula# #'f1))
    (and f0 f1 (vee f0 f1))]
   [(~or (⇒ f0 f1) (f0 ⇒ f1))
    (define f0 (formula# #'f0))
    (define f1 (formula# #'f1))
    (and f0 f1 (implies f0 f1))]
   [(~or (⇔ f0 f1) (f0 ⇔ f1))
    (define f0 (formula# #'f0))
    (define f1 (formula# #'f1))
    (and f0 f1 (iff f0 f1))]
   [(∀ v* (~optional ∣) f)
    (let ([v* (varDecls# #'v*)]
          [f (formula# #'f)])
      (and v* f (forall v* f)))]
   [(∃ v* ∣ f)
    (define v* (varDecls# #'v*))
    (define f (formula# #'f))
    (and v* f (exists v* f))]
   [_ #f]))

(define (expr# stx)
  (syntax-parse stx
   #:datum-literals (~ ^ * ∪ ∩ ∖ ∙ → ? : ∣)
   [x:id
    (var (syntax-e #'x))]
   [(~ e)
    (define e (expr# #'e))
    (and e (transpose e))]
   [(^ e)
    (define e (expr# #'e))
    (and e (closure e))]
   [(* e)
    (define e (expr# #'e))
    (and e (refl e))]
   [(~or (∪ e0 e1) (e0 ∪ e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (union e0 e1))]
   [(~or (∩ e0 e1) (e0 ∩ e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (intersection e0 e1))]
   [(~or (∖ e0 e1) (e0 ∖ e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (difference e0 e1))]
   [(~or (∙ e0 e1) (e0 ∙ e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (join e0 e1))]
   [(~or (→ e0 e1) (e0 → e1))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and e0 e1 (product e0 e1))]
   [(f ? e0 : e1)
    (define f (formula# #'f))
    (define e0 (expr# #'e0))
    (define e1 (expr# #'e1))
    (and f e0 e1 (if/else f e0 e1))]
   [(v* ∣ f)
    (define v* (varDecls# #'v*))
    (define f (formula# #'f))
    (and v* f (comprehension v* f))]
   [_ #f]))

(define (varDecls# stx)
  (syntax-parse stx
   #:datum-literals (:)
   [((v*:id : e*) ...)
    (define vd*
      (for/list ([v (in-list (syntax-e #'(v* ...)))]
                 [e (in-list (syntax-e #'(e* ...)))])
        (define e+ (expr# e))
        (and e+ (cons (syntax-e v) e+))))
    (and (for/and ([vd (in-list vd*)]) vd) vd*)]
   [_ #f]))

;; (-> Input-Port Problem)
(define (input-port->problem [source-path #f] [in-port (current-input-port)])
  (define U  (box #f))
  (define B* (box '()))
  (define F* (box #f))
  (let loop ()
    (let ([stx (read in-port)])
      (if (eof-object? stx)
        (void)
        (begin
         (syntax-parse #`#,stx ;; IDK why, but `read-syntax` alone just hangs
          #:datum-literals (universe var fuck)
          [(universe x*:id ...)
           ;; It always feels bad throwing away lexical information
           (set-box! U (syntax->datum #'(x* ...)))]
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
    (problem (unbox U) (unbox B*) (unbox F*))]))

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

(define (lint-problem kk)
  ;; TODO
  ;; - no unbound variables
  ;; -  .;...
  (void))

;; =============================================================================
;; === Bit Matrix
;; Model relations as matrices of boolean values
;;
;; TODO best representation?
;; - math/matrix (ha ha)
;; - bitvector library
;; - integer representation (native bitstrings)
;; - vector library (track trivial bounds?)
;; - function

;(provide
;  relBound->matrix
;)

(define (relBound->matrix kk rb)
  (bit-matrix
    (lambda (a*)
      (unless (= (length a*) (relBound-arity rb))
        (raise-user-error 'matrix "Expected ~a elements, got ~a" arity a*))
      (let ([a* (if (atom?* a*) a* (index->atom* a*))])
        (cond
         [(set-member? (relBound-lo* rb) a*)
          1]
         [(set-member? (relBound-hi* rb) a*)
          (\Nu v a*)] ;; TODO
         [else
          0])))))

(define (bit-matrix f)
  (unless (procedure? f)
    (raise-user-error 'bit-matrix "Can only make matrix from procedures"))
  ;; Cache needs abstraction, not sure how to implement now.
  ;; What is a matrix anyway? Just a function ?
  (void))


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
        u))
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

;; Break symmetries
(define (break-symmetries bool)
  (void))


;; Transform boolean formula to conjunctive normal form
(define (bool->cnf bool)
  (void))

;; Convert boolean model to a model of the original problem
;; TODO is a model different from a formula?
(define (bool->kodkod bool)
  (void))

