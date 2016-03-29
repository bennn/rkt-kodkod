#lang racket/base

;; TODO
;; - stop ignoring syntax information?
;; - compile forall/exists to lambdas, re-use Racket's identifier management
;; - atoms in tuples must be ordered by universe
;; - sparse tree representation (2.2.2)

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

(define (tuple=? x* y*)
  (let ([x*-nil (null? x*)]
        [y*-nil (null? y*)])
    (cond
     [(and x*-nil y*-nil)
      #t]
     [(or x*-nil y*-nil)
      #f]
     [else
      (and (symbol=? (car x*) (car y*))
           (tuple=? (cdr x*) (cdr y*)))])))

(define symbol=? eq?)

(define (make-constant . tuple*)
  (list->set tuple*))

(define (constant-arity c)
  (length (set-first c)))

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

(define (env-init)
  (hasheq))

(define (env-lookup b v)
  (hash-ref b v (lambda () (raise-user-error 'lookup))))

(define (env-update b v s)
  (hash-set b v s))

(define ⊕ env-update) ;; \oplus

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
    (for/set ([x (in-product (reverse s**-rev) 2)])
      x)]))

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
   ;; TODO allow (a b : T) ...
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
;; === Printing

(define INDENT (make-string 6 #\space))

(define (format-problem kk)
  (format "(problem\n  U = ~a\n  B = ~a\n  F = ~a\n)"
    (format-universe (problem-universe kk))
    (map format-relBound (problem-bound* kk))
    (map format-formula (problem-formula* kk))))

(define (format-universe u)
  u)

(define (format-relBound rb)
  (format "[~a :~a ~a ~a]\n~a"
    (relBound-id rb)
    (relBound-arity rb)
    (relBound-lo* rb)
    (relBound-hi* rb)
    INDENT))

(define (format-formula f)
  (format "~a\n~a" f INDENT))

;; =============================================================================
;; === Linting / Typechecking

(define (lint-problem kk)
  ;; TODO
  ;; - no unbound variables
  ;; -  .;...
  (void))

;;; =============================================================================
;;; === Bits / Booleans
;
;(struct bool () #:transparent)
;
;(define-syntax-rule (define-bool* [id e] ...)
;  (begin (struct id bool e #:transparent) ...))
;
;;; TODO unwrap these?
;(define-bool*
;  (bzero ())   ;; 0
;  (bone ())    ;; 1
;  (bvar (v))   ;; identifier
;  (bneg (b))
;  (band (b0 b1))
;  (bor (b0 b1))
;  (bjoin (b0 b1)) ;; ∙, dot product
;  (bproduct (b0 b1)) ;; ×, cross product
;  (bif/else (b0 b1 b2)))
;
;(define-syntax-rule (big-bor for-clause for-body)
;  (for/fold ([acc (bzero)])
;            for-clause
;    (bor acc for-body)))
;
;(define-syntax-rule (big-band for-clause for-body)
;  (for/fold ([acc (bone)])
;            for-clause
;    (band acc for-body)))
;
;;; =============================================================================
;;; === Bit Matrix
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
;(struct bit-matrix (
;  unsafe-num-columns     ;; Natural
;  unsafe-num-dimensions  ;; Natural
;  unsafe-proc            ;; (-> idx bool)
;) #:transparent )
;
;;; M
;;; First arg = integer, s raised to the d
;;; 2nd arg = (idx -> bool) function
;(define (procedure->bit-matrix cols dim f)
;  (unless (procedure? f)
;    ;; TODO use contract
;    (raise-user-error 'bit-matrix "Can only make matrix from procedures"))
;  ;; Cache needs abstraction, not sure how to implement now.
;  ;; What is a matrix anyway? Just a function ?
;  (bit-matrix cols dim f))
;
;(define (tuple->bit-matrix cols dim x*)
;  (define (ref y*)
;    (if (tuple=? x* y*)
;      (bone)
;      (bzero)))
;  (procedure->bit-matrix cols dim ref))
;
;;; Set of all indices in M
;;; ⦇ ⦈
;(define (bit-matrix-index* M)
;  'todo)
;
;(define-syntax-rule (in-indexes m)
;  (in-list (bit-matrix-index* M)))
;
;;; Size of `dimension-size^(# dimensions)`
;;; ⟦ ⟧
;(define (bit-matrix-size M)
;  (expt (bit-matrix-s M)
;        (bit-matrix-d M)))
;
;(define bit-matrix-s
;  bit-matrix-unsafe-num-columns)
;
;(define bit-matrix-d
;  bit-matrix-unsafe-num-dimensions)
;
;;; [ ]
;(define (bit-matrix-ref M x*)
;  ((bit-matrix-unsafe-proc M) x*))
;
;(define (bit-matrix-transpose M)
;  (define f (bit-matrix-unsafe-proc M))
;  (bit-matrix (bit-matrix-size M)
;    (lambda (x) (bneg (f x)))))
;
;;; -----------------------------------------------------------------------------
;
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
;; === Minimal Core Extraction (Ch. 4)

;; Recycling Core Extraction
;; Useful for identifying
;; - over-constraints (eliminate good)
;; - weak properties (allow bad)
;; - low analysis bounds
(define (rce)
  (void))
