#lang racket/base


#;(provide (contract-out
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
  ;; --- to-be-replaced
  "predicates.rkt"
  "private/util.rkt"
  ;; --- necessary
  racket/match
  racket/set
  (for-syntax racket/base syntax/parse)
  syntax/parse
  ;; --- maybe not necessary
  (only-in racket/list cartesian-product drop-right)
)

;; =============================================================================

;; -----------------------------------------------------------------------------
;; kodkod = problem
(struct problem (
  universe ;; (Listof Symbol)
  bound*   ;; (Listof Bound)
  formula* ;; (Listof Formula)
))

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

(struct no formula (e))           ;; Empty
(struct lone formula (e))         ;; at most one
(struct one formula (e))          ;; exactly one
(struct some formula (e))         ;; non-empty
(struct subset formula (e0 e1))   ;; subseteq
(struct equal formula (e0 e1))
(struct neg formula (f))
(struct wedge formula (f0 f1))
(struct vee formula (f0 f1))
(struct implies formula (f0 f1))
(struct iff formula (f0 f1))
(struct forall formula (v* f))
(struct exists formula (v* f))

;; -----------------------------------------------------------------------------

(struct expr ())

(struct var expr (v))
(struct transpose expr (e))        ;; ~
(struct closure expr (e))          ;; ^
(struct refl expr (e))             ;; *
(struct union expr (e1 e2))        ;; \cup
(struct intersection expr (e1 e2)) ;; \cap
(struct difference  expr (e1 e2))  ;; \setminus
(struct join  expr (e1 e2))        ;; .
(struct product expr (e1 e2))      ;; \rightarrow
(struct if/else expr (f e1 e2))    ;; f ? e1 : e2
(struct comprehension (v* f))      ;; { v* | f }

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
    (list->set (cartesian-product (reverse s**-rev)))]))

;; -----------------------------------------------------------------------------
;; Set operations

;; For now, just handle pairs
;; ??? are all the output tuples the same length?
;; (-> (Setof (Listof Atom)) (Setof (Listof Atom)))
(define (transitive-closure p1+p2*)
  ;; Find all paths from all p1's in the list of pairs
  (not-implemented))

(define (xor a b)
  (or (and a (not b))
      (and (not a) b)))

;; -----------------------------------------------------------------------------

(define (read-problem any)
  (cond
   [(path-string? any)
    (path-string->problem any)]
   [(input-port? any)
    (input-port->problem any)]
   [else
    (parse-error 'read-problem "Cannot read from source '~a'" any)]))

(define (path-string->problem ps)
  (with-input-from-file ps
    (lambda ()
      (input-port->problem (current-input-port) ps))))

(begin-for-syntax

  (define-syntax-class (kk f)
    #:attributes (value)
    (pattern e
     #:with e+ (f #'e)
     #:when (syntax-e #'e+)
     #:attr value (syntax-e #'e+)))
)

(define (relBound# stx)
  (syntax-parse stx
   [(v:id {(lo*:id ...) ...} {(hi*:id ...) ...})
    (define arity (arity=? (syntax-e #'((lo* ...) ...))
                           (syntax-e #'((hi* ...) ...))))
    (relBound (syntax-e #'v)
              arity
              (syntax->datum #'((lo* ...) ...))
              (syntax->datum #'((hi* ...) ...)))]
   [_ #f]))

(define (kkstx->value* stx)
  (map syntax-e (syntax-e stx)))

(define (formula# stx)
  (syntax-parse stx
   #:datum-literals (no lone one some ⊆ = ¬ ∨ ∧ ⇒ ⇔ ∀ : ∃ ∣)
   [(no e:(kk expr#))
    (no (syntax-e #'e.value))]
   [(lone e:(kk expr#))
    (lone (syntax-e #'e.value))]
   [(one e:(kk expr#))
    (one (syntax-e #'e.value))]
   [(some e:(kk expr#))
    (some (syntax-e #'e.value))]
   [(⊆ e*:(kk expr#) ...)
    (apply subset (kkstx->value* #'e*))]
   [(= e*:(kk expr#) ...)
    (apply equal (kkstx->value* #'e*))]
;   [(¬ f:(kk formula#))
;    (neg (syntax-e #'f.value))]
;   [(∧ f0:(kk formula#) f1:(kk formula#))
;    (wedge (syntax-e #'f0.value) (syntax-e #'f1.value))]
;   [(∨ f0:(kk formula#) f1:(kk formula#))
;    (vee (syntax-e #'f0.value) (syntax-e #'f1.value))]
;   [(⇒ f0:(kk formula#) f1:(kk formula#))
;    (implies (syntax-e #'f0.value) (syntax-e #'f1.value))]
;   [(⇔ f0:(kk formula#) f1:(kk formula#))
;    (iff (syntax-e #'f0.value) (syntax-e #'f1.value))]
;   [(∀ v*:(kk varDecls#) ∣ f:(kk formula#))
;    (forall (syntax-e #'v*.value) (syntax-e #'f.value))]
;   [(∃ v*:(kk varDecls#) ∣ f:(kk formula#))
;    (exists (syntax-e #'v*.value) (syntax-e #'f.value))]
   [_ #f]))

(define (expr# stx)
  (syntax-parse stx
   #:datum-literals (~ ^ * ∪ ∩ ∖ ∙ → ? : ∣)
   [x:id
    (var (syntax-e #'x))]
   [(~ e:(kk expr#))
    (transpose (syntax-e #'e.value))]
   [(^ e:(kk expr#))
    (closure (syntax-e #'e.value))]
   [(* e:(kk expr#))
    (refl (syntax-e #'e.value))]
   [(∪ e*:(kk expr#) ...)
    (apply union (kkstx->value* #'e*))]
   [(∩ e*:(kk expr#) ...)
    (apply intersection (kkstx->value* #'e*))]
;   [(∖ e0:(kk expr#) e1:(kk expr#))
;    (difference (syntax-e #'e0.value) (syntax-e #'e1.value))]
;   [(∙ e0:(kk expr#) e1:(kk expr#))
;    (join (syntax-e #'e0.value) (syntax-e #'e1.value))]
;   [(→ e0:(kk expr#) e1:(kk expr#))
;    (product (synta-e #'e0.value) (syntax-e #'e1.value))]
;   [(f:(kk formula#) ? e0:(kk expr#) : e1:(kk expr#))
;    (if/else (syntax-e #'f.value) (syntax-e #'e0.value) (syntax-e #'e1.value))]
;   [(v*:(kk varDecls#) ∣ f:(kk formula#))
;    (comprehension (syntax-e #'v*.value) (syntax-e #'f.value))]
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
(define (input-port->problem in-port [source-name #f])
  (define U  (box #f))
  (define B* (box '()))
  (define F* (box #f))
  (let loop ()
    (let ([stx (read-syntax in-port)])
      (if (eof-object? stx)
        (void)
        (begin
         (syntax-parse stx
          #:datum-literals (universe var formula)
          [((~optional universe) x*:id ...)
           ;; It always feels bad throwing away lexical information
           (set-box! U (syntax->datum #'(x* ...)))]
          [((~optional var) e* ...)
           #:with rb* (map relBound# (syntax-e #'(e* ...)))
           #:when (andmap syntax-e (syntax-e #'rb*))
           (set-box! B* (append (syntax-e #'rb*) (unbox B*)))]
          [((~optional formula) e* ...)
           #:with f* (map formula# (syntax-e #'(e* ...)))
           #:when (andmap syntax-e (syntax-e #'f*))
           (set-box! F* (append (syntax-e #'f*) (unbox F*)))]
          [_
           (parse-warning 'input-port->problem stx)])
         (loop)))))
  (cond
   [(not (unbox U))
    (parse-error 'input-port->problem "Failed to parse universe of atoms")]
   [else
    (problem (unbox U) (unbox B*) (unbox F*))]))

