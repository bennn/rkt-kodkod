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

#;(provide
  read-problem
  ;; (-> Any Problem)

  lint-problem
  ;; (-> Problem Void)

  format-problem
  ;; (-> Problem String)
  ;; Pretty printing

 #;(contract-out
  make-problem

  (make-kk:relBound
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
  kodkod/private/ast
  kodkod/private/exceptions
  kodkod/private/predicates
  kodkod/private/parameters

  racket/match
  racket/set
  ;(for-syntax racket/base syntax/parse)

  syntax/parse
  (only-in racket/list drop-right cartesian-product)
)

;; =============================================================================
;; === Parsing

(define (kk:relBound# stx)  ;; Syntax -> (U #f RelBound)
  (syntax-parse stx
   [(v:id {(lo*-stx:id ...) ...} {(hi*-stx:id ...) ...})
    (define lo* (syntax->datum #'((lo*-stx ...) ...)))
    (define hi* (syntax->datum #'((hi*-stx ...) ...)))
    (define arity (arity=? lo* hi*))
    (kk:relBound (syntax-e #'v) arity lo* hi*)]
   [_ #f]))

(define (kk:formula# stx)  ;; Syntax -> (U #f Formula)
  (syntax-parse stx
   #:datum-literals (no lone one some ⊆ = ¬ ∨ ∧ ⇒ ⇔ ∀ : ∃ ∣)
   [(no e)
    (let ([e (kk:expr# #'e)])
      (and e (f:no e)))]
   [(lone e)
    (let ([e (kk:expr# #'e)])
      (and e (f:lone e)))]
   [(one e)
    (let ([e (kk:expr# #'e)])
      (and e (f:one e)))]
   [(some e)
    (let ([e (kk:expr# #'e)])
      (and e (f:some e)))]
   [(~or (⊆ e0 e1) (e0 ⊆ e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (f:subset e0 e1)))]
   [(~or (= e0 e1) (e0 = e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (f:equal e0 e1)))]
   [(¬ f)
    (let ([f (kk:formula# #'f)])
      (and f (f:neg f)))]
   [(~or (∧ f0 f1) (f0 ∧ f1))
    (let ([f0 (kk:formula# #'f0)]
          [f1 (kk:formula# #'f1)])
      (and f0 f1 (f:wedge f0 f1)))]
   [(~or (∨ f0 f1) (f0 ∨ f1))
    (let ([f0 (kk:formula# #'f0)]
          [f1 (kk:formula# #'f1)])
      (and f0 f1 (f:vee f0 f1)))]
   [(~or (⇒ f0 f1) (f0 ⇒ f1))
    (let ([f0 (kk:formula# #'f0)]
          [f1 (kk:formula# #'f1)])
      (and f0 f1 (f:implies f0 f1)))]
   [(~or (⇔ f0 f1) (f0 ⇔ f1))
    (let ([f0 (kk:formula# #'f0)]
          [f1 (kk:formula# #'f1)])
      (and f0 f1 (f:iff f0 f1)))]
   [(∀ v* (~optional ∣) f)
    (let ([v* (kk:varDecls# #'v*)]
          [f (kk:formula# #'f)])
      (and v* f (f:forall v* f)))]
   [(∃ v* (~optional ∣) f)
    (let ([v* (kk:varDecls# #'v*)]
          [f (kk:formula# #'f)])
      (and v* f (f:exists v* f)))]
   [_ #f]))

(define (kk:expr# stx)  ;; Syntax -> (U #f Expr)
  (syntax-parse stx
   #:datum-literals (~ ^ * ∪ ∩ ∖ ∙ → ? : ∣)
   [x:id
    (e:var (syntax-e #'x))]
   [(~ e)
    (let ([e (kk:expr# #'e)])
      (and e (e:transpose e)))]
   [(^ e)
    (let ([e (kk:expr# #'e)])
      (and e (e:closure e)))]
   [(* e)
    (let ([e (kk:expr# #'e)])
      (and e (e:refl e)))]
   [(~or (∪ e0 e1) (e0 ∪ e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (e:union e0 e1)))]
   [(~or (∩ e0 e1) (e0 ∩ e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (e:intersection e0 e1)))]
   [(~or (∖ e0 e1) (e0 ∖ e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (e:difference e0 e1)))]
   [(~or (∙ e0 e1) (e0 ∙ e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (e:join e0 e1)))]
   [(~or (→ e0 e1) (e0 → e1))
    (let ([e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and e0 e1 (e:product e0 e1)))]
   [(f ? e0 : e1)
    (let ([f (kk:formula# #'f)]
          [e0 (kk:expr# #'e0)]
          [e1 (kk:expr# #'e1)])
      (and f e0 e1 (e:if/else f e0 e1)))]
   [(v* ∣ f)
    (let ([v* (kk:varDecls# #'v*)]
          [f (kk:formula# #'f)])
      (and v* f (e:comprehension v* f)))]
   [_ #f]))

(define (kk:varDecls# stx)
  (syntax-parse stx
   #:datum-literals (:)
   [((v**:id ... : e*) ...)
    (for/fold ([acc '()])
              ([v* (in-list (syntax-e #'((v** ...) ...)))]
               [e (in-list (syntax-e #'(e* ...)))])
      (and acc
        (let ([e+ (kk:expr# e)])
          (and e+
            (let ([v+ (for/list ([v (in-list (syntax-e v*))]) (kk:varDecl (syntax-e v) e+))])
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
         (syntax-parse #`#,stx ;; TODO `read-syntax` alone just hangs
          #:datum-literals (universe var formula)
          [((~optional universe) x*:id ...)
           ;; It always feels bad throwing away lexical information
           (set-box! U (kk:universe (syntax->datum #'(x* ...))))]
          [((~optional var) name:id lo hi)
           (set-box!/parse B* kk:relBound# (list #'(name lo hi)) #:src source-path)]
          [(formula e* ...)
           (set-box!/parse F* kk:formula# (syntax-e #'(e* ...)) #:src source-path)]
          [_
           (parse-warning source-path stx)])
         (loop)))))
  (cond
   [(not (unbox U))
    (parse-error source-path "Failed to parse universe of atoms")]
   [else
    (kk:problem (unbox U) (reverse (unbox B*)) (reverse (unbox F*)))]))

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
  (define U (kk:problem-universe kk))
  (for ([rb (in-list (kk:problem-bound* kk))])
    (for ([v (in-set (kk:relBound-fvs rb))])
      (unless (set-member? U v)
        (unbound-variable-error U v))))
  (define U+V (set-union U (kk:relBound*-bvs (kk:problem-bound* kk))))
  (for ([f (in-list (kk:problem-formula* kk))])
    (for ([v (in-set (kk:formula-fvs f))])
      (unless (set-member? U+V v)
        (unbound-variable-error (set-union U+V (kk:formula-bvs f #:over (set v))) v))))
  (void))


