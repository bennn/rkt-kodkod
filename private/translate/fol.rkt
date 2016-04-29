#lang racket/base

;; fol = first order logic

;; Convert first-order-logic to an internal representation

;; Originally `kodkod.engine.fol2sat.FOL2BoolTranslator`
;;  which was parameterized over a leaf interpreter
;;  and made a "boolean formula or matrix"

;; ? BooleanMatrix approximate
;; ? visit(Relation relation)

(provide
  kk:problem->kk:bool
)

(require
  kodkod/private/ast
  kodkod/private/bool
  kodkod/private/bitmatrix
  (only-in kodkod/private/dimensions
    make-dimensions
    universe->dimensions)
  kodkod/private/environment
  kodkod/private/translate/translation-cache

  racket/match
)

;; =============================================================================

(define *current-universe* (make-parameter #f))
;(define *current-bounds* (make-parameter #f))
(define *current-cache* (make-parameter #f))
(define *current-env* (make-parameter #f))

(define (universe->env [U0 #f])
  (define U (*current-universe*))
  (define D (universe->dimensions U))
  (for/fold ([b (env-init)])
            ([v (in-universe U)]
             [i (in-naturals)])
    (printf "ENV adding val for key '~a'\n" v)
    (env-put b v (var->bitmatrix D i))))

(define (bounds->env B*)
  (define U (*current-universe*))
  (define size (universe-size U))
  (for/fold ([b (env-init)])
            ([rb (in-list B*)])
    (match-define (kk:relBound id arity lo* hi*) rb)
    (define D (make-dimensions (for/list  ([_i (in-range size)]) arity)))
    (define M (bitmatrix-bot D))
    ;; -- populate M, using lo* and hi*
    ;; -- see Section 2.2.1 of dissertation
    (env-put b id M)))

(define (kk:problem->kk:bool kk)
  (define C (make-cache))
  (define U (kk:problem-universe kk))
  (define B* (kk:problem-bound* kk))
  (define F* (kk:problem-formula* kk))
  (parameterize* ([*current-universe* U]
                  [*current-cache* C]
                  [*current-env* (universe->env)]
                  [*current-env* (env-union (*current-env*)
                                            (bounds->env B*))])
    (kk:formula*->kk:bool F*)))

(define (kk:formula*->kk:bool F*)
  (for/fold ([acc (make-b:one)])
            ([F (in-list F*)])
    (make-b:and acc (kk:formula->kk:bool F))))

(define (kk:formula->kk:bool F)
  (match-kk:formula F
   [(f:no e)
    (bitmatrix-none
      (kk:expr->bitmatrix e))]
   [(f:lone e)
    (bitmatrix-lone
      (kk:expr->bitmatrix e))]
   [(f:one e)
    (bitmatrix-one
      (kk:expr->bitmatrix e))]
   [(f:some e)
    (bitmatrix-some
      (kk:expr->bitmatrix e))]
   [(f:subset e0 e1)
    (bitmatrix-subset
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(f:equal e0 e1)
    (bitmatrix=?
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(f:neg f)
    (make-b:neg
      (kk:formula->kk:bool f))]
   [(f:wedge f0 f1)
    (make-b:and
      (kk:formula->kk:bool f0)
      (kk:formula->kk:bool f1))]
   [(f:vee f0 f1)
    (make-b:or
      (kk:formula->kk:bool f0)
      (kk:formula->kk:bool f1))]
   [(f:implies f0 f1)
    (make-b:implies
      (kk:formula->kk:bool f0)
      (kk:formula->kk:bool f1))]
   [(f:iff f0 f1)
    (make-b:iff
      (kk:formula->kk:bool f0)
      (kk:formula->kk:bool f1))]
   [(f:forall v* f)
    (match v*
     ['()
      (make-b:one)]
     [(cons v v*)
      (raise-user-error 'forall->bool "Not implemented")
      ;(define e+ (kk:varDecl->bitmatrix v))
      ;(for/fold ([M (bitmatrix-one (universe-size (*current-universe*)))])
      ;          ([s (in-bitmatrix e+)]) ;; -- WHAT IS THIS
      ;  (bitmatrix-and M
      ;    (parameterize ([*current-env* (env-put (*current-env*) v s)])
      ;      (kk:formula->bitmatrix (f:forall v* f)))))
      ])]
   [(f:exists v* f)
    (raise-user-error 'exists->bool "Not implemented")]
))

(define (kk:expr->bitmatrix E)
  (match-kk:expr E
   [(e:var v)
    (env-ref (*current-env*) v)]
   [(e:transpose e)
    (bitmatrix-transpose
      (kk:expr->bitmatrix e))]
   [(e:closure e)
    (bitmatrix-closure
      (kk:expr->bitmatrix e))]
   [(e:refl e)
    (bitmatrix-or
      (bitmatrix-identity (universe->dimensions (*current-universe*)))
      (bitmatrix-closure (kk:expr->bitmatrix e)))]
   [(e:union e0 e1)
    (bitmatrix-or
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:intersection e0 e1)
    (bitmatrix-and
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:difference e0 e1)
    (bitmatrix-difference
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:join e0 e1)
    (bitmatrix-dot
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:product e0 e1)
    (bitmatrix-cross
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:if/else f e0 e1)
    (bitmatrix-choice
      (kk:formula->kk:bool f)
      (kk:expr->bitmatrix e0)
      (kk:expr->bitmatrix e1))]
   [(e:comprehension v* f)
    (raise-user-error 'comprehension-not-implemented)]
   ; (for/fold ([TODO])
   ;           ([ (in- (kk:varDecl*->bitmatrix v*))])
   ;   TODO)
))

(define (kk:varDecl*->bitmatrix V*)
  (for/list ([V (in-list V*)])
    (kk:varDecl->bitmatrix V)))

(define (kk:varDecl->bitmatrix V)
  (define v (kk:varDecl-v V))
  (define e (kk:varDecl-e V))
  (assert-universe-contains? (*current-universe*) v)
  (kk:expr->bitmatrix e))


