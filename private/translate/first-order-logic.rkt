#lang racket/base

;; Originally `kodkod.engine.fol2sat.FOL2BoolTranslator`
;;  which was parameterized over a leaf interpreter
;;  and made a "boolean formula or matrix"

;; ? BooleanMatrix approximate
;; ? visit(Relation relation)

(provide
  kk:problem->bitmatrix
)

(require
  kodkod/private/ast
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

(define (kk:problem->bitmatrix kk)
  (define C (make-cache))
  (define U (kk:problem-universe kk))
  (define B* (kk:problem-bound* kk))
  (define F* (kk:problem-formula* kk))
  (parameterize* ([*current-universe* U]
                  [*current-cache* C]
                  [*current-env* (universe->env)]
                  [*current-env* (env-union (*current-env*)
                                            (bounds->env B*))])
    (kk:formula*->bitmatrix F*)))

(define (kk:formula*->bitmatrix F*)
  (for/fold ([acc (bitmatrix-top (universe->dimensions (*current-universe*)))])
            ([F (in-list F*)])
    (bitmatrix-and acc (kk:formula->bitmatrix F))))

(define (kk:formula->bitmatrix F)
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
    (bitmatrix-negate
      (kk:formula->bitmatrix f))]
   [(f:wedge f0 f1)
    (bitmatrix-and
      (kk:formula->bitmatrix f0)
      (kk:formula->bitmatrix f1))]
   [(f:vee f0 f1)
    (bitmatrix-or
      (kk:formula->bitmatrix f0)
      (kk:formula->bitmatrix f1))]
   [(f:implies f0 f1)
    (bitmatrix-implies
      (kk:formula->bitmatrix f0)
      (kk:formula->bitmatrix f1))]
   [(f:iff f0 f1)
    (bitmatrix-iff
      (kk:formula->bitmatrix f0)
      (kk:formula->bitmatrix f1))]
   [(f:forall v* f)
    (match v*
     ['()
      (bitmatrix-one (universe-size (*current-universe*)))]
     [(cons v v*)
      (define e+ (kk:varDecl->bitmatrix v))
      (for/fold ([M (bitmatrix-one (universe-size (*current-universe*)))])
                ([s (in-bitmatrix e+)]) ;; -- WHAT IS THIS
        (bitmatrix-and M
          (parameterize ([*current-env* (env-put (*current-env*) v s)])
            (kk:formula->bitmatrix (f:forall v* f)))))])]
   [(f:exists v* f)
    (raise-user-error 'exists->bitmatrix "Not implemented")]
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
    (bitmatrix-choice ;; formula choice?
      (kk:formula->bitmatrix f)
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


