#lang racket/base

;; TODO

(require kodkod/private/predicates)
(provide (contract-out
  (bool-negate
   (-> bool/simpl! bool))
  (bool-and
   bool-nary/c)
  (bool-or
   bool-nary/c)
)
  TRUE FALSE
)

(require
)

(define (bool/simpl! b)
  (and (bool? b) (simpl! b)))

(define bool-nary/c
  (->* (bool/simpl!) () #:rest (Listof bool/simpl!) bool))

;; =============================================================================
;; --- booleans
;;     Internal representation

(module private racket/base
  (require
    kodkod/private/predicates
    (only-in kodkod/private/ast
      define-ADT))
  (define-ADT bool
    (b:zero ())   ;; 0 (constant)
    (b:one ())    ;; 1 (constant)
    (b:var ([v : Symbol]))   ;; identifier
    (b:neg ([b : bool?]))
    (b:and ([b0 : bool?] [b1 : bool?]))
    (b:or ([b0 : bool?] [b1 : bool?]))
    (b:if/else ([b0 : bool?] [b1 : bool?] [b2 : bool?])))
) (require 'private)

;; =============================================================================

(define (bool? b)
  (raise-user-error 'not-implemented))

(define (simpl! b)
  (raise-user-error 'not-implemented))

(define FALSE (b:zero))
(define TRUE (b:one))

(define-syntax-rule (big-bor for-clause for-body)
  (for/fold ([acc (bzero)])
            for-clause
    (bor acc for-body)))

(define-syntax-rule (big-band for-clause for-body)
  (for/fold ([acc (bone)])
            for-clause
    (band acc for-body)))

(define (bool-and b0 . b1*)
  (bool-and* b0 b1*))

(define (bool-and* b0 b1*)
  (raise-user-error 'not-implemented))
  ;(if (or (false? b0)
  ;        (for/or ([b1 (in-list b1*)]) (false? b1)))
  ;  FALSE
  ;  (raise-user-error 'not-implemented)))

(define (bool-or b0 . b1*)
  (bool-or* b0 b1*))

(define (bool-or* b0 b1*)
  (raise-user-error 'not-implemented))

(define (bool-negate b)
  (raise-user-error 'not-implemented))

(define (b-simplify b)
  (raise-user-error 'not-implemented))

