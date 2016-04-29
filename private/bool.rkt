#lang racket/base

;; Fancy constructors for kk:bool values
;; - lifted to handle #f
;; - automatically collapse, sometimes

;; aka circuits library

(require kodkod/private/predicates)
(provide (contract-out
  (make-b:zero
   (-> b:zero?))

  (make-b:one
   (-> b:one?))

  (make-b:var
   (-> (U #f Symbol) (U #f Bool)))

  (make-b:neg
   (-> (U #f Bool) (U #f Bool)))

  (make-b:and
   (-> (U #f Bool) (U #f Bool) (U #f Bool)))

  (make-b:or
   (-> (U #f Bool) (U #f Bool) (U #f Bool)))

  (make-b:if/else
   (-> (U #f Bool) (U #f Bool) (U #f Bool) (U #f Bool)))

  ;; -- combinators

  (make-b:implies
   (-> (U #f Bool) (U #f Bool) (U #f Bool)))

  (make-b:iff
   (-> (U #f Bool) (U #f Bool) (U #f Bool)))

  (make-b:difference
   (-> (U #f Bool) (U #f Bool) (U #f Bool)))
))

;; -----------------------------------------------------------------------------

(require
  kodkod/private/ast
)

;; =============================================================================

(define B:ZERO (b:zero))
(define B:ONE (b:one))

(define (make-b:zero)
  B:ZERO)

(define (make-b:one)
  B:ONE)

(define (make-b:var v)
  (and v (b:var v)))

(define (make-b:neg b)
  (and b
    (cond
     [(b:zero? b)
      (make-b:one)]
     [(b:one? b)
      (make-b:zero)]
     [else
      (b:neg b)])))

(define (make-b:and b0 b1)
  (and b0 b1
    (cond
     [(or (b:zero? b0) (b:zero? b1))
      (make-b:zero)]
     [(and (b:one? b0) (b:one? b1))
      (make-b:one)]
     [else
      (b:and b0 b1)])))

(define (make-b:or b0 b1)
  (and b0 b1
    (cond
     [(or (b:one? b0) (b:one? b1))
      (make-b:one)]
     [(or (b:zero? b0) (b:zero? b1))
      (make-b:zero)]
     [else
      (b:or b0 b1)])))

(define (make-b:if/else b0 b1 b2)
  (and b0 b1 b2
    (cond
     [(b:one? b0)
      b1]
     [(b:zero? b0)
      b2]
     [else
      (b:if/else b0 b1 b2)])))

(define (make-b:implies b0 b1)
  (make-b:or (make-b:neg b0) b1))

(define (make-b:iff b0 b1)
  (make-b:and (make-b:implies b0 b1)
              (make-b:implies b1 b0)))


(define (make-b:difference b0 b1)
  (make-b:if/else b1 (make-b:zero) b0))

