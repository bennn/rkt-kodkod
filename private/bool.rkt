#lang racket/base

;; Fancy constructors for kk:bool values
;; - lifted to handle #f
;; - automatically collapse, sometimes

(require kodkod/private/predicates)
(provide (contract-out
  (make-b:zero
   (-> b:zero?))

  (make-b:one
   (-> b:one?))

  (make-b:var
   (-> (U #f Symbol) (U #f kk:bool?)))

  (make-b:neg
   (-> (U #f kk:bool?) (U #f kk:bool?)))

  (make-b:and
   (-> (U #f kk:bool?) (U #f kk:bool?) (U #f kk:bool?)))

  (make-b:or
   (-> (U #f kk:bool?) (U #f kk:bool?) (U #f kk:bool?)))

  (make-b:if/else
   (-> (U #f kk:bool?) (U #f kk:bool?) (U #f kk:bool?) (U #f kk:bool?)))

  ;; -- combinators

  (make-b:difference
   (-> (U #f kk:bool?) (U #f kk:bool?) (U #f kk:bool?)))
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

(define (make-b:difference b0 b1)
  (make-b:if/else b1 (make-b:zero) b0))

