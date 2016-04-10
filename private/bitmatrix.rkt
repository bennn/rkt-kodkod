#lang racket/base

;; Boolean Matrix

(provide
)

(require
  racket/match
  (for-syntax racket/base syntax/parse)
  (only-in racket/vector
    vector-append)
  ;;
  (only-in kodkod/private/ast define-ADT)
  kodkod/private/predicates
  kodkod/private/sparse-sequence
)

;; =============================================================================

(define-ADT dimensions
  (d:square (
    [depth : Natural]
    [size : Natural]))
  (d:rectangle (
    [depth* : (Vectorof Natural)])))

(define (make-rectangle d*)
  ;; -- If square, make a d:square
  (let loop ([d* d*]
             [depth #f]
             [size 0])
    (cond
     [(null? d*)
      (d:square depth size)]
     [(or (not depth) (= (car d*) depth))
      (loop (cdr d*) (car d*) (+ size 1))]
     [else
      (d:rectangle (list->vector d*))])))

(define (dimensions-ref d i)
  (match-dimensions d
   [(d:square x s)
    (unless (< i s)
      (raise-user-error 'dimensions-ref "Invalid index ~a" i))
    x]
   [(d:rectangle d*)
    (vector-ref d* i)]))

(define (dimensions-dot d0 d1)
  (define n0 (dimensions-count d0))
  (define n1 (dimensions-count d1))
  (define n (- (+ n0 n1) 2))
  (define drop (dimensions-ref d1 0))
  (when (or (= n 0) (not (= drop (dimensions-ref d0 (- n0 1)))))
    (raise-user-error 'dimensions-dot "Illegal arguments '~a' and '~a'" d0 d1))
  (if (and (d:square? d0)
           (d:square? d1)
           (or (= 1 n0)
               (= 1 n1)
               (= (dimensions-ref d0 0)
                  (dimensions-ref d1 1))))
    (d:square n (dimensions-ref d0 0))
    (make-rectangle
      (vector-append (dimensions->vector d0) (dimensions->vector d1)))))

(define (dimensions-cross d0 d1)
  (define n0 (dimensions-count d0))
  (define n1 (dimensions-count d1))
  (if (and (d:square? d0)
           (d:square? d1)
           (= (dimensions-ref d0 0)
              (dimensions-ref d1 0)))
    (d:square (+ n0 n1) (dimensions-ref d0 0))
    (make-rectangle
      (vector-append (dimensions->vector d0) (dimensions->vector d1)))))

(define (dimensions->vector d)
  (match-dimensions d
   [(d:square depth size)
    (make-vector size depth)]
   [(d:rectangle d*)
    d*]))

(define (dimensions-count d)
  (match-dimensions d
   [(d:square depth size)
    size]
   [(d:rectangle d*)
    (vector-length d*)]))

(define (dimensions-transpose d)
  (let ((c (dimensions-count d)))
    (unless (= 2 c)
      (raise-user-error 'transpose "Unsupported for ~a dimensions" c)))
  (match-dimensions d
   [(d:square _ _)
    d]
   [(d:rectangle d*)
    (d:rectangle (vector (vector-ref d* 1) (vector-ref d* 0)))]))

(define (dimensions-capacity d)
  (match-dimensions d
   [(d:square d s)
    (expt d s)]
   [(d:rectangle d*)
    (for/product ([d (in-vector d*)]) d)]))

(define ((in-dimension? d) n)
  (and (exact-nonnegative-integer? n)
       (< n (dimensions-capacity d))))

;; -----------------------------------------------------------------------------

(define (bitmatrix-ref B . x*)
  'TODO)

(struct bitmatrix (
  dims  ;; Natural
  cells ;; sparse-sequence<%>
) #:property prop:procedure bitmatrix-ref
)

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)


)
