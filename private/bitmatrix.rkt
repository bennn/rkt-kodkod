#lang racket/base

;; Boolean Matrix

(require kodkod/private/predicates)
(provide (contract-out
  [bitmatrix-ref
   (->i ([B BitMatrix] [i Natural])
        #:pre (B i) (in-dimensions? (dims B) i)
        [_ Bool])]
  [bitmatrix-negate
   (-> BitMatrix BitMatrix)]
  [bitmatrix-and
   bitmatrix-binop/c] ;; TODO should be n-ary operation
  [bitmatrix-or
   bitmatrix-binop/c]

))

(require
  racket/class
  racket/match
  (for-syntax racket/base syntax/parse)
  (only-in racket/vector
    vector-append)
  ;;
  (only-in kodkod/private/ast define-ADT)
  kodkod/private/bool
  kodkod/private/sparse-sequence
)

;; =============================================================================

;; TODO need to put this in a submodule
(define-ADT dimensions
  (d:square (
    [depth : Natural]  ;; Depth of each dimension
    [size : Natural])) ;; Number of dimensions
  (d:rectangle (
    [depth* : (Vectorof Natural)])))  ;; size = (length depth*)

;; TODO n-ary
(define (dimensions=? d0 d1)
  (match-dimensions d0
   [(d:square d0 s0)
    (match d1
     [(d:square d1 s1)
      (and (= d0 d1) (= s0 s1))]
     [_ #f])]
   [(d:rectangle v0*)
    (match d1
     [(d:rectangle v1*)
      (and (= (vector-length v0*) (vector-length v1*))
           (for/and ([v0 (in-vector v0*)] [v1 (in-vector v1*)])
             (= v0 v1)))]
     [_ #f])]))

(define (make-rectangle d*-raw)
  ;; -- If square, make a d:square
  (define d* (if (list? d*-raw) d*-raw (vector->list d*-raw)))
  (let loop ([tmp* d*]
             [depth #f]
             [size 0])
    (cond
     [(null? tmp*)
      (d:square (or depth 0) size)]
     [(or (not depth) (= (car tmp*) depth))
      (loop (cdr tmp*) (car tmp*) (+ size 1))]
     [else
      (d:rectangle (list->vector d*))])))

(define-syntax-rule (dimensions-index-error i)
  (raise-user-error 'dimensions-ref "Invalid index ~a" i))

(define (dimensions-ref d i)
  (match-dimensions d
   [(d:square x s)
    (unless (and (<= 0 i) (< i s))
      (dimensions-index-error i))
    x]
   [(d:rectangle d*)
    (unless (and (<= 0 i) (< i (vector-length d*)))
      (dimensions-index-error i))
    (vector-ref d* i)]))

(define (dimensions-dot d0 d1)
  (define n0 (dimensions-count d0))
  (define n1 (dimensions-count d1))
  (cond
   [(zero? n0)   d0]
   [(zero? n1)   d1]
   [else
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
        (vector-append (dimensions->vector d0) (dimensions->vector d1))))]))

(define (dimensions-cross d0 d1)
  (define n0 (dimensions-count d0))
  (define n1 (dimensions-count d1))
  (cond
   [(zero? n0)
    d0]
   [(zero? n1)
    d1]
   [(and (d:square? d0) (d:square? d1)
         (= (dimensions-ref d0 0)
            (dimensions-ref d1 0)))
    (d:square (+ n0 n1) (dimensions-ref d0 0))]
   [else
    (make-rectangle
      (vector-append (dimensions->vector d0) (dimensions->vector d1)))]))

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
    (if (zero? s)
      0
      (expt d s))]
   [(d:rectangle d*)
    (for/product ([d (in-vector d*)]) d)]))

(define (in-dimensions? d n)
  (and (exact-nonnegative-integer? n)
       (< n (dimensions-capacity d))))

;; -----------------------------------------------------------------------------

(define (bitmatrix-ref B i)
  (send (cells B) ref i))

(struct bitmatrix (
  dimensions  ;; Natural
  cells       ;; sparse-sequence<%>
) #:property prop:procedure bitmatrix-ref
)

(define BitMatrix bitmatrix?)
(define dims  bitmatrix-dimensions)
(define cells bitmatrix-cells)

(define bitmatrix-binop/c
  (->i ([B0 BitMatrix] [B1 BitMatrix])
       #:pre (B0 B1) (dimensions=? (dims B0) (dims B1))
       [_ BitMatrix]))

(define (bitmatrix-density B)
  (send (cells B) size))

(define (bitmatrix-dense-indices B)
  (send (cells B) indices))

(define (bitmatrix-clone B)
  (bitmatrix (dims B) (send (cells B) clone)))

;; -----------------------------------------------------------------------------
;; --- Bitmatrix combinators

;; Return a bitmatrix with the opposite of B at every location.
;;  e.g. Change null cells to TRUE
(define (bitmatrix-negate B)
  (define ocells (cells B))
  (define !cells (send ocells clone/clear))
  (for ([i (in-range (dims B))])
    (cond
     [(send ocells ref i)
      => (lambda (v) (send !cells put (bool-negate  v)))]
     [else
      (send !cells put TRUE)]))
  (bitmatrix (dims B) !cells))

(define (bitmatrix-and B0 . B1*)
  (bitmatrix-and* B0 B1*))

(define (bitmatrix-and* B0 B1*)
  (define Acells (send (cells B0) clone/clear))
  ;; --
  (unless (or (send (cells B0) isEmpty?)
              (for/or ([B1 (in-list B1*)]) (send (cells B1) isEmpty?)))
    (for ([i (send (cells B0) indices)])
      (send Acells put
        (bool-and* (send (cells B0) get i)
                   (for/list ([B1 (in-list B1*)])
                     (send (cells B1) get i))))))
  (bitmatrix (dims B0) Acells))

(define (bitmatrix-or B0 . B1*)
  (bitmatrix-or* B0 B1*))

(define (bitmatrix-or* B0 B1*-arg)
  (define B* (for/list ([B (in-list (cons B0 B1*-arg))]
                        #:when (not (send (cells B) isEmpty?)))
               B))
  (cond
   [(null? B*)
    (bitmatrix-clone B0)]
   [(null? (cdr B*))
    (bitmatrix-clone (car B*))]
   [else
    (define Acells (send (cells (car B*)) clone/clear))
    ;; -- Take (binary)-OR of current cells and each matrice's dense entries
    (for* ([B (in-list B*)]
           [i (send (cells B) indices)])
      (define Bcells (cells B))
      (send Acells put (bool-or (send Acells ref i) (send Bcells ref i))))
    (bitmatrix (dims (car B*)) Acells)]))

(define (bitmatrix-cross B0 . B1*)
  (bitmatrix-cross* B0 B1*))

(define (bitmatrix-cross* B0 B1*-arg)
  (raise-user-error 'not-implemented))

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)

  ;; --- dimensions
  (let ([r0 (make-rectangle '())]
        [r1 (make-rectangle '(9 9 9 9 9 9 9 9 9))]
        [r2 (make-rectangle '(1 2 3))]
        [s0 (d:square 0 0)]
        [s1 (d:square 5 6)]
        [s2 (d:square 30 3)])

    (check-apply* d:square?
     [r0 => #t]
     [r1 => #t]
     [r2 => #f]
     [s0 => #t]
     [s1 => #t]
     [s2 => #t])

    (check-apply* d:rectangle?
     [r0 => #f]
     [r1 => #f]
     [r2 => #t]
     [s0 => #f]
     [s1 => #f]
     [s2 => #f])

    (check-apply* dimensions-ref
     [r1 0 => 9]
     [r1 1 => 9]
     [r2 0 => 1]
     [r2 2 => 3]
     [s1 5 => 5]
     [s1 4 => 5]
     [s2 1 => 30])
    (check-exn #rx"dimensions-ref"
      (lambda () (dimensions-ref r0 0)))
    (check-exn #rx"dimensions-ref"
      (lambda () (dimensions-ref s0 1)))
    (check-exn #rx"dimensions-ref"
      (lambda () (dimensions-ref r1 -1)))

    (check-apply* dimensions-dot
     [r0 r0
      => r0]
     [r0 s0
      => s0]
     [r1 r1
      => (d:square 16 9)]
     ;; TODO why? (understand what the function is supposed to do)
    )
    (check-exn #rx"dimensions-dot"
      (lambda () (dimensions-dot r2 r1)))
    (check-exn #rx"dimensions-dot"
      (lambda () (dimensions-dot r1 r2)))

    (check-apply* dimensions-cross
     [r0 r0
      => r0]
     [r1 r1
      => (d:square 18 9)]
     [r1 r2
      => (d:rectangle '#(9 9 9 9 9 9 9 9 9 1 2 3))]
     [s0 s1
      => s0]
     [s1 s1
      => (d:square 12 5)]
     [s1 s2
      => (d:rectangle '#(5 5 5 5 5 5 30 30 30))]
     [s2 s1
      => (d:rectangle '#(30 30 30 5 5 5 5 5 5))]
    )

    (check-apply* dimensions->vector
     [r0 => '#()]
     [r2 => '#(1 2 3)]
     [s1 => '#(5 5 5 5 5 5)]
     [s2 => '#(30 30 30)]
    )

    (check-apply* dimensions-count
     [r0 => 0]
     [r1 => 9]
     [r2 => 3]
     [s0 => 0]
     [s1 => 6]
     [s2 => 3]
    )

    (check-apply* dimensions-transpose
     [(make-rectangle '#(6 9))
      => (make-rectangle '#(9 6))]
     [(d:square 8 2)
      => (d:square 8 2)]
    )
    (check-exn #rx"transpose"
      (lambda () (dimensions-transpose r0)))
    (check-exn #rx"transpose"
      (lambda () (dimensions-transpose s1)))
    (check-exn #rx"transpose"
      (lambda () (dimensions-transpose r2)))

    (check-apply* dimensions-capacity
     [r0 => 0]
     [r2 => 6]
     [s0 => 0]
     [s1 => (expt 5 6)]
    )

  ) ;; --- dimensions
  ;; TODO dimensions=?
  ;; 

  ;; --- bitmatrix
  ;(let ([B (make-bitmatrix TODO)])
  ;) ;; --- bitmatrix

)
