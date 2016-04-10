#lang racket/base

(provide
  sparse-sequence=?
  sparse-sequence<%>
  tree-sequence%
  ;array-sequence%
  ;homogenous-sequence%
  ;range-sequence%
)

(require
  racket/class
  kodkod/private/int-tree
)

;; =============================================================================

(define (sparse-sequence=? S0 S1)
  (and (= (send S0 size) (send S1 size))
    (for/and ([i0 (send S0 indices)]
              [i1 (send S1 indices)])
      (= i0 i1))))

(define sparse-sequence<%>
  (interface ()
    ceil
    clear
    contains?
    containsIndex?
    first
    floor           ;; Like `ref`, but returns predecessor on failure
    indices
    isEmpty?
    last
    put
    putAll
    ref
    remove
    get-size
))

;; -----------------------------------------------------------------------------

;(define array-sequence%
;  (class* object% (sparse-sequence<%>)
;    (field
;     [entries '()]
;     [size 0])
;))

;; -----------------------------------------------------------------------------

;(define homogenous-sequence%
;  (class* object% (sparse-sequence<%>)
;    TODO
;))

;; -----------------------------------------------------------------------------

;(define range-sequence%
;  (class* object% (sparse-sequence<%>)
;    TODO
;))

;; -----------------------------------------------------------------------------

(define tree-sequence%
  (class* object% (sparse-sequence<%>)
    (field
     [size 0]
     [tree (make-int-tree)])
    (super-new)

  (define/public (ceil i)
    (int-tree-searchGTE (get-field tree this) i))

  (define/public (clear)
    (int-tree-clear (get-field tree this))
    (set-field! size this 0))

  (define/public (contains? v)
    (send this containsIndex? v)) ;; rly?

  (define/public (containsIndex? i)
    (if (int-tree-search (get-field tree this) i)
      #t
      #f))

  (define/public (first)
    (int-tree-min (get-field tree this)))

  (define/public (floor i)
    (int-tree-searchLTE (get-field tree this) i))

  (define/public (indices)
    (int-tree-indices (get-field tree this)))

  (define/public (isEmpty?)
    (zero? (get-field size this)))

  (define/public (last)
    (int-tree-max (get-field tree this)))

  (define/public (put i v)
    (define e (int-tree-search (get-field tree this) i))
    (if e
      (set-node-value! e v)
      (begin
        (size++)
        (int-tree-insert (get-field tree this) (make-node i v))
        #f)))

  (define/public (putAll that)
    (for ([i (send that indices)])
      (send this put i (send that ref i))))

  (define/public (ref i)
    (let ([n (int-tree-search (get-field tree this) i)])
      (if n
        (node->value n)
        #f)))

  (define/public (remove i)
    (define e (int-tree-search (get-field tree this) i))
    (if e
      (begin
        (size--)
        (int-tree-delete (get-field tree this) e)
        (node->value e))
      #f))

  (define/public (get-size)
    (get-field size this))

  (define/private (size++)
    (set-field! size this (+ (get-field size this) 1)))

  (define/private (size--)
    (set-field! size this (- (get-field size this) 1)))
))

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)

  (test-case "ops"
    (let ([ts (new tree-sequence%)]
          [N 10])
      (for ([i (in-range N)])
        (send ts put i i))
      ;; --
      (check-equal?
        (send ts get-size)
        N)
      (for ([i (in-range N)])
        (check-equal?
          (send ts ref i)
          i))
      ;; --
      (check-apply* (lambda (n) (let ((r (send ts ceil n))) (if r (node->value r) #f)))
       [9 => 9]
       [33 => #f]
       [0 => 0]
       [3 => 3]
       [-3 => 0])
      ;; -- contains
      (check-apply* (lambda (n) (send ts contains? n))
       [-2 => #f]
       [10 => #f]
       [ 1 => #t]
       [ 9 => #t])
      ;; --
      (check-apply* (lambda (n) (send ts containsIndex? n))
       [2 => #t]
       [-8 => #f])
      (check-equal?
        (node->value (send ts first))
        0)
      (check-apply* (lambda (n) (let ((r (send ts floor n))) (if r (node->value r) #f)))
       [0 => 0]
       [-1 => #f]
       [9 => 9]
       [111 => 9])
      (check-equal?
        (for/list ([i (send ts indices)]) i)
        (for/list ([i (in-range N)]) i))
      (check-equal?
        (send ts isEmpty?)
        #f)
      (check-equal?
        (node->value (send ts last))
        (- N 1))
      (check-equal?
        (begin
          (send ts put 10 10)
          (send ts remove 10)
          (send ts get-size))
        N)
      (check-equal?
        (begin
          (send ts remove 0)
          (send ts contains? 9))
        #t)
  ))

  (test-case "clear"
    (let ([ts (new tree-sequence%)]
          [N 9])
      (send ts putAll (new (class object% (super-new)
                             (define/public (ref i) i)
                             (define/public (indices) (in-range 0 N)))))
      (check-equal?
        (get-field size ts)
        N)
      (send ts clear)
      (check-equal?
        (get-field size ts)
        0)
  ))
)
