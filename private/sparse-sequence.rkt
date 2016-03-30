#lang racket/base

(provide
)

(require
  racket/class
  kodkod/private/int-tree
)

;; =============================================================================

(define (sparse=? S0 S1)
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
    floor
    indices
    isEmpty?
    last
    put
    putAll
    ref
    remove
    size
))

(define tree-sequence%
  (class* object% (sparse-sequence<%>)
    (field
     [size 0]
     [tree (make-int-tree)])
    (super-new)

  ;; Get, but returns successor on failure
  (define/public (ceil i)
    (int-tree-searchGTE (get-field tree this) i))

  (define/public (clear)
    (int-tree-clear (get-field tree this)))

  (define/public (contains? v)
    (send this containsIndex? v)) ;; rly?

  (define/public (containsIndex? i)
    (if (int-tree-search (get-field tree this) i)
      #t
      #f))

  (define/public (first)
    (int-tree-min (get-field tree this)))

  ;; Like get, but returns predecessor on failure
  (define/public (floor i)
    (int-tree-searchLTE (get-field tree this) i))

  (define/public (indices)
    (int-tree-indices (get-field tree this)))

  (define/public (isEmpty?)
    (zero? (get-field size this)))

  (define/public (last)
    (int-tree-max (get-field tree this)))

  (define/public (put i v)
    (define e (int-tree-search (get-field tree this)))
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

  (define (size++)
    (set-field! size this (+ (get-field size this) 1)))

  (define (size--)
    (set-field! size this (- (get-field size this) 1)))
))

