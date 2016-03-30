#lang racket/base


(define (id x)
  x)

(struct int-tree (
  color ;; Boolean, #t = black
  root  ;; (Boxof (U #f int-tree))
) #:transparent )

(struct node (
  color    ;; Boolean
  key      ;; Integer
  left     ;; Node
  parent   ;; Node
  right    ;; Node
) #:transparent
  #:mutable
)
;(define-type Node node)

;; -----------------------------------------------------------------------------

(define (make-int-tree c i)
  (int-tree c (box #f)))

(define (int-tree-clear I)
  (set-box! (int-tree-root I) #f))

(define (int-tree-insert I z)
  'todo)

(define (int-tree-search I k)
  (let loop ([n (unbox (int-tree-root I))])
    (and n
      (cond
       [(= k (node-key n))   n]
       [(< k (node-key n))   (loop (node-left n))]
       [else                 (loop (node-right n))]))))

(define (int-tree-searchGTE I k)
  (int-tree-search/f I k id node-successor))

(define (int-tree-searchLTE I k)
  (int-tree-search/f I k node-predecessor id))

(define (int-tree-search/f I k left-f right-f)
  (let loop ([n (unbox (int-tree-root I))])
    (and n
      (cond
       [(= k (node-key n))
        n]
       [(< k (node-key n))
        (define L (node-left n))
        (if L
          (loop L)
          (left-f n))]
       [else
        (define R (node-right n))
        (if R
          (loop R)
          (right-f R))]))))

;; -----------------------------------------------------------------------------

(define (node-free! o)
  (set-node-parent! o #f)
  (set-node-left! o #f)
  (set-node-right! o #f))

(define (node-max n)
  (and n
    (or (node-max (node-right n)) n)))

(define (node-min n)
  (and n
    (or (node-min (node-left n)) n)))

(define (node-predecessor n)
  (define l (unbox (node-left n)))
  (if l
    (node-max l)
    (let loop ([n n]
               [ancestor (node-parent n)])
      (if (and ancestor (eq? n (node-left ancestor)))
        (loop ancestor (node-parent ancestor))
        ancestor))))

(define (node-successor n)
  (define r (node-right n))
  (if r
    (node-min r)
    (let loop ([n n]
               [ancestor (node-parent n)])
      (if (and ancestor (eq? n (node-right ancestor)))
        (loop ancestor (node-parent ancestor))
        ancestor))))

(define (node-replace I o n)
  (define l (node-left o))
  (define r (node-right o))
  (define p (node-parent o))
  (set-node-color! n (node-color o))
  (set-node-parent! n p)
  (set-node-left! n l)
  (set-node-right! n r)
  (when l (set-node-parent! l n))
  (when r (set-node-parent! r n))
  (cond
   [(not p)
    (set-box! (int-tree-root I n))]
   [(eq? o (node-left p))
    (set-node-left! p n)]
   [else
    (set-ndoe-right! p n)])
  (node-free! o))

