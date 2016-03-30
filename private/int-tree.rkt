#lang racket/base

;; TODO as fallback, can use pfds/red-black-tree

(provide
  make-int-tree
  int-tree-clear
  int-tree-delete
  int-tree-indices
  int-tree-insert
  int-tree-max
  int-tree-min
  int-tree-search
  int-tree-searchGTE
  int-tree-searchLTE
  ;; ---
  make-node
  node->value
  set-node-value!
)

;; =============================================================================

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
  value    ;; Any
) #:transparent
  #:mutable
)
;(define-type Node node)

;; -----------------------------------------------------------------------------

(define (make-int-tree)
  (int-tree #t (box #f)))

(define (make-node k v)
  (node #f k #f #f #f v))

(define node->value
  node-value)

(define (int-tree-clear I)
  (set-box! (int-tree-root I) #f))

(define (int-tree-delete I z)
  (define y
    (if (or (not (node-left z)) (not (node-right z)))
      z
      (node-successor z)))
  (define x
    (or (node-left y) (node-right y)))
  (define yparent (node-parent y))
  (define yleft? (eq? y (and yparent (node-left yparent))))
  (define ycolor (node-color y))
  (when x (set-node-parent! x yparent))
  (cond
   [(not yparent)
    (set-box! (int-tree-root I) x)]
   [yleft?
    (set-node-left! yparent x)]
   [else
    (set-node-right! yparent x)])
  (when (not (eq? y z)) (node-replace I z y))
  (when ycolor
    (if x
      (delete-fixup I x)
      (when yparent
        (let ([yparent (if (eq? z yparent) y yparent)])
          (set-node-color! z #t)
          (set-node-left! z #f)
          (set-node-right! z #f)
          (set-node-parent! z yparent)
          (if yleft?
            (set-node-left! yparent z)
            (set-node-right! yparent z))
          (delete-fixup I x)
          (if (eq? z (node-left (node-parent z)))
            (set-node-left! (node-parent z) #f)
            (set-node-right! (node-parent z) #f))))))
  (node-free! z))

(define (int-tree-indices I)
  ;; TODO make lazy, with in-producer
  (let loop ([n (unbox (int-tree-root I))])
    (if n
      (append
        (loop (node-left n))
        (list (node-key n))
        (loop (node-right n)))
      '())))

(define (int-tree-insert I z)
  (define z-key (node-key z))
  (define y
    (let loop ([x (unbox (int-tree-root I))] [prev #f])
      (if (not x)
        prev
        (if (< z-key (node-key x))
          (loop (node-left x) x)
          (loop (node-right x) x)))))
  (set-node-parent! z y)
  (set-node-left! z #f)
  (set-node-right! z #f)
  (if (not y)
    (set-box! (int-tree-root I) z)
    (begin
      (set-node-color! z #f)
      (if (< z-key (node-key y))
        (set-node-left! y z)
        (set-node-right! y z))
      (insert-fixup I z))))

(define (int-tree-min I)
  (node-min (unbox (int-tree-root I))))

(define (int-tree-max I)
  (node-max (unbox (int-tree-root I))))

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
    (set-node-right! p n)])
  (node-free! o))

;; -----------------------------------------------------------------------------
;; --- private

(define-syntax-rule (setColor z c) (and z (set-node-color! z c)))
(define-syntax-rule (colorOf z) (and z (node-color z)))
(define-syntax-rule (leftOf z) (and z (node-left z)))
(define-syntax-rule (parentOf z) (and z (node-parent z)))
(define-syntax-rule (rightOf z) (and z (node-right z)))

(define (insert-fixup I z)
  (define root (unbox (int-tree-root I)))
  (let loop ([z z])
    (when (and z (not (eq? z root)) (not (node-color (node-parent z))))
      (if (eq? (node-parent z) (leftOf (parentOf (parentOf z))))
        (let ([y (rightOf (parentOf (parentOf z)))])
          (if (not (colorOf y))
            (begin
              (setColor (parentOf z) #f)
              (setColor y #t)
              (setColor (parentOf (parentOf z)) #f)
              (loop (parentOf (parentOf z))))
            (let ([z (if (eq? z (rightOf (parentOf z)))
                       (begin (rotateLeft I (parentOf z))
                              (parentOf z))
                       z)])
              (setColor (parentOf z) #t)
              (setColor (parentOf (parentOf z)) #f)
              (when (parentOf (parentOf z))
                (rotateRight I (parentOf (parentOf z))))
              (loop z))))
        (let ([y (leftOf (parentOf (parentOf z)))])
          (if (not (colorOf y))
            (begin
              (setColor (parentOf z) #t)
              (setColor y #t)
              (setColor (parentOf (parentOf z)) #f)
              (loop (parentOf (parentOf z))))
            (let ([z (if (eq? z (leftOf (parentOf z)))
                       (begin (rotateRight I (parentOf z))
                              (parentOf z))
                       z)])
              (setColor (parentOf z) #t)
              (setColor (parentOf (parentOf z)) #f)
              (when (parentOf (parentOf z))
                (rotateLeft I (parentOf (parentOf z))))
              (loop z)))))))
  (set-node-color! root #t))

(define (delete-fixup I x)
  (define root (unbox (int-tree-root I)))
  (let loop ([x x])
    (when (and (not (eq? x root)) (colorOf x))
      (if (eq? x (leftOf (parentOf x)))
        (let* ([sib (rightOf (parentOf x))]
               [sib (if (not (colorOf sib))
                      (begin
                        (setColor sib #t)
                        (setColor (parentOf x) #f)
                        (rotateLeft I (parentOf x))
                        (rightOf (parentOf x)))
                      sib)])
          (if (and (colorOf (leftOf sib)) (colorOf (rightOf sib)))
            (begin (setColor sib #f)
                   (loop (parentOf x)))
            (let ([sib (if (colorOf (rightOf sib))
                         (begin
                           (setColor (leftOf sib) #t)
                           (setColor sib #f)
                           (rotateRight I sib)
                           (rightOf (parentOf x)))
                         sib)])
              (setColor sib (colorOf (parentOf x)))
              (setColor (parentOf x) #t)
              (setColor (rightOf sib) #t)
              (rotateLeft I (parentOf x))
              (loop root))))
        (let* ([sib (leftOf (parentOf x))]
               [sib (if (not (colorOf sib))
                      (begin
                        (setColor sib #t)
                        (setColor (parentOf x) #f)
                        (rotateRight I (parentOf x))
                        (leftOf (parentOf x)))
                      sib)])
          (if (and (colorOf (rightOf sib)) (colorOf (leftOf sib)))
            (begin (setColor sib #f)
                   (loop (parentOf x)))
            (let ([sib (if (colorOf (leftOf sib))
                         (begin
                           (setColor (rightOf sib) #t)
                           (setColor sib #f)
                           (rotateLeft I sib)
                           (leftOf (parentOf x)))
                         sib)])
              (setColor sib (colorOf (parentOf x)))
              (setColor (parentOf x) #t)
              (setColor (leftOf sib) #t)
              (rotateRight I (parentOf x))
              (loop root)))))))
  (setColor x #t))

(define (rotateLeft I x)
  (define y (rightOf x))
  (set-node-right! x (node-left y))
  (when (node-left y)
    (set-node-parent! (node-left y) x))
  (set-node-parent! y (node-parent x))
  (cond
   [(not (node-parent x))
    (set-box! (int-tree-root I) y)]
   [(eq? (leftOf (parentOf x)) x)
    (set-node-left! (node-parent x) y)]
   [else
    (set-node-right! (node-parent x) y)])
  (set-node-left! y x)
  (set-node-parent! x y))

(define (rotateRight I x)
  (define y (node-left x))
  (set-node-left! x (node-right y))
  (when (node-right y)
    (set-node-parent! (node-right y) x))
  (set-node-parent! y (node-parent x))
  (cond
   [(not (node-parent x))
    (set-box! (int-tree-root I) y)]
   [(eq? x (node-right (node-parent x)))
    (set-node-right! (node-parent x) y)]
   [else
    (set-node-left! (node-parent x) y)])
  (set-node-right! y x)
  (set-node-parent! x y))

;; =============================================================================

(module+ test
  (require rackunit)


)
