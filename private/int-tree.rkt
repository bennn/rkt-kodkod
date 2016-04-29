#lang racket/base

;; TODO as fallback, can use pfds/red-black-tree

(require kodkod/private/predicates)
(provide (contract-out
  [struct int-tree (
    (color Boolean)
    (root (Box (U #f int-tree?))))]

  [struct node (
    ;; MUTABLE
    (color Boolean)
    (key Integer)
    (left node?)
    (parent node?)
    (right node?)
    (value Any))]

  ;; ---

  [make-int-tree
   (-> int-tree?)]

  [make-node
   (-> Key Any node?)]

  [int-tree-clone
   (-> int-tree? int-tree?)]

  [int-tree-clear
   (-> int-tree? Void)]

  [int-tree-delete
   (-> int-tree? node? Void)]

  [int-tree-indices
   (-> int-tree? (Sequenceof Key))]

  [int-tree-insert
   (-> int-tree? node? Void)]

  [int-tree-max
   (-> int-tree? Any)]

  [int-tree-min
   (-> int-tree? Any)]

  [int-tree-search
   (-> int-tree? Key Any)]

  [int-tree-searchGTE
   (-> int-tree? Key Any)]

  [int-tree-searchLTE
   (-> int-tree? Key Any)]

  [node->value
   (-> node? Any)]

))

(define Key (U Integer (Listof Integer)))

(define (=* k1* k2*)
  (if (integer? k1*)
    (= k1* k2*)
    (for/and ([k1 (in-list k1*)]
              [k2 (in-list k2*)])
      (= k1 k2))))

(define (<* k1* k2*)
  (if (integer? k1*)
    (< k1* k2*)
    (for/and ([k1 (in-list k1*)]
              [k2 (in-list k2*)])
      (< k1 k2))))

;; =============================================================================

(define (id x)
  x)

(struct int-tree (
  color ;; Boolean, #t = black
  root  ;; (Boxof (U #f node))
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

(define (int-tree-empty? I)
   (eq? #f (unbox (int-tree-root I))))

(define node->value
  node-value)

(define (int-tree-clone I)
  (int-tree (int-tree-color I)
            (box (node-clone (unbox (int-tree-root I))))))

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
        (if (<* z-key (node-key x))
          (loop (node-left x) x)
          (loop (node-right x) x)))))
  (set-node-parent! z y)
  (set-node-left! z #f)
  (set-node-right! z #f)
  (if (not y)
    (set-box! (int-tree-root I) z)
    (begin
      (set-node-color! z #f)
      (if (<* z-key (node-key y))
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
       [(=* k (node-key n))   n]
       [(<* k (node-key n))   (loop (node-left n))]
       [else                 (loop (node-right n))]))))

(define (int-tree-searchGTE I k)
  (int-tree-search/f I k id node-successor))

(define (int-tree-searchLTE I k)
  (int-tree-search/f I k node-predecessor id))

(define (int-tree-search/f I k left-f right-f)
  (let loop ([n (unbox (int-tree-root I))])
    (and n
      (cond
       [(=* k (node-key n))
        n]
       [(<* k (node-key n))
        (define L (node-left n))
        (if L
          (loop L)
          (left-f n))]
       [else
        (define R (node-right n))
        (if R
          (loop R)
          (right-f n))]))))

(define (list->int-tree x*)
  (define I (make-int-tree))
  (for ([x (in-list x*)])
    (int-tree-insert I (make-node x x)))
  I)

(define (int-tree->list I)
  (for/list ([i (int-tree-indices I)])
    (node->value (int-tree-search I i))))

;; -----------------------------------------------------------------------------

(define (node-clone n [parent #f])
  (and n
    (node (node-color n)
          (node-key n)
          (node-clone (node-left n) n)
          parent
          (node-clone (node-right n) n)
          (node-value n))))

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
  (define l (node-left n))
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

  (define digit* (for/list ([i (in-range 10)]) i))
  (define (digit-tree)
    (list->int-tree digit*))

  (test-case "make-int-tree"
    (let ([I (make-int-tree)])
      (check-true (int-tree? I))
      (check-true (int-tree-empty? I)))
  )

  (test-case "int-tree-clear"
    (let ([I (digit-tree)])
      (check-false (int-tree-empty? I))
      (int-tree-clear I)
      (check-true (int-tree-empty? I)))
  )

  (test-case "int-tree-delete"
    (let* ([I (digit-tree)]
           [d* (cdr digit*)])
      (int-tree-delete I (int-tree-search I 0))
      (check-equal? (int-tree->list I) d*)
      (check-false (int-tree-empty? I))
      (for ([i (in-list d*)])
        (int-tree-delete I (int-tree-search I i)))
      (check-true (int-tree-empty? I))))

  (test-case "int-tree-indices"
    (let* ([I (digit-tree)]
           [i* (for/list ([i (int-tree-indices I)]) i)])
      (check-equal?  i* digit*))
  )

  (test-case "int-tree-insert"
    (let* ([I (digit-tree)]
           [d0 (apply min digit*)]
           [d9 (apply max digit*)]
           [d10 (+ 1 d9)])
      (check-equal? (node->value (int-tree-min I)) d0)
      (check-equal? (node->value (int-tree-max I)) d9)
      (check-false (int-tree-search I d10))
      (int-tree-insert I (make-node d10 d10))
      (check-equal? (node->value (int-tree-max I)) d10)
      (check-true (and (int-tree-search I d10) #t)))
  )

  (test-case "int-tree-max"
    (let* ([I (digit-tree)])
      (check-false (int-tree-max (make-int-tree)))
      (check-equal? (node->value (int-tree-max I)) (apply max digit*)))
  )

  (test-case "int-tree-min"
    (let* ([I (digit-tree)])
      (check-false (int-tree-min (make-int-tree)))
      (check-equal? (node->value (int-tree-min I)) (apply min digit*)))
  )

  (test-case "int-tree-search"
    (let* ([I (digit-tree)]
           [d (car digit*)]
           [n1 (int-tree-search I d)]
           [n2 (int-tree-search I (+ 1 (apply max digit*)))])
      (check-equal? (node-key n1) d)
      (check-equal? (node->value n1) d)
      (check-false n2))
  )

  (test-case "int-tree-searchGTE"
    (let* ([I (digit-tree)]
           [d1 (apply min digit*)]
           [d0 (- d1 1)]
           [d2 (+ d1 1)]
           [d11 (+ d1 (length digit*))]
           [n1 (node->value (int-tree-searchGTE I d1))]
           [n0 (node->value (int-tree-searchGTE I d0))]
           [n2 (node->value (int-tree-searchGTE I d2))]
           [n11 (int-tree-searchGTE I d11)])
      (check-equal? n1 0)
      (check-equal? n0 0)
      (check-equal? n2 1)
      (check-equal? n11 #f))
  )

  (test-case "int-tree-searchLTE"
    (let* ([I (digit-tree)]
           [d1 (apply min digit*)]
           [d0 (- d1 1)]
           [d2 (+ d1 1)]
           [d11 (+ d1 (length digit*))]
           [n1 (node->value (int-tree-searchLTE I d1))]
           [n0 (int-tree-searchLTE I d0)]
           [n2 (node->value (int-tree-searchLTE I d2))]
           [n11 (node->value (int-tree-searchLTE I d11))])
      (check-equal? n1 0)
      (check-equal? n0 #f)
      (check-equal? n2 1)
      (check-equal? n11 9))
  )

  (test-case "make-node"
    (let* ([key 'key]
           [val 'val]
           [n (make-node key val)])
      (check-true (node? n))
      (check-equal? (node-key n) key)
      (check-equal? (node-value n) val)
      (check-equal? (node->value n) val))
  )

  (test-case "node->value"
    (let* ([k 536]
           [v 'value]
           [n (make-node k v)])
      (check-equal? (node->value n) v))
  )

)
