#lang racket/base

;; Boolean Matrix

;; TODO
;; - should use top/bot sequences
;; - strong contracts

(require kodkod/private/predicates)
(provide (contract-out

  [bitmatrix-put
   (-> BitMatrix (Listof Natural) Any Void)]

  [bitmatrix-ref
   (->i ([B BitMatrix] [i Natural])
        #:pre (B i) (in-dimensions? (dims B) i)
        [_ Bool])]

  ;; ---

  [bitmatrix-none
   (-> BitMatrix Bool)]

  [bitmatrix-lone
   (-> BitMatrix Bool)]

  [bitmatrix-one
   (-> BitMatrix Bool)]

  [bitmatrix-some
   (-> BitMatrix Bool)]

  [bitmatrix-subset
   (-> BitMatrix BitMatrix Bool)]

  [bitmatrix=?
   (-> BitMatrix BitMatrix Bool)]

  ;; ---

  [bitmatrix-identity
   (-> Dimensions BitMatrix)]

  [bitmatrix-top
   (-> Dimensions BitMatrix)]

  [bitmatrix-bot
   (-> Dimensions BitMatrix)]

  [var->bitmatrix
   (-> Dimensions Natural BitMatrix)]

  [bitmatrix-negate
   (-> BitMatrix BitMatrix)]
  [bitmatrix-closure
   (-> BitMatrix BitMatrix)]

  [bitmatrix-transpose
   (-> BitMatrix BitMatrix)]

  ;; TODO can some binops relax with binop/c ?
  ;;  (hint: yes)

  [bitmatrix-and
   bitmatrix-binop/c]

  [bitmatrix-or
   bitmatrix-binop/c]

  [bitmatrix-cross
   bitmatrix-binop/c]

  [bitmatrix-difference
   bitmatrix-binop/c]

  [bitmatrix-dot
   bitmatrix-binop/c]

  [bitmatrix-implies
   bitmatrix-binop/c]

  [bitmatrix-iff
   bitmatrix-binop/c]

  [in-bitmatrix
   (-> BitMatrix (Sequenceof Any))]
  ;; TODO what is an indexed entry?

  [bitmatrix-choice
   (-> Bool BitMatrix BitMatrix BitMatrix)]
))

(require
  racket/class
  racket/match
  (for-syntax racket/base syntax/parse)
  ;;
  kodkod/private/ast
  kodkod/private/bool
  kodkod/private/dimensions
  kodkod/private/sparse-sequence
)

;; =============================================================================

(define (bitmatrix-ref B i)
  (send (cells B) ref i))

(define (write-bitmatrix B port mode)
  (fprintf port "{bitmatrix ~a ~a}" (dims B) (cells B)))

(struct bitmatrix (
  dimensions  ;; Dimensions
  cells       ;; sparse-sequence<%>
) #:property prop:procedure bitmatrix-ref
  #:methods gen:custom-write
  [(define write-proc write-bitmatrix)]
)

(define BitMatrix bitmatrix?)
(define dims  bitmatrix-dimensions)
(define cells bitmatrix-cells)

(define bitmatrix-binop/c
  (-> BitMatrix BitMatrix BitMatrix))
;  (->i ([B0 BitMatrix] [B1 BitMatrix])
;       #:pre (B0 B1) (dimensions=? (dims B0) (dims B1))
;       [_ BitMatrix]))

(define (bitmatrix-density B)
  (send (cells B) size))

(define (bitmatrix-dense-indices B)
  (send (cells B) indices))

(define (bitmatrix-clone B)
  (bitmatrix (dims B) (send (cells B) clone)))

(define (bitmatrix-empty? B)
  (send (cells B) isEmpty?))

(define (bitmatrix-count B)
  (for/sum ([i* (bitmatrix-dense-indices B)]
            #:when (b:one? (B i*)))
    1))

(define (bitmatrix-put B i* v)
  (send (cells B) put i* v))

;; -----------------------------------------------------------------------------
;; --- Bitmatrix combinators

(define (bitmatrix-identity D)
  (define ts (new tree-sequence%))
  (define one (make-b:one))
  (for ([x* (in-dimensions D)]
        #:when (apply = x*))
    (send ts put x* one))
  (bitmatrix D ts))

(define (bitmatrix-top D)
  (define ts (new tree-sequence%))
  (define one (make-b:one))
  (for ([x* (in-dimensions D)])
    (send ts put x* one))
  (bitmatrix D ts))

(define (bitmatrix-bot D)
  (bitmatrix D (new tree-sequence%)))

(define (var->bitmatrix D i)
  (define B (bitmatrix-bot D))
  (bitmatrix-put B (list i i) (make-b:one))
  B)

;; No true elements
(define (bitmatrix-none B)
  (if (= 0 (bitmatrix-count B))
    (make-b:one)
    (make-b:zero)))

(define (bitmatrix-lone B)
  (if (<= (bitmatrix-count B) 1)
    (make-b:one)
    (make-b:zero)))

(define (bitmatrix-one B)
  (if (= (bitmatrix-count B) 1)
    (make-b:one)
    (make-b:zero)))

(define (bitmatrix-some B)
  (if (< 0 (bitmatrix-count B))
    (make-b:one)
    (make-b:zero)))

;; Return a bitmatrix with the opposite of B at every location.
;;  e.g. Change null cells to TRUE
(define (bitmatrix-negate B)
  (define ocells (cells B))
  (define !cells (send ocells clone/clear))
  (define one (make-b:one))
  (for ([i* (in-dimensions (dims B))])
    (cond
     [(send ocells ref i*)
      => (lambda (v) (send !cells put i* (make-b:neg v)))]
     [else
      (send !cells put i* one)]))
  (bitmatrix (dims B) !cells))

(define (bitmatrix-subset B0 B1)
  (for/fold ([acc (make-b:one)])
            ([i* (bitmatrix-dense-indices B0)])
    ;; B0(i*) = false
    ;;   else
    ;; B1(i*) != true
    (define B0i* (or (B0 i*) (make-b:zero)))
    (define B1i* (or (B1 i*) (make-b:zero)))
    (make-b:and
      acc
      (make-b:or
        (make-b:neg B0i*)
        B1i*))))

(define (bitmatrix=? B0 B1)
  (make-b:and (bitmatrix-subset B0 B1)
              (bitmatrix-subset B1 B0)))

;; -----------------------------------------------------------------------------

(define (bitmatrix-closure B)
  (define D (dims B))
  (unless (and (= 2 (dimensions-count D)) (d:square? D))
    (raise-user-error 'bitmatrix-closure "Non-square dimensions"))
  (if (bitmatrix-empty? B)
    (bitmatrix-clone B)
    (raise-user-error 'closure "Not implemented")))

(define (bitmatrix-transpose B)
  (define D (dims B))
  (define D+ (dimensions-transpose D))
  (define rows (dimensions-rows D))
  (define cols (dimensions-cols D))
  (raise-user-error 'transpose "Not implemented"))
  ;; L688 kodkod.engine.bool.BooleanMatrix
  ;(define C (send (cells B) clone))
  ;(for ([i* (in-

(define (bitmatrix-and B0 B1)
  (define Acells (send (cells B0) clone/clear))
  (unless (or (bitmatrix-empty? B0)
              (bitmatrix-empty? B1))
              (send (cells B1) isEmpty?))
    (for ([i* (send (cells B0) indices)])
      (send Acells put i*
        (make-b:and (send (cells B0) ref i*)
                    (send (cells B1) ref i*))))
  (bitmatrix (dims B0) Acells))

(define (bitmatrix-or B0 B1)
  (cond
   [(bitmatrix-empty? B1)
    (bitmatrix-clone B0)]
   [(bitmatrix-empty? B0)
    (bitmatrix-clone B1)]
   [else
    (define Acells (send (cells B0) clone))
    (define Bcells (cells B1))
    ;; -- Take (binary)-OR of current cells and each matrice's dense entries
    (for* ([i* (send Bcells indices)])
      (send Acells put i*
        (make-b:or (send Acells ref i*)
                   (send Bcells ref i*))))
    (bitmatrix (dims B0) Acells)]))

(define (bitmatrix-difference B0 B1)
  (define Acells (send (cells B0) clone))
  (define Bcells (cells B1))
  ;; --
  (for ([i* (send Bcells indices)])
    (send Acells put i*
      (make-b:difference (send Acells ref i*)
                         (send Bcells ref i*))))
  (bitmatrix (dims B0) Acells))

(define (bitmatrix-dot B0 B1)
  ;; TODO
  (raise-user-error 'nodot))
  ;(define Acells (send (cells B0) clone/clear))
  ;(define Bcells (cells B1))
  ;;; --
  ;(unless (or (bitmatrix-empty? B0)
  ;            (bitmatrix-empty? B1))
  ;            (send (cells B1) isEmpty?))
  ;  (for ([i (send (cells B0) indices)])
  ;    (send Acells put
  ;      (make-b:and (send (cells B0) ref i)
  ;                  (send (cells B1) ref i))))
  ;(bitmatrix (dims B0) Acells))

(define (bitmatrix-cross B0 B1)
  (raise-user-error 'bitmatrix-cross "Not implemented"))

(define (bitmatrix-implies B0 B1)
  (bitmatrix-or
    (bitmatrix-negate B0)
    B1))

(define (bitmatrix-iff B0 B1)
  (bitmatrix-and
    (bitmatrix-implies B0 B1)
    (bitmatrix-implies B1 B0)))

;; -----------------------------------------------------------------------------
;; --- more utilities

(define (in-bitmatrix B)
  (raise-user-error 'in-bitmatrix "Not implemented"))

(define (bitmatrix-choice b B1 B2)
  (cond
   [(b:one? b)
    B1]
   [(b:zero? b)
    B2]
   [else
    ;; TODO push `b` into matrix
    (raise-user-error 'bitmatrix-choice
      "Cannot branch on non-atomic condition")]))

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)

  (define U (kk:universe '(A B C D)))
  (define D (universe->dimensions U))
  (define B= (bitmatrix-identity D))
  (define B+ (bitmatrix-top D))
  (define B- (bitmatrix-bot D))

  (test-case "bitmatrix-density"
    (check-equal? (bitmatrix-density B=) 4)
    (check-equal? (bitmatrix-density B+) 16)
    (check-equal? (bitmatrix-density B-) 0)
  )

  (test-case "bitmatrix-dense-indices"
    (check-equal? (bitmatrix-dense-indices B=)
      (for/list ([i (in-range 4)]) (list i i)))
    (check-equal? (bitmatrix-dense-indices B+)
      (for*/list ([i (in-range 4)] [j (in-range 4)]) (list i j)))
    (check-equal? (bitmatrix-dense-indices B-) '())
  )

  (test-case "bitmatrix-empty?"
    (check-equal? (bitmatrix-empty? B+) #f)
    (check-equal? (bitmatrix-empty? B=) #f)
    (check-equal? (bitmatrix-empty? B-) #t)
  )

  (test-case "bitmatrix-none"
    (check-equal? (bitmatrix-none B+) (make-b:zero))
    (check-equal? (bitmatrix-none B=) (make-b:zero))
    (check-equal? (bitmatrix-none B-) (make-b:one))
  )

  (test-case "bitmatrix-lone"
    (check-equal? (bitmatrix-lone B=) (make-b:zero))
    (check-equal? (bitmatrix-lone B+) (make-b:zero))
    (check-equal? (bitmatrix-lone B-) (make-b:one))
  )

  (test-case "bitmatrix-one"
    (check-equal? (bitmatrix-one B=) (make-b:zero))
    (check-equal? (bitmatrix-one B+) (make-b:zero))
    (check-equal? (bitmatrix-one B-) (make-b:zero))
  )

  (test-case "bitmatrix-some"
    (check-equal? (bitmatrix-some B=) (make-b:one))
    (check-equal? (bitmatrix-some B+) (make-b:one))
    (check-equal? (bitmatrix-some B-) (make-b:zero))
  )

  (test-case "bitmatrix-negate"
    (check-equal? (bitmatrix-count (bitmatrix-negate B=)) (- 16 4))
    (check-equal? (bitmatrix-count (bitmatrix-negate B+)) 0)
    (check-equal? (bitmatrix-count (bitmatrix-negate B-)) 16)
  )

  (test-case "bitmatrix-and"
    (check-equal? (bitmatrix-count (bitmatrix-and B+ B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-and B- B+))  0)
    (check-equal? (bitmatrix-count (bitmatrix-and B- B-))  0)
    (check-equal? (bitmatrix-count (bitmatrix-and B+ B=))  4)
    (check-equal? (bitmatrix-count (bitmatrix-and B= B-))  0)
  )

  (test-case "bitmatrix-or"
    (check-equal? (bitmatrix-count (bitmatrix-or B+ B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-or B- B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-or B- B-))  0)
    (check-equal? (bitmatrix-count (bitmatrix-or B+ B=)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-or B= B-))  4)
  )

  (test-case "bitmatrix-difference"
    (check-equal? (bitmatrix-count (bitmatrix-difference B+ B+))  0)
    (check-equal? (bitmatrix-count (bitmatrix-difference B- B+))  0)
    (check-equal? (bitmatrix-count (bitmatrix-difference B+ B-)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-difference B- B-))  0)
    (check-equal? (bitmatrix-count (bitmatrix-difference B+ B=)) 12)
    (check-equal? (bitmatrix-count (bitmatrix-difference B= B-))  4)
  )

  (test-case "bitmatrix-implies"
    (check-equal? (bitmatrix-count (bitmatrix-implies B+ B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-implies B- B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-implies B+ B-))  0)
    (check-equal? (bitmatrix-count (bitmatrix-implies B- B-)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-implies B+ B=))  4)
    (check-equal? (bitmatrix-count (bitmatrix-implies B= B-)) 12)
  )

  (test-case "bitmatrix-iff"
    (check-equal? (bitmatrix-count (bitmatrix-iff B+ B+)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-iff B- B+))  0)
    (check-equal? (bitmatrix-count (bitmatrix-iff B+ B-))  0)
    (check-equal? (bitmatrix-count (bitmatrix-iff B- B-)) 16)
    (check-equal? (bitmatrix-count (bitmatrix-iff B+ B=))  4)
    (check-equal? (bitmatrix-count (bitmatrix-iff B= B-)) 12)
  )

  (test-case "bitmatrix=?"
    (check-equal? (bitmatrix=? B+ B+) (make-b:one))
    (check-equal? (bitmatrix=? B= B=) (make-b:one))
    (check-equal? (bitmatrix=? B- B-) (make-b:one))
    (check-equal? (bitmatrix=? B+ B=) (make-b:zero))
    (check-equal? (bitmatrix=? B+ B-) (make-b:zero))
    (check-equal? (bitmatrix=? B= B-) (make-b:zero))
    ;(check-equal? (bitmatrix=? (bitmatrix-and B+ B-) B-))
  )

  (test-case "bitmatrix-choice"
  )

  (test-case "bitmatrix-closure"
  )

)

