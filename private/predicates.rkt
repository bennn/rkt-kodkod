#lang racket/base

(provide
  arity=?
  ;; (-> (Listof (Listof Any)) * Boolean)
  ;; True if every sub-list inside all argument lists have the same length

  (rename-out ;; from racket/contract
   [any/c Any]
   [boolean? Boolean]
   [box/c Box]
   [integer? Integer]
   [listof Listof]
   [natural-number/c Natural]
   [or/c U]
   [set/c Setof]
   [parameter/c Parameterof]
   [sequence/c Sequenceof]
   [string? String]
   [symbol? Symbol]
   [vectorof Vectorof]
   [void? Void]
  )

  contract-out
  ->
  ->*
  ->i
)

(require
  racket/contract
  racket/sequence
  (only-in racket/set
    set/c)
)

;; =============================================================================

(define-syntax-rule (assert=? x y)
  (unless (equal? x y)
    (raise-user-error 'assert=? "~a /= ~a" x y)))

(define (arity=? . x***)
  (for*/fold ([arity #f])
             ([x** (in-list x***)]
              [x*  (in-list x**)])
    (if arity
      (begin
        (unless (= (length x*) arity)
          (raise-user-error 'arity=? "expected arity ~a, got ~a" arity x*))
        arity)
      (length x*))))

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)

  (check-apply* arity=?
   ['() '()
    => #f] ;; Weird case
   ['(()) '(())
    => 0]
   ['((a b c) (d e f)) '((g h i))
    => 3]
   ['{(a1 a2) (b1 b2)} '{(c1 c2) (d1 d2) (e1 e2)}
    => 2])
)
