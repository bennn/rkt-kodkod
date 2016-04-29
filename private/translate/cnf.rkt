#lang racket/base

;; cnf = conjunctive normal form

;; Convert various inputs to CNF

;; TODO
;; - cnf -> glucose etc

(require kodkod/private/predicates)
(provide
  kk:bool->cnf
)

;; -----------------------------------------------------------------------------

(require
  kodkod/private/ast
  kodkod/private/solver

  racket/match
)

;; =============================================================================

(struct cnf:var (
  +  ;; Boolean
  id ;; Symbol
) #:transparent )

(struct cnf:clauses (
  id ;; Symbol
  c* ;; (Listof (Listof cnf:var))
) #:transparent )

;; o = AND(i1, i2) ---> (i1 | !o) & (i2 | !o) & (!i1 | !i2 | o)
(define (cnf-and cnf1 cnf2)
  (define o (gensym 'and))
  (match-define (cnf:clauses i1 c1*) cnf1)
  (match-define (cnf:clauses i2 c2*) cnf2)
  (cnf:clauses o
    (list*
      (list (cnf:var #t i1) (cnf:var #f o))
      (list (cnf:var #t i2) (cnf:var #f o))
      (list (cnf:var #f i1) (cnf:var #f i2) (cnf:var #t o))
      (append c1* c2*))))

;; o = ITE(i, t, e) ---> (!i | !t | o) & (!i | t | !o) & (i | !e | o) & (i | e | !o)
(define (cnf-ite cnf0 cnf1 cnf2)
  (define o (gensym 'ite))
  (match-define (cnf:clauses i c0*) cnf0)
  (match-define (cnf:clauses t c1*) cnf1)
  (match-define (cnf:clauses e c2*) cnf2)
  (cnf:clauses o
    (list*
      (list (cnf:var #f i) (cnf:var #f t) (cnf:var #t o))
      (list (cnf:var #f i) (cnf:var #t t) (cnf:var #f o))
      (list (cnf:var #t i) (cnf:var #f e) (cnf:var #t o))
      (list (cnf:var #t i) (cnf:var #t e) (cnf:var #f o))
      (append c0* c1* c2*))))

(define (cnf-neg cnf)
  (match-define (cnf:clauses i c*) cnf)
  (cnf:clauses i
    (for/list ([c (in-list c*)])
      (for/list ([v (in-list c)])
        (match-define (cnf:var + id) v)
        (cnf:var (not +) id)))))

;; o = OR(i1, i2)  ---> (!i1 | o) & (!i2 | o) & (i1 | i2 | !o).
(define (cnf-or cnf1 cnf2)
  (define o (gensym 'or))
  (match-define (cnf:clauses i1 c1*) cnf1)
  (match-define (cnf:clauses i2 c2*) cnf2)
  (cnf:clauses o
    (list*
      (list (cnf:var #f i1) (cnf:var #t o))
      (list (cnf:var #f i2) (cnf:var #t o))
      (list (cnf:var #t i1) (cnf:var #t i2) (cnf:var #f o))
      (append c1* c2*))))

(define (cnf-sat)
  (cnf:clauses (gensym 'sat) '()))

(define (cnf-unsat)
  (define s (gensym 'var:unsat))
  (cnf:clauses (gensym 'unsat) (list (cnf:var #t s) (cnf:var #f s))))

(define (cnf-var v)
  (define s (string->symbol (format "var:~a" v)))
  (cnf:clauses s (list (list (cnf:var #t v)))))

;; -----------------------------------------------------------------------------

(define (kk:bool->cnf b)
  (match-kk:bool b
   [(b:zero)
    (cnf-unsat)]
   [(b:one)
    (cnf-sat)]
   [(b:var v)
    (cnf-var v)]
   [(b:neg b)
    (cnf-neg (kk:bool->cnf b))]
   [(b:and b0 b1)
    (cnf-and (kk:bool->cnf b0)
             (kk:bool->cnf b1))]
   [(b:or b0 b1)
    (cnf-or (kk:bool->cnf b0)
            (kk:bool->cnf b1))]
   [(b:if/else b0 b1 b2)
    (cnf-ite (kk:bool->cnf b0)
             (kk:bool->cnf b1)
             (kk:bool->cnf b2))]))

;; =============================================================================

(module+ test
  (require
    rackunit
    rackunit-abbrevs
    kodkod/private/bool
  )

  (let ([cnf (kk:bool->cnf (make-b:one))])
    (check-true (null? (cnf:clauses-c* cnf))))

)
