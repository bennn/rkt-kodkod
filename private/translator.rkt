#lang racket/base

;; TODO
;; - function composition instead of `let ...` ?

(provide
  translate-kk:problem
  ;; (-> Problem Circuit)

  ;evaluate
  ;; (-> Formula Instance Boolean)
  ;; Possible to implement this?

)

;; -----------------------------------------------------------------------------

(require
  kodkod/private/ast
  kodkod/private/translate/first-order-logic

  racket/match
)

;; =============================================================================

(define (translate-kk:problem kk)
  (let* ([kk (optimize-kk:problem kk)]
         [M (kk:problem->bitmatrix kk)])
    M))
;         [cnf (kk:bool->cnf cc)])
;    cnf))

;; =============================================================================
;; === Optimize

;; - break matrix symmetries
;; - skolemize results
;; that's all?
(define (optimize-kk:problem kk)
  (let ([kk (skolemize-kk:problem kk)])
    kk))

(define (skolemize-kk:problem kk)
  (printf "Warning: skolemization not implemented\n")
  kk)

;; =============================================================================
;; === Bool -> CNF

(define (kk:bool->cnf cc)
  (void))

;; =============================================================================
;; === Problem -> SAT
;
;(define-syntax-rule (unbound-atom kk a)
;  (raise-user-error 'kodkod "Invalid atom '~a', universe is ~a" a (problem-universe kk)))
;
;(define (atom->index kk a)
;  (or (for/first ([u (in-list (problem-universe kk))]
;                  [i (in-naturals)]
;                  #:when (eq? a u))
;        i)
;      (unbound-atom kk a)))
;
;(define (atom->index* kk a*)
;  (for/list ([a (in-list a*)])
;    (atom->index kk a)))
;
;(define (index->atom kk i)
;  (or (for/first ([u (in-list (problem-universe kk))]
;                  [j (in-naturals)]
;                  #:when (= i j))
;        u)
;      (unbound-atom kk i)))
;
;(define (index->atom* kk i*)
;  (for/list ([i (in-list i*)])
;    (index->atom kk i)))
;
;;; Convert a problem spec. to SAT
;(define (problem->sat kk)
;  ;; kodkod->bool
;  ;; symmetry-break
;  ;; bool->cnf
;  ;; model/bool->model/kodkod
;  (void))
;
;;; Turn a relational formula to boolean logic
;(define (problem->bool kk)
;  (void))
;
;;; Transform boolean formula to conjunctive normal form
;(define (bool->cnf bool)
;  (void))
;
;;; Convert boolean model to a model of the original problem
;;; TODO is a model different from a formula?
;(define (bool->kodkod bool)
;  (void))
;
