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
  kodkod/private/translate/fol
  kodkod/private/translate/cnf

  racket/match
)

;; =============================================================================

(define (translate-kk:problem kk)
  (let* ([kk (optimize-kk:problem kk)]
         [B (kk:problem->kk:bool kk)]
         [cnf (kk:bool->cnf B)])
    cnf))

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

