#lang racket/base

(provide (rename-out
  [kk-read read]
  [kk-read-syntax read-syntax]
))

(require
  kodkod/private/parser
  kodkod/private/translator
  syntax/strip-context
)

;; =============================================================================

(define (kk-read in)
  (syntax->datum (kk-read-syntax #f in)))

(define (kk-read-syntax src-path in)
  (define-values (r* cpu real gc)
    (time-apply (lambda () (translate-kk:problem (read-kk:problem src-path in))) '()))
  (printf "=== ~ams : ~a\n" real r*)
  ;(define kk (read-kk:problem src-path in))
  ;(define cnf (translate-kk:problem kk))
  ;(displayln cnf)
  (strip-context
    #'(module kodkod racket/base
        (printf "hello world\n"))))

