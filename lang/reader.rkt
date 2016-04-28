#lang racket/base

(provide (rename-out
  [kk-read read]
  [kk-read-syntax read-syntax]
))

(require
  kodkod/private/parser
  syntax/strip-context
)

;; =============================================================================

(define (kk-read in)
  (syntax->datum (kk-read-syntax #f in)))

(define (kk-read-syntax src-path in)
  (define kk (read-kk:problem src-path in))
  (displayln (format-kk:problem kk))
  (strip-context
    #'(module kodkod racket/base
        (printf "hello world\n"))))

