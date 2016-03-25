#lang racket/base

(provide (rename-out
  [kk-read read]
  [kk-read-syntax read-syntax]
))

(require
  kodkod/private/problem-spec

  syntax/strip-context
)

;; =============================================================================

(define (kk-read in)
  (syntax->datum (kk-read-syntax #f in)))

(define (kk-read-syntax src-path in)
  (define kk (read-problem src-path in))
  (lint-problem kk)
  (printf "got problem ~a\n" kk)
  (with-syntax ([mod-id 'kodkod])
    (strip-context
      #'(module mod-id racket/base
          (printf "hello world\n")))))

