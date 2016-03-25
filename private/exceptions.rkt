#lang racket/base

(provide
  not-implemented
  ;; 

  internal-error
  ;; (internal-error Symbol String Any *)

  parse-error

  parse-warning
)

;; =============================================================================

(define (not-implemented)
  (raise-user-error 'kodkod "Not implemented"))

(define-syntax-rule (internal-error loc msg arg* ...)
  (error (string->symbol (format "internal-error:~a" loc)) msg arg* ...))

(define-syntax-rule (parse-error loc msg arg* ...)
  (error (string->symbol (format "parse-error:~a" loc)) msg arg* ...))

(define-syntax-rule (parse-warning loc stx)
  (printf "WARNING (~a:~a) could not parse datum '~a'\n"
    (syntax-line stx) (syntax-column stx) (syntax->datum stx)))
