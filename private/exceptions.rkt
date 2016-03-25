#lang racket/base

(provide
  not-implemented
  ;; 

  internal-error
  ;; (internal-error Symbol String Any *)

  parse-error

  parse-warning

  debug
)

;; =============================================================================

(define (not-implemented)
  (raise-user-error 'kodkod "Not implemented"))

(define-syntax-rule (internal-error loc msg arg* ...)
  (error (string->symbol (format "internal-error:~a" loc)) msg arg* ...))

(define-syntax-rule (parse-error src msg arg* ...)
  (error 'parse-error
    (string-append
      (format msg arg* ...)
      (format "\n  src: ~a" src))))

(define-syntax-rule (parse-warning loc val)
  (printf "WARNING could not parse datum '~a'\n  at: ~a\n" val loc))

(define-syntax-rule (debug msg arg* ...)
  (when #t
    (printf msg arg* ...)
    (newline)))
