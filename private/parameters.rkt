#lang racket/base

(require
  kodkod/private/predicates
  (for-syntax racket/base syntax/parse)
)

;; =============================================================================

(define-for-syntax (parameter-id? id)
  (regexp-match? #rx"^\\*[A-Z]([A-Z\\-])*\\??\\*$" (symbol->string id)))

(define-syntax (define-parameter stx)
  (syntax-parse stx
   [(_ name:id ctc val)
    (unless (parameter-id? (syntax-e #'name))
      (raise-user-error 'define-parameter "Invalid parameter name '~a', should be ALL-CAPS with asterisks as the first and last characters." (syntax-e #'name)))
    (syntax/loc stx
      (begin (define name (make-parameter val))
             (provide (contract-out (name ctc)))))]))

;; -----------------------------------------------------------------------------

(define-parameter *PRINT-INDENT* String (make-string 6 #\space))
;; Amount to indent nested lines when printing
