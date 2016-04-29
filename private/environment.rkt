#lang racket/base

(provide
  env-init
  env-ref
  env-put
  ⊕
  env-union
)

;; =============================================================================
;; (define-type Binding (HashTable Symbol Constant))

(define (env-init)
  (hasheq))

(define (env-ref b v)
  (hash-ref b v (lambda () (raise-user-error 'env-ref "No value for key '~a'" v))))

(define (env-put b v s)
  (hash-set b v s))

(define ⊕ ;; \oplus
  env-put)

(define (env-union b0 b1)
  (for/fold ([b b0])
            ([(k v) (in-hash b1)])
    (env-put b k v)))

;; =============================================================================

(module+ test
  (require rackunit rackunit-abbrevs)

  (test-case "simple-env"
    (let ([E (env-init)])
      (check-exn #rx"ref"
        (lambda () (env-ref E 'yolo)))
      (define E+ (env-put E 'yolo 'wepa))
      (check-equal? (env-ref E+ 'yolo) 'wepa))
  )

)
