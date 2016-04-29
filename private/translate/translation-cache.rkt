#lang racket/base

;; TODO
;; - not implemented
;; - use hash/dict interface?

;; Cache for translating formulas to boolean circuits

(require kodkod/private/predicates)
(provide (contract-out
  (make-cache
   (->* [] [strategy?] Cache))

  (cache-ref
   (-> Cache Any Any))

  (cache-put
   (-> Cache Any Cache))
  ;; May not actually put the value in the cache!
  ;; Depends on the strategy
))

;; -----------------------------------------------------------------------------

(require
)

;; =============================================================================

(define CACHE-STRATEGIES
  '(null))

(define (strategy? s)
  (memq s CACHE-STRATEGIES))

;; -----------------------------------------------------------------------------

(struct cache (
  strategy ;; Strategy
) #:transparent )
(define Cache cache?)

(define (make-cache [strategy 'null])
  (cache strategy))

(define (cache-ref C v)
  #f)

(define (cache-put C v)
  C)
