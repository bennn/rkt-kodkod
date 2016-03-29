#lang racket/base
;#lang kodkod
;
;;; Should look something like this... want to define #lang sudoku
;;; TODO need to program these files!
;
;;; -----------------------------------------------------------------------------
;(universe
;  n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)
;
;;; -----------------------------------------------------------------------------
;(var
;  TODO)
;
;(define (make-row lo hi)
;  (let ([rng (map list (range lo (+ 1 hi)))])
;    (list rng rng)))
;
;(define num_1 (make-row 1 9))
;
;(define r1 (make-row 1 3))
;(define r2 (make-row 4 6))
;(define r3 (make-row 7 9))
;
;;; -----------------------------------------------------------------------------
;(formula
;  (∀ (x : num) (y : num) . (some (grid x y)))
;  (∀ (x : num) (y : num) . (no (grid x y) /\ (grid x (\ num y))))
;  (∀ (x : num) (y : num) . (no (grid x y) /\ (grix (\ num x) y)))
;
;  (∀ (x : r1) (y : r1)   . (no (grid x y) /\ (grid (\ r1 x) (\ r1 y))))
;  (∀ (x : r1) (y : r2)   . (no (grid x y) /\ (grid (\ r1 x) (\ r2 y))))
;  (∀ (x : r1) (y : r3)   . (no (grid x y) /\ (grid (\ r1 x) (\ r3 y))))
;
;  (∀ (x : r2) (y : r1)   . (no (grid x y) /\ (grid (\ r2 x) (\ r1 y))))
;  (∀ (x : r2) (y : r2)   . (no (grid x y) /\ (grid (\ r2 x) (\ r2 y))))
;  (∀ (x : r2) (y : r3)   . (no (grid x y) /\ (grid (\ r2 x) (\ r3 y))))
;
;  (∀ (x : r3) (y : r1)   . (no (grid x y) /\ (grid (\ r3 x) (\ r1 y))))
;  (∀ (x : r3) (y : r2)   . (no (grid x y) /\ (grid (\ r3 x) (\ r2 y))))
;  (∀ (x : r3) (y : r3)   . (no (grid x y) /\ (grid (\ r3 x) (\ r3 y))))
;)
