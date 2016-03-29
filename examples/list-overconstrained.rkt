#lang kodkod

;; Overconstrained ist specification
;; KodKod figure 4-1

;; TODO lots of redundancy in the variable decls

;; -----------------------------------------------------------------------------
(universe
 l0 l1 l2 t0 t1 t2)

;; -----------------------------------------------------------------------------
(var
  (List
   {}
   {(l0) (l1) (l2)}))

(var
  (Nil
   {}
   {(l0) (l1) (l2)}))

(var
  (Cons
   {}
   {(l0) (l1) (l2)}))

(var
  (Thing
   {}
   {(t0) (t1) (t2)}))

(var
  (car
   {}
   {(l0 t0) (l0 t1) (l0 t2)
    (l1 t0) (l1 t1) (l1 t2)
    (l2 t0) (l2 t1) (l2 t2)}))

(var
  (cdr
   {}
   {(l0 l0) (l0 l1) (l0 l2)
    (l1 l0) (l1 l1) (l1 l2)
    (l2 l0) (l2 l1) (l2 l2)}))

(var
  (equivTo
   {}
   {(l0 l0) (l0 l1) (l0 l2)
    (l1 l0) (l1 l1) (l1 l2)
    (l2 l0) (l2 l1) (l2 l2)}))

(var
  (prefixes
   {}
   {(l0 l0) (l0 l1) (l0 l2)
    (l1 l0) (l1 l1) (l1 l2)
    (l2 l0) (l2 l1) (l2 l2)}))

;; -----------------------------------------------------------------------------
(formula
  (List = (Cons ∪ Nil))
  (no (Cons ∩ Nil))

  (car ⊆ (Cons → Thing))
  (∀ ((a : Cons)) ∣ (one (a ∙ car)))

  (cdr ⊆ (Cons → List))
  (∀ ((a : Cons)) ∣ (one (a ∙ cdr)))
  (∀ ((a : List)) ∣ (∃ ([e : Nil]) ∣ (e ⊆ (a ∙ (^ cdr)))))

  (equivTo ⊆ (List → List))
  (∀ ((a : List) (b : List)) ∣ ((a ⊆ (b ∙ equivTo)) ⇔ (∧ (= (a ∙ car) (b ∙ car))
                                                       (= ((a ∙ cdr) ∙ equivTo)
                                                          ((b ∙ cdr) ∙ equivTo)))))

  (prefixes ⊆ (List → List))
  (∀ ((e : Nil) (a : List)) ∣ (e ⊆ (a ∙ prefixes)))
  (∀ ((e : Nil) (a : Cons)) ∣ (¬ (a ⊆ (e ∙ prefixes))))
  (∀ ((a : Cons) (b : Cons)) ∣ ((a ⊆ (b ∙ prefixes)) ⇔ (∧ (= (a ∙ car) (b ∙ car))
                                                        ((a ∙ cdr) ⊆ ((b ∙ cdr) ∙ prefixes)))))
                                                        ;; ⊆ works? Should be ∈
)

