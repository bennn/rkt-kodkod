kk
===

Kodkod, in Racket

(James Borholt is working on the same thing, but specialized to Rosette)



SAT Solver
---

Kodkod needs a SAT solver. Options:

- http://minisat.se/
- http://www.labri.fr/perso/lsimon/glucose/
  - https://github.com/wadoon/glucose
- http://fmv.jku.at/lingeling/
- https://github.com/msoos/cryptominisat


Small Model Theorem
---
- "if sat, there is a small proof"
- some prefix classes of FOL shown decidable via finite model property
  = satisfiable formulas have finite models
- verification : if no small models violate property and we know
                 the small model bound, we're done
- bound computed from syntax of spec Ai and property P
- lemma 1: depends on the size of index variables used in P
    not really sure how to use indices in a real formula


SATzilla
---
- empircal hardness models to choose solvers
- satzilla : construct per-instance algorithm portfolios
- 



Bounded Relational Logic
---

#### define ...



#### #:forall (var ... : type ...) | PROP



