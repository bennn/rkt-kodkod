#lang info
(define collection "kodkod")
(define deps '("base" "rackunit-abbrevs" "rackunit-lib"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define setup-collects '("examples" "lang" "private"))
(define compile-omit-paths '("cryptominisat" "glucose-syrup"))
(define pkg-desc "KodKod solver")
(define version "0.1")
(define pkg-authors '(ben)) ;; emina?
(define scribblings '(("scribblings/kodkod.scrbl")))