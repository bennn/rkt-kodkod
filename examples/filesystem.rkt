#lang kodkod

{d0 d1 f0 f1 f2}

(File      {}         {(f0) (f1) (f2)})
(Dir       {}         {(d0) (d1)})
(Root      {(d0)}     {(d0)})
(contents  {(d0 d1)}  {(d0 d0) (d0 d1) (d0 f0) (d0 f1) (d0 f2)
                       (d1 d0) (d1 d1) (d1 f0) (d1 f1) (d1 f2)})

(contents ⊆ (Dir → (Dir ∪ File)))
(∀ ([d : Dir]) ∣ (¬ (d ⊆ (d ∙ (^ contents)))))
(Root ⊆ Dir)
((File ∪ Dir) ⊆ (∙ Root (* contents)))
