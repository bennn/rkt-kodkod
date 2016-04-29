#lang kodkod

{true false}

(Bool      {(true) (false)}  {(true) (false)})
(var1      {}                {(true) (false)}) ;; Can I use Bool?
(var2      {}                {(true) (false)}) ;; Can I use Bool?

(var1 ⊆ Bool)

