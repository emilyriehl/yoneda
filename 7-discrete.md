# Discrete types

These formalisations correspond to Section 7 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites
TODO

## The definition
```rzk
-- [RS17, Definition 7.1]
-- Discrete types are types in which the hom-types are canonically equivalent to identity types.

#def id-to-arr 
    (A : U)             -- A type. 
    (x y : A)           -- Two points of type A.
    (p : x = y)         -- A path p from x to y in A.
    : hom A x y         -- An arrow p from x to y in A.
    := idJ(A, x, \y' -> \p' -> hom A x y', (id-arr A x), y, p) 

#def isDiscrete 
    (A : U)             -- A type. 
    : U
    := (x : A) -> (y : A) -> isEquiv (x =_{A} y) (hom A x y) (id-to-arr A x y)
```
