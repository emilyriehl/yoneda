# The Yoneda lemma

These formalisations correspond to Section 5 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

-- [RS17, Section 9]
-- Definition of evid and the Yoneda map as its claimed inverse

```rzk
#def
    evid : (A : U) -> (C : A -> U) -> (a : A)
        ->  ( (x : A) -> hom A a x -> C x) -> C a
    := \A -> \C -> \a -> \f -> (f a (id-arr A a))
-- TODO
-- #def
--  yon : 
```
