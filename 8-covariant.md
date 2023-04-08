# Covariantly functorial type families

These formalisations correspond to Section 8 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites
TODO

```rzk
-- [RS17, Section 8 Prelim]
-- The type of dependent arrows in C over f from u to v

#def dhom : (A : U) -> (x : A) -> (y : A) -> (f : hom A x y) -> (C : (x : A) -> U) -> (u : C x) -> (v : C y) -> U
  := \A -> \x -> \y -> \f -> \C -> \u -> \v -> <{t : 2 | Δ¹ t } -> C (f t) [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, u, v) ]>

-- [RS17, Section 8 Prelim]
#def dhom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> (alpha : hom2 A x y z f g h) -> (C : (x : A) -> U) -> (u : C x) -> (v : C y) -> (w : C z) -> (ff : dhom A x y f C u v) -> (gg : dhom A y z g C v w) -> (hh : dhom A x z h C u w) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h -> \alpha -> \C -> \u -> \v -> \w -> \ff -> \gg -> \hh -> <{(t1, t2) : 2 * 2 | Δ² (t1, t2)} -> C (alpha (t1, t2)) [ ∂Δ² (t1, t2) |->
        	recOR(t2 === 0_2, t1 === 1_2 \/ t2 === t1, ff t1, recOR(t1 === 1_2, t2 === t1, gg t2, hh t2)) ]>
        	
        	
 

```