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

  -- dependent hom with specified domain
#def dhomFrom : (A : U) -> (x : A) -> (y : A) -> (f : hom A x y) -> (C : (x : A) -> U) -> (u : C x) -> U
   := \A -> \x -> \y -> \f -> \C -> \u -> (∑ (v : C y), dhom A x y f C u v)

-- [RS17, Section 8 Prelim]
#def dhom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> (alpha : hom2 A x y z f g h) -> (C : (x : A) -> U) -> (u : C x) -> (v : C y) -> (w : C z) -> (ff : dhom A x y f C u v) -> (gg : dhom A y z g C v w) -> (hh : dhom A x z h C u w) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h -> \alpha -> \C -> \u -> \v -> \w -> \ff -> \gg -> \hh -> <{(t1, t2) : 2 * 2 | Δ² (t1, t2)} -> C (alpha (t1, t2)) [ ∂Δ² (t1, t2) |->
        	recOR(t2 === 0_2, t1 === 1_2 \/ t2 === t1, ff t1, recOR(t1 === 1_2, t2 === t1, gg t2, hh t2)) ]>

-- [RS17, Definition 8.2]
#def isCovFam : (A : U) -> (C : (a : A) -> U) -> U
	:= \A -> \C -> (x : A) -> (y : A) -> (f : hom A x y) -> (u : C x) 
--	-> isContr (∑ (v : C y), dhom A x y f C u v)
	-> isContr (dhomFrom A x y f C u)


-- Type of covariant families over a fixed type
#def covFam : (A : U) -> U
	:= \A -> (∑ (C :  ((a : A) -> U)), isCovFam A C)

-- [RS17, covariant transport and lift from beginning of Section 8.2]
-- TODO
-- #def covTrans : (A : U) -> (C : A -> U) -> (_ : isCovFam A C)
-- 				-> (x : A) -> (y : A) -> (f : hom A x y) -> (u : C x)
-- 				-> C y
-- 	:= \A -> \C -> \CisCov -> \x -> \y -> \f -> \u -> first (contraction-center CisCov)
        	
-- [RS17, Remark 8.3]
#def reindexOfCovFamIsCov : (A : U) -> (B : U) -> (F : (b : B) -> A) -> (C : (a : A) -> U) -> (AisCovFam : isCovFam A C) -> (isCovFam B (reindex A B F C))
	:= \A -> \B -> \F -> \C -> \AisCovFam -> \x -> \y -> \f -> \u ->
	(
	
	(contraction-center (∑ (v : C (F y)), 
								(dhom A (F x) (F y) (ap B A F x y f) C u v))
							(AisCovFam (F x) (F y) (ap B A F x y f) u),
								
		(contracting-htpy (∑ (v : C (F y)), 
								dhom A (F x) (F y) (ap B A F x y f) C u v))
							(AisCovFam (F x) (F y) (ap B A F x y f) u)
			)
			
	)

-- [RS17, alternative def. from Proposition 8.4]
#def isCovFam' : (A : U) -> (C : (a : A) -> U) -> U
	:= \A -> \C -> (x : A) -> (y : A) -> (f : hom A x y) -> (u : C x) 
	-> isContr <{t : 2 | Δ¹ t} -> C(f t) >
```

-- [RS17, Proposition 8.4]
-- We should prove this in one step since this amounts to transporting along equivalent types of lifting
--#def isCovFam-iff-CovFam' : (A : U) -> (C : (a : A) -> (_ : isCovFam A C) -> --isCovFam' A C
--	:= TODO

