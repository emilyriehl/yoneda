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
#def dhom 
	(A : U)						-- The base type.
	(x y : A)					-- Two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(C : A -> U)				-- A type family.
	(u : C x)					-- A lift of the domain.
	(v : C y)					-- A lift of the codomain.
	: U
  	:= <{t : 2 | Δ¹ t } -> C (f t) [t === 0_2 |-> u , t === 1_2 |-> v ]>

  -- dependent hom with specified domain
#def dhomFrom
	(A : U)						-- The base type.
	(x y : A)					-- Two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(C : A -> U)				-- A type family.
	(u : C x)					-- A lift of the domain.
	: U
   	:= (∑ (v : C y), dhom A x y f C u v)

-- [RS17, Section 8 Prelim]
#def dhom2 
	(A : U)							-- The base type.
	(x y z : A)						-- Three points in the base.
	(f : hom A x y)					-- An arrow in the base.
	(g : hom A y z)					-- An arrow in the base.
	(h : hom A x z)					-- An arrow in the base.
	(alpha : hom2 A x y z f g h)	-- A composition witness in the base.
	(C : A -> U)					-- A type family.
	(u : C x)						-- A lift of the initial point.
	(v : C y)						-- A lift of the second point.
	(w : C z)						-- A lift of the third point.
	(ff : dhom A x y f C u v)		-- A lift of the first arrow.
	(gg : dhom A y z g C v w)		-- A lift of the second arrow.
	(hh : dhom A x z h C u w)		-- A lift of the diagonal arrow.
	: U
  	:= <{(t1, t2) : 2 * 2 | Δ² (t1, t2)} -> C (alpha (t1, t2)) 
			[t2 === 0_2 |-> ff t1, 
			t1 === 1_2 |-> gg t2, 
			t2 === t1 |-> hh t2 ]>

-- [RS17, Definition 8.2]
#def isCovFam 
	(A : U)
	(C : A -> U)
	: U
	:= (x : A) -> (y : A) -> (f : hom A x y) -> (u : C x) 
		-> isContr (dhomFrom A x y f C u)

-- Type of covariant families over a fixed type
#def covFam (A : U) : U
	:= (∑ (C :  ((a : A) -> U)), isCovFam A C)

-- [RS17, covariant transport from beginning of Section 8.2]
#def covTrans
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisCov : isCovFam A C)
	(u : C x)
 	: C y
 	:= first (contraction-center (dhomFrom A x y f C u) (CisCov x y f u))

-- [RS17, covariant lift from beginning of Section 8.2]
#def covLift 
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisCov : isCovFam A C)
	(u : C x)
	: (dhom A x y f C u (covTrans A x y f C CisCov u))
 	:= second (contraction-center (dhomFrom A x y f C u) (CisCov x y f u))

#def covUniqueness
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisCov : isCovFam A C)
	(u : C x)
	(lift : dhomFrom A x y f C u)
	: (covTrans A x y f C CisCov u) = (first lift)
	:= total-path-to-base-path
		(C y)
		(\v -> dhom A x y f C u v)
		(contraction-center (dhomFrom A x y f C u) (CisCov x y f u))
		lift
		(contracting-htpy (dhomFrom A x y f C u) (CisCov x y f u) lift)

#def d-id-arr
	(A : U)
	(x : A)
	(C : A -> U)
	(u : C x)
	: dhom A x x (id-arr A x) C u u
	:= \t -> u

-- [RS17, Proposition 8.16, Part 2]
-- Covariant families preserve identities
#def covPresId
 	(A : U)
	(x : A)
 	(C : A -> U)
	(CisCov : isCovFam A C)
	(u : C x)
	: (covTrans A x x (id-arr A x) C CisCov u) = u
	:= covUniqueness A x x (id-arr A x) C CisCov u (u, d-id-arr A x C u)