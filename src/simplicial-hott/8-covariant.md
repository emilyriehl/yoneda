# Covariantly functorial type families

These formalisations correspond to Section 8 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for instance the notion of contractible types.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `5-segal-types.md` - We make use of the notion of Segal types and their structures.


## Dependent hom types

In a type family over a base type, there is a dependent hom type of arrows that live over a specified arrow in the base type.

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
  	:= <{t : 2 | Δ¹ t } -> C (f t) 
			[t === 0_2 |-> u, 
			t === 1_2 |-> v ]>
```

It will be convenient to collect together dependent hom types with fixed domain but varying codomain.

```rzk
#def dhomFrom
	(A : U)						-- The base type.
	(x y : A)					-- Two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(C : A -> U)				-- A type family.
	(u : C x)					-- A lift of the domain.
	: U
   	:= (∑ (v : C y), dhom A x y f C u v)
```

There is also a type of dependent commutative triangles over a base commutative triangle.

```rzk
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
```

## Covariant families

A family of types over a base type is covariant if every arrow in the base has a unique lift with specified domain.

```rzk
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
```

## Representable covariant families

If A is a Segal type and a : A is any term, then hom A a defines a covariant family over A, and conversely if this family is covariant for every a : A, then A must be a Segal type. The proof involves a rather lengthy composition of equivalences.

```rzk
#def representable-dhom
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	(v : hom A a y)				-- A lift of the codomain.
	: U
	:= dhom A x y f (\z -> hom A a z) u v

-- By uncurrying (RS 4.2) we have an equivalence:
#def representable-dhom-uncurry
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	(v : hom A a y)				-- A lift of the codomain.
	: Eq (representable-dhom A a x y f u v) 
	(<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s, 
											((t === 1_2) /\ Δ¹ s) |-> v s, 
											(Δ¹ t /\ (s === 0_2)) |-> a, 
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>)
	:= curry-uncurry 2 2 Δ¹ ∂Δ¹ Δ¹ ∂Δ¹ (\t s -> A) 
		(\(t, s) -> recOR(((t === 0_2) /\ Δ¹ s) |-> u s, 
						((t === 1_2) /\ Δ¹ s) |-> v s, 
						(Δ¹ t /\ (s === 0_2)) |-> a, 
						(Δ¹ t /\ (s === 1_2)) |-> f t ))

#def representable-dhomFrom
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: U
	:= dhomFrom A x y f (\z -> hom A a z) u						

-- By uncurrying (RS 4.2) we have an equivalence:
#def representable-dhomFrom-uncurry
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Eq (representable-dhomFrom A a x y f u)
		(∑ (v : hom A a y), (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s, 
											((t === 1_2) /\ Δ¹ s) |-> v s, 
											(Δ¹ t /\ (s === 0_2)) |-> a, 
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
	:= family-Eq-total-Eq (hom A a y) (\v -> representable-dhom A a x y f u v)
		(\v -> (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s, 
											((t === 1_2) /\ Δ¹ s) |-> v s, 
											(Δ¹ t /\ (s === 0_2)) |-> a, 
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(\v -> representable-dhom-uncurry A a x y f u v)

#def cofibration-union-test
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Eq <{(t, s) : 2 * 2 | ∂□ (t, s)} -> A 
			[ ((t === 0_2) /\ Δ¹ s) |-> u s, 
						(Δ¹ t /\ (s === 0_2)) |-> a, 
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>
       <{(t, s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a,  ((t === 1_2) /\ (s === 1_2)) |-> y ]>
	:= cofibration_union (2 * 2) 
	(\(t, s) -> (t === 1_2) /\ Δ¹ s)
	(\(t, s) -> ((t === 0_2) /\ Δ¹ s) \/ (Δ¹ t /\ (s === 0_2)) \/ (Δ¹ t /\ (s === 1_2)))
	(\(t, s) -> A)
	(\(t, s) -> recOR(((t === 0_2) /\ Δ¹ s) |-> u s, 
						(Δ¹ t /\ (s === 0_2)) |-> a, 
						(Δ¹ t /\ (s === 1_2)) |-> f t ))  

#def base-hom-trivial-expansion
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Eq (<{(t, s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a,  ((t === 1_2) /\ (s === 1_2)) |-> y ]>) 		
		(hom A a y)
	:= (\v -> (\r -> v ((1_2, r))), 
			((\v -> \(t, s) -> v s, 
				\v -> refl),
			(\v -> \(t, s) -> v s, 
				\v -> refl)))		

#def base-hom-expansion
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Eq <{(t, s) : 2 * 2 | ∂□ (t, s)} -> A 
			[ ((t === 0_2) /\ Δ¹ s) |-> u s, 
						(Δ¹ t /\ (s === 0_2)) |-> a, 
						(Δ¹ t /\ (s === 1_2)) |-> f t ]> 		
		(hom A a y)	
	:= compose_Eq 
		(<{(t, s) : 2 * 2 | ∂□ (t, s)} -> A 
			[ ((t === 0_2) /\ Δ¹ s) |-> u s, 
						(Δ¹ t /\ (s === 0_2)) |-> a, 
						(Δ¹ t /\ (s === 1_2)) |-> f t ]> )
		(<{(t, s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a,  ((t === 1_2) /\ (s === 1_2)) |-> y ]>) 		
		(hom A a y)
		(cofibration-union-test A a x y f u)
		(base-hom-trivial-expansion A a x y f u)
```

## Covariant lifts, transport, and uniqueness

In a covariant family C over a base type A, a term u : C x may be transported along an arrow f : hom A x y to give a term in C y.

```rzk
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
```

## Covariant functoriality

The covariant transport operation defines a covariantly functorial action of arrows in the base on terms in the fibers. In particular, there is an identity transport law.

```rzk
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
```

## Natural transformations

A fiberwise map between covariant families is automatically "natural" commuting with the covariant lifts.

```rzk
-- [RS17, Proposition 8.17]
-- Covariant naturality
#def covariant-transformation-application
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisCov : isCovFam A C)
	(DisCov : isCovFam A D)
	(phi : (z : A) -> C z -> D z)
	(u : C x)
	: dhomFrom A x y f D (phi x u)
	:= (phi y (covTrans A x y f C CisCov u), 
	\t -> phi (f t) (covLift A x y f C CisCov u t))

#def covariant-transformation-naturality
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisCov : isCovFam A C)
	(DisCov : isCovFam A D)
	(phi : (z : A) -> C z -> D z)
	(u : C x)
	: (covTrans A x y f D DisCov (phi x u)) = (phi y (covTrans A x y f C CisCov u))
	:= covUniqueness A x y f D DisCov (phi x u)
		(covariant-transformation-application A x y f C D CisCov DisCov phi u)
```