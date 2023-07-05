# Covariantly functorial type families

These formalisations correspond to Section 8 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the notion of contractible types.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `5-segal-types.md` - We make use of the notion of Segal types and their
  structures.

## Dependent hom types

In a type family over a base type, there is a dependent hom type of arrows that
live over a specified arrow in the base type.

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
			[t === 0_2 |-> u ,
			t === 1_2 |-> v ]>
```

It will be convenient to collect together dependent hom types with fixed domain
but varying codomain.

```rzk
#def dhomFrom
	(A : U)						-- The base type.
	(x y : A)					-- Two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(C : A -> U)				-- A type family.
	(u : C x)					-- A lift of the domain.
	: U
   	:= (Σ (v : C y) , dhom A x y f C u v)
```

There is also a type of dependent commutative triangles over a base commutative
triangle.

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
  	:= <{(t1 , t2) : 2 * 2 | Δ² (t1 , t2)} -> C (alpha (t1 , t2))
			[t2 === 0_2 |-> ff t1 ,
			t1 === 1_2 |-> gg t2 ,
			t2 === t1 |-> hh t2 ]>
```

## Covariant families

A family of types over a base type is covariant if every arrow in the base has a
unique lift with specified domain.

```rzk
-- [RS17, Definition 8.2]
#def isCovFam
	(A : U)
	(C : A -> U)
	: U
	:= (x : A) -> (y : A) -> (f : hom A x y) -> (u : C x)
		-> is-contr (dhomFrom A x y f C u)

-- Type of covariant families over a fixed type
#def covFam (A : U) : U
	:= (Σ (C : ((a : A) -> U)) , isCovFam A C)
```

## Representable covariant families

If A is a Segal type and a : A is any term, then hom A a defines a covariant
family over A, and conversely if this family is covariant for every a : A, then
A must be a Segal type. The proof involves a rather lengthy composition of
equivalences.

```rzk
#def dhom-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	(v : hom A a y)				-- A lift of the codomain.
	: U
	:= dhom A x y f (\ z -> hom A a z) u v

-- By uncurrying (RS 4.2) we have an equivalence:
#def uncurried-dhom-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	(v : hom A a y)				-- A lift of the codomain.
	: Equiv (dhom-representable A a x y f u v)
	(<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>)
	:= curry-uncurry 2 2 Δ¹ ∂Δ¹ Δ¹ ∂Δ¹ (\ t s -> A)
		(\ (t , s) -> recOR (((t === 0_2) /\ Δ¹ s) |-> u s ,
						((t === 1_2) /\ Δ¹ s) |-> v s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ))

#def dhomFrom-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: U
	:= dhomFrom A x y f (\ z -> hom A a z) u

-- By uncurrying (RS 4.2) we have an equivalence:
#def uncurried-dhomFrom-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(Σ (v : hom A a y) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
	:= total-equiv-family-equiv (hom A a y) (\ v -> dhom-representable A a x y f u v)
		(\ v -> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(\ v -> uncurried-dhom-representable A a x y f u v)

#def square-to-hom2-pushout
	(A : U)
	(w x y z : A)
	(u : hom A w x)
	(f : hom A x z)
	(g : hom A w y)
	(v : hom A y z)
	: (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> g t ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>)
	-> (Σ (d : hom A w z) , prod (hom2 A w x z u f d) (hom2 A w y z g v d))
	:= \ sq -> ((\ t -> sq (t , t)) , (\ (t , s) -> sq (s , t) , \ (t , s) -> sq (t , s)))

#def hom2-pushout-to-square
	(A : U)
	(w x y z : A)
	(u : hom A w x)
	(f : hom A x z)
	(g : hom A w y)
	(v : hom A y z)
	: (Σ (d : hom A w z) , prod (hom2 A w x z u f d) (hom2 A w y z g v d))
	-> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> g t ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>)
	:= \ (d , (alpha1 , alpha2)) (t , s) -> recOR (t <= s |-> alpha1 (s , t) ,
												s <= t |-> alpha2 (t , s))
#def Eq-square-hom2-pushout
	(A : U)
	(w x y z : A)
	(u : hom A w x)
	(f : hom A x z)
	(g : hom A w y)
	(v : hom A y z)
	: Equiv (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> g t ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>)
		(Σ (d : hom A w z) , prod (hom2 A w x z u f d) (hom2 A w y z g v d))
	:= (square-to-hom2-pushout A w x y z u f g v ,
		((hom2-pushout-to-square A w x y z u f g v , \ sq -> refl) ,
		(hom2-pushout-to-square A w x y z u f g v , \ alphas -> refl)))

#def representable-dhomFrom-uncurry-hom2
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (Σ (v : hom A a y) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(Σ (v : hom A a y) , (Σ (d : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
	:= total-equiv-family-equiv (hom A a y)
		(\ v -> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(\ v -> (Σ (d : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
		(\ v -> Eq-square-hom2-pushout A a x a y u f (id-arr A a) v)

#def representable-dhomFrom-hom2
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (Σ (v : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
	:= triple-comp-equiv
		(dhomFrom-representable A a x y f u)
		(Σ (v : hom A a y) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(Σ (v : hom A a y) , (Σ (d : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
		(Σ (d : hom A a y) , (Σ (v : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
		(uncurried-dhomFrom-representable A a x y f u)
		(representable-dhomFrom-uncurry-hom2 A a x y f u)
		(sigma-fubini (hom A a y) (hom A a y)
			(\ v d -> prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))

#def representable-dhomFrom-hom2-dist
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d)))
	:= right-cancel-equiv
		(dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d)))
		(Σ (d : hom A a y) , (Σ (v : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
		(representable-dhomFrom-hom2 A a x y f u)
		(total-equiv-family-equiv (hom A a y)
			(\ d -> (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d)))
			(\ d -> (Σ (v : hom A a y) , prod (hom2 A a x y u f d) (hom2 A a a y (id-arr A a) v d)))
			(\ d -> (prod-distribute-sigma (hom2 A a x y u f d) (hom A a y) (\ v -> hom2 A a a y (id-arr A a) v d))))
```

Now we introduce the hypothesis that A is Segal type.

```rzk
#def Segal-representable-dhomFrom-path-space
	(A : U)						-- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
	:= right-cancel-equiv
		(dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d)))
		(representable-dhomFrom-hom2-dist A a x y f u)
		(total-equiv-family-equiv (hom A a y)
			(\ d -> (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
			(\ d -> (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d)))
			(\ d -> (total-equiv-family-equiv (hom2 A a x y u f d)
				(\ alpha -> (Σ (v : hom A a y) , (v = d)))
				(\ alpha -> (Σ (v : hom A a y) , hom2 A a a y (id-arr A a) v d))
				(\ alpha -> (total-equiv-family-equiv (hom A a y)
					(\ v -> (v = d))
					(\ v -> hom2 A a a y (id-arr A a) v d)
					(\ v -> (Eq-Segal-homotopy-hom2 A AisSegal a y v d)))))))


#def codomain-based-paths-contraction
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	(d : hom A a y)
	: Equiv (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))) (hom2 A a x y u f d)
	:= equiv-projection-contractible-fibers (hom2 A a x y u f d) (\ alpha -> (Σ (v : hom A a y) , (v = d)))
		(\ alpha -> is-contr-codomain-based-paths (hom A a y) d)

#def is-segal-representable-dhomFrom-hom2
	(A : U)						-- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (hom2 A a x y u f d))
	:= comp-equiv
		(dhomFrom-representable A a x y f u)
		(Σ (d : hom A a y) , (prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
		(Σ (d : hom A a y) , (hom2 A a x y u f d))
		(Segal-representable-dhomFrom-path-space A AisSegal a x y f u)
		(total-equiv-family-equiv (hom A a y)
			(\ d -> prod (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d)))
			(\ d -> hom2 A a x y u f d)
			(\ d -> codomain-based-paths-contraction A a x y f u d))

#def is-segal-representable-dhomFrom-contractible
	(A : U)						-- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: is-contr (dhomFrom-representable A a x y f u)
	:= is-contr-is-equiv-to-contr (dhomFrom-representable A a x y f u)
				(Σ (d : hom A a y) , (hom2 A a x y u f d))
				(is-segal-representable-dhomFrom-hom2 A AisSegal a x y f u)
				(AisSegal a x y u f)
```

Finally, we see that covariant hom families in a Segal type are covariant.

```rzk
-- [RS, Proposition 8.13(<-)]
#def is-segal-representable-isCovFam
	(A : U)
	(AisSegal : is-segal A)
	(a : A)
	: isCovFam A (\ x -> hom A a x)
	:= \ x y f u -> is-segal-representable-dhomFrom-contractible A AisSegal a x y f u
```

The proof of the claimed converse result given in the original source is
circular - using Proposition 5.10, which holds only for Segal types - so instead
we argue as follows:

```rzk
-- [RS, Proposition 8.13(->)]
#def representable-isCovFam-is-segal
	(A : U)
	(repiscovfam : (a : A) -> isCovFam A (\ x -> hom A a x))
	: is-segal A
	:= \ x y z f g -> first-is-contr-sigma
		(Σ (h : hom A x z) , hom2 A x y z f g h)
		(\ hk -> Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v (first hk))
		(\ hk -> (first hk , \ (t , s) -> first hk s))
		(is-contr-is-equiv-to-contr
			(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v (first hk))
			(dhomFrom-representable A x y z g f)
			(inv-equiv (dhomFrom-representable A x y z g f)
				(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v (first hk))
				(comp-equiv
					(dhomFrom-representable A x y z g f)
					(Σ (h : hom A x z) , (prod (hom2 A x y z f g h) (Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v h)))
					(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v (first hk))
					(representable-dhomFrom-hom2-dist A x y z g f)
					(assoc-sigma
						(hom A x z)
						(\ h -> hom2 A x y z f g h)
						(\ h _ -> Σ (v : hom A x z) , hom2 A x x z (id-arr A x) v h))))
			(repiscovfam x y z g f))
```

While not needed to prove Proposition 8.13, it is interesting to observe that
the dependent hom types in a representable family can be understood as extension
types as follows.

```rzk
#def cofibration-union-test
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
			[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>
       <{(t , s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a , ((t === 1_2) /\ (s === 1_2)) |-> y ]>
	:= cofibration_union (2 * 2)
	(\ (t , s) -> (t === 1_2) /\ Δ¹ s)
	(\ (t , s) -> ((t === 0_2) /\ Δ¹ s) \/ (Δ¹ t /\ (s === 0_2)) \/ (Δ¹ t /\ (s === 1_2)))
	(\ (t , s) -> A)
	(\ (t , s) -> recOR (((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ))

#def base-hom-rewriting
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (<{(t , s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a , ((t === 1_2) /\ (s === 1_2)) |-> y ]>)
		(hom A a y)
	:= (\ v -> (\ r -> v ((1_2 , r))) ,
			((\ v -> \ (t , s) -> v s ,
				\ v -> refl) ,
			(\ v -> \ (t , s) -> v s ,
				\ v -> refl)))

#def base-hom-expansion
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
			[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>
		(hom A a y)
	:= comp-equiv
		(<{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
			[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]> )
		(<{(t , s) : 2 * 2 | ((t === 1_2) /\ (Δ¹ s))} -> A [ ((t === 1_2) /\ (s === 0_2)) |-> a , ((t === 1_2) /\ (s === 1_2)) |-> y ]>)
		(hom A a y)
		(cofibration-union-test A a x y f u)
		(base-hom-rewriting A a x y f u)

#def representable-dhomFrom-expansion
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (Σ (sq : <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
						[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> (sq (1_2 , s)) ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
		(Σ (v : hom A a y) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
	:= total-equiv-pullback-is-equiv (	<{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
			[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]> )
						(hom A a y)
						(first (base-hom-expansion A a x y f u))
						(second (base-hom-expansion A a x y f u))
			(\ v -> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))

#def representable-dhomFrom-composite-expansion
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
			(Σ (sq : <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
						[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> (sq (1_2 , s)) ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
	:= right-cancel-equiv (dhomFrom-representable A a x y f u)
				(Σ (sq : <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
						[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> (sq (1_2 , s)) ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))

		(Σ (v : hom A a y) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
			 (uncurried-dhomFrom-representable A a x y f u)
			 (representable-dhomFrom-expansion A a x y f u)

#def representable-dhomFrom-cofibration-composition
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t]> )
		(Σ (sq : <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
						[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> (sq (1_2 , s)) ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
	:= cofibration-composition (2 * 2) Δ¹×Δ¹ ∂□
			(\ (t , s) -> ((t === 0_2) /\ Δ¹ s) \/ (Δ¹ t /\ (s === 0_2)) \/ (Δ¹ t /\ (s === 1_2)))
			(\ ts -> A)
			(\ (t , s) -> recOR ( ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t))

#def representable-dhomFrom-as-extension-type
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A a x)				-- A lift of the domain.
	: Equiv (dhomFrom-representable A a x y f u)
		(<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [ ((t === 0_2) /\ Δ¹ s) |-> u s ,
												(Δ¹ t /\ (s === 0_2)) |-> a ,
												(Δ¹ t /\ (s === 1_2)) |-> f t]> )
	:= right-cancel-equiv (dhomFrom-representable A a x y f u)
				(<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [ ((t === 0_2) /\ Δ¹ s) |-> u s ,
												(Δ¹ t /\ (s === 0_2)) |-> a ,
												(Δ¹ t /\ (s === 1_2)) |-> f t]> )
				(Σ (sq : <{(t , s) : 2 * 2 | ∂□ (t , s)} -> A
						[ ((t === 0_2) /\ Δ¹ s) |-> u s ,
						(Δ¹ t /\ (s === 0_2)) |-> a ,
						(Δ¹ t /\ (s === 1_2)) |-> f t ]>) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> (sq (1_2 , s)) ,
											(Δ¹ t /\ (s === 0_2)) |-> a ,
											(Δ¹ t /\ (s === 1_2)) |-> f t ]>))
				(representable-dhomFrom-composite-expansion A a x y f u)
				(representable-dhomFrom-cofibration-composition A a x y f u)
```

## Covariant lifts, transport, and uniqueness

In a covariant family C over a base type A , a term u : C x may be transported
along an arrow f : hom A x y to give a term in C y.

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
	:= first-path-sigma
		(C y)
		(\ v -> dhom A x y f C u v)
		(contraction-center (dhomFrom A x y f C u) (CisCov x y f u))
		lift
		(contracting-htpy (dhomFrom A x y f C u) (CisCov x y f u) lift)
```

## Covariant functoriality

The covariant transport operation defines a covariantly functorial action of
arrows in the base on terms in the fibers. In particular, there is an identity
transport law.

```rzk
#def d-id-arr
	(A : U)
	(x : A)
	(C : A -> U)
	(u : C x)
	: dhom A x x (id-arr A x) C u u
	:= \ t -> u

-- [RS17, Proposition 8.16, Part 2]
-- Covariant families preserve identities
#def covPresId
 	(A : U)
	(x : A)
 	(C : A -> U)
	(CisCov : isCovFam A C)
	(u : C x)
	: (covTrans A x x (id-arr A x) C CisCov u) = u
	:= covUniqueness A x x (id-arr A x) C CisCov u (u , d-id-arr A x C u)
```

## Natural transformations

A fiberwise map between covariant families is automatically "natural" commuting
with the covariant lifts.

```rzk
-- [RS17, Proposition 8.17]
-- Covariant naturality
#def covariant-fiberwise-transformation-application
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisCov : isCovFam A C)
	(ϕ : (z : A) -> C z -> D z)
	(u : C x)
	: dhomFrom A x y f D (ϕ x u)
	:= (ϕ y (covTrans A x y f C CisCov u) ,
	\ t -> ϕ (f t) (covLift A x y f C CisCov u t))

#def naturality-covariant-fiberwise-transformation
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisCov : isCovFam A C)
	(DisCov : isCovFam A D)
	(ϕ : (z : A) -> C z -> D z)
	(u : C x)
	: (covTrans A x y f D DisCov (ϕ x u)) = (ϕ y (covTrans A x y f C CisCov u))
	:= covUniqueness A x y f D DisCov (ϕ x u)
		(covariant-fiberwise-transformation-application A x y f C D CisCov ϕ u)
```

## Contravariant families

A family of types over a base type is contravariant if every arrow in the base
has a unique lift with specified codomain.

```rzk
#def dhomTo
	(A : U)						-- The base type.
	(x y : A)					-- Two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(C : A -> U)				-- A type family.
	(v : C y)					-- A lift of the domain.
	: U
   	:= (Σ (u : C x) , dhom A x y f C u v)


-- [RS17, Definition 8.2, dual form]
#def isContraFam
	(A : U)
	(C : A -> U)
	: U
	:= (x : A) -> (y : A) -> (f : hom A x y) -> (v : C y)
		-> is-contr (dhomTo A x y f C v)

-- Type of contravariant families over a fixed type
#def contraFam (A : U) : U
	:= (Σ (C : A -> U) , isContraFam A C)
```

## Representable contravariant families

If A is a Segal type and a : A is any term, then the family \ x -> hom A x a
defines a contravariant family over A , and conversely if this family is
contravariant for every a : A , then A must be a Segal type. The proof involves
a rather lengthy composition of equivalences.

```rzk
#def dhom-contra-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A x a)				-- A lift of the domain.
	(v : hom A y a)				-- A lift of the codomain.
	: U
	:= dhom A x y f (\ z -> hom A z a) u v

-- By uncurrying (RS 4.2) we have an equivalence:
#def uncurried-dhom-contra-representable
	(A : U)						-- The ambient type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(u : hom A x a)				-- A lift of the domain.
	(v : hom A y a)				-- A lift of the codomain.
	: Equiv (dhom-contra-representable A a x y f u v)
	(<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>)
	:= curry-uncurry 2 2 Δ¹ ∂Δ¹ Δ¹ ∂Δ¹ (\ t s -> A)
		(\ (t , s) -> recOR (((t === 0_2) /\ Δ¹ s) |-> u s ,
						((t === 1_2) /\ Δ¹ s) |-> v s ,
						(Δ¹ t /\ (s === 0_2)) |-> f t ,
						(Δ¹ t /\ (s === 1_2)) |-> a ))

#def dhomTo-representable
	(A : U)					  -- The ambient type.
	(a x y : A)				-- The representing object and two points in the base.
	(f : hom A x y)		-- An arrow in the base.
	(v : hom A y a)		-- A lift of the codomain.
	: U
	:= dhomTo A x y f (\ z -> hom A z a) v

-- By uncurrying (RS 4.2) we have an equivalence:
#def uncurried-dhomTo-representable
	(A : U)						-- The ambient type.
	(a x y : A)				-- The representing object and two points in the base.
	(f : hom A x y)		-- An arrow in the base.
	(v : hom A y a)		-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
		(Σ (u : hom A x a) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>))
	:= total-equiv-family-equiv (hom A x a) (\ u -> dhom-contra-representable A a x y f u v)
		(\ u -> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>))
		(\ u -> uncurried-dhom-contra-representable A a x y f u v)

#def representable-dhomTo-uncurry-hom2
	(A : U)						-- The ambient type.
	(a x y : A)				-- The representing object and two points in the base.
	(f : hom A x y)		-- An arrow in the base.
	(v : hom A y a)		-- A lift of the codomain.
	: Equiv (Σ (u : hom A x a) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>))
		(Σ (u : hom A x a) , (Σ (d : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d) ))
	:= total-equiv-family-equiv (hom A x a)
		(\ u -> (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>))
		(\ u -> (Σ (d : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d) ))
		(\ u -> Eq-square-hom2-pushout A x a y a u (id-arr A a) f v)

#def representable-dhomTo-hom2
	(A : U)					-- The ambient type.
	(a x y : A)			-- The representing object and two points in the base.
	(f : hom A x y)	-- An arrow in the base.
	(v : hom A y a)	-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
		(Σ (d : hom A x a) , (Σ (u : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d) ))
	:= triple-comp-equiv
		(dhomTo-representable A a x y f v)
		(Σ (u : hom A x a) , (<{(t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A [((t === 0_2) /\ Δ¹ s) |-> u s ,
											((t === 1_2) /\ Δ¹ s) |-> v s ,
											(Δ¹ t /\ (s === 0_2)) |-> f t ,
											(Δ¹ t /\ (s === 1_2)) |-> a ]>))
		(Σ (u : hom A x a ) , (Σ (d : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d)))
		(Σ (d : hom A x a ) , (Σ (u : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d)))
		(uncurried-dhomTo-representable A a x y f v)
		(representable-dhomTo-uncurry-hom2 A a x y f v)
		(sigma-fubini (hom A x a) (hom A x a)
			(\ u d -> prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d)))

#def representable-dhomTo-hom2-swap
	(A : U)					-- The ambient type.
	(a x y : A)			-- The representing object and two points in the base.
	(f : hom A x y)	-- An arrow in the base.
	(v : hom A y a)	-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
    (Σ (d : hom A x a) , (Σ (u : hom A x a) , prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d) ))
	:= comp-equiv
      (dhomTo-representable A a x y f v)
      (Σ (d : hom A x a) , (Σ (u : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d) ))
      (Σ (d : hom A x a) , (Σ (u : hom A x a) , prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d) ))
      (representable-dhomTo-hom2 A a x y f v)
      (total-equiv-family-equiv (hom A x a)
        (\ d -> (Σ (u : hom A x a) , prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d) ))
        (\ d -> (Σ (u : hom A x a) , prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d) ))
        (\ d -> total-equiv-family-equiv (hom A x a)
          (\ u -> prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d))
          (\ u -> prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d))
          (\ u -> sym-prod (hom2 A x a a u (id-arr A a) d) (hom2 A x y a f v d))))

#def representable-dhomTo-hom2-dist
	(A : U)						-- The ambient type.
	(a x y : A)			  -- The representing object and two points in the base.
	(f : hom A x y)		-- An arrow in the base.
	(v : hom A y a)		-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
		(Σ (d : hom A x a ) , (prod (hom2 A x y a f v d)
      (Σ (u : hom A x a ) , hom2 A x a a u (id-arr A a) d)))
	:= right-cancel-equiv
		(dhomTo-representable A a x y f v)
		(Σ (d : hom A x a ) , (prod (hom2 A x y a f v d)
      (Σ (u : hom A x a ) , hom2 A x a a u (id-arr A a) d)))
		(Σ (d : hom A x a) , (Σ (u : hom A x a) , prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d)))
		(representable-dhomTo-hom2-swap A a x y f v)
		(total-equiv-family-equiv (hom A x a)
			(\ d -> (prod (hom2 A x y a f v d)
      (Σ (u : hom A x a ) , hom2 A x a a u (id-arr A a) d)))
			(\ d -> (Σ (u : hom A x a) , prod (hom2 A x y a f v d) (hom2 A x a a u (id-arr A a) d) ))
			(\ d -> (prod-distribute-sigma (hom2 A x y a f v d) (hom A x a) (\ u -> hom2 A x a a u (id-arr A a) d))))
```

Now we introduce the hypothesis that A is Segal type.

```rzk
#def Segal-representable-dhomTo-path-space
	(A : U)						-- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(v : hom A y a)				-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
		(Σ (d : hom A x a) , (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
	:= right-cancel-equiv
		(dhomTo-representable A a x y f v)
		(Σ (d : hom A x a) , (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
		(Σ (d : hom A x a) , (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (hom2 A x a a u (id-arr A a) d))))
		(representable-dhomTo-hom2-dist A a x y f v)
		(total-equiv-family-equiv (hom A x a)
			(\ d -> (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
			(\ d -> (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , hom2 A x a a u (id-arr A a) d)))
			(\ d -> (total-equiv-family-equiv (hom2 A x y a f v d)
				(\ α -> (Σ (u : hom A x a) , (u = d)))
				(\ α -> (Σ (u : hom A x a) , hom2 A x a a u (id-arr A a) d))
				(\ α -> (total-equiv-family-equiv (hom A x a)
					(\ u -> (u = d))
					(\ u -> hom2 A x a a u (id-arr A a) d)
					(\ u -> (Eq-Segal-homotopy-hom2' A AisSegal x a u d)))))))

#def is-segal-representable-dhomTo-hom2
	(A : U)						-- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					-- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(v : hom A y a)				-- A lift of the codomain.
	: Equiv (dhomTo-representable A a x y f v)
		(Σ (d : hom A x a) , (hom2 A x y a f v d))
	:= comp-equiv
		(dhomTo-representable A a x y f v)
		(Σ (d : hom A x a) , (prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
		(Σ (d : hom A x a) , (hom2 A x y a f v d))
		(Segal-representable-dhomTo-path-space A AisSegal a x y f v)
		(total-equiv-family-equiv (hom A x a)
			(\ d -> prod (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d)))
			(\ d -> hom2 A x y a f v d)
			(\ d -> codomain-based-paths-contraction A x y a v f d))

#def is-segal-representable-dhomTo-contractible
	(A : U)						    -- The ambient type.
	(AisSegal : is-segal A)		-- A proof that A is a Segal type.
	(a x y : A)					  -- The representing object and two points in the base.
	(f : hom A x y)				-- An arrow in the base.
	(v : hom A y a)				-- A lift of the codomain.
	: is-contr (dhomTo-representable A a x y f v)
	:= is-contr-is-equiv-to-contr (dhomTo-representable A a x y f v)
				(Σ (d : hom A x a) , (hom2 A x y a f v d))
				(is-segal-representable-dhomTo-hom2 A AisSegal a x y f v)
				(AisSegal x y a f v)
```

Finally, we see that contravariant hom families in a Segal type are
contravariant.

```rzk
-- [RS, Proposition 8.13(<-), dual]
#def is-segal-representable-isContraFam
	(A : U)
	(AisSegal : is-segal A)
	(a : A)
	: isContraFam A (\ x -> hom A x a)
	:= \ x y f v -> is-segal-representable-dhomTo-contractible A AisSegal a x y f v
```

The proof of the claimed converse result given in the original source is
circular - using Proposition 5.10, which holds only for Segal types - so instead
we argue as follows:

```rzk
-- [RS, Proposition 8.13(->), dual]
#def representable-isContraFam-is-segal
	(A : U)
	(repiscontrafam : (a : A) -> isContraFam A (\ x -> hom A x a))
	: is-segal A
	:= \ x y z f g -> first-is-contr-sigma
		(Σ (h : hom A x z) , hom2 A x y z f g h)
		(\ hk -> Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) (first hk))
		(\ hk -> (first hk , \ (t , s) -> first hk t))
		(is-contr-is-equiv-to-contr
			(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) (first hk))
			(dhomTo-representable A z x y f g)
			(inv-equiv (dhomTo-representable A z x y f g)
				(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) (first hk))
				(comp-equiv
					(dhomTo-representable A z x y f g)
					(Σ (h : hom A x z) , (prod (hom2 A x y z f g h) (Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) h)))
					(Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) , Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) (first hk))
					(representable-dhomTo-hom2-dist A z x y f g)
					(assoc-sigma
						(hom A x z)
						(\ h -> hom2 A x y z f g h)
						(\ h _ -> Σ (u : hom A x z) , hom2 A x z z u (id-arr A z) h))))
			(repiscontrafam z x y f g))
```

## Contravariant lifts, transport, and uniqueness

In a contravariant family C over a base type A, a term v : C y may be
transported along an arrow f : hom A x y to give a term in C x.

```rzk
-- [RS17, contravariant transport from beginning of Section 8.2]
#def contraTrans
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisContra : isContraFam A C)
	(v : C y)
 	: C x
 	:= first (contraction-center (dhomTo A x y f C v) (CisContra x y f v))

-- [RS17, contravariant lift from beginning of Section 8.2]
#def contraLift
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisContra : isContraFam A C)
	(v : C y)
	: (dhom A x y f C (contraTrans A x y f C CisContra v) v)
 	:= second (contraction-center (dhomTo A x y f C v) (CisContra x y f v))

#def contraUniqueness
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C : A -> U)
	(CisContra : isContraFam A C)
	(v : C y)
	(lift : dhomTo A x y f C v)
	: (contraTrans A x y f C CisContra v) = (first lift)
	:= first-path-sigma
		(C x)
		(\ u -> dhom A x y f C u v)
		(contraction-center (dhomTo A x y f C v) (CisContra x y f v))
		lift
		(contracting-htpy (dhomTo A x y f C v) (CisContra x y f v) lift)
```

## Contravariant functoriality

The contravariant transport operation defines a comtravariantly functorial
action of arrows in the base on terms in the fibers. In particular, there is an
identity transport law.

```rzk
-- [RS17, Proposition 8.16, Part 2, dual]
-- Comtravariant families preserve identities
#def contraPresId
 	(A : U)
	(x : A)
 	(C : A -> U)
	(CisContra : isContraFam A C)
	(u : C x)
	: (contraTrans A x x (id-arr A x) C CisContra u) = u
	:= contraUniqueness A x x (id-arr A x) C CisContra u (u , d-id-arr A x C u)
```

## Contravariant natural transformations

A fiberwise map between contrvariant families is automatically "natural"
commuting with the contravariant lifts.

```rzk
-- [RS17, Proposition 8.17, dual]
-- Contravariant naturality
#def contravariant-fiberwise-transformation-application
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisContra : isContraFam A C)
	(ϕ : (z : A) -> C z -> D z)
	(v : C y)
	: dhomTo A x y f D (ϕ y v)
	:= (ϕ x (contraTrans A x y f C CisContra v) ,
	\ t -> ϕ (f t) (contraLift A x y f C CisContra v t))

#def naturality-contravariant-fiberwise-transformation
	(A : U)
	(x y : A)
	(f : hom A x y)
	(C D : A -> U)
	(CisContra : isContraFam A C)
	(DisContra : isContraFam A D)
	(ϕ : (z : A) -> C z -> D z)
	(v : C y)
	: (contraTrans A x y f D DisContra (ϕ y v)) =
      (ϕ x (contraTrans A x y f C CisContra v))
	:= contraUniqueness A x y f D DisContra (ϕ y v)
		(contravariant-fiberwise-transformation-application A x y f C D CisContra ϕ v)
```
