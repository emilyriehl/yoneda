# The 2-category of Segal types

These formalisations correspond to Section 6 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `4-extension-types.md` — We use extension extensionality.
- `5-segal-types.md` - We use the notion of hom types.

## Functors

Functions between types induce an action on hom types, preserving sources and targets.

```rzk
-- [RS17, Section 6.1]
-- Action of maps on homs. Called "ap-hom" to avoid conflicting with "ap".
#def ap-hom
	(A B : U)
	(F : A -> B)
	(x y : A)
	(f : hom A x y)
	: hom B (F x) (F y)
  := \t -> F (f t)

#def ap-hom2
	(A B : U)
	(F : A -> B)
	(x y z : A)
	(f : hom A x y)
	(g : hom A y z)
	(h : hom A x z)
	(alpha : hom2 A x y z f g h)
	: hom2 B (F x) (F y) (F z) (ap-hom A B F x y f) (ap-hom A B F y z g) (ap-hom A B F x z h)
  := \t -> F (alpha t)

```

Functions between types automatically preserve identity arrows.

```rzk
-- [RS17, Proposition 6.1.a]
-- Preservation of identities follows from extension extensionality because these arrows are pointwise equal.
#def functors-pres-id
	(extext : ExtExt)
	(A B : U)
	(F : A -> B)
	(x : A)
	: (ap-hom A B F x x (id-arr A x)) = (id-arr B (F x))
	:= eq-ext-htpy
			extext
			2
			Δ¹
			∂Δ¹
			(\t -> B)
			(\t -> recOR(
				t === 0_2 |-> F x,
				t === 1_2 |-> F x))
			(ap-hom A B F x x (id-arr A x))
			(id-arr B (F x))
			(\t -> refl)

-- [RS17, Proposition 6.1.b]
-- Preservation of composition requires the Segal hypothesis.
#def functors-pres-comp
	(A B : U)
	(AisSegal : isSegal A)
	(BisSegal : isSegal B)
	(F : A -> B)
	(x y z : A)
	(f : hom A x y)
	(g : hom A y z)
	: (Segal-comp B BisSegal (F x) (F y) (F z) (ap-hom A B F x y f) (ap-hom A B F y z g)) = (ap-hom A B F x z (Segal-comp A AisSegal x y z f g))
	:= Segal-comp-uniqueness B BisSegal (F x) (F y) (F z) (ap-hom A B F x y f) (ap-hom A B F y z g) (ap-hom A B F x z (Segal-comp A AisSegal x y z f g))
	(ap-hom2 A B F x y z f g (Segal-comp A AisSegal x y z f g) (Segal-comp-witness A AisSegal x y z f g))
```
