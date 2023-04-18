# The 2-category of Segal types

These formalisations correspond to Section 6 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites
TODO

```rzk
-- [RS17, Section 6.1]
-- Action of maps on homs. Called "ap-arr" to avoid conflicting with "ap".
#def ap-arr 
	(A B : U)
	(F : A -> B)
	(x y : A)
	(f : hom A x y)
	: hom B (F x) (F y)
  := \t -> F (f t)
```

```rzk
-- [RS17, Proposition 6.1]
-- Preservation of identities follows from extension extensionality because these arrows are pointwise equal.
#def functors-pres-id
	(extext : ExtExt)
	(A B : U)
	(F : A -> B)
	(x : A) 
	: (ap-arr A B F x x (id-arr A x)) = (id-arr B (F x))
	:= extext 
		2
		Δ¹
		∂Δ¹
		(\{t : 2 | Δ¹ t} -> B)
		(\t -> recOR(
			t === 0_2 |-> F x,
			t === 1_2 |-> F x))
		(ap-arr A B F x x (id-arr A x))
		(id-arr B (F x))
		(\t -> refl)
```
