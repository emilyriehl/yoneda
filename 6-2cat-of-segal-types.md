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
-- Action of maps on homs
#def ap : (A : U) -> (B : U) -> (F : (x : A) -> B) -> (x : A) -> (y : A) -> (f : hom A x y) -> hom B (F x) (F y)
  := \A -> \B -> \F -> \x -> \y -> \f -> (\t -> (F (f t)))
```

```rzk
-- [RS17, Proposition 6.1]
-- Preservation of identities
#def functors-pres-id : (_ : ExtExt) -> (A : U) -> (AisSegal : isSegal A) -> (B : U) -> (BisSegal : isSegal B) -> (F : (x : A) -> B) -> (
	(x : A) -> 
	(ap A B F x x (id-arr A x)) =_{hom B (F x) (F x)} 
	(id-arr B (F x))
	)
	:= \extext -> \A -> \AisSegal -> \B -> \BisSegal -> \F -> (\x ->
	extext 
		2
		Δ¹
		∂Δ¹
		(\{t : 2 | Δ¹ t} -> B)
		(\t -> recOR(t === 0_2, t === 1_2, F x, F x))
		(ap A B F x x (id-arr A x))
		(id-arr B (F x))
		(\{t : 2 | Δ¹ t} -> refl_{F x})
	)
```