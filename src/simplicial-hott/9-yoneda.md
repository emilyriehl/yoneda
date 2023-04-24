# The Yoneda lemma

These formalisations correspond to Section 9 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for instance the axiom of function extensionality.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension extensionality.
- `5-segal-types.md` - We make heavy use of the notion of Segal types
- `8-covariant.md` - We use covariant type families.

## Natural transformations involving a representable functor

The Yoneda lemma characterizes natural transformations from a representable functor to a covariant family. Ordinary, such a natural transformation would involve a family of maps (phi : (z : A) -> hom A a z -> C z) together with a proof of naturality of these components, by as with covariant-transformation-naturality the naturality condition is automatic here.

```rzk
-- This unfolds a composition triangle to a square with an identity component
#def id-domain-square
    (A : U)                     -- The ambient type.
    (AisSegal : isSegal A)      -- A proof that A is Segal.
    (a x y : A)                 -- Three objects
    (g : hom A a x)
    (k : hom A x y)
    : (s : Δ¹) -> hom A a (k s)
    := \s t -> 
        recOR(t <= s |-> (id-comp-witness A a y (Segal-comp A AisSegal a x y g k)) (s , t), 
        s <= t |-> (Segal-comp-witness A AisSegal a x y g k) (t , s))

#def covariant-representable-transformation-application
	(A : U)
	(AisSegal : isSegal A)
	(a x y : A)
	(f : hom A a x)
	(g : hom A x y)
	(C : A -> U)
	(CisCov : isCovFam A C)
	(phi : (z : A) -> hom A a z -> C z)
	: dhomFrom A x y g C (phi x f)
	:= (phi y (Segal-comp A AisSegal a x y f g), 
	\s -> phi (g s) (\t -> (id-domain-square A AisSegal a x y f g s t)))

#def covariant-representable-transformation-naturality
	(A : U)
    (AisSegal : isSegal A)
	(a x y : A)
	(f : hom A a x)
	(g : hom A x y)
	(C : A -> U)
	(CisCov : isCovFam A C)
	(phi : (z : A) -> hom A a z -> C z)
	: (covTrans A x y g C CisCov (phi x f)) = (phi y (Segal-comp A AisSegal a x y f g))
	:= covUniqueness A x y g C CisCov (phi x f)
		(covariant-representable-transformation-application A AisSegal a x y f g C CisCov phi)
```

## The Yoneda maps

For any Segal type A and point a : A, the Yoneda lemma provides an equivalence between the type (z : A) -> hom A a z -> C z of natural transformations out of the functor represented by A and valued in an arbitrary covariant family C and the type C a.

```rzk
-- The map evid evaluates a natural transformation out of a representable functor at the identity arrow.
#def evid 
    (A : U)         					-- The ambient type.
    (a : A)       						-- The representing object.
	(C : A -> U)						-- A type family.
    : ((z : A) -> hom A a z -> C z) -> C a
    := \phi -> phi a (id-arr A a)

-- The inverse map only exists for Segal types.
#def yon
    (A : U)                 			-- The ambient type.
    (AisSegal : isSegal A)  			-- A proof that A is Segal.
    (a  : A)               				-- The representing object.
	(C : A -> U)						-- A type family.
	(CisCov : isCovFam A C)				-- A covariant family.
    : C a -> ((z : A) -> hom A a z -> C z)
    := \u z f -> covTrans A a z f C CisCov u

```
## The Yoneda composites

It remains to show that the Yoneda maps are inverses.

```rzk
-- One retraction is straightforward:
#def evid-yon
    (A : U)                 			-- The ambient type.
    (AisSegal : isSegal A)  			-- A proof that A is Segal.
    (a  : A)               				-- The representing object.
	(C : A -> U)						-- A type family.
	(CisCov : isCovFam A C)				-- A covariant family.
	(u : C a)
    : (evid A a C) ((yon A AisSegal a C CisCov) u) = u
    := covPresId A a C CisCov u

-- The other composite carries phi to an a priori distinct natural transformation.
-- We first show that these are pointwise equal at all x : A and f : hom A a x in two steps.
-- The first step:
#def yon-evid-partial
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    (phi : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A a x)	
	: ((yon A AisSegal a C CisCov)((evid A a C) phi)) x f = (phi x (Segal-comp A AisSegal a a x (id-arr A a) f)) -- phi x f
    := covariant-representable-transformation-naturality A AisSegal a a x (id-arr A a) f C CisCov phi

-- The second step:
#def yon-evid-ap
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    (phi : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A a x)	
    : (phi x (Segal-comp A AisSegal a a x (id-arr A a) f)) = phi x f
    := ap (hom A a x) (C x)
        (Segal-comp A AisSegal a a x (id-arr A a) f)
        f
        (phi x)
        (Segal-id-comp A AisSegal a x f)    

-- The composite yon-evid of phi equals phi at all x : A and f : hom A a x.
#def yon-evid-twice-pointwise
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    (phi : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A a x)	  
	: ((yon A AisSegal a C CisCov)((evid A a C) phi)) x f = phi x f
    := concat (C x)
        (((yon A AisSegal a C CisCov)((evid A a C) phi)) x f)
        (phi x (Segal-comp A AisSegal a a x (id-arr A a) f))
        (phi x f)
        (yon-evid-partial A AisSegal a C CisCov phi x f)
        (yon-evid-ap A AisSegal a C CisCov phi x f)

-- By funext, these are equals as functions of f pointwise in x.
#def yon-evid-once-pointwise    
    (funext : FunExt)    
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    (phi : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
	: ((yon A AisSegal a C CisCov)((evid A a C) phi)) x = phi x
    := funext
        (hom A a x)
        (\f -> C x)
        (\f -> ((yon A AisSegal a C CisCov)((evid A a C) phi)) x f)
        (\f -> (phi x f))
        (\f -> yon-evid-twice-pointwise A AisSegal a C CisCov phi x f)

-- By funext again, these are equal as functions of x and f.
#def yon-evid    
    (funext : FunExt)        
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    (phi : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    : ((yon A AisSegal a C CisCov)((evid A a C) phi)) = phi
    := funext
        A
        (\x -> (hom A a x -> C x))
        (\x -> ((yon A AisSegal a C CisCov)((evid A a C) phi)) x)
        (\x -> (phi x))
        (\x -> yon-evid-once-pointwise funext A AisSegal a C CisCov phi x)
```    

## The Yoneda lemma
The Yoneda lemma says that evaluation at the identity defines an equivalence.

```rzk
#def Yoneda-lemma
    (funext : FunExt)        
    (A : U)                 				-- The ambient type.
    (AisSegal : isSegal A)  				-- A proof that A is Segal.
    (a  : A)               					-- The representing object.
	(C : A -> U)							-- A type family.
	(CisCov : isCovFam A C)					-- A covariant family.
    : isEquiv ((z : A) -> hom A a z -> C z) (C a) (evid A a C)
    := ((yon A AisSegal a C CisCov,
            yon-evid funext A AisSegal a C CisCov),
        (yon A AisSegal a C CisCov,
            evid-yon A AisSegal a C CisCov))
```