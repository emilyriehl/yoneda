# The Yoneda lemma

These formalisations correspond to Section 9 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Natural transformations between representable functors
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

#def id-domain-square-transformation
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (s : Δ¹) -> hom A b (k s)
    := \s -> phi (k s) (\t -> (id-domain-square A AisSegal a x y g k s t))

#def id-domain-square-transformation-diagonal
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : hom A b y
    := \t -> id-domain-square-transformation A AisSegal a b x y g k phi t t

-- One half of the id-domain-square-transformation.
#def composite-of-transformation    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : hom2 A b x y
        (phi x g)
        k
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := \(t, s) -> (id-domain-square-transformation A AisSegal a b x y g k phi s t)

#def composite-of-transformation-coherence    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (Segal-comp A AisSegal b x y (phi x g) k) = 
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := Segal-comp-uniqueness A AisSegal b x y 
            (phi x g)
            k
            (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
            (composite-of-transformation A AisSegal a b x y g k phi)

-- The other half of the id-domain-square-transformation.
#def transformation-of-composite
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : hom2 A b b y 
        (id-arr A b) 
        (phi y (Segal-comp A AisSegal a x y g k))
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := \(s, t) -> (id-domain-square-transformation A AisSegal a b x y g k phi s t)    

#def transformation-of-composite-coherence    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (Segal-comp A AisSegal b b y (id-arr A b) (phi y (Segal-comp A AisSegal a x y g k))) = 
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := Segal-comp-uniqueness A AisSegal b b y 
            (id-arr A b) 
            (phi y (Segal-comp A AisSegal a x y g k))
            (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
            (transformation-of-composite A AisSegal a b x y g k phi)

#def transformation-of-composite-coherence-simplified    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (phi y (Segal-comp A AisSegal a x y g k)) = 
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := zag-zig-concat (hom A b y)
        (phi y (Segal-comp A AisSegal a x y g k)) 
        (Segal-comp A AisSegal b b y (id-arr A b) (phi y (Segal-comp A AisSegal a x y g k))) 
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
        (Segal-id-comp A AisSegal b y (phi y (Segal-comp A AisSegal a x y g k)))
        (transformation-of-composite-coherence A AisSegal a b x y g k phi)

#def fiberwise-is-natural
    (A : U)                                     -- The ambient type.
    (AisSegal : isSegal A)                      -- A proof that A is Segal.
    (a b x y : A)                               -- Four objects.
    (phi : (z : A) -> hom A a z -> hom A b z)   -- A natural transformation
    (g : hom A a x)                             -- An arrow from a to x.
    (k : hom A x y)                             -- An arrow from b to y.
    :  phi y (Segal-comp A AisSegal a x y g k) = Segal-comp A AisSegal b x y (phi x g) k
    := zig-zag-concat (hom A b y) 
        (phi y (Segal-comp A AisSegal a x y g k))
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
        (Segal-comp A AisSegal b x y (phi x g) k)
        (transformation-of-composite-coherence-simplified A AisSegal a b x y g k phi)
        (composite-of-transformation-coherence A AisSegal a b x y g k phi)
```

## The Yoneda maps

The Yoneda lemma provides an equivalence between the type of natural transformations between representable functors and the type of arrows between the representing objects.
```rzk
-- The map evid evaluates a natural transformation between representable functors at the identity arrow.
#def evid 
    (A : U)         -- The ambient type.
    (a b : A)       -- The representing objects
    : ((x : A) -> hom A a x -> hom A b x) -> hom A b a
    := \alpha -> alpha a (id-arr A a)

-- The inverse map only exists for Segal types.
#def yon
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    : hom A b a -> ((x : A) -> hom A a x -> hom A b x)
    := \f x g -> Segal-comp A AisSegal b a x f g

-- One retraction is straightforward:
#def evid-yon
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (f : hom A b a)
    : (evid A a b) ((yon A AisSegal a b) f) = f
    := Segal-comp-id A AisSegal b a f
```
-- The other composite carries alpha to an a prior distinct natural transformation. We first show that these are pointwise equal at all x : A and g : hom A a x
#def yon-evid
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (alpha : (x : A) -> hom A a x -> hom A b x)
    (x : A)
    (g : hom A a x)
    : (yon A AisSegal a b)((evid A a b) alpha)
    := 


Segal-comp A AisSegal b a x (alpha a (id-arr A a)) g

