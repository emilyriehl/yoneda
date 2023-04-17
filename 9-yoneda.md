# The Yoneda lemma

These formalisations correspond to Section 9 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Natural transformations between representable functors

In what follows, we'll consider a Segal type A with two fixed terms a and b. 

We show that a fiberwise map phi : (z : A) -> hom A a z -> hom A b z
automatically defines a natural transformation, despite appearing only to define the components of such.

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
    :  Segal-comp A AisSegal b x y (phi x g) k = phi y (Segal-comp A AisSegal a x y g k) 
    := zig-zag-concat (hom A b y) 
        (Segal-comp A AisSegal b x y (phi x g) k)
        (id-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
        (phi y (Segal-comp A AisSegal a x y g k))
        (composite-of-transformation-coherence A AisSegal a b x y g k phi)
        (transformation-of-composite-coherence-simplified A AisSegal a b x y g k phi)
```

## The Yoneda maps

The Yoneda lemma provides an equivalence between the type (z : A) -> hom A a z -> hom A b z of natural transformations between representable functors and the type hom A b a of arrows between the representing objects.
```rzk
-- The map evid evaluates a natural transformation between representable functors at the identity arrow.
#def evid 
    (A : U)         -- The ambient type.
    (a b : A)       -- The representing objects
    : ((z : A) -> hom A a z -> hom A b z) -> hom A b a
    := \phi -> phi a (id-arr A a)

-- The inverse map only exists for Segal types.
#def yon
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    : hom A b a -> ((z : A) -> hom A a z -> hom A b z)
    := \f z g -> Segal-comp A AisSegal b a z f g

-- One retraction is straightforward:
#def evid-yon
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (f : hom A b a)
    : (evid A a b) ((yon A AisSegal a b) f) = f
    := Segal-comp-id A AisSegal b a f

-- The other composite carries phi to an a prior distinct natural transformation. We first show that these are pointwise equal at all x : A and g : hom A a x
#def yon-evid-partial
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (phi : (z : A) -> hom A a z -> hom A b z)
    (x : A)
    (g : hom A a x)
    : ((yon A AisSegal a b)((evid A a b) phi)) x g = phi x (Segal-comp A AisSegal a a x (id-arr A a) g)  -- phi x g 
    := fiberwise-is-natural A AisSegal a b a x phi (id-arr A a) g

#def yon-evid-ap
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (phi : (z : A) -> hom A a z -> hom A b z)
    (x : A)
    (g : hom A a x)
    : phi x (Segal-comp A AisSegal a a x (id-arr A a) g) = phi x g
    := ap (hom A a x) (hom A b x)
        (Segal-comp A AisSegal a a x (id-arr A a) g)
        g
        (phi x)
        (Segal-id-comp A AisSegal a x g)

#def yon-evid-twice-pointwise
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (phi : (z : A) -> hom A a z -> hom A b z)
    (x : A)
    (g : hom A a x)     
    : ((yon A AisSegal a b)((evid A a b) phi)) x g = phi x g
    := concat (hom A b x)
        (((yon A AisSegal a b)((evid A a b) phi)) x g)
        (phi x (Segal-comp A AisSegal a a x (id-arr A a) g))
        (phi x g)
        (yon-evid-partial A AisSegal a b phi x g)
        (yon-evid-ap A AisSegal a b phi x g)

#def yon-evid-once-pointwise        
    (funext : FunExt)
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (phi : (z : A) -> hom A a z -> hom A b z)
    (x : A)
    : ((yon A AisSegal a b)((evid A a b) phi)) x = phi x
    := funext
        (hom A a x)
        (\g -> hom A b x)
        (\g -> (((yon A AisSegal a b)((evid A a b) phi)) x g))
        (\g -> (phi x g))
        (\g -> yon-evid-twice-pointwise A AisSegal a b phi x g)

#def yon-evid        
    (funext : FunExt)
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    (phi : (z : A) -> hom A a z -> hom A b z)
    : ((yon A AisSegal a b)((evid A a b) phi)) = phi
    := funext
        A
        (\x -> (hom A a x -> hom A b x))
        (\x -> (((yon A AisSegal a b)((evid A a b) phi)) x))
        (\x -> (phi x))
        (\x -> yon-evid-once-pointwise funext A AisSegal a b phi x)
```    

## The Yoneda lemma

The Yoneda lemma says that evaluation at the identity defines an equivalence.

```rzk
#def Yoneda-lemma
    (funext : FunExt)
    (A : U)                 -- The ambient type.
    (AisSegal : isSegal A)  -- A proof that A is Segal.
    (a b : A)               -- The representing objects
    : isEquiv ((z : A) -> hom A a z -> hom A b z) (hom A b a) (evid A a b)
    := ((yon A AisSegal a b,
            yon-evid funext A AisSegal a b),
        (yon A AisSegal a b,
            evid-yon A AisSegal a b))
```