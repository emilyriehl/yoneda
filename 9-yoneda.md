# The Yoneda lemma

These formalisations correspond to Section 9 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Natural transformations between representable functors
```rzk
-- some tests which fail to reproduce the issue below
#def test-square
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : (s : Δ¹) -> (t : Δ¹) -> A
    := \s t ->  recOR(t <= s |-> alpha (s , t), 
                    s <= t |-> beta (t , s))

#def test-with-id
    (A : U)
    (x y z : A)
    (d : hom A x z)
    (h : hom A x y)
    (k : hom A y z)
    (beta : hom2 A x y z h k d)
    : (s : Δ¹) -> (t : Δ¹) -> A
    := \s t ->  recOR(t <= s |-> (id-comp-witness A x z d) (s , t), 
                    s <= t |-> beta (t , s))

#def test-with-id-diagonal
    (A : U)
    (x y z : A)
    (d : hom A x z)
    (h : hom A x y)
    (k : hom A y z)
    (beta : hom2 A x y z h k d)
    : hom A x z
    := \t -> test-with-id A x y z d h k beta t t

#def id-extraction
    (A : U)
    (x y z : A)
    (d : hom A x z)
    (h : hom A x y)
    (k : hom A y z)
    (beta : hom2 A x y z h k d)
    : hom2 A x x z (id-arr A x) d d
    := \(t, s) -> test-with-id A x y z d h k beta t s

#def new-id-extraction
    (A : U)
    (x y z : A)
    (d : hom A x z)
    (h : hom A x y)
    (k : hom A y z)
    (beta : hom2 A x y z h k d)
    : hom2 A x x z (id-arr A x) d (test-with-id-diagonal A x y z d h k beta)
    := \(t, s) -> test-with-id A x y z d h k beta t s

#def beta-extraction            
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : hom2 A x y2 z h k d
    := \(t, s) -> test-square A x y1 y2 z f g d h k alpha beta s t        

#def alpha-extraction            
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : hom2 A x y1 z f g d
    := \(t, s) -> test-square A x y1 y2 z f g d h k alpha beta t s     

#def new-diagonal       
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : hom A x z
    := \t -> test-square A x y1 y2 z f g d h k alpha beta t t

#def new-alpha-extraction   
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : hom2 A x y1 z f g (new-diagonal A x y1 y2 z f g d h k alpha beta) 
    := \(t, s) -> test-square A x y1 y2 z f g d h k alpha beta t s    

#def new-beta-extraction   
    (A : U)
    (x y1 y2 z : A)
    (f : hom A x y1)
    (g : hom A y1 z)
    (d : hom A x z)
    (h : hom A x y2)
    (k : hom A y2 z)
    (alpha : hom2 A x y1 z f g d)
    (beta : hom2 A x y2 z h k d)
    : hom2 A x y2 z h k (new-diagonal A x y1 y2 z f g d h k alpha beta) 
    := \(t, s) -> test-square A x y1 y2 z f g d h k alpha beta s t  

-- This unfolds a composition triangle to a square with an identity component
#def fixed-domain-square
    (A : U)                     -- The ambient type.
    (AisSegal : isSegal A)      -- A proof that A is Segal.
    (a x y : A)                 -- Three objects
    (g : hom A a x)
    (k : hom A x y)
    : (s : Δ¹) -> hom A a (k s)
    := \s t -> 
        recOR(t <= s |-> (id-comp-witness A a y (Segal-comp A AisSegal a x y g k)) (s , t), 
        s <= t |-> (Segal-comp-witness A AisSegal a x y g k) (t , s))

#def fixed-domain-square-transformation
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (s : Δ¹) -> hom A b (k s)
    := \s -> phi (k s) (\t -> (fixed-domain-square A AisSegal a x y g k s t))

#def fixed-domain-square-transformation-diagonal
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : hom A b y
    := \t -> fixed-domain-square-transformation A AisSegal a b x y g k phi t t

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
        (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := \(t, s) -> (fixed-domain-square-transformation A AisSegal a b x y g k phi s t)

-- if t2 is swapped in for t1 at the end of the third constraint this fails; see below
#def transformation-of-composite-weird    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : { (t1, t2) : Δ² } -> A [
        t2 === 0_2 |-> b, -- (id-arr A b) 
        t1 === 1_2 |-> (phi y (Segal-comp A AisSegal a x y g k)) t2, 
                -- (phi y (Segal-comp A AisSegal a x y g k))
        t2 === t1 |-> (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi) t1]
                -- the above fails when t2 is swapped for t1 at the end of the line
                 --  (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := \(s, t) -> (fixed-domain-square-transformation A AisSegal a b x y g k phi s t)

--- This fails to recognize the diagonal composite; compare with above. 
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
        (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := \(s, t) -> (fixed-domain-square-transformation A AisSegal a b x y g k phi s t)    


#def transformation-of-composite-coherence-alt 
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (Segal-comp A AisSegal b b y (id-arr A b) (phi y (Segal-comp A AisSegal a x y g k))) = 
        (\t -> (transformation-of-composite-weird A AisSegal a b x y g k phi) (t, t))
        -- fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := Segal-comp-uniqueness A AisSegal b b y 
            (id-arr A b) 
            (phi y (Segal-comp A AisSegal a x y g k))
            (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
            (transformation-of-composite-weird A AisSegal a b x y g k phi)    

#def transformation-of-composite-coherence    
    (A : U)                                         -- The ambient type.
    (AisSegal : isSegal A)                          -- A proof that A is Segal.
    (a b x y : A)                                   -- Four objects
    (g : hom A a x)                                 -- An arrow from a to x.
    (k : hom A x y)                                 -- An arrow from b to y.
    (phi : (z : A) -> hom A a z -> hom A b z)       -- A fiberwise map.
    : (Segal-comp A AisSegal b b y (id-arr A b) (phi y (Segal-comp A AisSegal a x y g k))) = 
        (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
    := Segal-comp-uniqueness A AisSegal b b y 
            (id-arr A b) 
            (phi y (Segal-comp A AisSegal a x y g k))
            (fixed-domain-square-transformation-diagonal A AisSegal a b x y g k phi)
            (transformation-of-composite A AisSegal a b x y g k phi)
```

#def fiberwise-is-natural
    (A : U)                                     -- The ambient type.
    (AisSegal : isSegal A)                      -- A proof that A is Segal.
    (a b x y : A)                               -- Four objects.
    (phi : (z : A) -> hom A a z -> hom A b z)   -- A natural transformation
    (g : hom A a x)                             -- An arrow from a to x.
    (k : hom A x y)                             -- An arrow from b to y.
    : Segal-comp A AisSegal b x y (phi x g) k =_{hom A b y} 
    phi y (Segal-comp A AisSegal a x y g k)


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

