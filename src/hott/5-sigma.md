# 5. Sigma types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Identity types of sigma types
```rzk
-- Sigma-induction
#def ind-Sigma
        (A : U)
        (B : A -> U)
        (C : (∑(a : A), B a) -> U)
        (s : ∑(a : A), B a)
        (f : (a : A) -> (b : B a) -> C (a, b))
        : C s
        := (f (first s)) (second s)

-- [Rijke 22, Definition 9.3.1]
#def Eq-Sigma
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    : U
    := ∑(p : (first s) = (first t)), (transport A B (first s) (first t) p (second s)) = (second t)

-- [Rijke 22, used in Lemma 9.3.2]
#def refl-in-Sigma
    (A : U)
    (B : A -> U)
    (x : A)
    (y : B x)
    : ∑(p : (x = x)), ((transport A B x x refl_{x} y) = y)
    := (refl_{x}, refl_{y})

-- [Rijke 22, Lemma 9.3.2]
-- Eq-sigma is reflexive
#def reflexive-Eq-Sigma
       (A : U)
       (B : A -> U)
       (s : ∑(a : A), B a)
       : (Eq-Sigma A B s s)
       := (ind-Sigma 
      A
      B
     (\k -> (Eq-Sigma A B k k))
      s
     (\u v -> (refl_{u}, refl_{v}))
      )

-- [Rijke 22, Definition 9.3.3]
#def pair-eq
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    (p : s = t)
    : (Eq-Sigma A B s t)
    := idJ(∑(a : A), B a, s, \t' p' -> (Eq-Sigma A B s t'), (reflexive-Eq-Sigma A B s), t, p)

-- A path in a fiber defines a path in the total space
#def fibered-path-to-sigma-path 
    (A : U)
    (B : A -> U)
    (x : A)
    (u v : B x)
    (p : u = v) 
    : (x , u) =_{∑ (a : A), B a} (x , v)
    := idJ(B x, u, \v' p' -> (x , u) = (x , v'), refl, v, p)

-- A path through the total space projects to a path in the base
#def total-path-to-base-path 
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w) 
    : ((first z) = first w)
    := ap (∑ (a : A), B a) A z w (\u -> first u) p 

-- A path through the total space gives a path in a fiber using transport along the path in the base
#def total-path-to-fibered-path 
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w) 
    : (transport A B (first z) (first w) (total-path-to-base-path A B z w p) (second z)) = (second w)
    := idJ((∑ (a : A), B a), z, 
            \w' p' -> (transport A B (first z) (first w') (total-path-to-base-path A B z w' p') (second z)) = (second w'), 
            refl, w, p)