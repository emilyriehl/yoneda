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

-- I'd prefer to have the argument u after p but for now I've swapped them.
-- This fails to typecheck.
#def transport-total-path
    (A : U)
    (B : A -> U)
    (x y : A)
    (u : B x)
    (p : x = y)
    : (x, u) = (y, transport A B x y p u)
    := idJ(A, x, \y' p' -> (x, u) = (y', transport A B x y' p' u), refl, y, p)

-- This fails to typecheck, perhaps for the same reason as above?
#def pair-of-paths-to-path-of-pairs
    (A : U)
    (B : A -> U)
    (x y : A)
    (p : x = y)
    : (u : B x) -> (v : B y) -> ((transport A B x y p u) = v) -> (x, u) = (y, v)    
    := idJ(A, x, 
        \y' p' -> (u' : B x) -> (v' : B y') -> ((transport A B x y' p' u') = v') -> (x, u') = (y', v'),
        \(u' : B x) -> \(v' : B x) -> \(q' : (transport A B x x refl u') = v') -> (fibered-path-to-sigma-path A B x u' v' q'), 
        y, p) 

-- A path through the total space projects to a path in the base
#def total-path-to-base-path 
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w) 
    : ((first z) = first w)
    := ap (∑ (a : A), B a) A z w (\u -> first u) p 

-- A path through the total space gives a path in a fiber using transport along the path in the base.
-- Compare with pair-eq.
#def total-path-to-fibered-path 
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w) 
    : (transport A B (first z) (first w) (total-path-to-base-path A B z w p) (second z)) = (second w)
    := idJ((∑ (a : A), B a), z, 
            \w' p' -> (transport A B (first z) (first w') (total-path-to-base-path A B z w' p') (second z)) = (second w'), 
            refl, w, p)
```            

## Based path spaces

As an application, we prove the based path spaces are contractible.

```rzk
-- Transport in the space of paths starting at a is composition.
#def based-transport-is-composition
    (A : U)             -- The ambient type.
    (a x y : A)         -- The basepoint and two other points.
    (p : a = x)         -- An element of the based path space.
    (q : x = y)         -- A path in the base.
    : (transport A (\z -> (a = z)) x y q p) = (concat A a x y p q)
    := idJ(A, x, \y' q' -> (transport A (\z -> (a = z)) x y' q' p) = (concat A a x y' p q'), refl, y, q)

-- The center of contraction in the based path space is (a, refl)
#def based-path-center 
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : ∑ (x : A), a = x
    := (a, refl)
```

#def based-path-contracting-homotopy
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    (pp : ∑ (x : A), a = x)
    : (based-path-center A a) = pp
    := 
```            