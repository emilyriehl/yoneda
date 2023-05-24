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

-- A path through the total space projects to a path in the base.
-- Morally but not definitionally the first component of pair-eq.
-- Literally the same as first-path-sigma.
#def total-path-to-base-path
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w)
    : ((first z) = first w)
    := ap (∑ (a : A), B a) A z w (\u -> first u) p

-- A path through the total space gives a path in a fiber using transport along the path in the base.
-- Morally, but not definitionally, the second component of pair-eq.
-- Literally the same as second-path-sigma.
#def total-path-to-fibered-path
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w)
    : (transport A B (first z) (first w) (total-path-to-base-path A B z w p) (second z)) = (second w)
    := idJ((∑ (a : A), B a), z,
            \w' p' -> (transport A B (first z) (first w') (total-path-to-base-path A B z w' p') (second z)) = (second w'),
            refl, w, p)

-- A path in a fiber defines a path in the total space
#def fibered-path-to-sigma-path
    (A : U)
    (B : A -> U)
    (x : A)
    (u v : B x)
    (p : u = v)
    : (x , u) =_{∑ (a : A), B a} (x , v)
    := idJ(B x, u, \v' p' -> (x , u) = (x , v'), refl, v, p)

-- Essentially eq-pair but with explicit arguments.
#def pair-of-paths-to-path-of-pairs
    (A : U)
    (B : A -> U)
    (x y : A)
    (p : x = y)
    : (u : B x) -> (v : B y) -> ((transport A B x y p u) = v) -> (x, u) =_{∑ (z : A), B z} (y, v)
    := idJ(A, x,
        \y' p' -> (u' : B x) -> (v' : B y') -> ((transport A B x y' p' u') = v') -> (x, u') =_{∑ (z : A), B z} (y', v'),
        \(u' : B x) -> \(v' : B x) -> \(q' : (transport A B x x refl u') = v') -> (fibered-path-to-sigma-path A B x u' v' q'),
        y, p)

-- The inverse to pair-eq.
#def eq-pair
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    (e : Eq-Sigma A B s t)
    : (s = t)
    := pair-of-paths-to-path-of-pairs A B (first s) (first t) (first e) (second s) (second t) (second e)
```

## Based path spaces

As an application, we prove that based path spaces are contractible.

```rzk
-- Transport in the space of paths starting at a is concatenation.
#def based-transport-is-concat
    (A : U)             -- The ambient type.
    (a x y : A)         -- The basepoint and two other points.
    (p : a = x)         -- An element of the based path space.
    (q : x = y)         -- A path in the base.
    : (transport A (\z -> (a = z)) x y q p) = (concat A a x y p q)
    := idJ(A, x, \y' q' -> (transport A (\z -> (a = z)) x y' q' p) = (concat A a x y' p q'), refl, y, q)

-- The center of contraction in the based path space is (a, refl)
#def based-paths-center
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : ∑ (x : A), a = x
    := (a, refl)

-- The contracting homotopy.
#def based-paths-contracting-homotopy
    (A : U)                     -- The ambient type.
    (a : A)                     -- The basepoint.
    (p : ∑ (x : A), a = x)      -- Another based path.
    : (based-paths-center A a) =_{∑ (x : A), a = x} p
    := pair-of-paths-to-path-of-pairs A (\z -> a = z) a (first p) (second p) (refl) (second p)
        (concat (a = (first p))
        (transport A (\z -> (a = z)) a (first p) (second p) (refl))
        (concat A a a (first p) (refl) (second p))
        (second p)
        (based-transport-is-concat A a a (first p) (refl) (second p))
        (refl-concat A a (first p) (second p)))

-- Based path spaces are contractible
#def based-paths-contractible
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : isContr (∑ (x : A), a = x)
    := (based-paths-center A a, based-paths-contracting-homotopy A a)
```

## Fubini

Given a family over a pair of independent types, the order of summation is unimportant.

```rzk
#def sigma-fubini
    (A B : U)
    (C : A -> B -> U)
    : Eq (∑ (x : A), ∑ (y : B), C x y) (∑ (y : B), ∑ (x : A), C x y)
    := (\t -> (first (second t), (first t, second (second t))),
        ((\t -> (first (second t), (first t, second (second t))),
        \t -> refl),
        (\t -> (first (second t), (first t, second (second t))),
        \t -> refl)))
```

Products distribute inside a Sigma type:

```rzk
#def prod-distribute-sigma
    (A B : U)
    (C : B -> U)
    : Eq (prod A (∑ (b : B), C b)) (∑ (b : B), prod A (C b))
    := (\(a, (b, c)) -> (b, (a, c)),
            ((\(b, (a, c)) -> (a, (b, c)), \z -> refl),
            (\(b, (a, c)) -> (a, (b, c)), \z -> refl)))
```

## Associativity

```rzk
#def assoc
    (A : U)
    (B : A -> U)
    (C : (a : A) -> B a -> U)
    : Eq (∑ (a : A), ∑ (b : B a), C a b)
         (∑ (ab : ∑ (a : A), B a), C (first ab) (second ab))
    := (\(a, (b, c)) -> ((a, b), c),
        ((\((a, b), c) -> (a, (b, c)), \_ -> refl),
         (\((a, b), c) -> (a, (b, c)), \_ -> refl)))
```
