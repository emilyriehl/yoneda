# 4. Sigma types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Paths involving products

```rzk
#section paths-in-products

#variables A B : U

#def path-product
  (a a' : A)
  (b b' : B)
  (e_A : a = a')
  (e_B : b = b')
  : (a, b) =_{prod A B} (a', b')
  := transport A (\x -> (a, b) =_{prod A B} (x, b')) a a' e_A
      (transport B (\y -> (a, b) =_{prod A B} (a, y)) b b' e_B refl)

#def first-path-product
  (x y : prod A B)
  (e : x =_{prod A B} y)
  : first x = first y
  := ap (prod A B) A x y (\z -> first z) e

#def second-path-product
  (x y : prod A B)
  (e : x =_{prod A B} y)
  : second x = second y
  := ap (prod A B) B x y (\z -> second z) e

#end paths-in-products
```

## Identity types of sigma types

```rzk
#section paths-in-sigma

#variable A : U
#variable B : A -> U

#def first-path-sigma
  (s t : ∑ (a : A), B a)
  (e : s = t)
  : first s = first t
  := ap (∑ (a : A), B a) A s t (\z -> first z) e

#def second-path-sigma
  (s t : ∑ (a : A), B a)
  (e : s = t)
    : (transport A B (first s) (first t) (first-path-sigma s t e) (second s)) = (second t)
    := idJ((∑ (a : A), B a), s,
            \t' e' -> (transport A B (first s) (first t') (first-path-sigma s t' e') (second s)) = (second t'),
            refl, t, e)

-- [Rijke 22, Definition 9.3.1]
#def Eq-Sigma
  (s t : ∑(a : A), B a)
  : U
  := ∑(p : (first s) = (first t)), (transport A B (first s) (first t) p (second s)) = (second t)

-- [Rijke 22, Definition 9.3.3]
#def pair-eq
  (s t : ∑(a : A), B a)
  (e : s = t)
  : (Eq-Sigma s t)
  := (first-path-sigma s t e, second-path-sigma s t e)

-- A path in a fiber defines a path in the total space
#def sigma-path-fibered-path
  (x : A)
  (u v : B x)
  (p : u = v)
  : (x , u) =_{∑ (a : A), B a} (x , v)
  := idJ(B x, u, \v' p' -> (x , u) = (x , v'), refl, v, p)

-- Essentially eq-pair but with explicit arguments.
#def path-of-pairs-pair-of-paths
    (x y : A)
    (p : x = y)
    : (u : B x) -> (v : B y) -> ((transport A B x y p u) = v) -> (x, u) =_{∑ (z : A), B z} (y, v)
    := idJ(A, x,
        \y' p' -> (u' : B x) -> (v' : B y') -> ((transport A B x y' p' u') = v') -> (x, u') =_{∑ (z : A), B z} (y', v'),
        \u' v' q' -> (sigma-path-fibered-path x u' v' q'),
        y, p)

-- The inverse to pair-eq.
#def eq-pair
    (s t : ∑(a : A), B a)
    (e : Eq-Sigma s t)
    : (s = t)
    := path-of-pairs-pair-of-paths (first s) (first t) (first e) (second s) (second t) (second e)

#def eq-pair-pair-eq
  (s t : ∑(a : A), B a)
  (e : s = t)
  : (eq-pair s t (pair-eq s t e)) = e
  := idJ(∑(a : A), B a, s, \t' e' -> (eq-pair s t' (pair-eq s t' e')) = e', refl, t, e)


-- Here we've decomposed e : Eq-Sigma s t as (e0, e1) and decomposed s and t similarly for induction purposes
#def pair-eq-eq-pair-split
  (s0 : A)
  (s1 : B s0)
  (t0 : A)
  (e0 : s0 = t0)
  : (t1 : B t0) -> (e1 : (transport A B s0 t0 e0 s1) = t1) ->
    (pair-eq (s0, s1) (t0, t1) (eq-pair (s0, s1) (t0, t1) (e0, e1))) =_{Eq-Sigma (s0, s1) (t0, t1)} (e0, e1)
  := idJ(A, s0,
       \t0' e0' -> (t1 : B t0') -> (e1 : (transport A B s0 t0' e0' s1) = t1) ->
    (pair-eq (s0, s1) (t0', t1) (eq-pair (s0, s1) (t0', t1) (e0', e1))) =_{Eq-Sigma (s0, s1) (t0', t1)} (e0', e1), \t1 e1 -> idJ(B s0, s1,
              \t1' e1' -> (pair-eq (s0, s1) (s0, t1') (eq-pair (s0, s1) (s0, t1') (refl, e1'))) =_{Eq-Sigma (s0, s1) (s0, t1')} (refl, e1'), refl, t1, e1), t0, e0)

#def pair-eq-eq-pair
  (s t : ∑(a : A), B a)
  (e : Eq-Sigma s t)
  : (pair-eq s t (eq-pair s t e)) =_{Eq-Sigma s t} e
  := pair-eq-eq-pair-split (first s) (second s) (first t) (first e) (second t) (second e)

#def Eq-Sigma-Eq
  (s t : ∑(a : A), B a)
  : Eq (s = t) (Eq-Sigma s t)
  := (pair-eq s t, ((eq-pair s t, eq-pair-pair-eq s t),(eq-pair s t, pair-eq-eq-pair s t)))

#end paths-in-sigma
```

## Symmetry of products

```rzk
#def sym-prod
  (A B : U)
  : Eq (prod A B)(prod B A)
  := (\(a, b) -> (b, a),
        (
        (\(b, a) -> (a, b),\p -> refl),
        (\(b, a) -> (a, b),\p -> refl)
        )
      )
```

## Fubini

Given a family over a pair of independent types, the order of summation is
unimportant.

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
#def assoc-sigma
    (A : U)
    (B : A -> U)
    (C : (a : A) -> B a -> U)
    : Eq (∑ (a : A), ∑ (b : B a), C a b)
         (∑ (ab : ∑ (a : A), B a), C (first ab) (second ab))
    := (\(a, (b, c)) -> ((a, b), c),
        ((\((a, b), c) -> (a, (b, c)), \_ -> refl),
         (\((a, b), c) -> (a, (b, c)), \_ -> refl)))
```
