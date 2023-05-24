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

## Paths involving dependent sums

```rzk
#section paths-in-sigma

#variable A : U
#variable B : A -> U

#def first-path-sigma
  (x y : ∑ (a : A), B a)
  (e : x = y)
  : first x = first y
  := ap (∑ (a : A), B a) A x y (\z -> first z) e

#def second-path-sigma
  (x y : ∑ (a : A), B a)
  (e : x = y) 
    : (transport A B (first x) (first y) (first-path-sigma x y e) (second x)) = (second y)
    := idJ((∑ (a : A), B a), x, 
            \y' e' -> (transport A B (first x) (first y') (first-path-sigma x y' e') (second x)) = (second y'), 
            refl, y, e)

#end paths-in-sigma
```

## Identity types of sigma types
```rzk
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
       := (refl, refl)

-- [Rijke 22, Definition 9.3.3]
#def pair-eq
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    (p : s = t)
    : (Eq-Sigma A B s t)
    := idJ(∑(a : A), B a, s, \t' p' -> (Eq-Sigma A B s t'), (reflexive-Eq-Sigma A B s), t, p)

-- A path in a fiber defines a path in the total space
#def sigma-path-fibered-path 
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
        \(u' : B x) -> \(v' : B x) -> \(q' : (transport A B x x refl u') = v') -> (sigma-path-fibered-path A B x u' v' q'), 
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

