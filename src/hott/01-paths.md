# 1. Paths

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Some basic path algebra

```rzk

#section path-algebra

#variable A : U
#variables x y z : A

-- path reversal
#def rev 
  (p : x = y)       -- A path from x to y in A.
  : y = x           -- The reversal will be defined by path induction on p.
  := idJ(A, x, \y' p' -> y' = x, refl, y, p)

-- path composition by induction on the second path
#def concat 
  (p : x = y)       -- A path from x to y in A.
  (q : y = z)       -- A path from y to z in A.
  : (x = z)
  := idJ(A, y, \z' q' -> (x = z'), p, z, q)

-- an alternative construction of path composition by induction on the first path
-- this is useful in situations where it's easier to induction on the first path
#def altconcat 
  (p : x = y)       -- A path from x to y in A.
  : (y = z) -> (x = z)
  := idJ(A, x, \y' p' -> (y' = z) -> (x = z), \q' -> q', y, p)

#end path-algebra
```

## Some basic coherences in path algebra

```rzk
#section basic-path-coherence

#variable A : U
#variables w x y z : A

#def rev-involution
  (p : x = y)       -- A path from x to y in A.
  : (rev A y x (rev A x y p)) = p
  := idJ(A, x, \y' p' -> (rev A y' x (rev A x y' p')) = p', refl, y, p)

-- the coherence we don't have definitionally
#def refl-concat 
  (p : x = y)
  : (concat A x x y refl p) = p
  := idJ(A, x, \y' p' -> (concat A x x y' refl p') = p', refl, y, p)

-- associativity
#def concat-assoc  
  (p : w = x)         -- A path from w to x in A.
  (q : x = y)         -- A path from x to y in A.
  (r : y = z)         -- A path from y to z in A.
  : concat A w y z (concat A w x y p q) r = concat A w x z p (concat A x y z q r)
  := idJ(A, y, \z' r' -> concat A w y z' (concat A w x y p q) r' = concat A w x z' p (concat A x y z' q r'), refl, z, r)

#def assoc-concat  
  (p : w = x)         -- A path from w to x in A.
  (q : x = y)         -- A path from x to y in A.
  (r : y = z)         -- A path from y to z in A.
  : concat A w x z p (concat A x y z q r) = concat A w y z (concat A w x y p q) r
  := idJ(A, y, \z' r' -> concat A w x z' p (concat A x y z' q r') = concat A w y z' (concat A w x y p q) r', refl, z, r)

#def rev-right-inverse
  (p : x = y)
  : concat A x y x p (rev A x y p) = refl
  := idJ(A, x, \y' p' -> concat A x y' x p' (rev A x y' p') = refl, refl, y, p)

#def rev-left-inverse
  (p : x = y)
  : concat A y x y (rev A x y p) p = refl
  := idJ(A, x, \y' p' -> concat A y' x y' (rev A x y' p') p' = refl, refl, y, p)

-- concatenation of two paths with common codomain; defined using concat and rev
#def zig-zag-concat
  (p : x = y)       -- A path from x to y in A.
  (q : z = y)       -- A path from z to y in A.
  : (x = z)
  := concat A x y z p (rev A z y q)

-- concatenation of two paths with common domain; defined using concat and rev
#def zag-zig-concat  
  (p : y = x)       -- A path from y to x in A.
  (q : y = z)       -- A path from y to z in A. 
  : (x = z)
  := concat A x y z (rev A y x p) q

#def concat-right-cancel 
  (p q : x = y)     -- Two paths from x to y in A.
  (r : y = z)       -- A path from y to z in A.
  : ((concat A x y z p r) = (concat A x y z q r)) -> (p = q)
  := idJ(A, y, \z' r' -> (H : (concat A x y z' p r') = (concat A x y z' q r')) -> (p = q), \H -> H, z, r)    

#end basic-path-coherence
```

## Some derived coherences in path algebra

The statements or proofs of the following path algebra coherences reference one of the path algebra coherences defined above.

```rzk
#section derived-path-coherence
#variable A : U
#variables x y z : A

#def rev-concat
  (p : x = y)       -- A path from x to y in A.
  (q : y = z)       -- A path from y to z in A.
  : (rev A x z (concat A x y z p q)) = (concat A z y x (rev A y z q) (rev A x y p))
  := idJ(A, y, \z' q' -> (rev A x z' (concat A x y z' p q')) = (concat A z' y x (rev A y z' q') (rev A x y p)), 
    rev (y = x) (concat A y y x refl (rev A x y p)) (rev A x y p) (refl-concat A y x (rev A x y p)), z, q)

-- postwhiskering paths of paths
#def homotopy-concat 
  (p q : x = y)     -- Two paths from x to y in A.
  (H : p = q) 
  (r : y = z)
  : (concat A x y z p r) = (concat A x y z q r)
  := idJ(A, y, \z' r' -> (concat A x y z' p r') = (concat A x y z' q r'), H, z, r)

-- prewhiskering paths of paths is much harder
#def concat-homotopy 
  (p : x = y)
  : (z : A) -> (q : y = z) -> (r : y = z) -> (H : q = r) -> (concat A x y z p q) = (concat A x y z p r)
  := idJ(A, x, 
      \y' p' 
        -> (z : A) -> (q : y' = z) -> (r : y' = z) -> (H : q = r) 
        -> (concat A x y' z p' q) = (concat A x y' z p' r), 
      \z q r H
        -> concat (x = z) (concat A x x z refl q) r (concat A x x z refl r) 
            (concat (x = z) (concat A x x z refl q) q r (refl-concat A x z q) H) 
            (rev (x = z) (concat A x x z refl r) r (refl-concat A x z r)), 
        y, p)

-- a higher path comparing the two compositions
#def concat-altconcat 
  (p : x = y)       -- A path from x to y in A.
  : (q : y = z) -> (concat A x y z p q) = (altconcat A x y z p q)
  := idJ(A, x, 
      \y' -> \p' -> (q' : y' =_{A} z) -> (concat A x y' z p' q') =_{x =_{A} z} altconcat A x y' z p' q', 
      \q' -> refl-concat A x z q', y, p)

-- a higher path comparing the two compositions in the other order
#def altconcat-concat 
  (p : x = y)       -- A path from x to y in A.
  (q : y = z)       -- A path from y to z in A.
  : (altconcat A x y z p q) = concat A x y z p q
  := rev (x = z) (concat A x y z p q) (altconcat A x y z p q) (concat-altconcat p q)

-- this is easier to prove for altconcat then for concat
#def alt-triangle-rotation 
  (p : x = z)
  (q : x = y)
  : (r : y = z) -> (H : p = altconcat A x y z q r) -> (altconcat A y x z (rev A x y q) p) = r
  := idJ(A, x, 
      \y' q' -> (r' : y' =_{A} z) -> (H' : p = altconcat A x y' z q' r') 
        -> (altconcat A y' x z (rev A x y' q') p) = r', 
      \r' H' -> H', y, q)

#end derived-path-coherence

-- This needs to be outside the previous section because of the usage of concat-altconcat A y x
#def triangle-rotation 
  (A : U) 
  (x y z : A) 
  (p : x = z)
  (q : x = y) 
  (r : y = z)
  (H : p = concat A x y z q r)
  : (concat A y x z (rev A x y q) p) = r
  := concat (y = z)  (concat A y x z (rev A x y q) p)  (altconcat A y x z (rev A x y q) p) r
        (concat-altconcat A y x z (rev A x y q) p)
        (alt-triangle-rotation A x y z p q r 
          (concat (x = z) p (concat A x y z q r) (altconcat A x y z q r) 
            H 
            (concat-altconcat A x y z q r)))
```

## Application of functions to paths

```rzk
#def ap 
  (A B : U)
  (x y : A)
  (f : A -> B)
  (p : x = y)
  : (f x = f y)
  := idJ(A, x, \y' -> \p' -> (f x = f y'), refl, y, p)

#def ap-concat
  (A B : U)
  (x y z : A)
  (f : A -> B)
  (p : x = y)
  (q : y = z)
  : (ap A B x z f (concat A x y z p q)) = (concat B (f x) (f y) (f z) (ap A B x y f p) (ap A B y z f q))
  := idJ(A, y, 
    \z' q' -> (ap A B x z' f (concat A x y z' p q')) = (concat B (f x) (f y) (f z') (ap A B x y f p) (ap A B y z' f q')),
    refl, z, q)

#def rev-ap-rev 
  (A B : U)
  (x y : A)
  (f : A -> B)
  (p : x = y)
  : (rev B (f y) (f x) (ap A B y x f (rev A x y p))) = (ap A B x y f p)
  := idJ(A, x, \y' p' -> (rev B (f y') (f x) (ap A B y' x f (rev A x y' p'))) = (ap A B x y' f p'), refl, y, p)

-- For specific use
#def concat-ap-rev-ap-id  
  (A B : U)
  (x y : A)
  (f : A -> B)
  (p : x = y)
  : (concat B (f y) (f x) (f y) (ap A B y x f (rev A x y p)) (ap A B x y f p)) = refl
  := idJ(A, x, \y' p' -> (concat B (f y') (f x) (f y') (ap A B y' x f (rev A x y' p')) (ap A B x y' f p')) = refl, refl, y, p)

#def ap-id 
  (A : U)
  (x y : A)
  (p : x = y)
  : (ap A A x y (identity A) p) = p
    := idJ(A, x, \y' -> \p' -> (ap A A x y' (\z -> z) p') = p', refl, y, p)

-- application of a function to homotopic paths yields homotopic paths
#def ap-htpy 
  (A B : U)
  (x y : A)
  (f : A -> B)
  (p q : x = y)
  (H : p = q)
  : (ap A B x y f p) = (ap A B x y f q)
  := idJ(x = y, p, \q' H' -> (ap A B x y f p) = (ap A B x y f q'), refl, q, H)

#def ap-comp 
  (A B C : U)
  (x y : A)
  (f : A -> B)
  (g : B -> C)
  (p : x = y) 
  : (ap A C x y (composition A B C g f) p) = (ap B C (f x) (f y) g (ap A B x y f p))
    := idJ(A, x, 
          \y' p' -> (ap A C x y' (\z -> g (f z)) p') = (ap B C (f x) (f y') g (ap A B x y' f p')), refl, y, p)

#def rev-ap-comp 
  (A B C : U)
  (x y : A)
  (f : A -> B)
  (g : B -> C)
  (p : x = y) 
  : (ap B C (f x) (f y) g (ap A B x y f p)) = (ap A C x y (composition A B C g f) p) 
  := rev (g (f x) = g (f y)) (ap A C x y (\z -> g (f z)) p) (ap B C (f x) (f y) g (ap A B x y f p)) (ap-comp A B C x y f g p)
```    
## Transport 

```rzk
-- transport in a type family along a path in the base
#def transport 
  (A : U)
  (B : A -> U)
  (x y : A)
  (p : x = y)
  (u : B x)
  : B y
  := idJ(A, x, \y' p' -> B y', u, y, p)

-- The lift of a base path to a path from a term in the total space to its transport.
#def transport-lift
    (A : U)
    (B : A -> U)
    (x y : A)
    (p : x = y)
    (u : B x)
    : (x, u) =_{∑ (z : A), B z} (y, transport A B x y p u)
    := idJ(A, x, \y' p' -> (x, u) =_{∑ (z : A), B z} (y', transport A B x y' p' u), refl, y, p)

-- transport along concatenated paths
#def transport-concat
  (A : U)
  (B : A -> U)
  (x y z : A)
  (p : x = y)
  (q : y = z)
  (u : B x)
  : (transport A B x z (concat A x y z p q) u) = (transport A B y z q (transport A B x y p u))
  := idJ(A, y, \z' q' -> (transport A B x z' (concat A x y z' p q') u) = (transport A B y z' q' (transport A B x y p u)),
    refl, z, q)

#def transport-concat-rev
  (A : U)
  (B : A -> U)
  (x y z : A)
  (p : x = y)
  (q : y = z)
  (u : B x)
  : (transport A B y z q (transport A B x y p u)) = (transport A B x z (concat A x y z p q) u) 
  := idJ(A, y, \z' q' -> (transport A B y z' q' (transport A B x y p u)) = (transport A B x z' (concat A x y z' p q') u),
    refl, z, q)

-- for later use, some higher transport
#def transport2 
  (A : U)
  (B : A -> U)
  (x y : A)
  (p q : x = y)
  (H : p = q)
  (u : B x) 
  : (transport A B x y p u) = (transport A B x y q u)
  := idJ(x = y, p, \q' H' -> (transport A B x y p u) = (transport A B x y q' u), refl, q, H)  
```

## Dependent application

```rzk
-- Application of dependent functions on paths
#def apd 
  (A : U)
  (B : (a : A) -> U)
  (x y : A)
  (f : (z : A) -> B z)
  (p : x = y) 
  : ((transport A B x y p (f x)) = f y)
  := idJ(A, x, \y' -> \p' -> ((transport A B x y' p' (f x)) = f y'), refl, y, p)
```

## Higher-order concatenation

```rzk
-- triple concatenation
#def triple-concat
  (A : U)
  (a0 a1 a2 a3 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  : a0 = a3
  := concat A a0 a1 a3 p1 (concat A a1 a2 a3 p2 p3) 

#def quadruple-concat
  (A : U)
  (a0 a1 a2 a3 a4 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  (p4 : a3 = a4)
  : a0 = a4
  := triple-concat A a0 a1 a2 a4 p1 p2 (concat A a2 a3 a4 p3 p4)

#def quintuple-concat
  (A : U)
  (a0 a1 a2 a3 a4 a5 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  (p4 : a3 = a4)
  (p5 : a4 = a5)
  : a0 = a5
  := quadruple-concat A a0 a1 a2 a3 a5 p1 p2 p3 (concat A a3 a4 a5 p4 p5)

#def sextuple-concat
  (A : U)
  (a0 a1 a2 a3 a4 a5 a6 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  (p4 : a3 = a4)
  (p5 : a4 = a5)
  (p6 : a5 = a6)
  : a0 = a6
  := quintuple-concat A a0 a1 a2 a3 a4 a6 p1 p2 p3 p4 (concat A a4 a5 a6 p5 p6)

#def sextuple-concat-alternating
  (A : U)
  (a0 a1 : A)
  (p1 : a0 = a1)
  (a2 : A)
  (p2 : a1 = a2)
  (a3 : A)
  (p3 : a2 = a3)
  (a4 : A)
  (p4 : a3 = a4)
  (a5 : A)
  (p5 : a4 = a5)
  (a6 : A)
  (p6 : a5 = a6)
  : a0 = a6
  := quintuple-concat A a0 a1 a2 a3 a4 a6 p1 p2 p3 p4 (concat A a4 a5 a6 p5 p6)


#def 12ary-concat
  (A : U)
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  (p4 : a3 = a4)
  (p5 : a4 = a5)
  (p6 : a5 = a6)
  (p7 : a6 = a7)
  (p8 : a7 = a8)
  (p9 : a8 = a9)
  (p10 : a9 = a10)
  (p11 : a10 = a11)
  (p12 : a11 = a12)
  : a0 = a12
  := quintuple-concat A a0 a1 a2 a3 a4 a12 p1 p2 p3 p4 
      (quintuple-concat A a4 a5 a6 a7 a8 a12 p5 p6 p7 p8
        (quadruple-concat A a8 a9 a10 a11 a12 p9 p10 p11 p12))

-- Same as above but with alternating arguments
#def 12ary-concat-alternating
  (A : U)
  (a0 a1 : A)
  (p1 : a0 = a1)
  (a2 : A)
  (p2 : a1 = a2)
  (a3 : A)
  (p3 : a2 = a3)
  (a4 : A)
  (p4 : a3 = a4)
  (a5 : A)
  (p5 : a4 = a5)
  (a6 : A)
  (p6 : a5 = a6)
  (a7 : A)
  (p7 : a6 = a7)
  (a8 : A)
  (p8 : a7 = a8)
  (a9 : A)
  (p9 : a8 = a9)
  (a10 : A)
  (p10 : a9 = a10)
  (a11 : A)
  (p11 : a10 = a11)
  (a12 : A)
  (p12 : a11 = a12)
  : a0 = a12    
  := 12ary-concat A a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
      p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12

-- For convenience, here is a higher-order concatenation operation
#def 13ary-concat
  (A : U)
  (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : A)
  (p1 : a0 = a1)
  (p2 : a1 = a2)
  (p3 : a2 = a3)
  (p4 : a3 = a4)
  (p5 : a4 = a5)
  (p6 : a5 = a6)
  (p7 : a6 = a7)
  (p8 : a7 = a8)
  (p9 : a8 = a9)
  (p10 : a9 = a10)
  (p11 : a10 = a11)
  (p12 : a11 = a12)
  (p13 : a12 = a13)
  : a0 = a13
  := quintuple-concat A a0 a1 a2 a3 a4 a13 p1 p2 p3 p4 
      (quintuple-concat A a4 a5 a6 a7 a8 a13 p5 p6 p7 p8
        (quintuple-concat A a8 a9 a10 a11 a12 a13 p9 p10 p11 p12 p13))

-- Same as above but with alternating arguments
#def 13ary-concat-alternating
  (A : U)
  (a0 a1 : A)
  (p1 : a0 = a1)
  (a2 : A)
  (p2 : a1 = a2)
  (a3 : A)
  (p3 : a2 = a3)
  (a4 : A)
  (p4 : a3 = a4)
  (a5 : A)
  (p5 : a4 = a5)
  (a6 : A)
  (p6 : a5 = a6)
  (a7 : A)
  (p7 : a6 = a7)
  (a8 : A)
  (p8 : a7 = a8)
  (a9 : A)
  (p9 : a8 = a9)
  (a10 : A)
  (p10 : a9 = a10)
  (a11 : A)
  (p11 : a10 = a11)
  (a12 : A)
  (p12 : a11 = a12)
  (a13 : A)
  (p13 : a12 = a13)
  : a0 = a13    
  := 13ary-concat A a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13  
      p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 
```

## Products

```rzk
#def path-product
  (A B : U)
  (a a' : A)
  (b b' : B)
  (e_A : a = a')
  (e_B : b = b')
  : (a, b) =_{prod A B} (a', b')
  := transport A (\x -> (a, b) =_{prod A B} (x, b')) a a' e_A
      (transport B (\y -> (a, b) =_{prod A B} (a, y)) b b' e_B refl)

#def first-path-product
  (A B : U)
  (x y : prod A B)
  (e : x =_{prod A B} y)
  : first x = first y
  := ap (prod A B) A x y (\z -> first z) e

#def second-path-product
  (A B : U)
  (x y : prod A B)
  (e : x =_{prod A B} y)
  : second x = second y
  := ap (prod A B) B x y (\z -> second z) e

#def first-path-sigma
  (A : U)
  (B : A -> U)
  (x y : ∑ (a : A), B a)
  (e : x =_{∑ (a : A), B a} y)
  : first x = first y
  := ap (∑ (a : A), B a) A x y (\z -> first z) e

#def second-path-sigma
    (A : U)
    (B : A -> U)
    (z w : ∑ (a : A), B a)
    (p : z = w) 
    : (transport A B (first z) (first w) (first-path-sigma A B z w p) (second z)) = (second w)
    := idJ((∑ (a : A), B a), z, 
            \w' p' -> (transport A B (first z) (first w') (first-path-sigma A B z w' p') (second z)) = (second w'), 
            refl, w, p)  
```