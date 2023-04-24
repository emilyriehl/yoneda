# 1. Paths

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Some basic path algebra

```rzk
-- path reversal
#def rev 
  (A : U)           -- A type.
  (x y : A)         -- Two points.
  (p : x = y)       -- A path from x to y in A.
  : y = x           -- The reversal will be defined by path induction on p.
  := idJ(A, x, \y' p' -> y' = x, refl, y, p)

-- path composition by induction on the second path
#def concat 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : x = y)       -- A path from x to y in A.
  (q : y = z)       -- A path from y to z in A.
  : (x = z)
  := idJ(A, y, \z' q' -> (x = z'), p, z, q)

-- an alternative construction of path composition by induction on the first path
-- this is useful in situations where it's easier to induction on the first path
#def altconcat 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : x = y)       -- A path from x to y in A.
  : (y = z) -> (x = z)
  := idJ(A, x, \y' p' -> (y' = z) -> (x = z), \q' -> q', y, p)

-- the coherence we don't have definitionally
#def refl-concat 
  (A : U)
  (x y : A)
  (p : x = y)
  : (concat A x x y refl p) = p
  := idJ(A, x, \y' p' -> (concat A x x y' refl p') = p', refl, y, p)

-- a higher path comparing the two compositions
#def concat-altconcat 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : x = y)       -- A path from x to y in A.
  : (q : y = z) -> (concat A x y z p q) = (altconcat A x y z p q)
  := idJ(A, x, 
      \y' -> \p' -> (q' : y' =_{A} z) -> (concat A x y' z p' q') =_{x =_{A} z} altconcat A x y' z p' q', 
      \q' -> refl-concat A x z q', y, p)

-- a higher path comparing the two compositions in the other order
#def altconcat-concat 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : x = y)       -- A path from x to y in A.
  (q : y = z)       -- A path from y to z in A.
  : (altconcat A x y z p q) = concat A x y z p q
  := rev (x = z) (concat A x y z p q) (altconcat A x y z p q) (concat-altconcat A x y z p q)

-- concatenation of two paths with common codomain; defined using concat and rev
#def zig-zag-concat
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : x = y)       -- A path from x to y in A.
  (q : z = y)       -- A path from z to y in A.
  : (x = z)
  := concat A x y z p (rev A z y q)

-- concatenation of two paths with common domain; defined using concat and rev
#def zag-zig-concat  
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p : y = x)       -- A path from y to x in A.
  (q : y = z)       -- A path from y to z in A. 
  : (x = z)
  := concat A x y z (rev A y x p) q

#def concat-right-cancel 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p q : x = y)     -- Two paths from x to y in A.
  (r : y = z)       -- A path from y to z in A.
  : ((concat A x y z p r) = (concat A x y z q r)) -> (p = q)
  := idJ(A, y, \z' r' -> (H : (concat A x y z' p r') = (concat A x y z' q r')) -> (p = q), \H -> H, z, r)    

-- postwhiskering paths of paths
#def homotopy-concat 
  (A : U)           -- A type.
  (x y z : A)       -- Three points.
  (p q : x = y)     -- Two paths from x to y in A.
  (H : p = q) 
  (r : y = z)
  : (concat A x y z p r) = (concat A x y z q r)
  := idJ(A, y, \z' r' -> (concat A x y z' p r') = (concat A x y z' q r'), H, z, r)

-- prewhiskering paths of paths is much harder
#def concat-homotopy 
  (A : U) 
  (x y : A)
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

-- this is easier to prove for altconcat then for concat
#def alt-triangle-rotation 
  (A : U) 
  (x y z : A) 
  (p : x = z)
  (q : x = y)
  : (r : y = z) -> (H : p = altconcat A x y z q r) -> (altconcat A y x z (rev A x y q) p) = r
  := idJ(A, x, 
      \y' q' -> (r' : y' =_{A} z) -> (H' : p = altconcat A x y' z q' r') 
        -> (altconcat A y' x z (rev A x y' q') p) = r', 
      \r' H' -> H', y, q)

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

-- Application of functions to paths
#def ap 
  (A B : U)
  (x y : A)
  (f : A -> B)
  (p : x = y)
  : (f x = f y)
  := idJ(A, x, \y' -> \p' -> (f x = f y'), refl, y, p)

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
    
-- transport in a type family along a path in the base
#def transport 
  (A : U)
  (B : A -> U)
  (x y : A)
  (p : x = y)
  (u : B x)
  : B y
  := idJ(A, x, \y' p' -> B y', u, y, p)

-- I'd prefer to have the argument u after p but for now I've swapped them.
#def transport-total-path
    (A : U)
    (B : A -> U)
    (x y : A)
    (u : B x)
    (p : x = y)
    : (x, u) = (y, transport A B x y p u)
    := idJ(A, x, \y' p' -> (x, u) = (y', transport A B x y' p' u), refl, y, p)

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
