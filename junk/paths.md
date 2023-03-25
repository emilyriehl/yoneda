#lang rzk-1
-- Some definitions stolen from Nikolai Kudasov

# the bottom three layers of Voevodsky's hierarchy of types
```rzk
#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def isProp : (A : U) -> U
  := \(A : U) -> (x : A) -> (y : A) -> x =_{A} y

#def isSet : (A : U) -> U
  := \(A : U) -> (x : A) -> (y : A) -> isProp (x =_{A} y)
```

# some basic path algebra
```rzk
-- path reversal
#def rev : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) -> idJ(A, x, \(z : A) -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

-- path composition by induction on the second path
#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

-- an alternative construction of path composition by induction on the first path
#def altconcat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (q' : y' =_{A} z) -> (x =_{A} z), \(q' : x =_{A} z) -> q', y, p)

#def triple-concat : (A : U) -> (w : A) -> (x : A) -> (y : A) -> (z : A) -> (p : w =_{A} x) -> (q : x =_{A} y) -> (r : y =_{A} z)
  -> (w =_{A} z)
  := \A -> \w -> \x -> \y -> \z -> \p -> \q -> \r -> idJ(A, y, \z' -> \r' -> (w =_{A} z'), concat A w x y p q, z, r)



-- application of functions to paths
#def ap : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (x : A) -> B) -> (p : x =_{A} y) -> (f x =_{B} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (f x =_{B} f y'), refl_{f x : B}, y, p)

-- transport in a type family along a path in the base
#def transport : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (u : B x) -> B y
  := \A -> \B -> \x -> \y -> \p -> \u -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> B y', u, y, p)

-- for later use, some higher transport
#def transport2 : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (q : x =_{A} y) 
  -> (H : p =_{x =_{A} y} q) -> (u : B x) -> (transport A B x y p u) =_{B y} (transport A B x y q u)
  := \A -> \B -> \x -> \y -> \p -> \q -> \H -> \u -> idJ(x =_{A} y, p, \q' -> \H' -> (transport A B x y p u) =_{B y} (transport A B x y q' u), refl_{transport A B x y p u : B y}, q, H)

-- application of dependent functions to paths
#def apd : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (f : (z : A) -> B z) -> (p : x =_{A} y) 
  -> ((transport A B x y p (f x)) =_{B y} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(p' : x =_{A} y') 
  -> ((transport A B x y' p' (f x)) =_{B y'} f y'), refl_{f x : B x}, y, p)
```  


