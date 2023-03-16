#lang rzk-1
-- Some definitions stolen from Nikolai Kudasov

#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def isProp : (A : U) -> U
  := \(A : U) -> (x : A) -> (y : A) -> x =_{A} y

#def inv : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) -> idJ(A, x, \(z : A) -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

#def altconcat : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (z : A) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (z' : A) -> (q' : y' =_{A} z') -> (x =_{A} z'), \(z' : A) -> \(q' : x =_{A} z') -> q', y, p)

