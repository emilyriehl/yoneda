#lang rzk-1
-- compile on the command line with "stack exec rzk typecheck segal.md"

-- # Some simplicial topes
-- ```rzk
#def Δ¹ : (t : 2) -> TOPE
  := \(t : 2) -> TOP

#def ∂Δ¹ : (t : 2) -> TOPE
  := \(t : 2) -> (t === 0_2 \/ t === 1_2)

#def Δ² : (t : 2 * 2) -> TOPE
  := \(t, s) -> s <= t

#def ∂Δ² : (t : 2 * 2) -> TOPE
  := \(t, s) -> (s === 0_2 \/ t === 1_2 \/ s === t)

-- the (2,1)-horn
#def Λ : (t : 2 * 2) -> TOPE
  := \(t, s) -> (s === 0_2 \/ t === 1_2)

#def Δ³ : (t : 2 * 2 * 2) -> TOPE
  := \((t1, t2), t3) -> t3 <= t2 /\ t2 <= t1
-- ```

-- # contractibility and equivalences
-- ```rzk
#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def contraction-center : (A : U) -> (_ : isContr A) -> A
  := \(A : U) -> \pf -> (first pf)

#def prod : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (x : A), B

#def isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> ∑ (g : (_ : B) -> A), (prod ((x : A) -> (g (f x)) =_{A} x)) ((y : B) -> (f (g y)) =_{B} y)

#def Eq : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (f : (_ : A) -> B), ((isEquiv A) B) f
-- ```

-- # Segal types
-- ```rzk

#def hom : (A : U) -> (x : A) -> (y : A) -> U
  := \A -> \x -> \y -> <{t : 2 | Δ¹ t } -> A [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, x, y) ]>

#def hom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h ->
    <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	[ ∂Δ² (t, s) |->
        	recOR(s === 0_2, t === 1_2 \/ s === t, f t, recOR(t === 1_2, s === t, g s, h s)) ]>

#def isSegal : (A : U) -> U
  := \A -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) 
  -> isContr( ∑ (h : hom A x z), hom2 A x y z f g h)

-- Segal types have a composition functor
#def Segal-comp : (A : U) -> (_ : isSegal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (_ : hom A y z) -> (_ : hom A x y) -> hom A x z
  := \A -> \AisSegal -> \x -> \y -> \z -> \g -> \f -> first (first (AisSegal x y z f g))

-- Segal types have identity arrows
#def Segal-id : (A : U) -> (_ : isSegal A) -> (x : A) -> hom A x x
  := \A -> \AisSegal -> \x -> \{t : 2 | Δ¹ t} -> x 

-- the left and right unit laws for identities
#def Segal-comp-id : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
  -> hom2 A x y y f (Segal-id A AisSegal y) f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f t

#def Segal-id-comp : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
   -> hom2 A x x y (Segal-id A AisSegal x) f f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f s
-- ```
-- # characterizing Segal types

-- ```rzk
-- more generally, there is a restriction along any subspace inclusion
#def horn-restriction : (A : U) -> (f : <{t : 2 * 2 | Δ² t} -> A >) -> <{t : 2 * 2 | Λ t} -> A >
  := \A -> \f -> \t -> f t

#def composition : (A : U) -> (B : U) -> (C : U) -> (g : (b : B) -> C) -> (f : (a : A) -> B) -> (z : A) -> C
  := \A -> \B -> \C -> \g -> \f -> \z -> g (f z)

#def identity : (A : U) -> (a : A) -> A
  := \A -> \a -> a  

#def composition-identity : (A : U) -> (composition A A A (identity A) (identity A)) =_{(z : A) -> A} (identity A)
  := \A -> refl_{identity A : (a : A) -> A}

-- #def Segal-restriction-equiv : (A : U) -> (AisSegal : isSegal A) 
--  -> isEquiv (<{t : 2 * 2 | Δ² t} -> A >) (<{t : 2 * 2 | Λ t} -> A >) (horn-restriction A)
--  :=

-- ```