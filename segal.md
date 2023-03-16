#lang rzk-1
-- compile on the command line with "stack exec rzk typecheck segal.md"

-- some topes =/= shapes
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
  
-- some stuff towards the Segal types
#def hom : (A : U) -> (x : A) -> (y : A) -> U
  := \A -> \x -> \y -> <{t : 2 | Δ¹ t } -> A [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, x, y) ]>

-- this fails
-- #def badhom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> U
--   := \A -> \x -> \y -> \z -> \f -> \g -> \h ->
--     <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	[ ∂Δ² (t, s) |->
--        	recOR(s === 0_2, t === 1_2 \/ s === t, g t, recOR(t === 1_2, s === t, f s, h s)) ]>

#def hom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h ->
    <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	[ ∂Δ² (t, s) |->
        	recOR(s === 0_2, t === 1_2 \/ s === t, f t, recOR(t === 1_2, s === t, g s, h s)) ]>

#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def contraction-center : (A : U) -> (_ : isContr A) -> A
  := \(A : U) -> \pf -> (first pf)

#def is-Segal : (A : U) -> U
  := \A -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) 
  -> isContr( ∑ (h : hom A x z), hom2 A x y z f g h)

#def Segal-comp : (A : U) -> (_ : is-Segal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (_ : hom A y z) -> (_ : hom A x y) -> hom A x z
  := \A -> \AisSegal -> \x -> \y -> \z -> \g -> \f -> first (first (AisSegal x y z f g))

#def Segal-id : (A : U) -> (_ : is-Segal A) -> (x : A) -> hom A x x
  := \A -> \AisSegal -> \x -> \{t : 2 | Δ¹ t} -> x 

#def Segal-comp-id : (A : U) -> (AisSegal : is-Segal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
  -> hom2 A x y y f (Segal-id A AisSegal y) f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f t

#def Segal-id-comp : (A : U) -> (AisSegal : is-Segal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
   -> hom2 A x x y (Segal-id A AisSegal x) f f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f s