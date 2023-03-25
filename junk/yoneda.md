#lang rzk-1
-- compile on the command line with "stack exec rzk typecheck yoneda.md"

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

#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def hom : (A : U) -> (x : A) -> (y : A) -> U
  := \A -> \x -> \y -> <{t : 2 | Δ¹ t } -> A [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, x, y) ]>

#def hom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h ->
    <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	[ ∂Δ² (t, s) |->
        	recOR(s === 0_2, t === 1_2 \/ s === t, f t, recOR(t === 1_2, s === t, g s, h s)) ]>

#def is-Segal : (A : U) -> U
  := \A -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) 
  -> isContr( ∑ (h : hom A x z), hom2 A x y z f g h)
  
#def dhom : (A : U) -> (x : A) -> (y : A) -> (f : hom A x y) -> (C : (x : A) -> U) -> (u : C x) -> (v : C y) -> U
  := \A -> \x -> \y -> \f -> \C -> \u -> \v -> <{t : 2 | Δ¹ t} -> (C (f t)) [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, u, v) ]>
  

