# Segal Types

These formalisations correspond to Section 5 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/total-space.rzk` — we rely on `contractible-fibers-projection-equiv` and `total-space-projection` from that file in the proof of Theorem 5.5
- `3-simplicial-type-theory.rzk` — we rely on definitions of simplicies and their subshapes

## The Segal condition

```rzk
-- [RS17, Definition 5.1]
-- The type of arrow in A from x to y
#def hom : (A : U) -> (x : A) -> (y : A) -> U
  := \A -> \x -> \y -> <{t : 2 | Δ¹ t } -> A [ ∂Δ¹ t |-> recOR(t === 0_2, t === 1_2, x, y) ]>

-- [RS17, Definition 5.2]
#def hom2 : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> (h : hom A x z) -> U
  := \A -> \x -> \y -> \z -> \f -> \g -> \h ->
    <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	[ ∂Δ² (t, s) |->
        	recOR(s === 0_2, t === 1_2 \/ s === t, f t, recOR(t === 1_2, s === t, g s, h s)) ]>

-- [RS17, Definition 5.3]
#def isSegal : (A : U) -> U
  := \A -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) 
  -> isContr( ∑ (h : hom A x z), hom2 A x y z f g h)
```

```rzk
-- Segal types have a composition functor
#def Segal-comp : (A : U) -> (_ : isSegal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (_ : hom A y z) -> (_ : hom A x y) -> hom A x z
  := \A -> \AisSegal -> \x -> \y -> \z -> \g -> \f -> first (first (AisSegal x y z f g))
```

### Characterizing Segal types

```rzk
-- more generally, there is a restriction along any subspace inclusion
#def horn-restriction : (A : U) -> (f : <{t : 2 * 2 | Δ² t} -> A >) -> <{t : 2 * 2 | Λ t} -> A >
  := \A -> \f -> \{t : 2 * 2 | Λ t } -> f t

-- checking partial evaluations of functions
#def identity-identity-composition : (A : U) -> (composition A A A (identity A) (identity A)) =_{(z : A) -> A} (identity A)
  := \A -> refl_{identity A : (a : A) -> A}

#def horn
  : (A : U) ->
    (x : A) -> (y : A) -> (z : A) ->
    (f : hom A x y) ->
    (g : hom A y z) ->
    <{t : 2 * 2 | Λ t } -> A >
  := \A -> \x -> \y -> \z -> \f -> \g ->
    \{(t, s) : 2 * 2 | Λ (t, s) } -> 
      recOR(s === 0_2, t === 1_2, f t, g s)

-- Here, we prove the equivalence used in [RS17, Theorem 5.5].
-- However, we do this by constructing the equivalence directly,
-- instead of using a composition of equivalences, as it is easier to write down
-- and it computes better (we can use refl for the witnesses of the equivalence).
#def compositions-are-horn-fillings
  : (A : U) ->
    (x : A) -> (y : A) -> (z : A) ->
    (f : hom A x y) ->
    (g : hom A y z) ->
    Eq (∑ (h : hom A x z), hom2 A x y z f g h)
       <{t : 2 * 2 | Δ² t } -> A [ Λ t |-> horn A x y z f g t ]>
  := \A -> \x -> \y -> \z -> \f -> \g ->
    (\hh -> \{t : 2 * 2 | Δ² t} -> (second hh) t,
      ((\k -> (\(t : 2) -> k (t, t), \{(t, s) : 2 * 2 | Δ² (t, s)} -> k (t, s)), \hh -> refl_{hh}),
       (\k -> (\(t : 2) -> k (t, t), \{(t, s) : 2 * 2 | Δ² (t, s)} -> k (t, s)), \hh -> refl_{hh})))

#def restriction-equiv
  : (A : U) ->
    Eq (<{t : 2 * 2 | Δ² t} -> A >)
      (∑ (k : <{t : 2 * 2 | Λ t} -> A >),
        ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
          hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                 (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
  := \A ->
    (\k ->
      (\{t : 2 * 2 | Λ t} -> k t,
        (\(t : 2) -> k (t, t),
         \{t : 2 * 2 | Δ² t} -> k t)),
     ((\khh -> \{t : 2 * 2 | Δ² t} -> (second (second khh)) t, \k -> refl_{k}),
      (\khh -> \{t : 2 * 2 | Δ² t} -> (second (second khh)) t, \k -> refl_{k})))

-- [RS17, Theorem 5.5], the hard direction:
#def Segal-restriction-equiv : (A : U) -> (AisSegal : isSegal A) 
  -> Eq (<{t : 2 * 2 | Δ² t} -> A >) (<{t : 2 * 2 | Λ t} -> A >) -- (horn-restriction A)
  := \A -> \AisSegal ->
    compose_Eq
        (<{t : 2 * 2 | Δ² t} -> A >)
        (∑ (k : <{t : 2 * 2 | Λ t} -> A >),
            ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
            hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                    (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
        (<{t : 2 * 2 | Λ t} -> A >)
        (restriction-equiv A)
        (total-space-projection
            (<{t : 2 * 2 | Λ t} -> A >)
            (\k -> ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
                        hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                            (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h),
        (contractible-fibers-projection-equiv
            (<{t : 2 * 2 | Λ t} -> A >)
            (\k -> ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
                        hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                            (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
            (\k -> AisSegal (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                            (\t -> k (t, 0_2)) (\t -> k (1_2, t)))))

-- Verify that the mapping in (Segal-restriction-equiv A AisSegal)
-- is exactly (horn-restriction A)
#def Segal-restriction-equiv-test
  : (A : U) ->
    (AisSegal : isSegal A) ->
    (first (Segal-restriction-equiv A AisSegal)) =_{(_ : <{t : 2 * 2 | Δ² t} -> A >) -> <{t : 2 * 2 | Λ t} -> A >} (horn-restriction A)
  := \A -> \AisSegal -> refl_{horn-restriction A}

-- Theorem 5.5 justifies an alternate definition of isSegal
#def isSegal' : (A : U) -> U
  := \A -> isEquiv (<{t : 2 * 2 | Δ² t} -> A >) (<{t : 2 * 2 | Λ t} -> A >) (horn-restriction A) 

#def isSegal-isSegal' : (A : U) -> (_ : isSegal A) -> isSegal' A
  := \A -> \AisSegal -> second (Segal-restriction-equiv A AisSegal)  

#def isSegal'-isSegal : (A : U) -> (_ : isSegal' A) -> isSegal A
  := \A -> \e -> \x -> \y -> \z -> \f -> \g ->
      (projection-equiv-contractible-fibers 
        (<{t : 2 * 2 | Λ t} -> A >)
        (\k -> ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
                        hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                            (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
        (second (compose_Eq
          (∑ (k : <{t : 2 * 2 | Λ t} -> A >),
            ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
            hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                    (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
          (<{t : 2 * 2 | Δ² t} -> A >)
          (<{t : 2 * 2 | Λ t} -> A >)
          (sym_Eq
            (<{t : 2 * 2 | Δ² t} -> A >)
            (∑ (k : <{t : 2 * 2 | Λ t} -> A >),
              ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
              hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                      (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
            (restriction-equiv A))
          (horn-restriction A, e)
        )))
      (horn A x y z f g)  

-- these notions are equivalent, not just logically equivalent, because they are both propositions over A
#def isSegal-iff-isSegal' : (A : U) -> iff (isSegal A) (isSegal' A)      
  := \A -> (isSegal-isSegal' A , isSegal'-isSegal A)

-- [RS17, Theorem 5.6(i)] : if X is a type and A : X -> U is such that A(x) is a Segal type then (x : X) -> A x is a Segal type
#def partial-Segal-function-types : 
  (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  Eq (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)
  := \X -> \A -> \fiberwiseAisSegal ->
    flip-ext-fun
      (2 * 2)
      Δ² (\{t : 2 * 2 | Δ² t} -> BOT)
      X
      (\{t : 2 * 2 | Δ² t} -> A)
      (\{t : 2 * 2 | BOT} -> recBOT)

#def last-Segal-function-types : 
  (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  Eq (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >) ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)
  := \X -> \A -> \fiberwiseAisSegal ->
    flip-ext-fun
      (2 * 2)
      Λ (\{t : 2 * 2 | Λ t} -> BOT)
      X
      (\{t : 2 * 2 | Λ t} -> A)
      (\{t : 2 * 2 | BOT} -> recBOT)


#def next-Segal-function-types : (_ : FunExt) -> 
   (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  Eq ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)((x : X) -> <{t : 2 * 2 | Λ t} -> A x >) 
  := \funext -> \X -> \A -> \fiberwiseAisSegal -> 
    fibered-equiv-function-equiv funext X (\x -> <{t : 2 * 2 | Δ² t} -> A x >) (\x -> <{t : 2 * 2 | Λ t} -> A x >) (\x -> (horn-restriction (A x) , fiberwiseAisSegal x))

#def last-Segal-function-types-inv : 
  (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  Eq ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)(<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >) 
  := \X -> \A -> \fiberwiseAisSegal ->
    flip-ext-fun-inv
      (2 * 2)
      Λ (\{t : 2 * 2 | Λ t} -> BOT)
      X
      (\{t : 2 * 2 | Λ t} -> A)
      (\{t : 2 * 2 | BOT} -> recBOT)


#def partial-Segal-function-types' : 
  (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  isEquiv (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)(\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x)
  := \X -> \A -> \fiberwiseAisSegal ->
    second (flip-ext-fun
      (2 * 2)
      Δ² (\{t : 2 * 2 | Δ² t} -> BOT)
      X
      (\{t : 2 * 2 | Δ² t} -> A)
      (\{t : 2 * 2 | BOT} -> recBOT))

#def next-Segal-function-types' : (_ : FunExt) -> 
   (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  isEquiv ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)((x : X) -> <{t : 2 * 2 | Λ t} -> A x >) (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t)
  := \funext -> \X -> \A -> \fiberwiseAisSegal -> 
    second (fibered-equiv-function-equiv funext X (\x -> <{t : 2 * 2 | Δ² t} -> A x >) (\x -> <{t : 2 * 2 | Λ t} -> A x >) (\x -> (horn-restriction (A x) , fiberwiseAisSegal x)))

#def last-Segal-function-types-inv' : 
  (X : U) -> (A : (_ : X) -> U) ->
  (_ : (x : X) -> isSegal' (A x)) -> 
  isEquiv ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)(<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >) (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t)
  := \X -> \A -> \fiberwiseAisSegal ->
    second(flip-ext-fun-inv
      (2 * 2)
      Λ (\{t : 2 * 2 | Λ t} -> BOT)
      X
      (\{t : 2 * 2 | Λ t} -> A)
      (\{t : 2 * 2 | BOT} -> recBOT))      

#def Segal-function-types-function : 
  (X : U) -> (A : (_ : X) -> U) -> (_ : (x : X) -> isSegal' (A x)) -> 
  (_ : <{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) -> (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
  := \X -> \A -> \fiberwiseAisSegal -> horn-restriction ((x : X) -> A x)

#def Segal-function-types-function' : 
  (X : U) -> (A : (_ : X) -> U) -> (_ : (x : X) -> isSegal' (A x)) -> 
  (_ : <{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) -> (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
  := \X -> \A -> \fiberwiseAisSegal -> 
    (triple-composition 
    (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) 
    ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)
    ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)
    (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
     (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t)
     (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t)
     (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x))

#def Segal-function-types-function-pointwise-check : 
  (X : U) -> (A : (_ : X) -> U) -> (_ : (x : X) -> isSegal' (A x)) -> 
  (f : <{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) -> 
  (horn-restriction ((x : X) -> A x)) f =_{<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >}
  (triple-composition 
    (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) 
    ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)
    ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)
    (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
     (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t)
     (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t)
     (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x)) f
  := \X -> \A -> \fiberwiseAisSegal -> \f -> refl_{(horn-restriction ((x : X) -> A x)) f}

#def Segal-function-types-function-check : (_ : FunExt) -> 
  (X : U) -> (A : (_ : X) -> U) -> (_ : (x : X) -> isSegal' (A x)) -> 
  (horn-restriction ((x : X) -> A x)) =_{(_ : <{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) -> (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)}
  (triple-composition 
    (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) 
    ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)
    ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)
    (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
     (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t)
     (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t)
     (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x))
  := \funext -> \X -> \A -> \fiberwiseAisSegal -> 
    funext 
      <{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >
      (\base -> (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >))
      (horn-restriction ((x : X) -> A x))
      (triple-composition 
        (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >) 
        ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >)
        ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >)
        (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
        (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t)
        (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t)
        (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x))
      (Segal-function-types-function-pointwise-check X A fiberwiseAisSegal) 

#def Segal-function-types : (_ : FunExt) ->
   (X : U) -> (A : (_ : X) -> U) ->
   (_ : (x : X) -> isSegal' (A x)) ->
   isSegal' ((x : X) -> A x) 
   := \funext -> \X -> \A -> \fiberwiseAisSegal -> 
     triple_compose_isEquiv
       (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >)
       ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >) 
       ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >) 
       (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
        (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x) -- first equivalence
        (partial-Segal-function-types' X A fiberwiseAisSegal)
        (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t) -- second equivalence
        (next-Segal-function-types' funext X A fiberwiseAisSegal)
        (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t) -- third equivalence
        (last-Segal-function-types-inv' X A fiberwiseAisSegal)
```      

triple_compose_isEquiv
  : (A : U) ->
    (B : U) ->
    (C : U) ->
    (D : U) -> 
    (f : (_ : A) -> B) ->
    (_ : isEquiv A B f) ->
    (g : (_ : B) -> C) ->
    (_ : isEquiv B C g) -> 
    (h : (_ : C) -> D) ->
    (_ : isEquiv C D h) ->

## Identity

```rzk
-- [RS17, Definition 5.7]
-- Segal types have identity arrows
#def Segal-id : (A : U) -> (_ : isSegal A) -> (x : A) -> hom A x x
  := \A -> \AisSegal -> \x -> \{t : 2 | Δ¹ t} -> x 

-- [RS17, Proposition 5.8a]
-- the right unit law for identity
#def Segal-comp-id : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
  -> hom2 A x y y f (Segal-id A AisSegal y) f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f t

-- [RS17, Proposition 5.8b]
-- the left unit law for identity
#def Segal-id-comp : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (f : hom A x y) 
   -> hom2 A x x y (Segal-id A AisSegal x) f f
  := \A -> \AisSegal -> \x -> \y -> \f -> \{(t, s) : 2 * 2 | Δ² (t, s)} -> f s
```

## Associativity

To be done.

## Homotopies

To be done.

## Anodyne maps

To be done.