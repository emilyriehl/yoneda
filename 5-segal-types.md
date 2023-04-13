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
-- The type of arrows in A from x to y
#def hom
  (A : U)   -- A type.
  (x y : A) -- Two points in A.
  : U
  := (t : Δ¹) -> A [    -- (hom A x y) is a 1-simplex (an arrow) in A where
    t === 0_2 |-> x,    -- * the left endpoint is exactly x
    t === 1_2 |-> y     -- * the right endpoint is exactly y
  ]

-- [RS17, Definition 5.2]
-- the type of commutative triangles in A
#def hom2
  (A : U)           -- A type.
  (x y z : A)       -- Three points in A.
  (f : hom A x y)   -- An arrow in A from x to y.
  (g : hom A y z)   -- An arrow in A from y to z.
  (h : hom A x z)   -- An arrow in A from x to z.
  : U
  := { (t1, t2) : Δ² } -> A [   -- (hom2 A x y z f g h) is a 2-simplex (triangle) in A where
    t2 === 0_2 |-> f t1,        -- * the top edge is exactly f,
    t1 === 1_2 |-> g t2,        -- * the right edge is exactly g, and
    t2 === t1  |-> h t2         -- * the diagonal is exactly h
  ]

-- [RS17, Definition 5.3]
-- A type is Segal if every composable pair of arrows has a unique composite
#def isSegal 
  (A : U)         -- A type.
  : U
  := (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) -> isContr( ∑ (h : hom A x z), hom2 A x y z f g h)
```

```rzk
-- Segal types have a composition functor; written in diagrammatic order to match the order of arguments in isSegal
#def Segal-comp 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : hom A x z
  := first (first (AisSegal x y z f g))

-- Segal types have composition witnesses
#def Segal-comp-witness 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : hom2 A x y z f g (Segal-comp A AisSegal x y z f g)
  := second (first (AisSegal x y z f g))

-- If there is a witness that an arrow h is a composite of f and g, then the specified composite equals h.
#def Segal-comp-uniqueness 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  (h : hom A x z)               -- An arrow in A from x to z.
  (alpha : hom2 A x y z f g h)  -- A witness that h is a composite of f and g.
  : (Segal-comp A AisSegal x y z f g) =_{hom A x z} h
  := total-path-to-base-path 
      (hom A x z)
      (\(k : hom A x z) -> hom2 A x y z f g k)
      (Segal-comp A AisSegal x y z f g, Segal-comp-witness A AisSegal x y z f g)
      (h, alpha)
      (contracting-htpy (∑ (k : hom A x z), hom2 A x y z f g k) (AisSegal x y z f g) (h, alpha))
```

### Characterizing Segal types

```rzk
-- A pair of composable arrows form a horn.
#def horn
  (A : U)                       -- A type.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : <{t : 2 * 2 | Λ t } -> A >
  :=  \{(t, s) : 2 * 2 | Λ (t, s) } -> 
      recOR(
        s === 0_2 |-> f t, 
        t === 1_2 |-> g s
        )

-- The underlying horn of a simplex
#def horn-restriction   
  (A : U)                            -- A type.
  (alpha : <{t : 2 * 2 | Δ² t} -> A >)   -- A commutative triangle.
  : <{t : 2 * 2 | Λ t} -> A >
  :=  \{t : 2 * 2 | Λ t } -> alpha t

-- Here, we prove the equivalence used in [RS17, Theorem 5.5].
-- However, we do this by constructing the equivalence directly,
-- instead of using a composition of equivalences, as it is easier to write down
-- and it computes better (we can use refl for the witnesses of the equivalence).
#def compositions-are-horn-fillings
  (A : U)                       -- A type.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : Eq (∑ (h : hom A x z), hom2 A x y z f g h)
       <{t : 2 * 2 | Δ² t } -> A [ Λ t |-> horn A x y z f g t ]>
  := (\hh -> \{t : 2 * 2 | Δ² t} -> (second hh) t,
      ((\k -> (\(t : 2) -> k (t, t), \{(t, s) : 2 * 2 | Δ² (t, s)} -> k (t, s)), \hh -> refl_{hh}),
       (\k -> (\(t : 2) -> k (t, t), \{(t, s) : 2 * 2 | Δ² (t, s)} -> k (t, s)), \hh -> refl_{hh})))

#def restriction-equiv
  (A : U)                       -- A type.
  : Eq (<{t : 2 * 2 | Δ² t} -> A >)
      (∑ (k : <{t : 2 * 2 | Λ t} -> A >),
        ∑ (h : hom A (k (0_2, 0_2)) (k (1_2, 1_2))),
          hom2 A (k (0_2, 0_2)) (k (1_2, 0_2)) (k (1_2, 1_2))
                 (\t -> k (t, 0_2)) (\t -> k (1_2, t)) h)
  := (\k ->
      (\{t : 2 * 2 | Λ t} -> k t,
        (\(t : 2) -> k (t, t),
         \{t : 2 * 2 | Δ² t} -> k t)),
      ((\khh -> \{t : 2 * 2 | Δ² t} -> (second (second khh)) t, \k -> refl_{k}),
        (\khh -> \{t : 2 * 2 | Δ² t} -> (second (second khh)) t, \k -> refl_{k})))

-- [RS17, Theorem 5.5], the hard direction:
#def Segal-restriction-equiv 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  : Eq (<{t : 2 * 2 | Δ² t} -> A >) (<{t : 2 * 2 | Λ t} -> A >) -- (horn-restriction A)
  := compose_Eq
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
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  : (first (Segal-restriction-equiv A AisSegal)) =_{(_ : <{t : 2 * 2 | Δ² t} -> A >) -> <{t : 2 * 2 | Λ t} -> A >} (horn-restriction A)
  := refl_{horn-restriction A}

-- Theorem 5.5 justifies an alternate definition of isSegal
#def isSegal'
  (A : U)       -- A type.
  : U
  := isEquiv (<{t : 2 * 2 | Δ² t} -> A >) (<{t : 2 * 2 | Λ t} -> A >) (horn-restriction A) 

#def isSegal-isSegal' 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  : isSegal' A
  := second (Segal-restriction-equiv A AisSegal)  

#def isSegal'-isSegal 
  (A : U)                       -- A type.
  (AisSegal' : isSegal' A)      -- A proof that A is Segal'.
  : isSegal A
  := \x y z f g ->
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
          (horn-restriction A, AisSegal')
        )))
      (horn A x y z f g)  

-- these notions are equivalent, not just logically equivalent, because they are both propositions over A
#def isSegal-iff-isSegal' 
  (A : U)                       -- A type.
  : iff (isSegal A) (isSegal' A)      
  := (isSegal-isSegal' A , isSegal'-isSegal A)

-- [RS17, Corollary 5.6(i)] : if X is a type and A : X -> U is such that A(x) is a Segal type then (x : X) -> A x is a Segal type
#def Segal-function-types 
  (funext : FunExt)                                 -- This proof uses function extensionality defined in 4-equivalences.rzk
  (X : U)                                           -- A type.
  (A : (_ : X) -> U)                                -- A type family
  (fiberwiseAisSegal : (x : X) -> isSegal' (A x))   -- An assumption that the fibers are Segal types.
  : isSegal' ((x : X) -> A x) 
  := triple_compose_isEquiv
       (<{t : 2 * 2 | Δ² t} -> ((x : X) -> A x) >)
       ((x : X) -> <{t : 2 * 2 | Δ² t} -> A x >) 
       ((x : X) -> <{t : 2 * 2 | Λ t} -> A x >) 
       (<{t : 2 * 2 | Λ t} -> ((x : X) -> A x) >)
        (\g -> \x -> \{t : 2 * 2 | Δ² t} -> g t x) -- first equivalence
            (second (flip-ext-fun
              (2 * 2)
              Δ² (\{t : 2 * 2 | Δ² t} -> BOT)
              X
              (\{t : 2 * 2 | Δ² t} -> A)
              (\{t : 2 * 2 | BOT} -> recBOT)))
        (\h -> \x -> \{t : 2 * 2 | Λ t} -> h x t) -- second equivalence
          (second (fibered-equiv-function-equiv 
              funext 
              X 
              (\x -> <{t : 2 * 2 | Δ² t} -> A x >) 
              (\x -> <{t : 2 * 2 | Λ t} -> A x >) 
              (\x -> (horn-restriction (A x) , fiberwiseAisSegal x))))
        (\h -> \{t : 2 * 2 | Λ t} -> \x -> (h x) t) -- third equivalence
          (second(flip-ext-fun-inv
            (2 * 2)
            Λ (\{t : 2 * 2 | Λ t} -> BOT)
            X
            (\{t : 2 * 2 | Λ t} -> A)
            (\{t : 2 * 2 | BOT} -> recBOT)))

-- [RS17, Corollary 5.6(ii)] : if X is a shape and A : X -> U is such that A(x) is a Segal type then (x : X) -> A x is a Segal type
#def Segal-extension-types 
  (extext : ExtExt)                                             -- This proof uses extension extensionality, defined in 4-extension-types.md
  (I : CUBE)                                                    -- A cube.
  (psi : (s : I) -> TOPE)                                       -- A tope.
  (A : <{s : I | psi s} -> U >)                                 -- An extension type.
  (fiberwiseAisSegal : <{s : I | psi s} -> isSegal' (A s) >)    -- An assumption that the fibers are Segal types.
  : isSegal' (<{s : I | psi s} -> A s >) 
  := triple_compose_isEquiv
        (<{t : 2 * 2 | Δ² t} -> <{s : I | psi s} -> A s > >) 
        (<{s : I | psi s} -> <{t : 2 * 2 | Δ² t} -> A s > >)
        (<{s : I | psi s} -> <{t : 2 * 2 | Λ t} -> A s > >)
        (<{t : 2 * 2 | Λ t} -> <{s : I | psi s} -> A s > >)
        (\g -> \{s : I | psi s} -> \{t : 2 * 2 | Δ² t} -> g t s)  -- first equivalence
            (second(fubini
              (2 * 2)
              I 
              Δ²
              (\{t : 2 * 2 | Δ² t} -> BOT)
              psi
              (\{s : I | psi s} -> BOT)
              (\{t : 2 * 2 | Δ² t} -> \{s : I | psi s} -> A s)
              (\{u : (2 * 2) * I | BOT} -> recBOT)))
        (\h -> \{s : I | psi s} -> \{t : 2 * 2 | Λ t} -> h s t) -- second equivalence
          (second (fibered-equiv-extension-equiv extext I psi  
            (\{s : I | psi s} -> <{t : 2 * 2 | Δ² t} -> A s >)
            (\{s : I | psi s} -> <{t : 2 * 2 | Λ t} -> A s >)
            (\{s : I | psi s} -> (horn-restriction (A s), fiberwiseAisSegal s))     ))
        (\h -> \{t : 2 * 2 | Λ t} -> \{s : I | psi s} -> (h s) t) -- third equivalence
          (second(fubini
            I 
            (2 * 2)
            psi
            (\{s : I | psi s} -> BOT)
            Λ
            (\{t : 2 * 2 | Λ t} -> BOT)
            (\{s : I | psi s} -> \{t : 2 * 2 | Λ t} -> A s)
            (\{u : I * (2 * 2) | BOT} -> recBOT)))        

-- The type of arrows in a type.
#def arr        -- A type
  (A : U) 
  : U
  := (t : Δ¹) -> A

-- A special case of [RS17, Corollary 5.6(ii)], using is-Segal'.
#def Segal'-arrow-types 
  (extext : ExtExt)                         -- This proof uses extension extensionality, defined in 4-extension-types.md
  (A : U)                                   -- A type.
  (AisSegal : isSegal' A)                   -- A proof that A isSegal'.
  : isSegal' (arr A)
  := Segal-extension-types
        extext
        2
        Δ¹
        (\{t : 2 | Δ¹ t} -> A)
        (\{t : 2 | Δ¹ t} -> AisSegal)  

-- A special case of [RS17, Corollary 5.6(ii)], using is-Segal.
#def Segal-arrow-types 
  (extext : ExtExt)                         -- This proof uses extension extensionality, defined in 4-extension-types.md
  (A : U)                                   -- A type.
  (AisSegal : isSegal A)                    -- A proof that A is Segal.
  : isSegal (arr A)
  := isSegal'-isSegal (arr A)
      (Segal-extension-types
        extext
        2
        Δ¹
        (\{t : 2 | Δ¹ t} -> A)
        (\{t : 2 | Δ¹ t} -> (isSegal-isSegal' A AisSegal)))
```

## Identity

```rzk
-- [RS17, Definition 5.7]
-- all types have identity arrows
#def id-arr
  (A : U)               -- A type.
  (x : A)               -- A point in A.
  : hom A x x
  := \{t : 2 | Δ¹ t} -> x 

-- [RS17, Proposition 5.8a]
-- the right unit law for identity
#def comp-id-witness 
  (A : U)                   -- A type.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : hom2 A x y y f (id-arr A y) f
  := \{(t, s) : 2 * 2 | Δ² (t, s)} -> f t

-- If A is Segal then the right unit law holds
#def Segal-comp-id
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : (Segal-comp A AisSegal x y y f (id-arr A y)) =_{hom A x y} f
  := Segal-comp-uniqueness
      A
      AisSegal
      x y y
      f
      (id-arr A y)
      f
      (comp-id-witness A x y f)

-- [RS17, Proposition 5.8b]
-- the left unit law for identity
#def id-comp-witness 
  (A : U)                   -- A type.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : hom2 A x x y (id-arr A x) f f
  := \{(t, s) : 2 * 2 | Δ² (t, s)} -> f s

-- If A is Segal then the left unit law holds
#def Segal-id-comp
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : (Segal-comp A AisSegal x x y (id-arr A x) f) =_{hom A x y} f
  := Segal-comp-uniqueness
      A
      AisSegal
      x x y
      (id-arr A x)
      f
      f
      (id-comp-witness A x y f)
```

## Associativity

```rzk
#def unfolding-square : (A : U) -> (_ : <{vu : 2 * 2 | Δ² vu} -> A >) -> <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A >
  := \A -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-test : (A : U) -> (x : A) -> 
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [(first vu) === 0_2 /\ (second vu) === 0_2 |-> x ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [(first ts) === 0_2 /\ (second ts) === 0_2 |-> x ] >
  := \A -> \x -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-another-test : (A : U) -> (f : <{t : 2 | Δ¹ t} -> A >) -> 
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [(second vu) === 0_2 |-> f (first vu) ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [(first ts) === 0_2 |-> f (second ts) ] >
  := \A -> \f -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-yet-another-test : (A : U) -> (x : A) -> (y : A) -> (f : hom A x y) -> 
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [(second vu) === 0_2 |-> f (first vu) ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [(first ts) === 0_2 |-> f (second ts) ] >
  := \A -> \x -> \y -> \f -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-horn-left-test : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) ->
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [ Λ vu |-> horn A x y z f g vu ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [(first ts) === 0_2 |-> f (second ts)] >
  := \A -> \x -> \y -> \z -> \f -> \g -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-horn-right-test : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) ->
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [ Λ vu |-> horn A x y z f g vu ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [(first ts) === 1_2 |-> g(second ts) ] >
  := \A -> \x -> \y -> \z -> \f -> \g -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def unfolding-square-horn-combined-test : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) ->
  (_ : <{vu : 2 * 2 | Δ² vu} -> A [ Λ vu |-> horn A x y z f g vu ] >) -> 
  <{ts : 2 * 2 | Δ¹×Δ¹ ts} -> A [ (first ts) === 0_2 \/ (first ts) === 1_2 |-> recOR ((first ts) === 0_2, (first ts) === 1_2, f(second ts), g(second ts)) ] >
  := \A -> \x -> \y -> \z -> \f -> \g -> \simp -> \{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

-- #def boundary-unfolding-square : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (f : hom A x y) -> (g : hom A y z) 
--   -> (_ : <{vu : 2 * 2 | Δ² vu} -> A [ Λ vu |-> horn A x y z f g vu ] >) 
--  -> <{ts : 2 * 2 | □ ts} -> 
--      A [ || ts |-> recOR((first ts) === 0_2, (first ts) === 1_2, f (second ts), g (second ts))] >
--  := \A -> \x -> \y -> \z -> \f -> \g -> \simp -> \{(t, s) : 2 * 2 | □ (t, s)}  -> recOR(t <= s, s <= t, simp (s , t), simp (t , s))

#def square-to-arr-in-arr : (A : U) -> (_ : <{vu : 2 * 2 | TOP} -> A >) -> (<{t : 2 | Δ¹ t} -> <{s : 2 | Δ¹ s} -> A > >)
  := \A -> \square -> \{t : 2 | Δ¹ t} -> \{s : 2 | Δ¹ s} -> square ((t , s))

-- the following failed until I changed the variable names in hom2 to (t2, t1); now this isn't needed
#def Segal-comp-witness-triangle : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (f : hom A x y) -> (g : hom A y z) -> <{(t, s) : 2 * 2 | Δ² (t, s)} -> A	>
  := \A -> \AisSegal -> \x -> \y -> \z -> \f -> \g -> (Segal-comp-witness A AisSegal x y z f g)

-- for use in the proof of associativity
#def Segal-comp-witness-square : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (f : hom A x y) -> (g : hom A y z) -> <{w : 2 * 2 | TOP} -> A >
  := \A -> \AisSegal -> \x -> \y -> \z -> \f -> \g -> unfolding-square A 
        (extension-projection
          (2 * 2)
          (Δ²)
          (∂Δ²)
          (\{w : 2 * 2 | Δ² w} -> A)
          (\{(v, u) : 2 * 2 | ∂Δ² (v, u)} -> 
            recOR(u === 0_2, v === 1_2 \/ u === v, f v, 
              recOR(v === 1_2, u === v, g u, (Segal-comp A AisSegal x y z f g) u))) 
          (Segal-comp-witness A AisSegal x y z f g))

#def Segal-arr-in-arr : (A : U) -> (AisSegal : isSegal A) -> (x : A) -> (y : A) -> (z : A) 
  -> (f : hom A x y) -> (g : hom A y z) -> hom (arr A) f g
  := \A -> \AisSegal -> \x -> \y -> \z -> \f -> \g -> 
    square-to-arr-in-arr A (Segal-comp-witness-square A AisSegal x y z f g)

#def Segal-horn-in-arrow : (A : U) -> (AisSegal : isSegal A) -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) ->     <{t : 2 * 2 | Λ t } -> arr A >
  := \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h ->
    horn (arr A) f g h
        (Segal-arr-in-arr A AisSegal w x y f g)
        (Segal-arr-in-arr A AisSegal x y z g h)

#def Segal-associativity-witness : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) ->
     hom2 (arr A) f g h (Segal-arr-in-arr A AisSegal w x y f g) (Segal-arr-in-arr A AisSegal x y z g h)
        (Segal-comp (arr A) (Segal-arrow-types extext A AisSegal) 
          f g h 
          (Segal-arr-in-arr A AisSegal w x y f g) (Segal-arr-in-arr A AisSegal x y z g h))
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> 
    (Segal-comp-witness (arr A) (Segal-arrow-types extext A AisSegal) 
      f g h
      (Segal-arr-in-arr A AisSegal w x y f g) (Segal-arr-in-arr A AisSegal x y z g h))

#def Segal-associativity-prism : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) -> <{t : (2 * 2) * 2 | Δ²×Δ¹ t} -> A >
  :=  \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \(t, s) -> 
    (Segal-associativity-witness extext A AisSegal w x y z f g h) t s

-- extracted via the middle-simplex map \((t, s), r) -> ((t, r), s) from Δ³ to Δ²×Δ¹
#def Segal-associativity-tetrahedron : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) -> <{t : (2 * 2) * 2 | Δ³ t} -> A >
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \((t, s), r) -> 
    (Segal-associativity-prism extext A AisSegal w x y z f g h) ((t, r), s)

-- the diagonal composite; fails to recognize that the codomain is z (more comprehensible error message)
#def Segal-triple-composite-also-fails : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) -> hom A w z -- <{t : 2 | Δ¹ t} -> A [t === 0_2 |-> w] >
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \t ->
    (Segal-associativity-prism extext A AisSegal w x y z f g h) ((t, t), t)

-- the diagonal composite; fails to recognize that the codomain is z (long error message)
#def Segal-triple-composite-fails : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) -> hom A w z -- <{t : 2 | Δ¹ t} -> A [t === 0_2 |-> w] > 
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \t ->
    (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, t), t)

-- the diagonal composite can be found here
#def Segal-triple-composite : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) -> hom A w z 
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \t ->
    (Segal-comp (arr A) (Segal-arrow-types extext A AisSegal) 
          f g h 
          (Segal-arr-in-arr A AisSegal w x y f g) (Segal-arr-in-arr A AisSegal x y z g h)) t t

#def Segal-left-associativity-witness : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) 
  -> hom2 A w y z (Segal-comp A AisSegal w x y f g) h (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \(t, s) -> 
    (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, t), s)
 
#def Segal-right-associativity-witness : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) 
  -> hom2 A w x z f (Segal-comp A AisSegal x y z g h) (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h -> \(t, s) -> 
  (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, s), s)

#def Segal-left-associativity : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) ->
  (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h) =_{hom A w z}
  (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h ->
      Segal-comp-uniqueness 
        A AisSegal w y z (Segal-comp A AisSegal w x y f g) h
        (Segal-triple-composite extext A AisSegal w x y z f g h)
        (Segal-left-associativity-witness extext A AisSegal w x y z f g h)

#def Segal-right-associativity : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) ->
  (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h)) =_{hom A w z}
  (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h ->
      Segal-comp-uniqueness 
        A AisSegal w x z f (Segal-comp A AisSegal x y z g h)
        (Segal-triple-composite extext A AisSegal w x y z f g h)
        (Segal-right-associativity-witness extext A AisSegal w x y z f g h)

#def Segal-associativity : (extext : ExtExt) -> (A : U) -> (AisSegal : isSegal A) 
  -> (w : A) -> (x : A) -> (y : A) -> (z : A)
  -> (f : hom A w x) -> (g : hom A x y) -> (h : hom A y z) ->
  (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h) =_{hom A w z}
  (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h)) 
  := \extext -> \A -> \AisSegal -> \w -> \x -> \y -> \z -> \f -> \g -> \h ->
    zig-zag-concat (hom A w z) 
      (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h)
      (Segal-triple-composite extext A AisSegal w x y z f g h)
      (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h))
      (Segal-left-associativity extext A AisSegal w x y z f g h) 
      (Segal-right-associativity extext A AisSegal w x y z f g h)
```


## Homotopies

To be done.

## Anodyne maps

To be done.