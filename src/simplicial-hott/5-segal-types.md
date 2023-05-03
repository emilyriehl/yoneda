# Segal Types

These formalisations correspond to Section 5 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/1-paths.md` - We require basic path algebra.
- `hott/2-contractible.md` - We require the notion of contractible types and their data.
- `hott/total-space.md` — We rely on `contractible-fibers-projection-equiv` and `total-space-projection` in the proof of Theorem 5.5.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension extensionality.

## Hom types

Extension types are used to define the type of arrows between fixed terms:

<svg style="float: right" viewBox="0 0 200 60" width="150" height="60">
  <polyline points="40,30 160,30" stroke="blue" stroke-width="3" marker-end="url(#arrow-blue)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
</svg>

```rzk
-- [RS17, Definition 5.1]
-- The type of arrows in A from x to y.
#def hom
  (A : U)   -- A type.
  (x y : A) -- Two points in A.
  : U                   -- (hom A x y) is a 1-simplex (an arrow)
  := (t : Δ¹) -> A [    -- in A where
    t === 0_2 |-> x,    -- * the left endpoint is exactly x
    t === 1_2 |-> y     -- * the right endpoint is exactly y
  ]
```

Extension types are also used to define the type of commutative triangles:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="200">
  <path style="fill: rgb(0,128,255,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,40 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110">h</text>
</svg>

```rzk
-- [RS17, Definition 5.2]
-- the type of commutative triangles in A
#def hom2
  (A : U)           -- A type.
  (x y z : A)       -- Three points in A.
  (f : hom A x y)   -- An arrow in A from x to y.
  (g : hom A y z)   -- An arrow in A from y to z.
  (h : hom A x z)   -- An arrow in A from x to z.
  : U                           -- (hom2 A x y z f g h) is a 2-simplex (triangle)
  := { (t1, t2) : Δ² } -> A [   -- in A where
    t2 === 0_2 |-> f t1,        -- * the top edge is exactly f,
    t1 === 1_2 |-> g t2,        -- * the right edge is exactly g, and
    t2 === t1  |-> h t2         -- * the diagonal is exactly h
  ]
```

## The Segal condition

A type is Segal if every composable pair of arrows has a unique composite. Note this is a considerable simplification of the usual Segal condition, which also requires homotopical uniqueness of higher-order composites.

```rzk
-- [RS17, Definition 5.3]
#def isSegal 
  (A : U)         -- A type.
  : U
  := (x : A) -> (y : A) -> (z : A) -> 
      (f : hom A x y) -> (g : hom A y z) -> 
      isContr( ∑ (h : hom A x z), hom2 A x y z f g h)
```
Segal types have a composition functor and witnesses to the composition relation:

```rzk
-- Composition is written in diagrammatic order to match the order of arguments in isSegal.
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
```

Composition in a Segal type is unique in the following sense. If there is a witness that an arrow h is a composite of f and g, then the specified composite equals h.

<svg style="float: right" viewBox="0 0 200 380" width="125">
  <path style="fill: rgb(175,175,175,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,45 170,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30" fill="grey">x</text>
  <text x="170" y="30" fill="grey">y</text>
  <text x="170" y="170" fill="grey">z</text>
  <text x="100" y="15" fill="grey">f</text>
  <text x="185" y="100" fill="grey">g</text>
  <text x="90" y="110">h</text>
  <text x="125" y="75" fill="grey">α</text>
  <text x="100" y="145" fill="red" rotate="90" style="font-size: 50px">=</text>
  <path style="fill: rgb(128,0,0,0.5); stroke-cap: round;" d="M 52 240 L 160 240 L 160 348 Z"></path>
  <polyline points="40,230 160,230" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,245 170,360" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,240 160,360" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="230" fill="grey">x</text>
  <text x="170" y="230" fill="grey">y</text>
  <text x="170" y="370" fill="grey">z</text>
  <text x="100" y="215" fill="grey">f</text>
  <text x="185" y="300" fill="grey">g</text>
  <text x="90" y="310" transform="rotate(45, 90, 310)" fill="red">Segal-comp</text>
  <text x="120" y="280" fill="rgb(128,0,0)" transform="rotate(45, 120, 280)" style="font-size: 10px">Segal-comp-witness</text>
</svg>

```rzk
#def Segal-comp-uniqueness 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  (h : hom A x z)               -- An arrow in A from x to z.
  (alpha : hom2 A x y z f g h)  -- A witness that h is a composite of f and g.
  : (Segal-comp A AisSegal x y z f g) = h
  := total-path-to-base-path 
      (hom A x z)
      (\k -> hom2 A x y z f g k)
      (Segal-comp A AisSegal x y z f g, 
        Segal-comp-witness A AisSegal x y z f g)
      (h, alpha)
      (contracting-htpy 
        (∑ (k : hom A x z), hom2 A x y z f g k) 
        (AisSegal x y z f g) 
        (h, alpha))
```

### Characterizing Segal types

Our aim is to prove that a type is Segal if and only if the horn-restriction map, defined below, is an equivalence.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
</svg>

```rzk
-- A pair of composable arrows form a horn.
#def horn
  (A : U)           -- A type.
  (x y z : A)       -- Three points in A.
  (f : hom A x y)   -- An arrow in A from x to y.
  (g : hom A y z)   -- An arrow in A from y to z.
  : Λ -> A
  := \(t, s) -> recOR(
    s === 0_2 |-> f t, 
    t === 1_2 |-> g s
  )
```

```rzk
-- The underlying horn of a simplex
#def horn-restriction (A : U)
  : (Δ² -> A) -> (Λ -> A)
  :=  \f t -> f t

-- An alternate definition of Segal types.
#def isSegal' (A : U) : U
  := isEquiv (Δ² -> A) (Λ -> A) (horn-restriction A) 
```  

Now we prove this definition is equivalent to the original one.

```rzk
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
      ((\k -> (\(t : 2) -> k (t, t), \(t, s) -> k (t, s)), \hh -> refl),
       (\k -> (\(t : 2) -> k (t, t), \(t, s) -> k (t, s)), \hh -> refl)))

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
  : (first (Segal-restriction-equiv A AisSegal)) = (horn-restriction A)
  := refl

-- Segal types are Segal' types.
#def isSegal-isSegal' 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  : isSegal' A
  := second (Segal-restriction-equiv A AisSegal)  

-- Segal' types are Segal types.
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

-- [RS17, Theorem 5.5] proves that both notions of Segal types are logically equivalent.
#def isSegal-iff-isSegal' 
  (A : U)                       -- A type.
  : iff (isSegal A) (isSegal' A)      
  := (isSegal-isSegal' A , isSegal'-isSegal A)
```

## Segal function and extension types

Using the new characterization of Segal types, we can show that the type of functions or extensions into a family of Segal types is again a Segal type.

```rzk
-- [RS17, Corollary 5.6(i)] : if X is a type and A : X -> U is such that
-- A(x) is a Segal type for all x then (x : X) -> A x is a Segal type
#def Segal-function-types 
  (funext : FunExt)                                 -- This proof uses function extensionality.
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

-- [RS17, Corollary 5.6(ii)] : if X is a shape and A : X -> U is such that 
-- A(x) is a Segal type for all x then (x : X) -> A x is a Segal type
#def Segal-extension-types 
  (extext : ExtExt)                                             -- This proof uses extension extensionality.
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
```
In particular, the arrow type of a Segal type is Segal.

```rzk
-- The type of arrows in a type.
#def arr        -- A type
  (A : U) 
  : U
  := (t : Δ¹) -> A

-- A special case of [RS17, Corollary 5.6(ii)], using is-Segal'.
#def Segal'-arrow-types 
  (extext : ExtExt)                         -- This proof uses extension extensionality.
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
  (extext : ExtExt)                         -- This proof uses extension extensionality.
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

All types have identity arrows and witnesses to the identity composition law.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="100" y="15" fill="red">x</text>
</svg>

```rzk
-- [RS17, Definition 5.7]
-- all types have identity arrows
#def id-arr
  (A : U)               -- A type.
  (x : A)               -- A point in A.
  : hom A x x
  := \{t : 2 | Δ¹ t} -> x 
```

Witness for the right identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">y</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk
-- [RS17, Proposition 5.8a]
-- the right unit law for identity
#def comp-id-witness 
  (A : U)                   -- A type.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : hom2 A x y y f (id-arr A y) f
  := \{(t, s) : 2 * 2 | Δ² (t, s)} -> f t
```

Witness for the left identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">x</text>
  <text x="185" y="100">f</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk
-- [RS17, Proposition 5.8b]
-- the left unit law for identity
#def id-comp-witness 
  (A : U)                   -- A type.
  (x y : A)                 -- Two points in A.
  (f : hom A x y)           -- An arrow from x to y in A.
  : hom2 A x x y (id-arr A x) f f
  := \{(t, s) : 2 * 2 | Δ² (t, s)} -> f s
```

In a Segal type, where composition is unique, it follows that composition with an identity arrow recovers the original arrow. 
Thus, an identity axiom was not needed in the definition of Segal types.

```rzk
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

We now prove that composition in a Segal type is associative, by using the fact that the type of arrows in a Segal type is itself a Segal type.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,170 160,170" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">•</text>
  <text x="170" y="30">•</text>
  <text x="170" y="170">•</text>
  <text x="30" y="170" fill="red">•</text>
</svg>

```rzk
#def unfolding-square 
  (A : U)                         -- A type.
  (triangle : Δ² -> A)            -- A triangle in A.
  : Δ¹×Δ¹ -> A                    -- A square in A, defined by gluing
  := \(t, s) ->                   -- two copies of the triangle along the common diagonal edge.
    recOR(t <= s |-> triangle (s , t), 
        s <= t |-> triangle (t , s))
```

For use in the proof of associativity:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="45,170 160,170" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110" transform="rotate(45, 90, 110)" fill="red">Segal-comp</text>
  <text x="100" y="190">g</text>
  <text x="15" y="100">f</text>
</svg>

```rzk
#def Segal-comp-witness-square 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : Δ¹×Δ¹ -> A 
  := unfolding-square A (Segal-comp-witness A AisSegal x y z f g)
```

The Segal-comp-witness-square as an arrow in the arrow type:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
</svg>

```rzk
#def Segal-arr-in-arr 
  (A : U)                       -- A type.
  (AisSegal : isSegal A)        -- A proof that A is Segal.
  (x y z : A)                   -- Three points in A.
  (f : hom A x y)               -- An arrow in A from x to y.
  (g : hom A y z)               -- An arrow in A from y to z.
  : hom (arr A) f g
  := \t -> \s -> (Segal-comp-witness-square A AisSegal x y z f g) (t, s)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="40,170 160,170" stroke="lightgrey" stroke-width="3"></polyline>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 100 L 160 100 L 100 130 Z"></path>
  <polyline points="100,70 100,190" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,105 105,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,105 95,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="155,35 105,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,35 95,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="155,175 105,195" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,175 95,195" stroke="lightgrey" stroke-width="3"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="30" y="170">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="60">y</text>
  <text x="100" y="200">z</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="150">h</text>
</svg>

```rzk
#def Segal-associativity-witness 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : hom2 (arr A) f g h
      (Segal-arr-in-arr A AisSegal w x y f g)
      (Segal-arr-in-arr A AisSegal x y z g h)
      (Segal-comp (arr A) (Segal-arrow-types extext A AisSegal) 
      f g h 
      (Segal-arr-in-arr A AisSegal w x y f g) 
      (Segal-arr-in-arr A AisSegal x y z g h))
  := (Segal-comp-witness (arr A) (Segal-arrow-types extext A AisSegal) 
      f g h
      (Segal-arr-in-arr A AisSegal w x y f g) 
      (Segal-arr-in-arr A AisSegal x y z g h))
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
-- The Segal-associativity-witness curries to define a diagram Δ²×Δ¹ -> A.
-- The Segal-associativity-tetrahedron is extracted via the middle-simplex map \((t, s), r) -> ((t, r), s) from Δ³ to Δ²×Δ¹
#def Segal-associativity-tetrahedron 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : Δ³ -> A
  := \((t, s), r) -> 
    (Segal-associativity-witness extext A AisSegal w x y z f g h) (t, r) s
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
-- the diagonal composite of three arrows extracted from the Segal-associativity-tetrahedron
#def Segal-triple-composite 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : hom A w z 
  := \t -> 
    (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, t), t)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 40 35 L 165 35 L 165 160 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 40 L 160 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def Segal-left-associativity-witness 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : hom2 A w y z 
    (Segal-comp A AisSegal w x y f g) 
    h 
    (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \(t, s) -> 
    (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, t), s)
```

The front face:

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 155 35 L 100 185 Z"></path>
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 165 40 L 165 165 L 115 185 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk 
#def Segal-right-associativity-witness 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : hom2 A w x z 
    f 
    (Segal-comp A AisSegal x y z g h) 
    (Segal-triple-composite extext A AisSegal w x y z f g h)
  := \(t, s) -> 
    (Segal-associativity-tetrahedron extext A AisSegal w x y z f g h) ((t, s), s)
```

```rzk
#def Segal-left-associativity 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h) =
      (Segal-triple-composite extext A AisSegal w x y z f g h)
  := Segal-comp-uniqueness 
        A AisSegal w y z (Segal-comp A AisSegal w x y f g) h
        (Segal-triple-composite extext A AisSegal w x y z f g h)
        (Segal-left-associativity-witness extext A AisSegal w x y z f g h)

#def Segal-right-associativity 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h)) =
      (Segal-triple-composite extext A AisSegal w x y z f g h)
  := Segal-comp-uniqueness 
        A AisSegal w x z f (Segal-comp A AisSegal x y z g h)
        (Segal-triple-composite extext A AisSegal w x y z f g h)
        (Segal-right-associativity-witness extext A AisSegal w x y z f g h)

#def Segal-associativity 
  (extext : ExtExt)         -- This proof uses extension extensionality.
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y z : A)             -- Four points in A.
  (f : hom A w x)           -- An arrow in A from w to x.
  (g : hom A x y)           -- An arrow in A from x to y.
  (h : hom A y z)           -- An arrow in A from y to z.
  : (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h) =
      (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h)) 
  := zig-zag-concat (hom A w z) 
      (Segal-comp A AisSegal w y z (Segal-comp A AisSegal w x y f g) h)
      (Segal-triple-composite extext A AisSegal w x y z f g h)
      (Segal-comp A AisSegal w x z f (Segal-comp A AisSegal x y z g h))
      (Segal-left-associativity extext A AisSegal w x y z f g h) 
      (Segal-right-associativity extext A AisSegal w x y z f g h)
```

## Homotopies

We may define a "homotopy" to be a path between parallel arrows. In a Segal type, homotopies are equivalent to terms in hom2 types involving an identity arrow.


```rzk
#def homotopy-to-hom2
  (A : U)
  (x y : A)
  (f g : hom A x y)
  (p : f = g)
  : (hom2 A x x y (id-arr A x) f g)
  := idJ(hom A x y, f, 
          \g' p' -> (hom2 A x x y (id-arr A x) f g'), 
          (id-comp-witness A x y f), g, p)

#def homotopy-to-hom2-total-map
  (A : U)
  (x y : A)
  (f : hom A x y)
  : (∑ (g : hom A x y), f = g) -> 
      (∑ (g : hom A x y), (hom2 A x x y (id-arr A x) f g))
  := \(g, p) -> (g, homotopy-to-hom2 A x y f g p)

#def Segal-homotopy-to-hom2-total-map-isEquiv
  (A : U)
  (AisSegal : isSegal A)
  (x y : A)
  (f : hom A x y)
  : isEquiv 
      (∑ (g : hom A x y), f = g)
      (∑ (g : hom A x y), (hom2 A x x y (id-arr A x) f g))
      (homotopy-to-hom2-total-map A x y f)
  := areContr-isEquiv 
        (∑ (g : hom A x y), f = g)
        (∑ (g : hom A x y), (hom2 A x x y (id-arr A x) f g))
        (based-paths-contractible (hom A x y) f)
        (AisSegal x x y (id-arr A x) f)
        (homotopy-to-hom2-total-map A x y f)

-- [RS17, Proposition 5.10]
#def Eq-Segal-homotopy-hom2
  (A : U)
  (AisSegal : isSegal A)
  (x y : A)
  (f g : hom A x y)
  : Eq (f = g) (hom2 A x x y (id-arr A x) f g)
  := (homotopy-to-hom2 A x y f g, 
    total-equiv-family-of-equiv (hom A x y) 
      (\g -> (f = g))
      (\g -> (hom2 A x x y (id-arr A x) f g))
      (homotopy-to-hom2 A x y f)
      (Segal-homotopy-to-hom2-total-map-isEquiv A AisSegal x y f)
      g)
```

More generally, a homotopy between a composite and another map is equivalent to the data provided by a commutative triangle with that boundary.

```rzk
#def Segal-eq-to-hom2
  (A : U)
  (AisSegal : isSegal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  (p : (Segal-comp A AisSegal x y z f g) = h)
  : (hom2 A x y z f g h)
  := idJ(hom A x z, (Segal-comp A AisSegal x y z f g), 
          \h' p' -> (hom2 A x y z f g h'), 
          Segal-comp-witness A AisSegal x y z f g, h, p)

#def Segal-eq-to-hom2-total-map
  (A : U)
  (AisSegal : isSegal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : (∑ (h : hom A x z), (Segal-comp A AisSegal x y z f g) = h) -> 
      (∑ (h : hom A x z), (hom2 A x y z f g h))
  := \(h, p) -> (h, Segal-eq-to-hom2 A AisSegal x y z f g h p)

#def Segal-eq-to-hom2-total-map-isEquiv
  (A : U)
  (AisSegal : isSegal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : isEquiv 
      (∑ (h : hom A x z), (Segal-comp A AisSegal x y z f g) = h)
      (∑ (h : hom A x z), (hom2 A x y z f g h))
      (Segal-eq-to-hom2-total-map A AisSegal x y z f g)
  := areContr-isEquiv 
        (∑ (h : hom A x z), (Segal-comp A AisSegal x y z f g) = h)
        (∑ (h : hom A x z), (hom2 A x y z f g h))
        (based-paths-contractible (hom A x z) (Segal-comp A AisSegal x y z f g) )
        (AisSegal x y z f g)
        (Segal-eq-to-hom2-total-map A AisSegal x y z f g)

-- [RS17, Proposition 5.12]
#def Eq-Segal-eq-hom2
  (A : U)
  (AisSegal : isSegal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  : Eq ((Segal-comp A AisSegal x y z f g) = h) (hom2 A x y z f g h)
  := (Segal-eq-to-hom2 A AisSegal x y z f g h, 
    total-equiv-family-of-equiv (hom A x z) 
      (\h -> (Segal-comp A AisSegal x y z f g) = h)
      (\h -> hom2 A x y z f g h)
      (Segal-eq-to-hom2 A AisSegal x y z f g)
      (Segal-eq-to-hom2-total-map-isEquiv A AisSegal x y z f g)
      h)
```


Homotopies form a congruence, meaning that homotopies are respected by composition:

```rzk
-- [RS17, Proposition 5.13]
#def Segal-homotopy-congruence  
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (x y z : A)
  (f g : hom A x y)
  (h k : hom A y z)
  (p : f = g)
  (q : h = k)
  : (Segal-comp A AisSegal x y z f h) = (Segal-comp A AisSegal x y z g k)
  := idJ(hom A y z, h, \k' q' -> (Segal-comp A AisSegal x y z f h) = (Segal-comp A AisSegal x y z g k'),
    idJ(hom A x y, f, \g' p' -> (Segal-comp A AisSegal x y z f h) = (Segal-comp A AisSegal x y z g' h), refl, g, p)
    , k, q)

-- As a special case of the above:
#def Segal-homotopy-postwhisker 
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (x y z : A)
  (f g : hom A x y)
  (h : hom A y z)
  (p : f = g)
  : (Segal-comp A AisSegal x y z f h) = (Segal-comp A AisSegal x y z g h)
  := Segal-homotopy-congruence A AisSegal x y z f g h h p refl

-- As a special case of the above:
#def Segal-homotopy-prewhisker 
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y : A)
  (k : hom A w x)
  (f g : hom A x y)
  (p : f = g)
  : (Segal-comp A AisSegal w x y k f) = (Segal-comp A AisSegal w x y k g)
  := Segal-homotopy-congruence A AisSegal w x y k k f g refl p

-- [RS17, Proposition 5.14(a)]
#def Segal-homotopy-postwhisker-is-ap 
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (x y z : A)
  (f g : hom A x y)
  (h : hom A y z)
  (p : f = g)
  : (Segal-homotopy-postwhisker A AisSegal x y z f g h p) = 
    ap (hom A x y) (hom A x z) f g (\k -> Segal-comp A AisSegal x y z k h) p
  := idJ(hom A x y, f, \g' p' -> (Segal-homotopy-postwhisker A AisSegal x y z f g' h p') = 
    ap (hom A x y) (hom A x z) f g' (\k -> Segal-comp A AisSegal x y z k h) p', refl, g, p)

-- [RS17, Proposition 5.14(b)]
#def Segal-homotopy-prewhisker-is-ap 
  (A : U)                   -- A type.
  (AisSegal : isSegal A)    -- A proof that A is Segal.  
  (w x y : A)
  (k : hom A w x)
  (f g : hom A x y)
  (p : f = g)
  : (Segal-homotopy-prewhisker A AisSegal w x y k f g p) = 
    ap (hom A x y) (hom A w y) f g (Segal-comp A AisSegal w x y k) p
  := idJ(hom A x y, f, \g' p' -> (Segal-homotopy-prewhisker A AisSegal w x y k f g' p') = 
    ap (hom A x y) (hom A w y) f g' (Segal-comp A AisSegal w x y k) p', refl, g, p)
```

<!-- Definitions for the SVG images above -->
<svg width="0" height="0">
  <defs>
    <style data-bx-fonts="Noto Serif">@import url(https://fonts.googleapis.com/css2?family=Noto+Serif&display=swap);</style>
    <marker
      id="arrow-blue"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="blue" fill="blue" />
    </marker>
    <marker
      id="arrow-red"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="red" fill="red" />
    </marker>
    <marker
      id="arrow-grey"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="grey" fill="grey" />
    </marker>
    <marker
      id="arrow"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="black" fill="black" />
    </marker>
  </defs>
  <style>
    text, textPath {
      font-family: Noto Serif;
      font-size: 20px;
      dominant-baseline: middle;
      text-anchor: middle;
    }
  </style>
</svg>