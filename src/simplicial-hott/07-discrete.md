# Discrete types

These formalisations correspond to Section 7 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/1-paths.md` - We require basic path algebra.
- `hott/4-equivalences.md` - We require the notion of equivalence between types.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `4-extension-types.md` — We use extension extensionality.
- `5-segal-types.md` - We use the notion of hom types.

## The definition

Discrete types are types in which the hom-types are canonically equivalent to identity types.

```rzk
-- [RS17, Definition 7.1]
#def id-to-arr
    (A : U)             -- A type.
    (x y : A)           -- Two points of type A.
    (p : x = y)         -- A path p from x to y in A.
    : hom A x y         -- An arrow p from x to y in A.
    := idJ(A, x, \y' -> \p' -> hom A x y', (id-arr A x), y, p)

#def isDiscrete
    (A : U)             -- A type.
    : U
    := (x : A) -> (y : A) -> isEquiv (x =_{A} y) (hom A x y) (id-to-arr A x y)
```

## Families of discrete types

By function extensionality, the dependent function type associated to a family of discrete types is discrete.

```rzk
#def Eq-discrete-family
    (funext : FunExt)
    (X : U)
    (A : X -> U)
    (Aisdiscrete : (x : X) -> isDiscrete (A x))
    (f g : (x : X) -> A x)
    : Eq (f = g)(hom ((x : X) -> A x) f g)
    := triple_compose_Eq
        (f = g)
        ((x : X) -> f x = g x)
        ((x : X) -> hom (A x) (f x) (g x))
        (hom ((x : X) -> A x) f g)
            (FunExtEq funext X A f g)
            (fibered-Eq-function-Eq funext X
                (\x -> (f x = g x))(\x -> hom (A x) (f x) (g x))
                (\x -> (id-to-arr (A x) (f x) (g x),(Aisdiscrete x (f x) (g x)))))
            (flip-ext-fun-inv 2 Δ¹ ∂Δ¹ X (\t x -> A x) (\t x -> recOR (t === 0_2 |-> f x, t === 1_2 |-> g x)))

#def Eq-discrete-family-map
    (funext : FunExt)
    (X : U)
    (A : X -> U)
    (Aisdiscrete : (x : X) -> isDiscrete (A x))
    (f g : (x : X) -> A x)
    (h : f = g)
    : id-to-arr ((x : X) -> A x) f g h = (first (Eq-discrete-family funext X A Aisdiscrete f g)) h
    := idJ((x : X) -> A x, f, \g' h' ->  id-to-arr ((x : X) -> A x) f g' h' = (first (Eq-discrete-family funext X A Aisdiscrete f g')) h', refl, g, h)

-- [RS17, Proposition 7.2]
#def isDiscrete-dependent-function-discrete-family
    (funext : FunExt)
    (X : U)
    (A : X -> U)
    (Aisdiscrete : (x : X) -> isDiscrete (A x))
    : isDiscrete ((x : X) -> A x)
    := \f g -> isEquiv-homotopic-isEquiv
            (f = g)
            (hom ((x : X) -> A x) f g)
            (id-to-arr ((x : X) -> A x) f g)
            (first (Eq-discrete-family funext X A Aisdiscrete f g))
            (Eq-discrete-family-map funext X A Aisdiscrete f g)
            (second (Eq-discrete-family funext X A Aisdiscrete f g))
```
