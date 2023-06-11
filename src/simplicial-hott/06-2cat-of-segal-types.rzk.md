# The 2-category of Segal types

These formalisations correspond to Section 6 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use extension extensionality.
- `5-segal-types.md` - We use the notion of hom types.

## Functors

Functions between types induce an action on hom types, preserving sources and
targets.

```rzk
-- [RS17, Section 6.1]
-- Action of maps on homs. Called "ap-hom" to avoid conflicting with "ap".
#def ap-hom
  (A B : U)
  (F : A -> B)
  (x y : A)
  (f : hom A x y)
  : hom B (F x) (F y)
  := \t -> F (f t)

#def ap-hom2
  (A B : U)
  (F : A -> B)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  (alpha : hom2 A x y z f g h)
  : hom2 B (F x) (F y) (F z) (ap-hom A B F x y f) (ap-hom A B F y z g) (ap-hom A B F x z h)
  := \t -> F (alpha t)
```

Functions between types automatically preserve identity arrows.

```rzk
-- [RS17, Proposition 6.1.a]
-- Preservation of identities follows from extension extensionality because these arrows are pointwise equal.
#def functors-pres-id
  (extext : ExtExt)
  (A B : U)
  (F : A -> B)
  (x : A)
  : (ap-hom A B F x x (id-arr A x)) = (id-arr B (F x))
  := eq-ext-htpy
      extext
      2
      Δ¹
      ∂Δ¹
      (\t -> B)
      (\t -> recOR(
        t === 0_2 |-> F x,
        t === 1_2 |-> F x))
      (ap-hom A B F x x (id-arr A x))
      (id-arr B (F x))
      (\t -> refl)

-- [RS17, Proposition 6.1.b]
-- Preservation of composition requires the Segal hypothesis.
#def functors-pres-comp
  (A B : U)
  (AisSegal : isSegal A)
  (BisSegal : isSegal B)
  (F : A -> B)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  :
    ( Segal-comp B BisSegal
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g))
    =
    ( ap-hom A B F x z (Segal-comp A AisSegal x y z f g))
  :=
    Segal-comp-uniqueness B BisSegal
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g)
      ( ap-hom A B F x z (Segal-comp A AisSegal x y z f g))
      ( ap-hom2 A B F x y z f g
        ( Segal-comp A AisSegal x y z f g)
        ( Segal-comp-witness A AisSegal x y z f g))
```

## Natural transformations

This corresponds to Section 6.2 in [RS17].

Given two simplicial maps `f g : (x : A) -> B x`, a **natural transformation**
from `f` to `g` is an arrow `η : hom ((x : A) -> B x) f g` between them.

```rzk
#def nat-trans
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  : U
  := hom ((x : A) -> (B x)) f g
```

Equivalently, natural transformations can be determined by their **components**,
i.e. as a family of arrows `(x : A) → hom (B x) (f x) (g x)`.

```rzk
#def nat-trans-components
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  : U
  := (x : A) -> hom (B x) (f x) (g x)
```

```rzk
#def ev-components-nat-trans
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  (η : nat-trans A B f g)
  : nat-trans-components A B f g
  := \ x t -> η t x

#def nat-trans-nat-trans-components
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  (η : nat-trans-components A B f g)
  : nat-trans A B f g
  := \ t x -> η x t
```

### Natural transformation extensionality

```rzk
-- [RS17, Proposition 6.3]
#def is-equiv-ev-components-nat-trans
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  : isEquiv
      ( nat-trans A B f g)
      ( nat-trans-components A B f g)
      ( ev-components-nat-trans A B f g)
  :=
    ( ( \ η t x -> η x t , \ _ -> refl) ,
      ( \ η t x -> η x t , \ _ -> refl))

#def equiv-components-nat-trans
  (A : U)
  (B : A -> U)
  (f g : (x : A) -> (B x))
  : Eq
      ( nat-trans A B f g)
      ( nat-trans-components A B f g)
  :=
    ( ev-components-nat-trans A B f g ,
      is-equiv-ev-components-nat-trans A B f g)
```

### Horizontal composition

Horizontal composition of natural transformations makes sense over any type. In
particular, contrary to what is written in [RS17] we do not need `C` to be
Segal.

```rzk
#def horizontal-comp-nat-trans
  (A B C : U)
  (f g : A -> B)
  (f' g' : B -> C)
  (η : nat-trans A (\ _ -> B) f g)
  (η' : nat-trans B (\ _ -> C) f' g')
  : nat-trans A (\ _ -> C) (\ x -> f' (f x)) (\ x -> g' (g x))
  := \ t x -> η' t (η t x)

#def horizontal-comp-nat-trans-components
  (A B C : U)
  (f g : A -> B)
  (f' g' : B -> C)
  (η : nat-trans-components A (\ _ -> B) f g)
  (η' : nat-trans-components B (\ _ -> C) f' g')
  : nat-trans-components A (\ _ -> C) (\ x -> f' (f x)) (\ x -> g' (g x))
  := \ x t -> η' (η x t) t
```

### Vertical composition

We can define vertical composition for natural transformations in families of
Segal types.

```rzk
#def vertical-comp-nat-trans-components
  (A : U)
  (B : A -> U)
  (BisSegal : (x : A) -> isSegal (B x))
  (f g h : (x : A) -> (B x))
  (η : nat-trans-components A B f g)
  (η' : nat-trans-components A B g h)
  : nat-trans-components A B f h
  := \ x -> Segal-comp (B x) (BisSegal x) (f x) (g x) (h x) (η x) (η' x)

#def vertical-comp-nat-trans
  (A : U)
  (B : A -> U)
  (BisSegal : (x : A) -> isSegal (B x))
  (f g h : (x : A) -> (B x))
  (η : nat-trans A B f g)
  (η' : nat-trans A B g h)
  : nat-trans A B f h
  :=
    \ t x ->
    vertical-comp-nat-trans-components A B BisSegal f g h
      ( \ x t -> η t x)
      ( \ x t -> η' t x)
      ( x)
      ( t)
```

The identity natural transformation is identity arrows on components

```rzk
-- [RS17, Proposition 6.5(ii)]
#def id-arr-components-id-nat-trans
  (A : U)
  (B : A -> U)
  (f : (x : A) -> (B x))
  (a : A)
  : (\ t -> id-arr ((x : A) -> B x) f t a) =_{Δ¹ -> B a} id-arr (B a) (f a)
  := refl
```
