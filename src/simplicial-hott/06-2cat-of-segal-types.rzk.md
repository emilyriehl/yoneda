# The 2-category of Segal types

These formalisations correspond to Section 6 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use extension extensionality.
- `5-segal-types.md` - We use the notion of hom types.

Some of the definitions in this file rely on extension extensionality:

```rzk
#assume extext : ExtExt
```

## Functors

Functions between types induce an action on hom types, preserving sources and
targets. The action is called `#!rzk ap-hom` to avoid conflicting with
`#!rzk ap`.

```rzk title="RS17, Section 6.1"
#def ap-hom
  ( A B : U)
  ( F : A → B)
  ( x y : A)
  ( f : hom A x y)
  : hom B (F x) (F y)
  := \ t → F (f t)

#def ap-hom2
  ( A B : U)
  ( F : A → B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  (α : hom2 A x y z f g h)
  : hom2 B (F x) (F y) (F z)
    ( ap-hom A B F x y f) (ap-hom A B F y z g) (ap-hom A B F x z h)
  := \ t → F (α t)
```

Functions between types automatically preserve identity arrows. Preservation of
identities follows from extension extensionality because these arrows are
pointwise equal.

```rzk title="RS17, Proposition 6.1.a"
#def functors-pres-id uses (extext)
  ( A B : U)
  ( F : A → B)
  ( x : A)
  : ( ap-hom A B F x x (id-hom A x)) = (id-hom B (F x))
  := eq-ext-htpy
      extext
      2
      Δ¹
      ∂Δ¹
      ( \ t → B)
      ( \ t → recOR
      ( t ≡ 0₂ ↦ F x ,
        t ≡ 1₂ ↦ F x))
      ( ap-hom A B F x x (id-hom A x))
      ( id-hom B (F x))
      ( \ t → refl)
```

Preservation of composition requires the Segal hypothesis.

```rzk title="RS17, Proposition 6.1.b"
#def functors-pres-comp
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( F : A → B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  :
    ( comp-Segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g))
    =
    ( ap-hom A B F x z (comp-Segal A is-segal-A x y z f g))
  :=
    uniqueness-comp-Segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g)
      ( ap-hom A B F x z (comp-Segal A is-segal-A x y z f g))
      ( ap-hom2 A B F x y z f g
        ( comp-Segal A is-segal-A x y z f g)
        ( witness-comp-Segal A is-segal-A x y z f g))
```

## Natural transformations

This corresponds to Section 6.2 in [RS17].

Given two simplicial maps `#!rzk f g : (x : A) → B x` , a **natural
transformation** from `#!rzk f` to `#!rzk g` is an arrow
`#!rzk η : hom ((x : A) → B x) f g` between them.

```rzk
#def nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : U
  := hom ((x : A) → (B x)) f g
```

Equivalently , natural transformations can be determined by their **components**
, i.e. as a family of arrows `#!rzk (x : A) → hom (B x) (f x) (g x)`.

```rzk
#def nat-trans-components
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : U
  := ( x : A) → hom (B x) (f x) (g x)
```

```rzk
#def ev-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  ( η : nat-trans A B f g)
  : nat-trans-components A B f g
  := \ x t → η t x

#def nat-trans-nat-trans-components
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  ( η : nat-trans-components A B f g)
  : nat-trans A B f g
  := \ t x → η x t
```

### Natural transformation extensionality

```rzk title="RS17, Proposition 6.3"
#def is-equiv-ev-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : is-equiv
      ( nat-trans A B f g)
      ( nat-trans-components A B f g)
      ( ev-components-nat-trans A B f g)
  :=
    ( ( \ η t x → η x t , \ _ → refl) ,
      ( \ η t x → η x t , \ _ → refl))

#def equiv-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : Equiv (nat-trans A B f g) (nat-trans-components A B f g)
  :=
    ( ev-components-nat-trans A B f g ,
      is-equiv-ev-components-nat-trans A B f g)
```

### Horizontal composition

Horizontal composition of natural transformations makes sense over any type. In
particular , contrary to what is written in [RS17] we do not need `#!rzk C` to
be Segal.

```rzk
#def horizontal-comp-nat-trans
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans A (\ _ → B) f g)
  ( η' : nat-trans B (\ _ → C) f' g')
  : nat-trans A (\ _ → C) (\ x → f' (f x)) (\ x → g' (g x))
  := \ t x → η' t (η t x)

#def horizontal-comp-nat-trans-components
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans-components A (\ _ → B) f g)
  ( η' : nat-trans-components B (\ _ → C) f' g')
  : nat-trans-components A (\ _ → C) (\ x → f' (f x)) (\ x → g' (g x))
  := \ x t → η' (η x t) t
```

### Vertical composition

We can define vertical composition for natural transformations in families of
Segal types.

```rzk
#def vertical-comp-nat-trans-components
  ( A : U)
  ( B : A → U)
  ( is-segal-B : (x : A) → is-segal (B x))
  ( f g h : (x : A) → (B x))
  ( η : nat-trans-components A B f g)
  ( η' : nat-trans-components A B g h)
  : nat-trans-components A B f h
  := \ x → comp-Segal (B x) (is-segal-B x) (f x) (g x) (h x) (η x) (η' x)

#def vertical-comp-nat-trans
  ( A : U)
  ( B : A → U)
  ( is-segal-B : (x : A) → is-segal (B x))
  ( f g h : (x : A) → (B x))
  ( η : nat-trans A B f g)
  ( η' : nat-trans A B g h)
  : nat-trans A B f h
  :=
    \ t x →
    vertical-comp-nat-trans-components A B is-segal-B f g h
      ( \ x' t' → η t' x')
      ( \ x' t' → η' t' x')
      ( x)
      ( t)
```

The identity natural transformation is identity arrows on components

```rzk title="RS17, Proposition 6.5(ii)"
#def id-arr-components-id-nat-trans
  ( A : U)
  ( B : A → U)
  ( f : (x : A) → (B x))
  ( a : A)
  : ( \ t → id-hom ((x : A) → B x) f t a) =_{Δ¹ → B a} id-hom (B a) (f a)
  := refl
```
