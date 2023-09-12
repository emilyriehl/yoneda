# Cocartesian families

These formalizations capture cocartesian families as treated in BW23.

The goal, for now, is not to give a general structural account as in the paper
but rather to provide the definitions and results that are necessary to prove
the cocartesian Yoneda Lemma.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension
  extensionality.
- `5-segal-types.md` - We make heavy use of the notion of Segal types
- `10-rezk-types.md`- We use Rezk types.

## (Iso-)Inner families

This is a (tentative and redundant) definition of (iso-)inner families. In the
future, hopefully, these can be replaced by instances of orthogonal and LARI
families.

```rzk
#def is-inner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-segal B) (is-segal (Σ (b : B) , P b)))
    ( (b : B) → (is-segal (P b)))

#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-rezk B) (is-rezk (Σ (b : B) , P b)))
    ( (b : B) → (is-segal (P b)))
```

## Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    (b'' : B) → (v : hom B b' b'') → (w : hom B b b'') →
      (sigma : hom2 B b b' b'' u v w) → (e'' : P b'') →
      (h : dhom B b b'' w P e e'') →
      is-contr
        ( Σ ( g : dhom B b' b'' v P e' e'') ,
          ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

## Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ (e' : P b') ,
      Σ (f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

## Cocartesian family

A family over cocartesian if it is isoinner and any arrow in
the has a cocartesian lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → ( b' : B) → ( u : hom B b b') →
      ( e : P b) → ( Σ (e' : P b'),
        ( Σ (f : dhom B b b' u P e e'), is-cocartesian-arrow B b b' u P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-cocartesian-lifts B P)
```
