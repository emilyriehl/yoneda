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
- `8-covariant.md` - We use covariant type families.
- `10-rezk-types.md`- We use Rezk types.

## (Iso-)Inner families

This is a (tentative and redundant) definition of (iso-)inner families. In the
future, hopefully, these can be replaced by instances of orthogonal and LARI
families.

```rzk
#def totalType
  (B : U)
  (P : B -> U)
  : U
  := Σ (b : B) , P b

#def isInnerFam
  (B : U)
  (P : B -> U)
  : U
  := product (product (is-segal B) (is-segal (totalType B P))) ((b : B) -> (is-segal (P b)))

#def is-isoInnerFam
  (B : U)
  (P : B -> U)
  : U
  := product (product (is-rezk B) (is-rezk (totalType B P))) ((b : B) -> (is-segal (P b)))
```

## Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def isCocartArr
  (B : U)
  (b b' : B)
  (u : hom B b b')
  (P : B -> U)
  (e : P b)
  (e' : P b')
  (f : dhom B b b' u P e e')
  : U
  := (b'' : B)
  -> (v : hom B b' b'')
  -> (w : hom B b b'')
  -> (sigma : hom2 B b b' b'' u v w)
  -> (e'' : P b'')
  -> (h : dhom B b b'' w P e e'')
  -> is-contr
      ( Σ ( g : dhom B b' b'' v P e' e'') ,
          ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

## Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def CocartLift
    (B : U)
    (b b' : B)
    (u : hom B b b')
    (P : B -> U)
    (e : P b)
    : U
    := Σ (e' : P b') , Σ (f : dhom B b b' u P e e') , isCocartArr B b b' u P e e' f
```

#def cocart-is-prop (B : U) (Bis-rezk : is-rezk B) (b b' : B) (u : hom B b b')
(P : B -> U) (TPis-rezk : is-rezk (totalType B P)) (PisfibRezk : (b : B) ->
is-rezk (P b)) (e : P b) (e' : P b') (f : dhom B b b' u P e e') (fiscocart :
isCocartArr B b b' u P e e' f) : is-contr (CocartLift B b b' u P e) := ( (e' , f
, fiscocart) , \ d -> \ g ->

```

```
