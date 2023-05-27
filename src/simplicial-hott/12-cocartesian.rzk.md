# Cocartesian families

These formalizations capture cocartesian families as treated in BW23.

The goal, for now, is not to give a general structural account as in the paper but ratger to provide the definitions and results that are necessary to prove the cocartesian Yoneda Lemma.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for instance the axiom of function extensionality.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension extensionality.
- `5-segal-types.md` - We make heavy use of the notion of Segal types
- `8-covariant.md` - We use covariant type families.

## Type of fiberwise Segal families over a base type

```rzk
#def innerFam
    (B : U)
    : U
    :=
    (∑(P : B -> U), (b : B) -> (isSegal (P b)))
```

## Definition of cocartesian lifts

-- [BW23, Definition 5.1.1]
-- the proposition that a dependent arrow in a family is cocartesian
-- (alternative version using unpacked extension types because this is preferred for usage)

```rzk
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
    -> isContr (∑(g : dhom B b' b'' v P e' e''), (dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

# Definition of cocartesian lifts

-- [BW23, Definition 5.1.2]
-- the type of cocartesian lifts of a fixed arrow in the base with a given starting point in the fiber

```rzk
#def CocartLift
    (B : U)
    (b b' : B)
    (u : hom B b b')
    (P : B -> U)
    (e : P b)
    : U
    := ∑(e' : P b'), ∑(f : dhom B b b' u P e e'), isCocartArr B b b' u P e e' f

#def isInitial
    (A : U)
    (a : A)
    : U
    := (x : A) -> isContr(hom A a x)

-- In a Segal type, initial objects are isomorphic.
#def initial-iso
    (A : U)
    (AisSegal : isSegal A)
    (a b : A)
    (ainitial : isInitial A a)
    (binitial : isInitial A b)
    : Iso A AisSegal a b
    := (first (ainitial b),
        ((first (binitial a),
            contractible-connecting-htpy (hom A a a) (ainitial a) (Segal-comp A AisSegal a b a (first (ainitial b)) (first (binitial a))) (id-arr A a))
        ,
        (first (binitial a),
            contractible-connecting-htpy (hom A b b) (binitial b) (Segal-comp A AisSegal b a b (first (binitial a)) (first (ainitial b))) (id-arr A b))
        ))
```
