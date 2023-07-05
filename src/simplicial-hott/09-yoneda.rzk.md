# The Yoneda lemma

These formalisations correspond to Section 9 of the RS17 paper.

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

## Natural transformations involving a representable functor

Fix a Segal type A and a term a : A. The Yoneda lemma characterizes natural
transformations from the representable type family hom A a : A -> U to a
covariant type family C : A -> U.

Ordinary, such a natural transformation would involve a family of maps

ϕ : (z : A) -> hom A a z -> C z

together with a proof of naturality of these components, but by
naturality-covariant-fiberwise-transformation naturality is automatic.

```rzk
#def naturality-covariant-fiberwise-representable-transformation
  (A : U)
    (AisSegal : is-segal A)
  (a x y : A)
  (f : hom A a x)
  (g : hom A x y)
  (C : A -> U)
  (CisCov : isCovFam A C)
  (ϕ : (z : A) -> hom A a z -> C z)
  : (covTrans A x y g C CisCov (ϕ x f)) = (ϕ y (Segal-comp A AisSegal a x y f g))
  := naturality-covariant-fiberwise-transformation A x y g (\ z -> hom A a z) C
        (is-segal-representable-isCovFam A AisSegal a)
        CisCov
        ϕ f
```

## The Yoneda maps

For any Segal type A and term a : A, the Yoneda lemma provides an equivalence
between the type (z : A) -> hom A a z -> C z of natural transformations out of
the functor (hom A a) and valued in an arbitrary covariant family C and the type
(C a).

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the covariant transport operation.

```rzk
-- The map evid evaluates a natural transformation
-- out of a representable functor at the identity arrow.
#def evid
    (A : U)                   -- The ambient type.
    (a : A)                   -- The representing object.
  (C : A -> U)            -- A type family.
    : ((z : A) -> hom A a z -> C z) -> C a
    := \ ϕ -> ϕ a (id-arr A a)

-- The inverse map only exists for Segal types.
#def yon
    (A : U)                       -- The ambient type.
    (AisSegal : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
  (C : A -> U)            -- A type family.
  (CisCov : isCovFam A C)        -- A covariant family.
    : C a -> ((z : A) -> hom A a z -> C z)
    := \ u z f -> covTrans A a z f C CisCov u

```

## The Yoneda composites

It remains to show that the Yoneda maps are inverses.

```rzk
-- One retraction is straightforward:
#def evid-yon
    (A : U)                       -- The ambient type.
    (AisSegal : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
  (C : A -> U)            -- A type family.
  (CisCov : isCovFam A C)        -- A covariant family.
  (u : C a)
    : (evid A a C) ((yon A AisSegal a C CisCov) u) = u
    := covPresId A a C CisCov u
```

The other composite carries ϕ to an a priori distinct natural transformation. We
first show that these are pointwise equal at all x : A and f : hom A a x in two
steps.

```rzk
#section yon-evid

#variable A : U                     -- The ambient type.
#variable AisSegal : is-segal A    -- A proof that A is Segal.
#variable a : A                 -- The representing object.
#variable C : A -> U        -- A type family.
#variable CisCov : isCovFam A C    -- A covariant family.

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A a x.
#def yon-evid-twice-pointwise
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A a x)
  : ((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) x f = ϕ x f
    := concat (C x)
        (((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) x f)
        (ϕ x (Segal-comp A AisSegal a a x (id-arr A a) f))
        (ϕ x f)
        (naturality-covariant-fiberwise-representable-transformation
            A AisSegal a a x (id-arr A a) f C CisCov ϕ )
        (ap (hom A a x) (C x)
            (Segal-comp A AisSegal a a x (id-arr A a) f)
            f
            (ϕ x)
            (Segal-id-comp A AisSegal a x f))

-- By funext, these are equals as functions of f pointwise in x.
#def yon-evid-once-pointwise
    (funext : FunExt)
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
  : ((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) x = ϕ x
    := eq-htpy funext
        (hom A a x)
        (\ f -> C x)
        (\ f -> ((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) x f)
        (\ f -> (ϕ x f))
        (\ f -> yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def yon-evid
    (funext : FunExt)
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    : ((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) = ϕ
    := eq-htpy funext
        A
        (\ x -> (hom A a x -> C x))
        (\ x -> ((yon A AisSegal a C CisCov) ((evid A a C) ϕ )) x)
        (\ x -> (ϕ x))
        (\ x -> yon-evid-once-pointwise funext ϕ x)

#end yon-evid
```

## The Yoneda lemma

The Yoneda lemma says that evaluation at the identity defines an equivalence.

```rzk
#def Yoneda-lemma
    (funext : FunExt)
    (A : U)                         -- The ambient type.
    (AisSegal : is-segal A)          -- A proof that A is Segal.
    (a : A)                         -- The representing object.
  (C : A -> U)              -- A type family.
  (CisCov : isCovFam A C)          -- A covariant family.
    : is-equiv ((z : A) -> hom A a z -> C z) (C a) (evid A a C)
    := ((yon A AisSegal a C CisCov ,
            yon-evid A AisSegal a C CisCov funext) ,
        (yon A AisSegal a C CisCov ,
            evid-yon A AisSegal a C CisCov))
```

## Yoneda for contravariant families

Dually, the Yoneda lemma for contravariant type families characterizes natural
transformations from the contravariant family represented by a term a : A in a
Segal type to a contravariant type family C : A -> U.

By naturality-contravariant-fiberwise-transformation naturality is again
automatic.

```rzk
#def naturality-contravariant-fiberwise-representable-transformation
  (A : U)
  (AisSegal : is-segal A)
  (a x y : A)
  (f : hom A y a)
  (g : hom A x y)
  (C : A -> U)
  (CisContra : isContraFam A C)
  (ϕ : (z : A) -> hom A z a -> C z)
  : (contraTrans A x y g C CisContra (ϕ y f)) =
        (ϕ x (Segal-comp A AisSegal x y a g f))
  := naturality-contravariant-fiberwise-transformation A x y g
        (\ z -> hom A z a) C
        (is-segal-representable-isContraFam A AisSegal a)
        CisContra
        ϕ f
```

For any Segal type `A` and term `a : A`, the contravariant Yoneda lemma provides
an equivalence between the type `(z : A) -> hom A z a -> C z` of natural
transformations out of the functor `(\ x -> hom A x a)` and valued in an
arbitrary contravariant family `C` and the type `(C a)`.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the contravariant transport operation.

```rzk
-- The map evid evaluates a natural transformation
-- out of a representable functor at the identity arrow.
#def contra-evid
    (A : U)                   -- The ambient type.
    (a : A)                   -- The representing object.
    (C : A -> U)            -- A type family.
    : ((z : A) -> hom A z a -> C z) -> C a
    := \ ϕ -> ϕ a (id-arr A a)

-- The inverse map only exists for Segal types and contravariant families.
#def contra-yon
    (A : U)                             -- The ambient type.
    (AisSegal : is-segal A)               -- A proof that A is Segal.
    (a : A)                             -- The representing object.
    (C : A -> U)                        -- A type family.
    (CisContra : isContraFam A C)        -- A contrariant family.
    : C a -> ((z : A) -> hom A z a -> C z)
    := \ v z f -> contraTrans A z a f C CisContra v
```

It remains to show that the Yoneda maps are inverses.

```rzk
-- One retraction is straightforward:
#def contra-evid-yon
    (A : U)                       -- The ambient type.
    (AisSegal : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
    (C : A -> U)            -- A type family.
    (CisContra : isContraFam A C)        -- A contravariant family.
    (v : C a)
    : (contra-evid A a C) ((contra-yon A AisSegal a C CisContra) v) = v
    := contraPresId A a C CisContra v
```

The other composite carries ϕ to an a priori distinct natural transformation. We
first show that these are pointwise equal at all x : A and f : hom A x a in two
steps.

```rzk
#section contra-yon-evid

#variable A : U                          -- The ambient type.
#variable AisSegal : is-segal A          -- A proof that A is Segal.
#variable a : A                         -- The representing object.
#variable C : A -> U                    -- A type family.
#variable CisContra : isContraFam A C    -- A contravariant family.

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A x a.
#def contra-yon-evid-twice-pointwise
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A x a)
  : ((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) x f = ϕ x f
    := concat (C x)
        (((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) x f)
        (ϕ x (Segal-comp A AisSegal x a a f (id-arr A a)))
        (ϕ x f)
        (naturality-contravariant-fiberwise-representable-transformation
            A AisSegal a x a (id-arr A a) f C CisContra ϕ )
        (ap (hom A x a) (C x)
            (Segal-comp A AisSegal x a a f (id-arr A a))
            f
            (ϕ x)
            (Segal-comp-id A AisSegal x a f))

-- By funext, these are equals as functions of f pointwise in x.
#def contra-yon-evid-once-pointwise
    (funext : FunExt)
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    (x : A)
  : ((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) x = ϕ x
    := eq-htpy funext
        (hom A x a)
        (\ f -> C x)
        (\ f ->
          ((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) x f)
        (\ f -> (ϕ x f))
        (\ f -> contra-yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def contra-yon-evid
    (funext : FunExt)
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    : ((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) = ϕ
    := eq-htpy funext
        A
        (\ x -> (hom A x a -> C x))
        (\ x ->
          ((contra-yon A AisSegal a C CisContra) ((contra-evid A a C) ϕ )) x)
        (\ x -> (ϕ x))
        (\ x -> contra-yon-evid-once-pointwise funext ϕ x)

#end contra-yon-evid
```

The contravariant Yoneda lemma says that evaluation at the identity defines an
equivalence.

```rzk
#def contra-Yoneda-lemma
    (funext : FunExt)
    (A : U)                         -- The ambient type.
    (AisSegal : is-segal A)          -- A proof that A is Segal.
    (a : A)                         -- The representing object.
    (C : A -> U)                    -- A type family.
    (CisContra : isContraFam A C)    -- A contravariant family.
    : is-equiv ((z : A) -> hom A z a -> C z) (C a) (contra-evid A a C)
    := ((contra-yon A AisSegal a C CisContra ,
            contra-yon-evid A AisSegal a C CisContra funext) ,
        (contra-yon A AisSegal a C CisContra ,
            contra-evid-yon A AisSegal a C CisContra))
```
