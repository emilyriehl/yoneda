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
    (is-segal-A : is-segal A)
  (a x y : A)
  (f : hom A a x)
  (g : hom A x y)
  (C : A -> U)
  (CisCov : is-covariant A C)
  (ϕ : (z : A) -> hom A a z -> C z)
  : (covariant-transport A x y g C CisCov (ϕ x f)) = (ϕ y (Segal-comp A is-segal-A a x y f g))
  := naturality-covariant-fiberwise-transformation A x y g (\ z -> hom A a z) C
        (is-segal-representable-is-covariant A is-segal-A a)
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
    (is-segal-A : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
  (C : A -> U)            -- A type family.
  (CisCov : is-covariant A C)        -- A covariant family.
    : C a -> ((z : A) -> hom A a z -> C z)
    := \ u z f -> covariant-transport A a z f C CisCov u
```

## The Yoneda composites

It remains to show that the Yoneda maps are inverses.

```rzk
-- One retraction is straightforward:
#def evid-yon
    (A : U)                       -- The ambient type.
    (is-segal-A : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
  (C : A -> U)            -- A type family.
  (CisCov : is-covariant A C)        -- A covariant family.
  (u : C a)
    : (evid A a C) ((yon A is-segal-A a C CisCov) u) = u
    := id-arr-covariant-transport A a C CisCov u
```

The other composite carries ϕ to an a priori distinct natural transformation. We
first show that these are pointwise equal at all x : A and f : hom A a x in two
steps.

```rzk
#section yon-evid

#variable A : U                     -- The ambient type.
#variable is-segal-A : is-segal A    -- A proof that A is Segal.
#variable a : A                 -- The representing object.
#variable C : A -> U        -- A type family.
#variable CisCov : is-covariant A C    -- A covariant family.

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A a x.
#def yon-evid-twice-pointwise
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A a x)
  : ((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) x f = ϕ x f
    := concat (C x)
        (((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) x f)
        (ϕ x (Segal-comp A is-segal-A a a x (id-arr A a) f))
        (ϕ x f)
        (naturality-covariant-fiberwise-representable-transformation
            A is-segal-A a a x (id-arr A a) f C CisCov ϕ )
        (ap (hom A a x) (C x)
            (Segal-comp A is-segal-A a a x (id-arr A a) f)
            f
            (ϕ x)
            (Segal-id-comp A is-segal-A a x f))

-- By funext, these are equals as functions of f pointwise in x.
#def yon-evid-once-pointwise
    (funext : FunExt)
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    (x : A)
  : ((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) x = ϕ x
    := eq-htpy funext
        (hom A a x)
        (\ f -> C x)
        (\ f -> ((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) x f)
        (\ f -> (ϕ x f))
        (\ f -> yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def yon-evid
    (funext : FunExt)
    (ϕ : (z : A) -> hom A a z -> C z)     -- A natural transformation.
    : ((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) = ϕ
    := eq-htpy funext
        A
        (\ x -> (hom A a x -> C x))
        (\ x -> ((yon A is-segal-A a C CisCov) ((evid A a C) ϕ )) x)
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
    (is-segal-A : is-segal A)          -- A proof that A is Segal.
    (a : A)                         -- The representing object.
  (C : A -> U)              -- A type family.
  (CisCov : is-covariant A C)          -- A covariant family.
    : is-equiv ((z : A) -> hom A a z -> C z) (C a) (evid A a C)
    := ((yon A is-segal-A a C CisCov ,
            yon-evid A is-segal-A a C CisCov funext) ,
        (yon A is-segal-A a C CisCov ,
            evid-yon A is-segal-A a C CisCov))
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
  (is-segal-A : is-segal A)
  (a x y : A)
  (f : hom A y a)
  (g : hom A x y)
  (C : A -> U)
  (CisContra : isContraFam A C)
  (ϕ : (z : A) -> hom A z a -> C z)
  : (contraTrans A x y g C CisContra (ϕ y f)) =
        (ϕ x (Segal-comp A is-segal-A x y a g f))
  := naturality-contravariant-fiberwise-transformation A x y g
        (\ z -> hom A z a) C
        (is-segal-representable-isContraFam A is-segal-A a)
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
    (is-segal-A : is-segal A)               -- A proof that A is Segal.
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
    (is-segal-A : is-segal A)        -- A proof that A is Segal.
    (a : A)                       -- The representing object.
    (C : A -> U)            -- A type family.
    (CisContra : isContraFam A C)        -- A contravariant family.
    (v : C a)
    : (contra-evid A a C) ((contra-yon A is-segal-A a C CisContra) v) = v
    := contraPresId A a C CisContra v
```

The other composite carries ϕ to an a priori distinct natural transformation. We
first show that these are pointwise equal at all x : A and f : hom A x a in two
steps.

```rzk
#section contra-yon-evid

#variable A : U                          -- The ambient type.
#variable is-segal-A : is-segal A          -- A proof that A is Segal.
#variable a : A                         -- The representing object.
#variable C : A -> U                    -- A type family.
#variable CisContra : isContraFam A C    -- A contravariant family.

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A x a.
#def contra-yon-evid-twice-pointwise
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    (x : A)
    (f : hom A x a)
  : ((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) x f = ϕ x f
    := concat (C x)
        (((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) x f)
        (ϕ x (Segal-comp A is-segal-A x a a f (id-arr A a)))
        (ϕ x f)
        (naturality-contravariant-fiberwise-representable-transformation
            A is-segal-A a x a (id-arr A a) f C CisContra ϕ )
        (ap (hom A x a) (C x)
            (Segal-comp A is-segal-A x a a f (id-arr A a))
            f
            (ϕ x)
            (Segal-comp-id A is-segal-A x a f))

-- By funext, these are equals as functions of f pointwise in x.
#def contra-yon-evid-once-pointwise
    (funext : FunExt)
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    (x : A)
  : ((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) x = ϕ x
    := eq-htpy funext
        (hom A x a)
        (\ f -> C x)
        (\ f ->
          ((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) x f)
        (\ f -> (ϕ x f))
        (\ f -> contra-yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def contra-yon-evid
    (funext : FunExt)
    (ϕ : (z : A) -> hom A z a -> C z)     -- A natural transformation.
    : ((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) = ϕ
    := eq-htpy funext
        A
        (\ x -> (hom A x a -> C x))
        (\ x ->
          ((contra-yon A is-segal-A a C CisContra) ((contra-evid A a C) ϕ )) x)
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
    (is-segal-A : is-segal A)          -- A proof that A is Segal.
    (a : A)                         -- The representing object.
    (C : A -> U)                    -- A type family.
    (CisContra : isContraFam A C)    -- A contravariant family.
    : is-equiv ((z : A) -> hom A z a -> C z) (C a) (contra-evid A a C)
    := ((contra-yon A is-segal-A a C CisContra ,
            contra-yon-evid A is-segal-A a C CisContra funext) ,
        (contra-yon A is-segal-A a C CisContra ,
            contra-evid-yon A is-segal-A a C CisContra))
```

From a type-theoretic perspective, the Yoneda lemma is a “directed” version of
the “transport” operation for identity types. This suggests a “dependently
typed” generalization of the Yoneda lemma, analogous to the full induction
principle for identity types. We prove this as a special case of a result about
covariant families over a type with an initial object.

## Initial objects

A term $a$ in a type $A$ is initial if all of its mapping-out hom types are
contractible.

```rzk title="RS17, Definition 9.6"
#def is-initial
  (A : U)
  (a : A)
  : U
  := (x : A) -> is-contr (hom A a x)
```

```rzk
#section initial-evaluation-equivalence

#variable A : U
#variable a : A
#variable is-initial-a : is-initial A a
#variable C : A -> U
#variable is-covariant-C : is-covariant A C

#def arrows-from-initial
  (x : A)
  : hom A a x
  := contraction-center (hom A a x) (is-initial-a x)

#def identity-component-arrows-from-initial
  : arrows-from-initial a = id-arr A a
  := contracting-htpy (hom A a a) (is-initial-a a) (id-arr A a)

#def ind-initial uses (is-initial-a)
  (u : C a)
  : (x : A) -> C x
  :=
    \ x -> covariant-transport A a x (arrows-from-initial x) C is-covariant-C u

#def has-section-ev-pt uses (is-initial-a)
  : has-section ((x : A) -> C x) (C a) (ev-pt A a C)
  :=
    ( ( ind-initial),
      ( \ u ->
        concat
          ( C a)
          ( covariant-transport A a a
            ( arrows-from-initial a) C is-covariant-C u)
          ( covariant-transport A a a
            ( id-arr A a) C is-covariant-C u)
          ( u)
          ( ap
            ( hom A a a)
            ( C a)
            ( arrows-from-initial a)
            ( id-arr A a)
            ( \ f ->
              covariant-transport A a a f C is-covariant-C u)
            ( identity-component-arrows-from-initial))
          ( id-arr-covariant-transport A a C is-covariant-C u)))

#def ind-initial-ev-pt-pointwise uses (is-initial-a)
  (s : (x : A) -> C x)
  (b : A)
  : ind-initial (ev-pt A a C s) b = s b
  :=
    covariant-uniqueness
      ( A)
      ( a)
      ( b)
      ( arrows-from-initial b)
      ( C)
      ( is-covariant-C)
      ( ev-pt A a C s)
      ( ( s b, \ t -> s (arrows-from-initial b t)))

#end initial-evaluation-equivalence
```

We now prove that induction from an initial element in the base of a covariant
family defines an inverse equivalence to evaluation at the element.

```rzk title="RS17, Theorem 9.7"
#def is-equiv-covariant-ev-initial
  (funext : FunExt)
  (A : U)
  (a : A)
  (is-initial-a : is-initial A a)
  (C : A -> U)
  (is-covariant-C : is-covariant A C)
  : is-equiv ((x : A) -> C x) (C a) (ev-pt A a C)
  :=
    ( ( ( ind-initial A a is-initial-a C is-covariant-C ),
        ( \ s -> eq-htpy
                  funext
                    ( A)
                    ( C)
                    ( ind-initial
                        A a is-initial-a C is-covariant-C (ev-pt A a C s))
                    ( s)
                    ( ind-initial-ev-pt-pointwise
                        A a is-initial-a C is-covariant-C s))),
      ( has-section-ev-pt A a is-initial-a C is-covariant-C))
```

## Initial objects in slice categories

We now show that the type of arrows in a Segal type $A$ with domain $a$ has an
initial object given by the identity arrow at $a$. This makes use of the
following equivalence.

```rzk
#def equiv-hom-in-slice
  (A : U)
  (a x : A)
  (f : hom A a x)
  : Equiv
    ( hom (Σ (z : A), hom A a z) (a, id-arr A a) (x, f))
    ( {t : 2 | Δ¹ t} -> hom A a (f t) [t === 0_2 |-> id-arr A a])
  :=
    ( \ h t s -> (second (h s)) t,
      (( \ k s -> ( k 1_2 s, \ t -> k t s),
        \ h -> refl),
      ( \ k s -> ( k 1_2 s, \ t -> k t s),
        \ k -> refl)))
```

Since $hom A a$ is covariant when $A$ is Segal, this latter type is
contractible.

```rzk
#def is-contr-is-segal-hom-in-slice
  (A : U)
  (is-segal-A : is-segal A)
  (a x : A)
  (f : hom A a x)
  : is-contr ( {t : 2 | Δ¹ t} -> hom A a (f t) [t === 0_2 |-> id-arr A a])
  :=
    ( second (has-unique-lifts-with-fixed-domain-iff-is-covariant
                A (\ z -> hom A a z)))
      ( is-segal-representable-is-covariant A is-segal-A a)
      a x f (id-arr A a)
```

This proves the initiality of identity arrows in the slice of a Segal type.

```rzk title="RS17, Lemma 9.8"
#def is-initial-id-arr-is-segal
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  : is-initial (Σ (z : A), hom A a z) (a, id-arr A a)
  :=
    \ (x, f) ->
    is-contr-is-equiv-to-contr
      ( hom (Σ (z : A), hom A a z) (a, id-arr A a) (x, f))
      ( {t : 2 | Δ¹ t} -> hom A a (f t) [t === 0_2 |-> id-arr A a])
      ( equiv-hom-in-slice A a x f)
      ( is-contr-is-segal-hom-in-slice A is-segal-A a x f)
```

## Dependent Yoneda lemma

The dependent Yoneda lemma now follows by specializing these results.

```rzk
#def dependent-ev-id
  (A : U)
  (a : A)
  (C : (Σ (z : A), hom A a z) -> U)
  : ((p : Σ (z : A), hom A a z) -> C p) -> C (a, id-arr A a)
  := \ s -> s (a, id-arr A a)

#def dependent-yoneda-lemma'
  (funext : FunExt)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (Σ (z : A), hom A a z) -> U)
  (is-covariant-C : is-covariant (Σ (z : A), hom A a z) C)
  : is-equiv
      ( (p : Σ (z : A), hom A a z) -> C p)
      ( C (a, id-arr A a))
      ( dependent-ev-id A a C)
  :=
    is-equiv-covariant-ev-initial
      ( funext)
      ( Σ (z : A), hom A a z)
      ( (a, id-arr A a))
      ( is-initial-id-arr-is-segal A is-segal-A a)
      ( C)
      ( is-covariant-C)
```

The actual dependent Yoneda is equivalent to the result just proven, just with
an equivalent type in the domain of the evaluation map.

```rzk title="RS17, Theorem 9.5"
#def dependent-yoneda-lemma
  (funext : FunExt)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (Σ (z : A), hom A a z) -> U)
  (is-covariant-C : is-covariant (Σ (z : A), hom A a z) C)
  : is-equiv
      ( (x : A) -> (f : hom A a x) -> C (x, f))
      ( C (a, id-arr A a))
      ( \ s -> s a (id-arr A a))
  :=
    LeftCancel-is-equiv
      ( (p : Σ (z : A), hom A a z) -> C p)
      ( (x : A) -> (f : hom A a x) -> C (x, f))
      ( C (a, id-arr A a))
      ( first (equiv-dependent-curry A (\ z -> hom A a z)(\ x f -> C (x, f))))
      ( second (equiv-dependent-curry A (\ z -> hom A a z)(\ x f -> C (x, f))))
      ( \ s -> s a (id-arr A a))
      ( dependent-yoneda-lemma' funext A is-segal-A a C is-covariant-C)
```

## Final objects

```rzk
#def is-final
  (A : U)
  (a : A)
  : U
  := (x : A) -> is-contr (hom A x a)
```
