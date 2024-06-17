# A self contained proof of the Yoneda lemma

This file, which is independent of the rest of the repository, contains a self-
contained proof of the Yoneda lemma in the special case where both functors
are contravariantly representable. This is intended for expository purposes.

Terms are annotated "*" when they are redefinitions (or specializations of
redefinitions) of results with the same name in the broader repository.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

Some of the definitions in this file rely on function extensionality:

```rzk
#assume funext : FunExt
```

## Natural transformations involving a representable functor

Fix a pre-∞-category $A$ and terms $a b : A$. The Yoneda lemma characterizes
natural transformations between the type families contravariantly represented
by these terms.

Ordinarily, such a natural transformation would involve a family of maps

`#!rzk ϕ : (z : A) → hom A z a → hom A z b`

together with a proof of naturality of these components, but by
naturality-covariant-fiberwise-transformation naturality is automatic.

```rzk
#def naturality-contravariant-fiberwise-representable-transformation*
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A y a)
  ( g : hom A x y)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( contravariant-transport A x y g
      ( \ z → hom A z b)
      ( is-contravariant-representable-is-pre-∞-category A is-pre-∞-category-A b)
      ( ϕ y f))
  = ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a g f))
  :=
    naturality-contravariant-fiberwise-transformation A x y g
      ( \ z → hom A z a) (\ z → hom A z b)
      ( is-contravariant-representable-is-pre-∞-category A is-pre-∞-category-A a)
      ( is-contravariant-representable-is-pre-∞-category A is-pre-∞-category-A b)
      ( ϕ)
      ( f)

-- Same as the above but without the contravariant transport.
-- This unfolds a composition triangle to a square with an identity component
#def id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( x y a : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : ( t : Δ¹) → hom A (f t) a
  := \ t s →
    recOR
      ( s ≤ t ↦
        ( witness-comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)
          ( t , s)
      , t ≤ s ↦
        ( comp-id-witness A x a
          ( comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)) (s , t))

-- We apply the transformation phi to the square just constructed.
#def transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( t : Δ¹) → hom A (f t) b
  := \ t → ϕ (f t) (\ s → id-codomain-square A is-pre-∞-category-A x y a f v t s)

-- This extracts the diagonal composite of the square.
#def diagonal-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom A x b
  :=
    \ t →
    transformation-id-codomain-square A is-pre-∞-category-A a b x y f v ϕ t t

-- One half of transformation-id-codomain-square.
#def witness-comp-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom2 A x y b f (ϕ y v)
    ( diagonal-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)
  :=
    \ (t , s) →
   transformation-id-codomain-square A is-pre-∞-category-A a b x y f v ϕ t s

-- The associated coherence.
#def coherence-witness-comp-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    uniqueness-comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v)
      ( diagonal-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)
      ( witness-comp-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)

-- The other half of transformation-id-codomain-square.
#def witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : hom2 A x b b
    ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( id-hom A b)
    ( diagonal-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)
  :=
    \ (t , s) →
   transformation-id-codomain-square A is-pre-∞-category-A a b x y f v ϕ s t

-- The associated coherence.
#def coherence-witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( comp-is-pre-∞-category A is-pre-∞-category-A x b b
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
      ( id-hom A b))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    uniqueness-comp-is-pre-∞-category A is-pre-∞-category-A x b b
    ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( id-hom A b)
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( witness-id-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)

#def simplified-coherence-witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    zag-zig-concat (hom A x b)
    ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( comp-is-pre-∞-category A is-pre-∞-category-A x b b
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
      ( id-hom A b))
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( comp-id-is-pre-∞-category A is-pre-∞-category-A x b
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)))
    ( coherence-witness-id-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)

#def naturality-contravariant-fiberwise-representable-transformation**
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
  = ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
  :=
    zig-zag-concat (hom A x b)
    ( comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( coherence-witness-comp-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( simplified-coherence-witness-id-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
```

For any pre-∞-category $A$ terms $a b : A$, the contravariant Yoneda lemma
provides an equivalence between the type `#!rzk (z : A) → hom A z a → hom A z b`
of natural transformations and the type `#!rzk hom A a b`.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the contravariant transport operation.

The following map, `#!rzk contra-evid` evaluates a natural transformation out of
a representable functor at the identity arrow.

```rzk
#def contra-evid*
  ( A : U)
  ( a b : A)
  : ( ( z : A) → hom A z a → hom A z b) → hom A a b
  := \ ϕ → ϕ a (id-hom A a)
```

The inverse map only exists for pre-∞-categories.

```rzk
#def contra-yon*
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := \ v z f → comp-is-pre-∞-category A is-pre-∞-category-A z a b f v
```

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def contra-evid-yon*
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b : A)
  ( v : hom A a b)
  : contra-evid* A a b (contra-yon* A is-pre-∞-category-A a b v) = v
  :=
    id-comp-is-pre-∞-category A is-pre-∞-category-A a b v
```

The other composite carries $ϕ$ to an a priori distinct natural transformation.
We first show that these are pointwise equal at all `#!rzk x : A` and
`#!rzk f : hom A x a` in two steps.

```rzk
#section contra-yon-evid

#variable A : U
#variable is-pre-∞-category-A : is-pre-∞-category A
#variables a b : A
```

The composite `#!rzk contra-yon-evid` of `#!rzk ϕ` equals `#!rzk ϕ` at all
`#!rzk x : A` and `#!rzk f : hom A x a`.

```rzk
#def contra-yon-evid-twice-pointwise*
  ( ϕ : (z : A) → hom A z a → hom A z b)
  ( x : A)
  ( f : hom A x a)
  : ( ( contra-yon* A is-pre-∞-category-A a b)
        ( ( contra-evid* A a b) ϕ)) x f = ϕ x f
  :=
    concat
      ( hom A x b)
      ( ( ( contra-yon* A is-pre-∞-category-A a b)
            ( ( contra-evid* A a b) ϕ)) x f)
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x a a f (id-hom A a)))
      ( ϕ x f)
      ( naturality-contravariant-fiberwise-representable-transformation**
          A is-pre-∞-category-A a b x a f (id-hom A a) ϕ)
      ( ap
        ( hom A x a)
        ( hom A x b)
        ( comp-is-pre-∞-category A is-pre-∞-category-A x a a f (id-hom A a))
        ( f)
        ( ϕ x)
        ( comp-id-is-pre-∞-category A is-pre-∞-category-A x a f))
```

By `#!rzk funext`, these are equals as functions of `#!rzk f` pointwise in
`#!rzk x`.

```rzk
#def contra-yon-evid-once-pointwise* uses (funext)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  ( x : A)
  : ( ( contra-yon* A is-pre-∞-category-A a b)
        ( ( contra-evid* A a b) ϕ)) x = ϕ x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → hom A x b)
      ( \ f →
        ( ( contra-yon* A is-pre-∞-category-A a b)
          ( ( contra-evid* A a b) ϕ)) x f)
      ( \ f → (ϕ x f))
      ( \ f → contra-yon-evid-twice-pointwise* ϕ x f)
```

By `#!rzk funext` again, these are equal as functions of `#!rzk x` and
`#!rzk f`.

```rzk
#def contra-yon-evid* uses (funext)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : contra-yon* A is-pre-∞-category-A a b (contra-evid* A a b ϕ) = ϕ
  :=
    eq-htpy funext
      ( A)
      ( \ x → (hom A x a → hom A x b))
      ( contra-yon* A is-pre-∞-category-A a b (contra-evid* A a b ϕ))
      ( ϕ)
      ( contra-yon-evid-once-pointwise* ϕ)

#end contra-yon-evid
```

The contravariant Yoneda lemma says that evaluation at the identity defines an
equivalence.

```rzk
#def contra-yoneda-lemma* uses (funext)
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b : A)
  : is-equiv ((z : A) → hom A z a → hom A z b) (hom A a b) (contra-evid* A a b)
  :=
    ( ( ( contra-yon* A is-pre-∞-category-A a b)
      , ( contra-yon-evid* A is-pre-∞-category-A a b))
    , ( ( contra-yon* A is-pre-∞-category-A a b)
      , ( contra-evid-yon* A is-pre-∞-category-A a b)))
```

## Contravariant Naturality

The equivalence of the Yoneda lemma is natural in both $a : A$ and $b : A$.

Naturality in $a$ follows from the fact that the maps `#!rzk evid` and
`#!rzk yon` are fiberwise equivalences between contravariant families over $A$,
though it requires some work, which has not yet been formalized, to prove that
the domain is contravariant.

Naturality in $b$ is not automatic but can be proven easily:

```rzk title="RS17, Lemma 9.2(i), dual"
#def is-natural-in-family-contra-evid*
  ( A : U)
  ( a b b' : A)
  ( ψ : (z : A) → hom A z b → hom A z b')
  ( φ : (z : A) → hom A z a → hom A z b)
  : ( comp ((z : A) → hom A z a → hom A z b) (hom A a b) (hom A a b')
      ( ψ a) (contra-evid* A a b)) φ
  = ( comp ((z : A) → hom A z a → hom A z b) ((z : A) → hom A z a → hom A z b')
      ( hom A a b')
      ( contra-evid* A a b') (\ α z g → ψ z (α z g))) φ
  := refl
```

```rzk title="RS17, Lemma 9.2(ii), dual"
#def is-natural-in-family-contra-yon-twice-pointwise*
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b b' : A)
  ( ψ : (z : A) → hom A z b → hom A z b')
  ( u : hom A a b)
  ( x : A)
  ( f : hom A x a)
  : ( comp (hom A a b) (hom A a b') ((z : A) → hom A z a → hom A z b')
      ( contra-yon* A is-pre-∞-category-A a b') (ψ a)) u x f
  = ( comp (hom A a b)
      ( ( z : A) → hom A z a → hom A z b)
      ( ( z : A) → hom A z a → hom A z b')
      ( \ α z g → ψ z (α z g))
      ( contra-yon* A is-pre-∞-category-A a b)) u x f
  :=
    naturality-contravariant-fiberwise-representable-transformation**
      A is-pre-∞-category-A b b' x a f u ψ


#def is-natural-in-family-contra-yon-once-pointwise* uses (funext)
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b b' : A)
  ( ψ : (z : A) → hom A z b → hom A z b')
  ( u : hom A a b)
  ( x : A)
  : ( comp (hom A a b) (hom A a b') ((z : A) → hom A z a → hom A z b')
      ( contra-yon* A is-pre-∞-category-A a b') (ψ a)) u x
  = ( comp (hom A a b)
      ( ( z : A) → hom A z a → hom A z b)
      ( ( z : A) → hom A z a → hom A z b')
      ( \ α z g → ψ z (α z g))
      ( contra-yon* A is-pre-∞-category-A a b)) u x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → hom A x b')
      ( \ f →
        ( comp (hom A a b) (hom A a b') ((z : A) → hom A z a → hom A z b')
          ( contra-yon* A is-pre-∞-category-A a b') (ψ a)) u x f)
      ( \ f →
        ( comp (hom A a b)
          ( ( z : A) → hom A z a → hom A z b)
          ( ( z : A) → hom A z a → hom A z b')
        ( \ α z g → ψ z (α z g))
        ( contra-yon* A is-pre-∞-category-A a b)) u x f)
      ( \ f →
        is-natural-in-family-contra-yon-twice-pointwise*
          A is-pre-∞-category-A a b b' ψ u x f)

#def is-natural-in-family-contra-yon* uses (funext)
  ( A : U)
  ( is-pre-∞-category-A : is-pre-∞-category A)
  ( a b b' : A)
  ( ψ : (z : A) → hom A z b → hom A z b')
  ( u : hom A a b)
  : ( comp (hom A a b) (hom A a b') ((z : A) → hom A z a → hom A z b')
      ( contra-yon* A is-pre-∞-category-A a b') (ψ a)) u
  = ( comp (hom A a b)
      ( ( z : A) → hom A z a → hom A z b)
      ( ( z : A) → hom A z a → hom A z b')
      ( \ α z g → ψ z (α z g))
      ( contra-yon* A is-pre-∞-category-A a b)) u
  :=
    eq-htpy funext
      ( A)
      ( \ x → hom A x a → hom A x b')
      ( \ x →
        ( comp (hom A a b) (hom A a b') ((z : A) → hom A z a → hom A z b')
          ( contra-yon* A is-pre-∞-category-A a b') (ψ a)) u x)
      ( \ x →
        ( comp (hom A a b)
          ( ( z : A) → hom A z a → hom A z b)
          ( ( z : A) → hom A z a → hom A z b')
        ( \ α z g → ψ z (α z g))
        ( contra-yon* A is-pre-∞-category-A a b)) u x)
      ( \ x →
        is-natural-in-family-contra-yon-once-pointwise*
          A is-pre-∞-category-A a b b' ψ u x)
```
