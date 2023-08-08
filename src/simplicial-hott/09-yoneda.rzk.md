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

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Natural transformations involving a representable functor

Fix a Segal type $A$ and a term $a : A$. The Yoneda lemma characterizes natural
transformations from the representable type family `hom A a : A → U` to a
covariant type family `C : A → U`.

Ordinarily, such a natural transformation would involve a family of maps

`ϕ : (z : A) → hom A a z → C z`

together with a proof of naturality of these components, but by
naturality-covariant-fiberwise-transformation naturality is automatic.

```rzk
#def naturality-covariant-fiberwise-representable-transformation
  (A : U)
  (is-segal-A : is-segal A)
  (a x y : A)
  (f : hom A a x)
  (g : hom A x y)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  (ϕ : (z : A) → hom A a z → C z)
  : (covariant-transport A x y g C is-covariant-C (ϕ x f)) =
    (ϕ y (Segal-comp A is-segal-A a x y f g))
  :=
    naturality-covariant-fiberwise-transformation A x y g
      (\ z → hom A a z)
      ( C)
      ( is-segal-representable-is-covariant A is-segal-A a)
      ( is-covariant-C)
      ( ϕ)
      ( f)
```

## The Yoneda maps

For any Segal type $A$ and term $a : A$, the Yoneda lemma provides an
equivalence between the type `(z : A) → hom A a z → C z` of natural
transformations out of the functor `hom A a` and valued in an arbitrary
covariant family $C$ and the type $C a$.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the covariant transport operation.

```rzk
-- The map evid evaluates a natural transformation
-- out of a representable functor at the identity arrow.
#def evid
  (A : U)
  (a : A)
  (C : A → U)
  : ((z : A) → hom A a z → C z) → C a
  := \ ϕ → ϕ a (id-arr A a)

-- The inverse map only exists for Segal types.
#def yon
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  : C a → ((z : A) → hom A a z → C z)
  := \ u x f → covariant-transport A a x f C is-covariant-C u
```

## The Yoneda composites

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def evid-yon
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  (u : C a)
  : (evid A a C) ((yon A is-segal-A a C is-covariant-C) u) = u
  := id-arr-covariant-transport A a C is-covariant-C u
```

The other composite carries $ϕ$ to an a priori distinct natural transformation.
We first show that these are pointwise equal at all `x : A` and `f : hom A a x`
in two steps.

```rzk
#section yon-evid

#variable A : U
#variable is-segal-A : is-segal A
#variable a : A
#variable C : A → U
#variable is-covariant-C : is-covariant A C

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A a x.
#def yon-evid-twice-pointwise
  (ϕ : (z : A) → hom A a z → C z)
  (x : A)
  (f : hom A a x)
  : ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) x f = ϕ x f
  :=
    concat
      ( C x)
      ( ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) x f)
      ( ϕ x (Segal-comp A is-segal-A a a x (id-arr A a) f))
      ( ϕ x f)
      ( naturality-covariant-fiberwise-representable-transformation
        A is-segal-A a a x (id-arr A a) f C is-covariant-C ϕ )
      ( ap
        ( hom A a x)
        ( C x)
        ( Segal-comp A is-segal-A a a x (id-arr A a) f)
        ( f)
        ( ϕ x)
        ( Segal-id-comp A is-segal-A a x f))

-- By funext, these are equals as functions of f pointwise in x.
#def yon-evid-once-pointwise uses (funext)
  (ϕ : (z : A) → hom A a z → C z)
  (x : A)
  : ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) x = ϕ x
  :=
    eq-htpy funext
      ( hom A a x)
      ( \ f → C x)
      ( \ f → ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) x f)
      ( \ f → (ϕ x f))
      ( \ f → yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def yon-evid uses (funext)
  (ϕ : (z : A) → hom A a z → C z)
  : ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) = ϕ
  := eq-htpy funext
      ( A)
      ( \ x → (hom A a x → C x))
      ( \ x → ((yon A is-segal-A a C is-covariant-C) ((evid A a C) ϕ )) x)
      ( \ x → (ϕ x))
      ( \ x → yon-evid-once-pointwise ϕ x)

#end yon-evid
```

## The Yoneda lemma

The Yoneda lemma says that evaluation at the identity defines an equivalence.
This is proven combining the previous steps.

```rzk title="RS17, Theorem 9.1"
#def Yoneda-lemma uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  : is-equiv ((z : A) → hom A a z → C z) (C a) (evid A a C)
  :=
    ( ( ( yon A is-segal-A a C is-covariant-C),
        ( yon-evid A is-segal-A a C is-covariant-C)),
      ( ( yon A is-segal-A a C is-covariant-C),
        ( evid-yon A is-segal-A a C is-covariant-C)))
```

## Naturality

The equivalence of the Yoneda lemma is natural in both $a : A$ and $C : A → U$.

Naturality in $a$ follows from the fact that the maps `evid` and `yon` are
fiberwise equivalences between covariant families over $A$, though it requires
some work, to prove that the domain is covariant.

```rzk
#def is-covariant-yoneda-domain uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  : is-covariant A (\ a → (z : A) → hom A a z → C z)
  :=
    equiv-is-covariant
    ( extext)
    ( A)
    ( \ a -> (z : A) → hom A a z → C z)
    ( C)
    ( \ a -> (evid A a C, Yoneda-lemma A is-segal-A a C is-covariant-C))
    ( is-covariant-C)

#def is-natural-in-object-evid uses (funext extext)
  (A : U)
  (is-segal-A : is-segal A)
  (a b : A)
  (f : hom A a b)
  (C : A -> U)
  (is-covariant-C : is-covariant A C)
  (ϕ : (z : A) → hom A a z → C z)
  : (covariant-transport A a b f C is-covariant-C (evid A a C ϕ)) =
    (evid A b C (covariant-transport A a b f ( \ x -> (z : A) → hom A x z → C z)     (is-covariant-yoneda-domain A is-segal-A C is-covariant-C) ϕ))
  :=
    naturality-covariant-fiberwise-transformation
    ( A)
    ( a)
    ( b)
    ( f)
    ( \ x -> (z : A) → hom A x z → C z)
    ( C)
    ( is-covariant-yoneda-domain A is-segal-A C is-covariant-C)
    ( is-covariant-C)
    ( \ x -> evid A x C)
    ( ϕ)


```

Naturality in $C$ is not automatic but can be proven easily:

```rzk title="RS17, Lemma 9.2(i)"
#def is-natural-in-family-evid
  (A : U)
  (a : A)
  (C D : A → U)
  (ψ : (z : A) → C z → D z)
  (φ : (z : A) → hom A a z → C z)
  : (composition ((z : A) → hom A a z → C z) (C a) (D a) (ψ a) (evid A a C)) φ =
    (composition ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z) (D a)
    (evid A a D) ( \ α z g → ψ z (α z g))) φ
  := refl
```

```rzk title="RS17, Lemma 9.2(ii)"
#def is-natural-in-family-yon-twice-pointwise
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-covariant-C : is-covariant A C)
  (is-covariant-D : is-covariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  (x : A)
  (f : hom A a x)
  : (composition (C a) (D a) ((z : A) → hom A a z → D z)
      (yon A is-segal-A a D is-covariant-D) (ψ a)) u x f =
    (composition (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      (\ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x f
  := naturality-covariant-fiberwise-transformation
      A a x f C D is-covariant-C is-covariant-D ψ u

#def is-natural-in-family-yon-once-pointwise uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-covariant-C : is-covariant A C)
  (is-covariant-D : is-covariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  (x : A)
  : (composition (C a) (D a) ((z : A) → hom A a z → D z)
      (yon A is-segal-A a D is-covariant-D) (ψ a)) u x =
    (composition (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      (\ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x
  :=
    eq-htpy funext
      ( hom A a x)
      ( \ f → D x)
      ( \ f →
        ( composition (C a) (D a) ((z : A) → hom A a z → D z)
          ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x f)
      ( \ f →
        ( composition (C a)((z : A) → hom A a z → C z)((z : A) → hom A a z → D z)
        ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x f)
      ( \ f →
        is-natural-in-family-yon-twice-pointwise
          A is-segal-A a C D is-covariant-C is-covariant-D ψ u x f)

#def is-natural-in-family-yon uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-covariant-C : is-covariant A C)
  (is-covariant-D : is-covariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  : (composition (C a) (D a) ((z : A) → hom A a z → D z)
      (yon A is-segal-A a D is-covariant-D) (ψ a)) u =
    (composition (C a) ((z : A) → hom A a z → C z) ((z : A) → hom A a z → D z)
      (\ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u
  :=
    eq-htpy funext
      ( A )
      ( \ x → hom A a x → D x)
      ( \ x →
        ( composition (C a) (D a) ((z : A) → hom A a z → D z)
          ( yon A is-segal-A a D is-covariant-D) (ψ a)) u x)
      ( \ x →
        ( composition (C a)((z : A) → hom A a z → C z)((z : A) → hom A a z → D z)
        ( \ α z g → ψ z (α z g)) (yon A is-segal-A a C is-covariant-C)) u x)
      ( \ x →
        is-natural-in-family-yon-once-pointwise
          A is-segal-A a C D is-covariant-C is-covariant-D ψ u x)
```

## Yoneda for contravariant families

Dually, the Yoneda lemma for contravariant type families characterizes natural
transformations from the contravariant family represented by a term $a : A$ in a
Segal type to a contravariant type family $C : A → U$.

By `naturality-contravariant-fiberwise-transformation` naturality is again
automatic.

```rzk
#def naturality-contravariant-fiberwise-representable-transformation
  (A : U)
  (is-segal-A : is-segal A)
  (a x y : A)
  (f : hom A y a)
  (g : hom A x y)
  (C : A → U)
  (is-contravariant-C : is-contravariant A C)
  (ϕ : (z : A) → hom A z a → C z)
  : (contravariant-transport A x y g C is-contravariant-C (ϕ y f)) =
    (ϕ x (Segal-comp A is-segal-A x y a g f))
  :=
    naturality-contravariant-fiberwise-transformation A x y g
      ( \ z → hom A z a) C
      ( is-segal-representable-is-contravariant A is-segal-A a)
      ( is-contravariant-C)
      ( ϕ)
      ( f)
```

For any Segal type $A$ and term $a : A$, the contravariant Yoneda lemma provides
an equivalence between the type `(z : A) → hom A z a → C z` of natural
transformations out of the functor `\ z → hom A z a` and valued in an arbitrary
contravariant family $C$ and the type $C a$.

One of the maps in this equivalence is evaluation at the identity. The inverse
map makes use of the contravariant transport operation.

```rzk
-- The map evid evaluates a natural transformation
-- out of a representable functor at the identity arrow.
#def contra-evid
  (A : U)
  (a : A)
  (C : A → U)
  : ( (z : A) → hom A z a → C z) → C a
  := \ ϕ → ϕ a (id-arr A a)

-- The inverse map only exists for Segal types and contravariant families.
#def contra-yon
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-contravariant-C : is-contravariant A C)
  : C a → ((z : A) → hom A z a → C z)
  := \ v z f → contravariant-transport A z a f C is-contravariant-C v
```

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def contra-evid-yon
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-contravariant-C : is-contravariant A C)
  (v : C a)
  : contra-evid A a C ((contra-yon A is-segal-A a C is-contravariant-C) v) = v
  := id-arr-contravariant-transport A a C is-contravariant-C v
```

The other composite carries $ϕ$ to an a priori distinct natural transformation.
We first show that these are pointwise equal at all `x : A` and `f : hom A x a`
in two steps.

```rzk
#section contra-yon-evid

#variable A : U
#variable is-segal-A : is-segal A
#variable a : A
#variable C : A → U
#variable is-contravariant-C : is-contravariant A C

-- The composite yon-evid of ϕ equals ϕ at all x : A and f : hom A x a.
#def contra-yon-evid-twice-pointwise
  (ϕ : (z : A) → hom A z a → C z)
  (x : A)
  (f : hom A x a)
  : ((contra-yon A is-segal-A a C is-contravariant-C)
        ((contra-evid A a C) ϕ)) x f = ϕ x f
  :=
    concat
      ( C x)
      ( ((contra-yon A is-segal-A a C is-contravariant-C)
            ((contra-evid A a C) ϕ )) x f)
      ( ϕ x (Segal-comp A is-segal-A x a a f (id-arr A a)))
      ( ϕ x f)
      ( naturality-contravariant-fiberwise-representable-transformation
          A is-segal-A a x a (id-arr A a) f C is-contravariant-C ϕ )
      ( ap
        ( hom A x a)
        ( C x)
        ( Segal-comp A is-segal-A x a a f (id-arr A a))
        ( f)
        ( ϕ x)
        ( Segal-comp-id A is-segal-A x a f))

-- By funext, these are equals as functions of f pointwise in x.
#def contra-yon-evid-once-pointwise uses (funext)
  (ϕ : (z : A) → hom A z a → C z)
  (x : A)
  : ((contra-yon A is-segal-A a C is-contravariant-C)
        ((contra-evid A a C) ϕ )) x = ϕ x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → C x)
      ( \ f →
        ( (contra-yon A is-segal-A a C is-contravariant-C)
          ( (contra-evid A a C) ϕ )) x f)
      ( \ f → (ϕ x f))
      ( \ f → contra-yon-evid-twice-pointwise ϕ x f)

-- By funext again, these are equal as functions of x and f.
#def contra-yon-evid uses (funext)
  (ϕ : (z : A) → hom A z a → C z)
  : (contra-yon A is-segal-A a C is-contravariant-C)((contra-evid A a C) ϕ) = ϕ
  :=
    eq-htpy funext
      ( A)
      ( \ x → (hom A x a → C x))
      ( \ x →
        ( (contra-yon A is-segal-A a C is-contravariant-C)
              ((contra-evid A a C) ϕ )) x)
      ( \ x → (ϕ x))
      ( \ x → contra-yon-evid-once-pointwise ϕ x)

#end contra-yon-evid
```

The contravariant Yoneda lemma says that evaluation at the identity defines an
equivalence.

```rzk
#def contra-Yoneda-lemma uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : A → U)
  (is-contravariant-C : is-contravariant A C)
  : is-equiv ((z : A) → hom A z a → C z) (C a) (contra-evid A a C)
  :=
    ( ( ( contra-yon A is-segal-A a C is-contravariant-C),
        ( contra-yon-evid A is-segal-A a C is-contravariant-C)),
      ( ( contra-yon A is-segal-A a C is-contravariant-C),
        ( contra-evid-yon A is-segal-A a C is-contravariant-C)))
```

## Contravariant Naturality

The equivalence of the Yoneda lemma is natural in both $a : A$ and $C : A → U$.

Naturality in $a$ follows from the fact that the maps `evid` and `yon` are
fiberwise equivalences between contravariant families over $A$, though it
requires some work, which has not yet been formalized, to prove that the domain
is contravariant.

Naturality in $C$ is not automatic but can be proven easily:

```rzk title="RS17, Lemma 9.2(i), dual"
#def is-natural-in-family-contra-evid
  (A : U)
  (a : A)
  (C D : A → U)
  (ψ : (z : A) → C z → D z)
  (φ : (z : A) → hom A z a → C z)
  : (composition ((z : A) → hom A z a → C z) (C a) (D a)
      (ψ a) (contra-evid A a C)) φ =
    (composition ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z) (D a)
      (contra-evid A a D) ( \ α z g → ψ z (α z g))) φ
  := refl
```

```rzk title="RS17, Lemma 9.2(ii), dual"
#def is-natural-in-family-contra-yon-twice-pointwise
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-contravariant-C : is-contravariant A C)
  (is-contravariant-D : is-contravariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  (x : A)
  (f : hom A x a)
  : (composition (C a) (D a) ((z : A) → hom A z a → D z)
      (contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x f =
    (composition (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      (\ α z g → ψ z (α z g))
      (contra-yon A is-segal-A a C is-contravariant-C)) u x f
  := naturality-contravariant-fiberwise-transformation
      A x a f C D is-contravariant-C is-contravariant-D ψ u

#def is-natural-in-family-contra-yon-once-pointwise uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-contravariant-C : is-contravariant A C)
  (is-contravariant-D : is-contravariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  (x : A)
  : (composition (C a) (D a) ((z : A) → hom A z a → D z)
      (contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x =
    (composition (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      (\ α z g → ψ z (α z g))
      (contra-yon A is-segal-A a C is-contravariant-C)) u x
  :=
    eq-htpy funext
      ( hom A x a)
      ( \ f → D x)
      ( \ f →
        ( composition (C a) (D a) ((z : A) → hom A z a → D z)
          ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x f)
      ( \ f →
        ( composition (C a)((z : A) → hom A z a → C z)((z : A) → hom A z a → D z)
        ( \ α z g → ψ z (α z g))
        ( contra-yon A is-segal-A a C is-contravariant-C)) u x f)
      ( \ f →
        is-natural-in-family-contra-yon-twice-pointwise
          A is-segal-A a C D is-contravariant-C is-contravariant-D ψ u x f)

#def is-natural-in-family-contra-yon uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C D : A → U)
  (is-contravariant-C : is-contravariant A C)
  (is-contravariant-D : is-contravariant A D)
  (ψ : (z : A) → C z → D z)
  (u : C a)
  : (composition (C a) (D a) ((z : A) → hom A z a → D z)
      (contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u =
    (composition (C a) ((z : A) → hom A z a → C z) ((z : A) → hom A z a → D z)
      (\ α z g → ψ z (α z g))
      (contra-yon A is-segal-A a C is-contravariant-C)) u
  :=
    eq-htpy funext
      ( A )
      ( \ x → hom A x a → D x)
      ( \ x →
        ( composition (C a) (D a) ((z : A) → hom A z a → D z)
          ( contra-yon A is-segal-A a D is-contravariant-D) (ψ a)) u x)
      ( \ x →
        ( composition (C a)((z : A) → hom A z a → C z)((z : A) → hom A z a → D z)
        ( \ α z g → ψ z (α z g))
        ( contra-yon A is-segal-A a C is-contravariant-C)) u x)
      ( \ x →
        is-natural-in-family-contra-yon-once-pointwise
          A is-segal-A a C D is-contravariant-C is-contravariant-D ψ u x)
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
  := (x : A) → is-contr (hom A a x)
```

Initial objects satisfy an induction principle relative to covariant families.

```rzk
#section initial-evaluation-equivalence

#variable A : U
#variable a : A
#variable is-initial-a : is-initial A a
#variable C : A → U
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
  : (x : A) → C x
  :=
    \ x → covariant-transport A a x (arrows-from-initial x) C is-covariant-C u

#def has-cov-section-ev-pt uses (is-initial-a)
  : has-section ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ind-initial),
      ( \ u →
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
            ( \ f →
              covariant-transport A a a f C is-covariant-C u)
            ( identity-component-arrows-from-initial))
          ( id-arr-covariant-transport A a C is-covariant-C u)))

#def ind-initial-ev-pt-pointwise uses (is-initial-a)
  (s : (x : A) → C x)
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
      ( ( s b, \ t → s (arrows-from-initial b t)))

#end initial-evaluation-equivalence
```

We now prove that induction from an initial element in the base of a covariant
family defines an inverse equivalence to evaluation at the element.

```rzk title="RS17, Theorem 9.7"
#def is-equiv-covariant-ev-initial uses (funext)
  (A : U)
  (a : A)
  (is-initial-a : is-initial A a)
  (C : A → U)
  (is-covariant-C : is-covariant A C)
  : is-equiv ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ( ind-initial A a is-initial-a C is-covariant-C ),
        ( \ s → eq-htpy
                  funext
                    ( A)
                    ( C)
                    ( ind-initial
                        A a is-initial-a C is-covariant-C (ev-pt A a C s))
                    ( s)
                    ( ind-initial-ev-pt-pointwise
                        A a is-initial-a C is-covariant-C s))),
      ( has-cov-section-ev-pt A a is-initial-a C is-covariant-C))
```

## Initial objects in slice categories

The type `coslice A a` is the type of arrows in $A$ with domain $a$.

```rzk
#def coslice
  (A : U)
  (a : A)
  : U
  := Σ (z : A) , (hom A a z)
```

We now show that the coslice under $a$ in a Segal type $A$ has an initial object
given by the identity arrow at $a$. This makes use of the following equivalence.

```rzk
#def equiv-hom-in-coslice
  (A : U)
  (a x : A)
  (f : hom A a x)
  : Equiv
    ( hom (coslice A a) (a, id-arr A a) (x, f))
    ( (t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-arr A a])
  :=
    ( \ h t s → (second (h s)) t,
      (( \ k s → ( k 1₂ s, \ t → k t s),
        \ h → refl),
      ( \ k s → ( k 1₂ s, \ t → k t s),
        \ k → refl)))
```

Since $hom A a$ is covariant when $A$ is Segal, this latter type is
contractible.

```rzk
#def is-contr-is-segal-hom-in-coslice
  (A : U)
  (is-segal-A : is-segal A)
  (a x : A)
  (f : hom A a x)
  : is-contr ( (t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-arr A a])
  :=
    ( second (has-unique-fixed-domain-lifts-iff-is-covariant
                A (\ z → hom A a z)))
      ( is-segal-representable-is-covariant A is-segal-A a)
      ( a)
      ( x)
      ( f)
      ( id-arr A a)
```

This proves the initiality of identity arrows in the coslice of a Segal type.

```rzk title="RS17, Lemma 9.8"
#def is-initial-id-arr-is-segal
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  : is-initial (coslice A a) (a, id-arr A a)
  :=
    \ (x, f) →
    is-contr-is-equiv-to-contr
      ( hom (coslice A a) (a, id-arr A a) (x, f))
      ( (t : Δ¹) → hom A a (f t) [t ≡ 0₂ ↦ id-arr A a])
      ( equiv-hom-in-coslice A a x f)
      ( is-contr-is-segal-hom-in-coslice A is-segal-A a x f)
```

## Dependent Yoneda lemma

The dependent Yoneda lemma now follows by specializing these results.

```rzk
#def dependent-ev-id
  (A : U)
  (a : A)
  (C : (coslice A a) → U)
  : ((p : coslice A a) → C p) → C (a, id-arr A a)
  := \ s → s (a, id-arr A a)

#def dependent-yoneda-lemma' uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (coslice A a) → U)
  (is-covariant-C : is-covariant (coslice A a) C)
  : is-equiv
      ( (p : coslice A a) → C p)
      ( C (a, id-arr A a))
      ( dependent-ev-id A a C)
  :=
    is-equiv-covariant-ev-initial
      ( coslice A a)
      ( (a, id-arr A a))
      ( is-initial-id-arr-is-segal A is-segal-A a)
      ( C)
      ( is-covariant-C)
```

The actual dependent Yoneda is equivalent to the result just proven, just with
an equivalent type in the domain of the evaluation map.

```rzk title="RS17, Theorem 9.5"
#def dependent-yoneda-lemma uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (coslice A a) → U)
  (is-covariant-C : is-covariant (coslice A a) C)
  : is-equiv
      ( (x : A) → (f : hom A a x) → C (x, f))
      ( C (a, id-arr A a))
      ( \ s → s a (id-arr A a))
  :=
    left-cancel-is-equiv
      ( (p : coslice A a) → C p)
      ( (x : A) → (f : hom A a x) → C (x, f))
      ( C (a, id-arr A a))
      ( first (equiv-dependent-curry A (\ z → hom A a z)(\ x f → C (x, f))))
      ( second (equiv-dependent-curry A (\ z → hom A a z)(\ x f → C (x, f))))
      ( \ s → s a (id-arr A a))
      ( dependent-yoneda-lemma' A is-segal-A a C is-covariant-C)
```

## Final objects

A term $a$ in a type $A$ is initial if all of its mapping-out hom types are
contractible.

```rzk
#def is-final
  (A : U)
  (a : A)
  : U
  := (x : A) → is-contr (hom A x a)
```

Final objects satisfy an induction principle relative to contravariant families.

```rzk
#section final-evaluation-equivalence

#variable A : U
#variable a : A
#variable is-final-a : is-final A a
#variable C : A → U
#variable is-contravariant-C : is-contravariant A C

#def arrows-to-final
  (x : A)
  : hom A x a
  := contraction-center (hom A x a) (is-final-a x)

#def identity-component-arrows-to-final
  : arrows-to-final a = id-arr A a
  := contracting-htpy (hom A a a) (is-final-a a) (id-arr A a)

#def ind-final uses (is-final-a)
  (u : C a)
  : (x : A) → C x
  :=
    \ x →
    contravariant-transport A x a (arrows-to-final x) C is-contravariant-C u

#def has-contra-section-ev-pt uses (is-final-a)
  : has-section ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ind-final),
      ( \ u →
        concat
          ( C a)
          ( contravariant-transport A a a
            ( arrows-to-final a) C is-contravariant-C u)
          ( contravariant-transport A a a
            ( id-arr A a) C is-contravariant-C u)
          ( u)
          ( ap
            ( hom A a a)
            ( C a)
            ( arrows-to-final a)
            ( id-arr A a)
            ( \ f →
              contravariant-transport A a a f C is-contravariant-C u)
            ( identity-component-arrows-to-final))
          ( id-arr-contravariant-transport A a C is-contravariant-C u)))

#def ind-final-ev-pt-pointwise uses (is-final-a)
  (s : (x : A) → C x)
  (b : A)
  : ind-final (ev-pt A a C s) b = s b
  :=
    contravariant-uniqueness
      ( A)
      ( b)
      ( a)
      ( arrows-to-final b)
      ( C)
      ( is-contravariant-C)
      ( ev-pt A a C s)
      ( ( s b, \ t → s (arrows-to-final b t)))

#end final-evaluation-equivalence
```

We now prove that induction from a final element in the base of a contravariant
family defines an inverse equivalence to evaluation at the element.

```rzk title="RS17, Theorem 9.7, dual"
#def is-equiv-contravariant-ev-final uses (funext)
  (A : U)
  (a : A)
  (is-final-a : is-final A a)
  (C : A → U)
  (is-contravariant-C : is-contravariant A C)
  : is-equiv ((x : A) → C x) (C a) (ev-pt A a C)
  :=
    ( ( ( ind-final A a is-final-a C is-contravariant-C ),
        ( \ s → eq-htpy
                  funext
                    ( A)
                    ( C)
                    ( ind-final
                        A a is-final-a C is-contravariant-C (ev-pt A a C s))
                    ( s)
                    ( ind-final-ev-pt-pointwise
                        A a is-final-a C is-contravariant-C s))),
      ( has-contra-section-ev-pt A a is-final-a C is-contravariant-C))
```

## Final objects in slice categories

The type `slice A a` is the type of arrows in $A$ with codomain $a$.

```rzk
#def slice
  (A : U)
  (a : A)
  : U
  := Σ (z : A) , (hom A z a)
```

We now show that the slice over $a$ in a Segal type $A$ has a final object given
by the identity arrow at $a$. This makes use of the following equivalence.

```rzk
#def equiv-hom-in-slice
  (A : U)
  (a x : A)
  (f : hom A x a)
  : Equiv
    ( hom (slice A a) (x, f) (a, id-arr A a))
    ( (t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-arr A a])
  :=
    ( \ h t s → (second (h s)) t,
      (( \ k s → ( k 0₂ s, \ t → k t s),
        \ h → refl),
      ( \ k s → ( k 0₂ s, \ t → k t s),
        \ k → refl)))
```

Since $\ z → hom A z a$ is contravariant when $A$ is Segal, this latter type is
contractible.

```rzk
#def is-contr-is-segal-hom-in-slice
  (A : U)
  (is-segal-A : is-segal A)
  (a x : A)
  (f : hom A x a)
  : is-contr ( (t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-arr A a])
  :=
    ( second (has-unique-fixed-codomain-lifts-iff-is-contravariant
                A (\ z → hom A z a)))
      ( is-segal-representable-is-contravariant A is-segal-A a)
      ( x)
      ( a)
      ( f)
      ( id-arr A a)
```

This proves the finality of identity arrows in the slice of a Segal type.

```rzk title="RS17, Lemma 9.8, dual"
#def is-final-id-arr-is-segal
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  : is-final (slice A a) (a, id-arr A a)
  :=
    \ (x, f) →
    is-contr-is-equiv-to-contr
      ( hom (slice A a) (x, f) (a, id-arr A a))
      ( (t : Δ¹) → hom A (f t) a [t ≡ 1₂ ↦ id-arr A a])
      ( equiv-hom-in-slice A a x f)
      ( is-contr-is-segal-hom-in-slice A is-segal-A a x f)
```

## Contravariant Dependent Yoneda lemma

The contravariant version of the dependent Yoneda lemma now follows by
specializing these results.

```rzk
#def contra-dependent-ev-id
  (A : U)
  (a : A)
  (C : (slice A a) → U)
  : ((p : slice A a) → C p) → C (a, id-arr A a)
  := \ s → s (a, id-arr A a)

#def contra-dependent-yoneda-lemma' uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (slice A a) → U)
  (is-contravariant-C : is-contravariant (slice A a) C)
  : is-equiv
      ( (p : slice A a) → C p)
      ( C (a, id-arr A a))
      ( contra-dependent-ev-id A a C)
  :=
    is-equiv-contravariant-ev-final
      ( slice A a)
      ( (a, id-arr A a))
      ( is-final-id-arr-is-segal A is-segal-A a)
      ( C)
      ( is-contravariant-C)
```

The actual contravariant dependent Yoneda is equivalent to the result just
proven, just with an equivalent type in the domain of the evaluation map.

```rzk title="RS17, Theorem 9.5, dual"
#def contra-dependent-yoneda-lemma uses (funext)
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  (C : (slice A a) → U)
  (is-contravariant-C : is-contravariant (slice A a) C)
  : is-equiv
      ( (x : A) → (f : hom A x a) → C (x, f))
      ( C (a, id-arr A a))
      ( \ s → s a (id-arr A a))
  :=
    left-cancel-is-equiv
      ( (p : slice A a) → C p)
      ( (x : A) → (f : hom A x a) → C (x, f))
      ( C (a, id-arr A a))
      ( first (equiv-dependent-curry A (\ z → hom A z a)(\ x f → C (x, f))))
      ( second (equiv-dependent-curry A (\ z → hom A z a)(\ x f → C (x, f))))
      ( \ s → s a (id-arr A a))
      ( contra-dependent-yoneda-lemma'
          A is-segal-A a C is-contravariant-C)
```
