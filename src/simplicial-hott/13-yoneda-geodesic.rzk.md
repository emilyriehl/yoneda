# A self contained proof of the Yoneda lemma

This file, which is independent of the rest of the simplicial HoTT repository,
contains a self-contained proof of the ∞-categorical Yoneda lemma in the
special case where both functors are contravariantly representable. This is
intended for expository purposes.

We capitalize the first letter of the terms defined here when they are either
duplications of our specializations of terms defined in the braoder repository.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

The definitions and proofs reference standard concepts from
homotopy type theory including a universe of types denoted `#!rzk U`, the notion of contractible types, and the notion of
equivalence between types.

Some of the definitions in this file rely on function extensionality:

```rzk
#assume funext : FunExt
```

an axiom which characterizes the identity types of function types.

## Simplices

The language for synthetic ∞-categories includes a primative notion
called **shapes** which can be used to index type-valued diagrams.
Shapes are carved out of directed **cubes**, which are cartesian
products of the directed 1-cube `#!rzk 2`, via predicates called
topes. To state and prove the Yoneda lemma we require only two
examples of shapes, the 1-simplex and 2-simplex defined below.
In the rest of the library, these shapes are denoted using the more
common superscripts.

```rzk title="The 1-simplex"
#def Δ₁
  : 2 → TOPE
  := \ t → TOP
```

```rzk title="The 2-simplex"
#def Δ₂
  : ( 2 × 2) → TOPE
  := \ (t , s) → s ≤ t
```

## Hom types

Extension types are used to define the type of arrows between fixed terms:

<svg style="float: right" viewBox="0 0 200 60" width="150" height="60">
  <polyline points="40,30 160,30" stroke="blue" stroke-width="3" marker-end="url(#arrow-blue)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
</svg>

```rzk title="RS17, Definition 5.1"
#def Hom
  ( A : U)
  ( x y : A)
  : U
  :=
    ( t : Δ₁)
  → A [ t ≡ 0₂ ↦ x , -- the left endpoint is exactly x
        t ≡ 1₂ ↦ y]   -- the right endpoint is exactly y

```

Extension types are also used to define the type of commutative triangles:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="200">
  <path style="fill: rgb(0,128,255,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,40 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110">h</text>
</svg>

```rzk title="RS17, Definition 5.2"
#def Hom2
  ( A : U)
  ( x y z : A)
  ( f : Hom A x y)
  ( g : Hom A y z)
  ( h : Hom A x z)
  : U
  :=
    ( ( t₁ , t₂) : Δ₂)
  → A [ t₂ ≡ 0₂ ↦ f t₁ , -- the top edge is exactly `f`,
        t₁ ≡ 1₂ ↦ g t₂ , -- the right edge is exactly `g`, and
        t₂ ≡ t₁ ↦ h t₂]   -- the diagonal is exactly `h`
```

## Types with composition

A type is **a pre-∞-category** if every composable pair of arrows has a unique
composite. Note this is a considerable simplification of the usual Segal
condition, which also requires homotopical uniqueness of higher-order
composites.

```rzk title="RS17, Definition 5.3"
#def Is-pre-∞-category
  ( A : U)
  : U
  :=
    ( x : A) → (y : A) → (z : A)
  → ( f : Hom A x y) → (g : Hom A y z)
  → is-contr (Σ (h : Hom A x z) , (Hom2 A x y z f g h))
```

Pre-∞-categories have a composition functor and witnesses to the composition
relation. Composition is written in diagrammatic order to match the order of
arguments in `#!rzk is-pre-∞-category`.

```rzk
#def Comp-is-pre-∞-category
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( x y z : A)
  ( f : Hom A x y)
  ( g : Hom A y z)
  : Hom A x z
  := first (first (is-pre-∞-category-A x y z f g))

#def Witness-comp-is-pre-∞-category
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( x y z : A)
  ( f : Hom A x y)
  ( g : Hom A y z)
  : Hom2 A x y z f g (Comp-is-pre-∞-category A is-pre-∞-category-A x y z f g)
  := second (first (is-pre-∞-category-A x y z f g))
```

Composition in a pre-∞-category is unique in the following sense. If there is a
witness that an arrow $h$ is a composite of $f$ and $g$, then the specified
composite equals $h$.

<svg style="float: right" viewBox="0 0 200 380" width="125">
  <path style="fill: rgb(175,175,175,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,45 170,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30" fill="grey">x</text>
  <text x="170" y="30" fill="grey">y</text>
  <text x="170" y="170" fill="grey">z</text>
  <text x="100" y="15" fill="grey">f</text>
  <text x="185" y="100" fill="grey">g</text>
  <text x="90" y="110">h</text>
  <text x="125" y="75" fill="grey">α</text>
  <text x="100" y="145" fill="red" rotate="90" style="font-size: 50px">=</text>
  <path style="fill: rgb(128,0,0,0.5); stroke-cap: round;" d="M 52 240 L 160 240 L 160 348 Z"></path>
  <polyline points="40,230 160,230" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,245 170,360" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,240 160,360" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="230" fill="grey">x</text>
  <text x="170" y="230" fill="grey">y</text>
  <text x="170" y="370" fill="grey">z</text>
  <text x="100" y="215" fill="grey">f</text>
  <text x="185" y="300" fill="grey">g</text>
  <text x="90" y="310" transform="rotate(45, 90, 310)" fill="red">comp-is-pre-∞-category</text>
  <text x="120" y="280" fill="rgb(128,0,0)" transform="rotate(45, 120, 280)" style="font-size: 10px">Witness-comp-is-pre-∞-category</text>
</svg>

```rzk
#def Uniqueness-comp-is-pre-∞-category
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( x y z : A)
  ( f : Hom A x y)
  ( g : Hom A y z)
  ( h : Hom A x z)
  ( alpha : Hom2 A x y z f g h)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x y z f g) = h
  :=
    first-path-Σ
      ( Hom A x z)
      ( Hom2 A x y z f g)
      ( Comp-is-pre-∞-category A is-pre-∞-category-A x y z f g
      , Witness-comp-is-pre-∞-category A is-pre-∞-category-A x y z f g)
      ( h , alpha)
      ( homotopy-contraction
        ( Σ ( k : Hom A x z) , (Hom2 A x y z f g k))
        ( is-pre-∞-category-A x y z f g)
        ( h , alpha))
```

## Identity

All types have identity arrows and witnesses to the identity composition law.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="100" y="15" fill="red">x</text>
</svg>

```rzk title="RS17, Definition 5.7"
#def Id-hom
  ( A : U)
  ( x : A)
  : Hom A x x
  := \ t → x
```

Witness for the right identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">y</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk title="RS17, Proposition 5.8a"
#def Comp-id-witness
  ( A : U)
  ( x y : A)
  ( f : Hom A x y)
  : Hom2 A x y y f (Id-hom A y) f
  := \ (t , s) → f t
```

Witness for the left identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">x</text>
  <text x="185" y="100">f</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk title="RS17, Proposition 5.8b"
#def Id-comp-witness
  ( A : U)
  ( x y : A)
  ( f : Hom A x y)
  : Hom2 A x x y (Id-hom A x) f f
  := \ (t , s) → f s
```

In a pre-∞-category, where composition is unique, it follows that composition
with an identity arrow recovers the original arrow. Thus, an identity axiom was
not needed in the definition of pre-∞-categories.

```rzk title="If A is a pre-∞-category then the right unit law holds"
#def Comp-id-is-pre-∞-category
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( x y : A)
  ( f : Hom A x y)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x y y f (Id-hom A y))
    = f
  :=
    Uniqueness-comp-is-pre-∞-category
      ( A)
      ( is-pre-∞-category-A)
      ( x) (y) (y)
      ( f)
      ( Id-hom A y)
      ( f)
      ( Comp-id-witness A x y f)
```

```rzk title="If A is a pre-∞-category then the left unit law holds"
#def Id-comp-is-pre-∞-category
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( x y : A)
  ( f : Hom A x y)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x x y (Id-hom A x) f)
    = f
  :=
    Uniqueness-comp-is-pre-∞-category
      ( A)
      ( is-pre-∞-category-A)
      ( x) (x) (y)
      ( Id-hom A x)
      ( f)
      ( f)
      ( Id-comp-witness A x y f)
```

Associativity is similarly automatic for pre-∞-categories, but since this is not
needed to prove the Yoneda lemma, it will not be discussed here.

## Natural transformations between representable functors

Fix a pre-∞-category $A$ and terms $a b : A$. The Yoneda lemma characterizes
natural transformations between the type families contravariantly represented by
these terms.

Ordinarily, such a natural transformation would involve a family of maps

`#!rzk ϕ : (z : A) → Hom A z a → Hom A z b`

together with a proof of naturality of these components, but we will prove in
`#!rzk naturality-contravariant-fiberwise-representable-transformation`
that naturality is automatic.

```rzk
-- We apply a fiberwise transformation ϕ to a square of a particular form.
#def square-representable-transformation
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : ( t : Δ¹) → Hom A (f t) b
  :=
    \ t →
    ϕ
      ( f t)
      ( \ s →
        recOR
        ( s ≤ t ↦
          ( Witness-comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)
            ( t , s)
        , t ≤ s ↦
          ( Comp-id-witness A x a
            ( Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)) (s , t)))

-- This extracts the diagonal composite of the square.
#def diagonal-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : Hom A x b
  :=
    \ t →
    square-representable-transformation A is-pre-∞-category-A a b x y f v ϕ t t

-- One half of transformation-id-codomain-square.
#def witness-comp-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : Hom2 A x y b f (ϕ y v)
    ( diagonal-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)
  :=
    \ (t , s) →
   square-representable-transformation A is-pre-∞-category-A a b x y f v ϕ t s

-- The associated coherence.
#def coherence-witness-comp-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    Uniqueness-comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v)
      ( diagonal-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)
      ( witness-comp-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)

-- The other half of transformation-id-codomain-square.
#def witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : Hom2 A x b b
    ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( Id-hom A b)
    ( diagonal-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)
  :=
    \ (t , s) →
   square-representable-transformation A is-pre-∞-category-A a b x y f v ϕ s t

-- The associated coherence.
#def coherence-witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x b b
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
      ( Id-hom A b))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    Uniqueness-comp-is-pre-∞-category A is-pre-∞-category-A x b b
    ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( Id-hom A b)
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( witness-id-transformation-id-codomain-square
          A is-pre-∞-category-A a b x y f v ϕ)

#def simplified-coherence-witness-id-transformation-id-codomain-square
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    = ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
  :=
    zag-zig-concat (Hom A x b)
    ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( Comp-is-pre-∞-category A is-pre-∞-category-A x b b
      ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
      ( Id-hom A b))
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( Comp-id-is-pre-∞-category A is-pre-∞-category-A x b
      ( ϕ x (comp-is-pre-∞-category A is-pre-∞-category-A x y a f v)))
    ( coherence-witness-id-transformation-id-codomain-square
      A is-pre-∞-category-A a b x y f v ϕ)
```

We now prove that a fiberwise natural transformation
`#!rzk ϕ : (z : A) → Hom A z a → Hom A z b` is automatically natural:
for arrows `#!rzk f : Hom A x y` and `#!rzk v : Hom A y a` in a pre-∞-category,
the composite of `#!rzk f` with `#!rzk ϕ y v` equals the arrow obtained by
`#!rzk ϕ x` applied to the composite of `#!rzk f` with `#!rzk v`.

```rzk
#def Naturality-contravariant-fiberwise-representable-transformation
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b x y : A)
  ( f : Hom A x y)
  ( v : Hom A y a)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : ( Comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
  = ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
  :=
    zig-zag-concat (Hom A x b)
    ( Comp-is-pre-∞-category A is-pre-∞-category-A x y b f (ϕ y v))
    ( diagonal-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x y a f v))
    ( coherence-witness-comp-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
    ( simplified-coherence-witness-id-transformation-id-codomain-square
        A is-pre-∞-category-A a b x y f v ϕ)
```

## The Yoneda lemma

For any pre-∞-category $A$ terms $a b : A$, the contravariant Yoneda lemma
provides an equivalence between the type`#!rzk (z : A) → Hom A z a → Hom A z b`
of natural transformations and the type `#!rzk Hom A a b`.

One of the maps in this equivalence is evaluation at the identity. The
inverse map makes use of the contravariant transport operation.

The following map, `#!rzk contra-evid` evaluates a natural transformation
out of a representable functor at the identity arrow.

```rzk
#def Contra-evid
  ( A : U)
  ( a b : A)
  : ( ( z : A) → Hom A z a → Hom A z b) → Hom A a b
  := \ ϕ → ϕ a (Id-hom A a)
```

The inverse map only exists for pre-∞-categories.

```rzk
#def Contra-yon
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b : A)
  : Hom A a b → ((z : A) → Hom A z a → Hom A z b)
  := \ v z f → Comp-is-pre-∞-category A is-pre-∞-category-A z a b f v
```

It remains to show that the Yoneda maps are inverses. One retraction is
straightforward:

```rzk
#def Contra-evid-yon
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b : A)
  ( v : Hom A a b)
  : Contra-evid A a b (Contra-yon A is-pre-∞-category-A a b v) = v
  :=
    Id-comp-is-pre-∞-category A is-pre-∞-category-A a b v
```

The other composite carries $ϕ$ to an a priori distinct natural
transformation. We first show that these are pointwise equal at all
`#!rzk x : A` and `#!rzk f : Hom A x a` in two steps.

```rzk
#section contra-yon-evid

#variable A : U
#variable is-pre-∞-category-A : Is-pre-∞-category A
#variables a b : A
```

The composite `#!rzk Contra-yon-evid` of `#!rzk ϕ` equals `#!rzk ϕ` at all
`#!rzk x : A` and `#!rzk f : Hom A x a`.

```rzk
#def Contra-yon-evid-twice-pointwise
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  ( x : A)
  ( f : Hom A x a)
  : ( ( Contra-yon A is-pre-∞-category-A a b)
        ( ( Contra-evid A a b) ϕ)) x f = ϕ x f
  :=
    concat
      ( Hom A x b)
      ( ( ( Contra-yon A is-pre-∞-category-A a b)
            ( ( Contra-evid A a b) ϕ)) x f)
      ( ϕ x (Comp-is-pre-∞-category A is-pre-∞-category-A x a a f (Id-hom A a)))
      ( ϕ x f)
      ( Naturality-contravariant-fiberwise-representable-transformation
          A is-pre-∞-category-A a b x a f (Id-hom A a) ϕ)
      ( ap
        ( Hom A x a)
        ( Hom A x b)
        ( Comp-is-pre-∞-category A is-pre-∞-category-A x a a
          f (Id-hom A a))
        ( f)
        ( ϕ x)
        ( Comp-id-is-pre-∞-category A is-pre-∞-category-A x a f))
```

By `#!rzk funext`, these are equals as functions of `#!rzk f` pointwise in
`#!rzk x`.

```rzk
#def Contra-yon-evid-once-pointwise uses (funext)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  ( x : A)
  : ( ( Contra-yon A is-pre-∞-category-A a b)
        ( ( Contra-evid A a b) ϕ)) x = ϕ x
  :=
    eq-htpy funext
      ( Hom A x a)
      ( \ f → Hom A x b)
      ( \ f →
        ( ( Contra-yon A is-pre-∞-category-A a b)
          ( ( Contra-evid A a b) ϕ)) x f)
      ( \ f → (ϕ x f))
      ( \ f → Contra-yon-evid-twice-pointwise ϕ x f)
```

By `#!rzk funext` again, these are equal as functions of `#!rzk x` and
`#!rzk f`.

```rzk
#def Contra-yon-evid uses (funext)
  ( ϕ : (z : A) → Hom A z a → Hom A z b)
  : Contra-yon A is-pre-∞-category-A a b (Contra-evid A a b ϕ) = ϕ
  :=
    eq-htpy funext
      ( A)
      ( \ x → (Hom A x a → Hom A x b))
      ( Contra-yon A is-pre-∞-category-A a b (Contra-evid A a b ϕ))
      ( ϕ)
      ( Contra-yon-evid-once-pointwise ϕ)

#end contra-yon-evid
```

The contravariant Yoneda lemma says that evaluation at the identity defines an
equivalence.

```rzk
#def Contra-yoneda-lemma uses (funext)
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a b : A)
  : is-equiv ((z : A) → Hom A z a → Hom A z b) (Hom A a b) (Contra-evid A a b)
  :=
    ( ( ( Contra-yon A is-pre-∞-category-A a b)
      , ( Contra-yon-evid A is-pre-∞-category-A a b))
    , ( ( Contra-yon A is-pre-∞-category-A a b)
      , ( Contra-evid-yon A is-pre-∞-category-A a b)))
```

## Contravariant Naturality

The equivalences of the Yoneda lemma is natural in both $a : A$ and $b : A$.
Naturality of the map`#!rzk Contra-yon` follows formally from naturality of
`#!rzk Contra-evid`, so we prove only the latter, which is easier.

Naturality in $b$ is not automatic but can be proven by reflexivity:

```rzk title="RS17, Lemma 9.2(i), dual"
#def Is-natural-in-family-contra-evid
  ( A : U)
  ( a b b' : A)
  ( ψ : (z : A) → Hom A z b → Hom A z b')
  ( φ : (z : A) → Hom A z a → Hom A z b)
  : ( comp ((z : A) → Hom A z a → Hom A z b) (Hom A a b) (Hom A a b')
      ( ψ a) (Contra-evid A a b)) φ
  = ( comp ((z : A) → Hom A z a → Hom A z b) ((z : A) → Hom A z a → Hom A z b')
      ( Hom A a b')
      ( Contra-evid A a b') (\ α z g → ψ z (α z g))) φ
  := refl
```

Naturality in $a$ in fact follows formally. By a generalization of
`#!rzk Naturality-contravariant-fiberwise-representable-transformation` which is
no harder to prove, any fiberwise map between contravariant families over
$a : A$ is automatically natural. Since it would take time to introduce the
notion of contravariant family and prove that the domain of  `#!rzk Contra-evid`
is one, we instead give a direct proof of naturality in $a : A$.

```rzk title="RS17, Lemma 9.2(i), dual"
#def Is-natural-in-object-contra-evid
  ( A : U)
  ( is-pre-∞-category-A : Is-pre-∞-category A)
  ( a' a b : A)
  ( k : Hom A a' a)
  ( φ : (z : A) → Hom A z a → Hom A z b)
  : ( comp ((z : A) → Hom A z a → Hom A z b) (Hom A a b) (Hom A a' b)
      ( \ f → Comp-is-pre-∞-category A is-pre-∞-category-A a' a b k f)
      ( Contra-evid A a b)) φ
  = ( comp ((z : A) → Hom A z a → Hom A z b) ((z : A) → Hom A z a' → Hom A z b)
      ( Hom A a' b)
      ( Contra-evid A a' b)
      ( \ α z g →
          α z (Comp-is-pre-∞-category A is-pre-∞-category-A z a' a g k))) φ
  :=
    concat (Hom A a' b)
    ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a b k (φ a (Id-hom A a)))
    ( φ a' (Comp-is-pre-∞-category A is-pre-∞-category-A a' a a k (Id-hom A a)))
    ( φ a' (Comp-is-pre-∞-category A is-pre-∞-category-A a' a' a (Id-hom A a') k))
    ( Naturality-contravariant-fiberwise-representable-transformation
      A is-pre-∞-category-A a b a' a k (Id-hom A a) φ)
    ( ap (hom A a' a) (hom A a' b)
      ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a a k (Id-hom A a))
      ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a' a (Id-hom A a') k)
      ( \ h → φ a' h)
      ( concat (hom A a' a)
        ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a a k (Id-hom A a))
        ( k)
        ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a' a (Id-hom A a') k)
        ( Comp-id-is-pre-∞-category A is-pre-∞-category-A a' a k)
        ( rev (hom A a' a)
          ( Comp-is-pre-∞-category A is-pre-∞-category-A a' a' a (Id-hom A a') k)
          ( k)
          ( Id-comp-is-pre-∞-category A is-pre-∞-category-A a' a k))))
```
