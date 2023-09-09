# Segal Types

These formalisations correspond to Section 5 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/1-paths.md` - We require basic path algebra.
- `hott/2-contractible.md` - We require the notion of contractible types and
  their data.
- `hott/total-space.md` — We rely on
  `#!rzk is-equiv-projection-contractible-fibers` and
  `#!rzk total-space-projection` in the proof of Theorem 5.5.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension
  extensionality.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Hom types

Extension types are used to define the type of arrows between fixed terms:

<svg style="float: right" viewBox="0 0 200 60" width="150" height="60">
  <polyline points="40,30 160,30" stroke="blue" stroke-width="3" marker-end="url(#arrow-blue)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
</svg>

```rzk title="RS17, Definition 5.1"
#def hom
  ( A : U)
  ( x y : A)
  : U
  :=
    ( t : Δ¹) →
    A [ t ≡ 0₂ ↦ x ,  -- the left endpoint is exactly x
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
#def hom2
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  : U
  :=
    ( (t1 , t2) : Δ²) →
    A [ t2 ≡ 0₂ ↦ f t1 ,  -- the top edge is exactly `f`,
        t1 ≡ 1₂ ↦ g t2 ,  -- the right edge is exactly `g`, and
        t2 ≡ t1 ↦ h t2]  -- the diagonal is exactly `h`
```

## The Segal condition

A type is **Segal** if every composable pair of arrows has a unique composite.
Note this is a considerable simplification of the usual Segal condition, which
also requires homotopical uniqueness of higher-order composites.

```rzk title="RS17, Definition 5.3"
#def is-segal
  ( A : U)
  : U
  :=
    (x : A) → (y : A) → (z : A) →
    (f : hom A x y) → (g : hom A y z) →
    is-contr (Σ (h : hom A x z) , (hom2 A x y z f g h))
```

Segal types have a composition functor and witnesses to the composition
relation. Composition is written in diagrammatic order to match the order of
arguments in `#!rzk is-segal`.

```rzk
#def comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom A x z
  := first (first (is-segal-A x y z f g))

#def witness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
  := second (first (is-segal-A x y z f g))
```

Composition in a Segal type is unique in the following sense. If there is a
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
  <text x="90" y="310" transform="rotate(45, 90, 310)" fill="red">comp-is-segal</text>
  <text x="120" y="280" fill="rgb(128,0,0)" transform="rotate(45, 120, 280)" style="font-size: 10px">witness-comp-is-segal</text>
</svg>

```rzk
#def uniqueness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : ( comp-is-segal A is-segal-A x y z f g) = h
  :=
    first-path-Σ
      ( hom A x z)
      ( hom2 A x y z f g)
      ( comp-is-segal A is-segal-A x y z f g ,
        witness-comp-is-segal A is-segal-A x y z f g)
      ( h , alpha)
      ( homotopy-contraction
        ( Σ (k : hom A x z) , (hom2 A x y z f g k))
        ( is-segal-A x y z f g)
        ( h , alpha))
```

## Characterizing Segal types

Our aim is to prove that a type is Segal if and only if the
`#!rzk horn-restriction` map, defined below, is an equivalence.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
</svg>

A pair of composable arrows form a horn.

```rzk
#def horn
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Λ → A
  :=
    \ (t , s) →
    recOR
      ( s ≡ 0₂ ↦ f t ,
        t ≡ 1₂ ↦ g s)
```

The underlying horn of a simplex:

```rzk
#def horn-restriction
  ( A : U)
  : (Δ² → A) → (Λ → A)
  := \ f t → f t
```

This provides an alternate definition of Segal types.

```rzk
#def is-local-horn-inclusion
  ( A : U)
  : U
  := is-equiv (Δ² → A) (Λ → A) (horn-restriction A)
```

Now we prove this definition is equivalent to the original one. Here, we prove
the equivalence used in [RS17, Theorem 5.5]. However, we do this by constructing
the equivalence directly, instead of using a composition of equivalences, as it
is easier to write down and it computes better (we can use refl for the
witnesses of the equivalence).

```rzk
#def compositions-are-horn-fillings
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Equiv
    ( Σ (h : hom A x z) , (hom2 A x y z f g h))
    ( (t : Δ²) → A [ Λ t ↦ horn A x y z f g t])
  :=
    ( \ hh t → (second hh) t ,
      ( ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s)) ,
          \ hh → refl) ,
        ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s)) ,
          \ hh → refl)))

#def equiv-horn-restriction
  ( A : U)
  : Equiv
    ( Δ² → A)
    ( Σ ( k : Λ → A) ,
        ( Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
            ( hom2 A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
              ( h))))
  :=
    ( \ k →
      ( \ t → k t ,
        ( \ t → k (t , t) ,
          \ t → k t)) ,
      ( ( \ khh t → (second (second khh)) t ,
          \ k → refl) ,
        ( \ khh t → (second (second khh)) t ,
          \ k → refl)))
```

```rzk title="RS17, Theorem 5.5 (the hard direction)"
#def equiv-horn-restriction-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : Equiv (Δ² → A) (Λ → A)
  :=
    equiv-comp
      ( Δ² → A)
      ( Σ ( k : Λ → A) ,
          ( Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
                ( h))))
      ( Λ → A)
      ( equiv-horn-restriction A)
      ( total-space-projection
        ( Λ → A)
        ( \ k →
          Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
            ( hom2 A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
              ( h))) ,
      ( is-equiv-projection-contractible-fibers
          ( Λ → A)
          ( \ k →
            Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
                ( h)))
          ( \ k →
            is-segal-A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t)))))
```

We verify that the mapping in `#!rzk Segal-equiv-horn-restriction A is-segal-A`
is exactly `#!rzk horn-restriction A`.

```rzk
#def test-equiv-horn-restriction-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : (first (equiv-horn-restriction-is-segal A is-segal-A)) = (horn-restriction A)
  := refl
```

```rzk title="Segal types are types that are local at the horn inclusion"
#def is-local-horn-inclusion-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : is-local-horn-inclusion A
  := second (equiv-horn-restriction-is-segal A is-segal-A)
```

```rzk title="Types that are local at the horn inclusion are Segal types"
#def is-segal-is-local-horn-inclusion
  ( A : U)
  ( is-local-horn-inclusion-A : is-local-horn-inclusion A)
  : is-segal A
  :=
    \ x y z f g →
    contractible-fibers-is-equiv-projection
      ( Λ → A)
      ( \ k →
        Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
          ( hom2 A
            ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
            ( \ t → k (t , 0₂))
            ( \ t → k (1₂ , t))
            ( h)))
      ( second
        ( equiv-comp
          ( Σ ( k : Λ → A) ,
            Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂))
                ( \ t → k (1₂ , t))
                ( h)))
          ( Δ² → A)
          ( Λ  → A)
          ( inv-equiv
            ( Δ² → A)
            ( Σ ( k : Λ → A) ,
              Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
                ( hom2 A
                  ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                  ( \ t → k (t , 0₂))
                  ( \ t → k (1₂ , t))
                  ( h)))
            ( equiv-horn-restriction A))
          ( horn-restriction A , is-local-horn-inclusion-A)))
    ( horn A x y z f g)
```

We have now proven that both notions of Segal types are logically equivalent.

```rzk title="RS17, Theorem 5.5"
#def is-segal-iff-is-local-horn-inclusion
  ( A : U)
  : iff ( is-segal A) (is-local-horn-inclusion A)
  := ( is-local-horn-inclusion-is-segal A , is-segal-is-local-horn-inclusion A)
```

## Segal function and extension types

Using the new characterization of Segal types, we can show that the type of
functions or extensions into a family of Segal types is again a Segal type. For
instance if $X$ is a type and $A : X → U$ is such that $A x$ is a Segal type for
all $x$ then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(i)"
#def is-segal-function-type uses (funext)
  ( X : U)
  ( A : X → U)
  ( fiberwise-is-segal-A : (x : X) → is-local-horn-inclusion (A x))
  : is-local-horn-inclusion ((x : X) → A x)
  :=
    is-equiv-triple-comp
      ( Δ² → ((x : X) → A x))
      ( (x : X) → Δ² → A x)
      ( (x : X) → Λ → A x)
      ( Λ → ((x : X) → A x))
      ( \ g x t → g t x) -- first equivalence
      ( second (flip-ext-fun
        ( 2 × 2)
        ( Δ²)
        ( \ t → BOT)
        ( X)
        (\ t → A)
        (\ t → recBOT)))
      ( \ h x t → h x t) -- second equivalence
      ( second (equiv-function-equiv-family
        ( funext)
        ( X)
        ( \ x → (Δ² → A x))
        ( \ x → (Λ → A x))
        ( \ x → (horn-restriction (A x) , fiberwise-is-segal-A x))))
      ( \ h t x → (h x) t) -- third equivalence
      ( second (flip-ext-fun-inv
        ( 2 × 2)
        ( Λ)
        ( \ t → BOT)
        ( X)
        ( \ t → A)
        ( \ t → recBOT)))
```

If $X$ is a shape and $A : X → U$ is such that $A x$ is a Segal type for all $x$
then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(ii)"
#def is-segal-extension-type' uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( fiberwise-is-segal-A : (s : ψ) → is-local-horn-inclusion (A s))
  : is-local-horn-inclusion ((s : ψ) → A s)
  :=
    is-equiv-triple-comp
      ( Δ² → (s : ψ) → A s)
      ( (s : ψ) → Δ² → A s)
      ( (s : ψ) → Λ → A s)
      ( Λ → (s : ψ) → A s)
      ( \ g s t → g t s)  -- first equivalence
      ( second
        ( fubini
          ( 2 × 2)
          ( I)
          ( Δ²)
          ( \ t → BOT)
          ( ψ)
          ( \ s → BOT)
          ( \ t s → A s)
          ( \ u → recBOT)))
      ( \ h s t → h s t) -- second equivalence
      ( second (equiv-extension-equiv-family extext I ψ
        ( \ s → Δ² → A s)
        ( \ s → Λ → A s)
        ( \ s → (horn-restriction (A s) , fiberwise-is-segal-A s))))
      ( \ h t s → (h s) t) -- third equivalence
      ( second
        ( fubini
          ( I)
          ( 2 × 2)
          ( ψ)
          ( \ s → BOT)
          ( Λ)
          ( \ t → BOT)
          ( \ s t → A s)
          ( \ u → recBOT)))

#def is-segal-extension-type uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( fiberwise-is-segal-A : (s : ψ) → is-segal (A s))
  : is-segal ((s : ψ) → A s)
  :=
    is-segal-is-local-horn-inclusion
      ( (s : ψ) → A s)
      ( is-segal-extension-type'
        ( I) (ψ) (A)
        ( \ s → is-local-horn-inclusion-is-segal (A s) (fiberwise-is-segal-A s)))
```

In particular, the arrow type of a Segal type is Segal. First, we define the
arrow type:

```rzk
#def arr
  ( A : U)
  : U
  := Δ¹ → A
```

For later use, an equivalent characterization of the arrow type.

```rzk
#def arr-Σ-hom
  ( A : U)
  : ( arr A) → (Σ (x : A) , (Σ (y : A) , hom A x y))
  := \ f → (f 0₂ , (f 1₂ , f))

#def is-equiv-arr-Σ-hom
  ( A : U)
  : is-equiv (arr A) (Σ (x : A) , (Σ (y : A) , hom A x y)) (arr-Σ-hom A)
  :=
    ( ( \ (x , (y , f)) → f , \ f → refl) ,
      ( \ (x , (y , f)) → f , \ xyf → refl))

#def equiv-arr-Σ-hom
  ( A : U)
  : Equiv (arr A) (Σ (x : A) , (Σ (y : A) , hom A x y))
  := ( arr-Σ-hom A , is-equiv-arr-Σ-hom A)
```

```rzk title="RS17, Corollary 5.6(ii), special case for locality at the horn inclusion"
#def is-local-horn-inclusion-arr uses (extext)
  ( A : U)
  ( is-segal-A : is-local-horn-inclusion A)
  : is-local-horn-inclusion (arr A)
  :=
    is-segal-extension-type'
      ( 2)
      ( Δ¹)
      ( \ _ → A)
      ( \ _ → is-segal-A)
```

```rzk title="RS17, Corollary 5.6(ii), special case for the Segal condition"
#def is-segal-arr uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  : is-segal (arr A)
  :=
    is-segal-extension-type
      ( 2)
      ( Δ¹)
      ( \ _ → A)
      ( \ _ → is-segal-A)
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
#def id-hom
  ( A : U)
  ( x : A)
  : hom A x x
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
#def comp-id-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x y y f (id-hom A y) f
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
#def id-comp-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x x y (id-hom A x) f f
  := \ (t , s) → f s
```

In a Segal type, where composition is unique, it follows that composition with
an identity arrow recovers the original arrow. Thus, an identity axiom was not
needed in the definition of Segal types.

```rzk title="If A is Segal then the right unit law holds"
#def comp-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  :=
    uniqueness-comp-is-segal
      ( A)
      ( is-segal-A)
      ( x) (y) (y)
      ( f)
      ( id-hom A y)
      ( f)
      ( comp-id-witness A x y f)
```

```rzk title="If A is Segal then the left unit law holds"
#def id-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (comp-is-segal A is-segal-A x x y (id-hom A x) f) =_{hom A x y} f
  :=
    uniqueness-comp-is-segal
      ( A)
      ( is-segal-A)
      ( x) (x) (y)
      ( id-hom A x)
      ( f)
      ( f)
      ( id-comp-witness A x y f)
```

## Associativity

We now prove that composition in a Segal type is associative, by using the fact
that the type of arrows in a Segal type is itself a Segal type.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,170 160,170" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">•</text>
  <text x="170" y="30">•</text>
  <text x="170" y="170">•</text>
  <text x="30" y="170" fill="red">•</text>
</svg>

```rzk
#def unfolding-square
  ( A : U)
  ( triangle : Δ² → A)
  : Δ¹×Δ¹ → A
  :=
    \ (t , s) →
    recOR
      ( t ≤ s ↦ triangle (s , t) ,
        s ≤ t ↦ triangle (t , s))
```

For use in the proof of associativity:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="45,170 160,170" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110" transform="rotate(45, 90, 110)" fill="red">comp-is-segal</text>
  <text x="100" y="190">g</text>
  <text x="15" y="100">f</text>
</svg>

```rzk
#def witness-square-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Δ¹×Δ¹ → A
  := unfolding-square A (witness-comp-is-segal A is-segal-A x y z f g)
```

The `#!rzk witness-square-comp-is-segal` as an arrow in the arrow type:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
</svg>

```rzk
#def arr-in-arr-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom (arr A) f g
  := \ t s → witness-square-comp-is-segal A is-segal-A x y z f g (t , s)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="40,170 160,170" stroke="lightgrey" stroke-width="3"></polyline>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 100 L 160 100 L 100 130 Z"></path>
  <polyline points="100,70 100,190" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,105 105,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,105 95,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="155,35 105,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,35 95,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="155,175 105,195" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,175 95,195" stroke="lightgrey" stroke-width="3"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="30" y="170">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="60">y</text>
  <text x="100" y="200">z</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="150">h</text>
</svg>

```rzk
#def witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 (arr A) f g h
      (arr-in-arr-is-segal A is-segal-A w x y f g)
      (arr-in-arr-is-segal A is-segal-A x y z g h)
      (comp-is-segal (arr A) (is-segal-arr A is-segal-A)
      f g h
      (arr-in-arr-is-segal A is-segal-A w x y f g)
      (arr-in-arr-is-segal A is-segal-A x y z g h))
  :=
    witness-comp-is-segal
      ( arr A)
      ( is-segal-arr A is-segal-A)
      f g h
      ( arr-in-arr-is-segal A is-segal-A w x y f g)
      ( arr-in-arr-is-segal A is-segal-A x y z g h)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

The `#!rzk witness-associative-is-segal` curries to define a diagram
$Δ²×Δ¹ → A$. The `#!rzk tetrahedron-associative-is-segal` is extracted via the
middle-simplex map $((t , s) , r) ↦ ((t , r) , s)$ from $Δ³$ to $Δ²×Δ¹$.

```rzk
#def tetrahedron-associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : Δ³ → A
  :=
    \ ((t , s) , r) →
    (witness-asociative-is-segal A is-segal-A w x y z f g h) (t , r) s
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

The diagonal composite of three arrows extracted from the
`#!rzk tetrahedron-associative-is-segal`.

```rzk
#def triple-comp-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom A w z
  :=
    \ t →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , t) , t)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 40 35 L 165 35 L 165 160 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 40 L 160 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def left-witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w y z
    (comp-is-segal A is-segal-A w x y f g)
    h
    (triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    \ (t , s) →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , t) , s)
```

The front face:

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 155 35 L 100 185 Z"></path>
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 165 40 L 165 165 L 115 185 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def right-witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w x z
    ( f)
    ( comp-is-segal A is-segal-A x y z g h)
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    \ (t , s) →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , s) , s)
```

```rzk
#def left-associativity-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h) =
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    uniqueness-comp-is-segal
      A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h
      ( triple-comp-is-segal A is-segal-A w x y z f g h)
      ( left-witness-asociative-is-segal A is-segal-A w x y z f g h)

#def right-associativity-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h)) =
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    uniqueness-comp-is-segal
      ( A) (is-segal-A) (w) (x) (z) (f) (comp-is-segal A is-segal-A x y z g h)
      ( triple-comp-is-segal A is-segal-A w x y z f g h)
      ( right-witness-asociative-is-segal A is-segal-A w x y z f g h)

#def associativity-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h) =
    ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
  :=
    zig-zag-concat
    ( hom A w z)
    ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
    ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
    ( left-associativity-is-segal A is-segal-A w x y z f g h)
    ( right-associativity-is-segal A is-segal-A w x y z f g h)


#def postcomp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (z : A) → (hom A z x) → (hom A z y)
  := \ z g → (comp-is-segal A is-segal-A z x y g f)

#def precomp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (z : A) → (hom A y z) → (hom A x z)
  := \ z → comp-is-segal A is-segal-A x y z f
```

## Homotopies

We may define a "homotopy" to be a path between parallel arrows. In a Segal
type, homotopies are equivalent to terms in hom2 types involving an identity
arrow.

```rzk
#def map-hom2-homotopy
  ( A : U)
  ( x y : A)
  ( f g : hom A x y)
  : (f = g) → (hom2 A x x y (id-hom A x) f g)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' → (hom2 A x x y (id-hom A x) f g'))
      ( id-comp-witness A x y f)
      ( g)

#def map-total-hom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : ( Σ (g : hom A x y) , (f = g)) →
    ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
  := \ (g , p) → (g , map-hom2-homotopy A x y f g p)

#def is-equiv-map-total-hom2-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
      ( map-total-hom2-homotopy A x y f)
  :=
    is-equiv-are-contr
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
      ( is-contr-based-paths (hom A x y) f)
      ( is-segal-A x x y (id-hom A x) f)
      ( map-total-hom2-homotopy A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def equiv-homotopy-hom2-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f h : hom A x y)
  : Equiv (f = h) (hom2 A x x y (id-hom A x) f h)
  :=
    ( ( map-hom2-homotopy A x y f h) ,
      ( total-equiv-family-of-equiv
        ( hom A x y)
        ( \ k → (f = k))
        ( \ k → (hom2 A x x y (id-hom A x) f k))
        ( map-hom2-homotopy A x y f)
        ( is-equiv-map-total-hom2-homotopy-is-segal A is-segal-A x y f)
        ( h)))
```

A dual notion of homotopy can be defined similarly.

```rzk
#def map-hom2-homotopy'
  ( A : U)
  ( x y : A)
  ( f g : hom A x y)
  ( p : f = g)
  : (hom2 A x y y f (id-hom A y) g)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' → (hom2 A x y y f (id-hom A y) g'))
      ( comp-id-witness A x y f)
      ( g)
      ( p)

#def map-total-hom2-homotopy'
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : ( Σ (g : hom A x y) , (f = g)) →
    ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
  := \ (g , p) → (g , map-hom2-homotopy' A x y f g p)

#def is-equiv-map-total-hom2-homotopy'-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
      ( map-total-hom2-homotopy' A x y f)
  :=
    is-equiv-are-contr
      ( Σ (g : hom A x y) , (f = g))
      ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
      ( is-contr-based-paths (hom A x y) f)
      ( is-segal-A x y y f (id-hom A y))
      ( map-total-hom2-homotopy' A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def equiv-homotopy-hom2'-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f h : hom A x y)
  : Equiv (f = h) (hom2 A x y y f (id-hom A y) h)
  :=
    ( ( map-hom2-homotopy' A x y f h) ,
      ( total-equiv-family-of-equiv
        ( hom A x y)
        ( \ k → (f = k))
        ( \ k → (hom2 A x y y f (id-hom A y) k))
        ( map-hom2-homotopy' A x y f)
        ( is-equiv-map-total-hom2-homotopy'-is-segal A is-segal-A x y f)
        ( h)))
```

More generally, a homotopy between a composite and another map is equivalent to
the data provided by a commutative triangle with that boundary.

```rzk
#def map-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( p : (comp-is-segal A is-segal-A x y z f g) = h)
  : ( hom2 A x y z f g h)
  :=
    ind-path
      ( hom A x z)
      ( comp-is-segal A is-segal-A x y z f g)
      ( \ h' p' → hom2 A x y z f g h')
      ( witness-comp-is-segal A is-segal-A x y z f g)
      ( h)
      ( p)

#def map-total-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h) →
    ( Σ (h : hom A x z) , (hom2 A x y z f g h))
  := \ (h , p) → (h , map-hom2-eq-is-segal A is-segal-A x y z f g h p)

#def is-equiv-map-total-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : is-equiv
      ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h)
      ( Σ (h : hom A x z) , (hom2 A x y z f g h))
      ( map-total-hom2-eq-is-segal A is-segal-A x y z f g)
  :=
    is-equiv-are-contr
      ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h)
      ( Σ (h : hom A x z) , (hom2 A x y z f g h))
      ( is-contr-based-paths (hom A x z) (comp-is-segal A is-segal-A x y z f g))
      ( is-segal-A x y z f g)
      ( map-total-hom2-eq-is-segal A is-segal-A x y z f g)
```

```rzk title="RS17, Proposition 5.12"
#def extensionality-hom2-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( k : hom A x z)
  : Equiv ((comp-is-segal A is-segal-A x y z f g) = k) (hom2 A x y z f g k)
  :=
    ( ( map-hom2-eq-is-segal A is-segal-A x y z f g k) ,
      ( total-equiv-family-of-equiv
        ( hom A x z)
        ( \ m → (comp-is-segal A is-segal-A x y z f g) = m)
        ( hom2 A x y z f g)
        ( map-hom2-eq-is-segal A is-segal-A x y z f g)
        ( is-equiv-map-total-hom2-eq-is-segal A is-segal-A x y z f g)
        ( k)))
```

Homotopies form a congruence, meaning that homotopies are respected by
composition:

```rzk title="RS17, Proposition 5.13"
#def congruence-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h k : hom A y z)
  ( p : f = g)
  ( q : h = k)
  : ( comp-is-segal A is-segal-A x y z f h) = (comp-is-segal A is-segal-A x y z g k)
  :=
    ind-path
      ( hom A y z)
      ( h)
      ( \ k' q' →
        ( comp-is-segal A is-segal-A x y z f h) =
        ( comp-is-segal A is-segal-A x y z g k'))
      ( ind-path
        ( hom A x y)
        ( f)
        ( \ g' p' →
          ( comp-is-segal A is-segal-A x y z f h) =
          ( comp-is-segal A is-segal-A x y z g' h))
        ( refl)
        ( g)
        ( p))
      ( k)
      ( q)
```

As a special case of the above:

```rzk
#def postwhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h : hom A y z)
  ( p : f = g)
  : ( comp-is-segal A is-segal-A x y z f h) = (comp-is-segal A is-segal-A x y z g h)
  := congruence-homotopy-is-segal A is-segal-A x y z f g h h p refl
```

As a special case of the above:

```rzk
#def prewhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y : A)
  ( k : hom A w x)
  ( f g : hom A x y)
  ( p : f = g)
  : ( comp-is-segal A is-segal-A w x y k f) = (comp-is-segal A is-segal-A w x y k g)
  := congruence-homotopy-is-segal A is-segal-A w x y k k f g refl p
```

```rzk title="RS17, Proposition 5.14(a)"
#def compute-postwhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h : hom A y z)
  ( p : f = g)
  : ( postwhisker-homotopy-is-segal A is-segal-A x y z f g h p) =
    ( ap (hom A x y) (hom A x z) f g (\ k → comp-is-segal A is-segal-A x y z k h) p)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' →
        ( postwhisker-homotopy-is-segal A is-segal-A x y z f g' h p') =
        ( ap
          (hom A x y) (hom A x z)
          (f) (g') (\ k → comp-is-segal A is-segal-A x y z k h) (p')))
      ( refl)
      ( g)
      ( p)
```

```rzk title="RS17, Proposition 5.14(b)"
#def prewhisker-homotopy-is-ap-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y : A)
  ( k : hom A w x)
  ( f g : hom A x y)
  ( p : f = g)
  : ( prewhisker-homotopy-is-segal A is-segal-A w x y k f g p) =
    ( ap (hom A x y) (hom A w y) f g (comp-is-segal A is-segal-A w x y k) p)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' →
        ( prewhisker-homotopy-is-segal A is-segal-A w x y k f g' p') =
        ( ap (hom A x y) (hom A w y) f g' (comp-is-segal A is-segal-A w x y k) p'))
      ( refl)
      ( g)
      ( p)

#section is-segal-Unit

#def is-contr-Unit : is-contr Unit := (unit , \ _ → refl)

#def is-contr-Δ²→Unit uses (extext)
  : is-contr (Δ² → Unit)
  :=
    ( \ _ → unit ,
      \ k →
      eq-ext-htpy extext
        ( 2 × 2) Δ² (\ _ → BOT)
        ( \ _ → Unit) (\ _ → recBOT)
        ( \ _ → unit) k
        ( \ _ → refl))

#def is-segal-Unit uses (extext)
  : is-segal Unit
  :=
    \ x y z f g →
    is-contr-is-retract-of-is-contr
      ( Σ (h : hom Unit x z) , (hom2 Unit x y z f g h))
      ( Δ² → Unit)
      ( ( \ (_ , k) → k) ,
        ( \ k → ((\ t → k (t , t)) , k) , \ _ → refl))
      ( is-contr-Δ²→Unit)

#end is-segal-Unit
```

<!-- Definitions for the SVG images above -->
<svg width="0" height="0">
  <defs>
    <style data-bx-fonts="Noto Serif">@import url(https://fonts.googleapis.com/css2?family=Noto+Serif&display=swap);</style>
    <marker
      id="arrow-blue"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="blue" fill="blue" />
    </marker>
    <marker
      id="arrow-red"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="red" fill="red" />
    </marker>
    <marker
      id="arrow-grey"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="grey" fill="grey" />
    </marker>
    <marker
      id="arrow"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="black" fill="black" />
    </marker>
  </defs>
  <style>
    text, textPath {
      font-family: Noto Serif;
      font-size: 20px;
      dominant-baseline: middle;
      text-anchor: middle;
    }
  </style>
</svg>
