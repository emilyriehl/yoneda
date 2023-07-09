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
- `hott/total-space.md` — We rely on `is-equiv-projection-contractible-fibers`
  and `total-space-projection` in the proof of Theorem 5.5.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension
  extensionality.

## Hom types

Extension types are used ∂to define the type of arrows between fixed terms:

<svg style="float: right" viewBox="0 0 200 60" width="150" height="60">
  <polyline points="40,30 160,30" stroke="blue" stroke-width="3" marker-end="url(#arrow-blue)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
</svg>

```rzk title="RS17, Definition 5.1"
-- The type of arrows in A from x to y.
#def hom
  (A : U)
  (x y : A)
  : U
  := (t : Δ¹) -> A [
    t === 0_2 |-> x ,    -- * the left endpoint is exactly x
    t === 1_2 |-> y     -- * the right endpoint is exactly y
  ]
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
-- the type of commutative triangles in A
#def hom2
  (A : U)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  : U
  := { (t1 , t2) : Δ² } -> A [
    t2 === 0_2 |-> f t1 ,        -- * the top edge is exactly `f`,
    t1 === 1_2 |-> g t2 ,        -- * the right edge is exactly `g`, and
    t2 === t1 |-> h t2         -- * the diagonal is exactly `h`
  ]
```

## The Segal condition

A type is Segal if every composable pair of arrows has a unique composite. Note
this is a considerable simplification of the usual Segal condition, which also
requires homotopical uniqueness of higher-order composites.

```rzk title="RS17, Definition 5.3"
#def is-segal
  (A : U)
  : U
  := (x : A) -> (y : A) -> (z : A) ->
      (f : hom A x y) -> (g : hom A y z) ->
      is-contr ( Σ (h : hom A x z) , hom2 A x y z f g h)
```

Segal types have a composition functor and witnesses to the composition
relation. Composition is written in diagrammatic order to match the order of
arguments in `is-segal`.

```rzk
#def Segal-comp
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : hom A x z
  := first (first (is-segal-A x y z f g))

#def Segal-comp-witness
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : hom2 A x y z f g (Segal-comp A is-segal-A x y z f g)
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
  <text x="90" y="310" transform="rotate(45, 90, 310)" fill="red">Segal-comp</text>
  <text x="120" y="280" fill="rgb(128,0,0)" transform="rotate(45, 120, 280)" style="font-size: 10px">Segal-comp-witness</text>
</svg>

```rzk
#def Segal-comp-uniqueness
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  (alpha : hom2 A x y z f g h)
  : (Segal-comp A is-segal-A x y z f g) = h
  := first-path-Σ
      (hom A x z)
      (\ k -> hom2 A x y z f g k)
      (Segal-comp A is-segal-A x y z f g ,
        Segal-comp-witness A is-segal-A x y z f g)
      (h , alpha)
      (contracting-htpy
        (Σ (k : hom A x z) , hom2 A x y z f g k)
        (is-segal-A x y z f g)
        (h , alpha))
```

## Characterizing Segal types

Our aim is to prove that a type is Segal if and only if the `horn-restriction`
map, defined below, is an equivalence.

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
  (A : U)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : Λ -> A
  :=
    \ (t , s) ->
    recOR
    ( s === 0_2 |-> f t ,
      t === 1_2 |-> g s)
```

The underlying horn of a simplex:

```rzk
#def horn-restriction (A : U)
  : (Δ² -> A) -> (Λ -> A)
  := \ f t -> f t
```

This provides an alternate definition of Segal types.

```rzk
#def is-local-horn-inclusion (A : U) : U
  := is-equiv (Δ² -> A) (Λ -> A) (horn-restriction A)
```

Now we prove this definition is equivalent to the original one. Here, we prove
the equivalence used in [RS17, Theorem 5.5]. However, we do this by constructing
the equivalence directly, instead of using a composition of equivalences, as it
is easier to write down and it computes better (we can use refl for the
witnesses of the equivalence).

```rzk
#def compositions-are-horn-fillings
  (A : U)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : Equiv
    ( Σ (h : hom A x z) , hom2 A x y z f g h)
    ( {t : 2 * 2 | Δ² t } -> A [ Λ t |-> horn A x y z f g t ])
  :=
    ( \ hh -> \{t : 2 * 2 | Δ² t} -> (second hh) t ,
      ( ( \ k -> (\ (t : 2) -> k (t , t) , \ (t , s) -> k (t , s)) ,
          \ hh -> refl) ,
        ( \ k -> (\ (t : 2) -> k (t , t) , \ (t , s) -> k (t , s)) ,
          \ hh -> refl)))

#def equiv-horn-restriction
  (A : U)
  : Equiv
    ( Δ² -> A)
    ( Σ ( k : Λ -> A) ,
        ( Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
            ( hom2 A
              ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
              ( \ t -> k (t , 0_2)) (\ t -> k (1_2 , t))
              ( h))))
  :=
    ( \ k ->
      ( \ {t : 2 * 2 | Λ t} -> k t ,
        ( \ (t : 2) -> k (t , t) ,
          \ {t : 2 * 2 | Δ² t} -> k t)) ,
      ( ( \ khh -> \  {t : 2 * 2 | Δ² t} -> (second (second khh)) t ,
          \ k -> refl_{k}) ,
        ( \ khh -> \  {t : 2 * 2 | Δ² t} -> (second (second khh)) t ,
          \ k -> refl_{k})))
```

```rzk title="RS17, Theorem 5.5 (the hard direction)"
#def Segal-equiv-horn-restriction
  (A : U)
  (is-segal-A : is-segal A)
  : Equiv (Δ² -> A) (Λ -> A)
  :=
    comp-equiv
      ( Δ² -> A)
      ( Σ ( k : Λ -> A) ,
          ( Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
              ( hom2 A
                ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                ( \ t -> k (t , 0_2)) (\ t -> k (1_2 , t))
                ( h))))
      ( Λ -> A)
      ( equiv-horn-restriction A)
      ( total-space-projection
        ( Λ -> A )
        ( \ k ->
          Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
            ( hom2 A
              ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
              ( \ t -> k (t , 0_2)) (\ t -> k (1_2 , t))
              ( h))) ,
      ( is-equiv-projection-contractible-fibers
          ( Λ -> A)
          ( \ k ->
            Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
              ( hom2 A
                ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                ( \ t -> k (t , 0_2)) (\ t -> k (1_2 , t))
                ( h)))
          ( \ k ->
            is-segal-A
              ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
              ( \ t -> k (t , 0_2)) (\ t -> k (1_2 , t)))))

-- Verify that the mapping in (Segal-equiv-horn-restriction A is-segal-A)
-- is exactly (horn-restriction A)
#def Segal-equiv-horn-restriction-test
  ( A : U)
  ( is-segal-A : is-segal A)
  : (first (Segal-equiv-horn-restriction A is-segal-A)) = (horn-restriction A)
  := refl
```

Segal types are types that are local at the horn inclusion:

```rzk
#def is-local-horn-inclusion-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : is-local-horn-inclusion A
  := second (Segal-equiv-horn-restriction A is-segal-A)
```

Types that are local at the horn inclusion are Segal types:

```rzk
#def is-segal-is-local-horn-inclusion
  ( A : U)
  ( is-local-horn-inclusion-A : is-local-horn-inclusion A)
  : is-segal A
  :=
    \ x y z f g ->
    contractible-fibers-is-equiv-projection
      (  Λ -> A )
      ( \ k ->
        Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
          ( hom2 A
            ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
            ( \ t -> k (t , 0_2))
            ( \ t -> k (1_2 , t))
            ( h)))
      ( second
        ( comp-equiv
          ( Σ ( k : Λ -> A ) ,
            Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
              ( hom2 A
                ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                ( \ t -> k (t , 0_2))
                ( \ t -> k (1_2 , t))
                ( h)))
          (  {t : 2 * 2 | Δ² t} -> A )
          (  {t : 2 * 2 | Λ t} -> A )
          ( inv-equiv
            (  {t : 2 * 2 | Δ² t} -> A )
            ( Σ ( k :  {t : 2 * 2 | Λ t} -> A ) ,
              Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
                ( hom2 A
                  ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                  ( \ t -> k (t , 0_2))
                  ( \ t -> k (1_2 , t))
                  ( h)))
            ( equiv-horn-restriction A))
          ( horn-restriction A , is-local-horn-inclusion-A)))
    ( horn A x y z f g)
```

We have now proven that both notions of Segal types are logically equivalent.

```rzk title="RS17, Theorem 5.5"
#def is-segal-iff-is-local-horn-inclusion
  (A : U)
  : iff (is-segal A) (is-local-horn-inclusion A)
  := (is-local-horn-inclusion-is-segal A , is-segal-is-local-horn-inclusion A)
```

## Segal function and extension types

Using the new characterization of Segal types, we can show that the type of
functions or extensions into a family of Segal types is again a Segal type. For
instance if $X$ is a type and $A : X → U$ is such that $A x$ is a Segal type for
all $x$ then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(i)"
#def Segal-function-types
  (funext : FunExt)
  (X : U)
  (A : (_ : X) -> U)
  (fiberwise-is-segal-A : (x : X) -> is-local-horn-inclusion (A x))
  : is-local-horn-inclusion ((x : X) -> A x)
  := triple-compose-is-equiv
       (Δ² -> ((x : X) -> A x) )
       ((x : X) -> Δ² -> A x )
       ((x : X) -> Λ -> A x )
       (Λ -> ((x : X) -> A x) )
        (\ g -> \ x -> \ {t : 2 * 2 | Δ² t} -> g t x) -- first equivalence
            (second (flip-ext-fun
              (2 * 2)
              Δ² (\{t : 2 * 2 | Δ² t} -> BOT)
              X
              (\ {t : 2 * 2 | Δ² t} -> A)
              (\ {t : 2 * 2 | BOT} -> recBOT)))
        (\ h -> \ x -> \ {t : 2 * 2 | Λ t} -> h x t) -- second equivalence
          (second (function-equiv-fibered-equiv
              funext
              X
              (\ x -> {t : 2 * 2 | Δ² t} -> A x )
              (\ x -> {t : 2 * 2 | Λ t} -> A x )
              (\ x -> (horn-restriction (A x) , fiberwise-is-segal-A x))))
        (\ h -> \{t : 2 * 2 | Λ t} -> \ x -> (h x) t) -- third equivalence
          (second(flip-ext-fun-inv
            (2 * 2)
            Λ (\ {t : 2 * 2 | Λ t} -> BOT)
            X
            (\ {t : 2 * 2 | Λ t} -> A)
            (\ {t : 2 * 2 | BOT} -> recBOT)))
```

If $X$ is a shape and $A : X → U$ is such that $A x$ is a Segal type for all $x$
then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(ii)"
#def Segal-extension-types
  (extext : ExtExt)
  (I : CUBE)
  (ψ : (s : I) -> TOPE)
  (A : {s : I | ψ s} -> U )
  (fiberwise-is-segal-A : {s : I | ψ s} -> is-local-horn-inclusion (A s) )
  : is-local-horn-inclusion ({s : I | ψ s} -> A s )
  := triple-compose-is-equiv
        ({t : 2 * 2 | Δ² t} -> {s : I | ψ s} -> A s  )
        ({s : I | ψ s} -> {t : 2 * 2 | Δ² t} -> A s  )
        ({s : I | ψ s} -> {t : 2 * 2 | Λ t} -> A s  )
        ({t : 2 * 2 | Λ t} -> {s : I | ψ s} -> A s  )
        (\ g -> \{s : I | ψ s} -> \{t : 2 * 2 | Δ² t} -> g t s)  -- first equivalence
            (second (fubini
              (2 * 2)
              I
              Δ²
              (\{t : 2 * 2 | Δ² t} -> BOT)
              ψ
              (\{s : I | ψ s} -> BOT)
              (\{t : 2 * 2 | Δ² t} -> \{s : I | ψ s} -> A s)
              (\{u : (2 * 2) * I | BOT} -> recBOT)))
        (\ h -> \{s : I | ψ s} -> \{t : 2 * 2 | Λ t} -> h s t) -- second equivalence
          (second (fibered-Eq-extension-Equiv extext I ψ
            (\{s : I | ψ s} -> {t : 2 * 2 | Δ² t} -> A s )
            (\{s : I | ψ s} -> {t : 2 * 2 | Λ t} -> A s )
            (\{s : I | ψ s} -> (horn-restriction (A s) , fiberwise-is-segal-A s)) ))
        (\ h -> \{t : 2 * 2 | Λ t} -> \{s : I | ψ s} -> (h s) t) -- third equivalence
          (second (fubini
            I
            (2 * 2)
            ψ
            (\{s : I | ψ s} -> BOT)
            Λ
            (\{t : 2 * 2 | Λ t} -> BOT)
            (\{s : I | ψ s} -> \{t : 2 * 2 | Λ t} -> A s)
            (\{u : I * (2 * 2) | BOT} -> recBOT)))
```

In particular, the arrow type of a Segal type is Segal. First, we define the
arrow type:

```rzk
#def arr
  (A : U)
  : U
  := (t : Δ¹) -> A
```

For later use, an equivalent characterization of the arrow type.

```rzk
#def Eq-arr
  (A : U)
  : Equiv (arr A) (Σ (x : A) , (Σ (y : A) , hom A x y))
  :=
    ( \ f -> (f 0_2 , (f 1_2 , f)) ,
      ( ( \ (x , (y , f)) -> f , \ f -> refl) ,
        ( \ (x , (y , f)) -> f , \ xyf -> refl)))
```

```rzk title="RS17, Corollary 5.6(ii)"
-- special case using `is-local-horn-inclusion`
#def Segal'-arrow-types
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-local-horn-inclusion A)
  : is-local-horn-inclusion (arr A)
  := Segal-extension-types
        extext
        2
        Δ¹
        (\{t : 2 | Δ¹ t} -> A)
        (\{t : 2 | Δ¹ t} -> is-segal-A)

-- special case using `is-segal`
#def Segal-arrow-types
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  : is-segal (arr A)
  := is-segal-is-local-horn-inclusion (arr A)
      (Segal-extension-types
        extext
        2
        Δ¹
        (\{t : 2 | Δ¹ t} -> A)
        (\{t : 2 | Δ¹ t} -> (is-local-horn-inclusion-is-segal A is-segal-A)))
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
-- all types have identity arrows
#def id-arr
  (A : U)
  (x : A)
  : hom A x x
  := \{t : 2 | Δ¹ t} -> x
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
-- the right unit law for identity
#def comp-id-witness
  (A : U)
  (x y : A)
  (f : hom A x y)
  : hom2 A x y y f (id-arr A y) f
  := \{ (t , s) : 2 * 2 | Δ² (t , s)} -> f t
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
-- the left unit law for identity
#def id-comp-witness
  (A : U)
  (x y : A)
  (f : hom A x y)
  : hom2 A x x y (id-arr A x) f f
  := \{ (t , s) : 2 * 2 | Δ² (t , s)} -> f s
```

In a Segal type, where composition is unique, it follows that composition with
an identity arrow recovers the original arrow. Thus, an identity axiom was not
needed in the definition of Segal types.

```rzk
-- If A is Segal then the right unit law holds
#def Segal-comp-id
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : (Segal-comp A is-segal-A x y y f (id-arr A y)) =_{hom A x y} f
  := Segal-comp-uniqueness
      A
      is-segal-A
      x y y
      f
      (id-arr A y)
      f
      (comp-id-witness A x y f)

-- If A is Segal then the left unit law holds
#def Segal-id-comp
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : (Segal-comp A is-segal-A x x y (id-arr A x) f) =_{hom A x y} f
  := Segal-comp-uniqueness
      A
      is-segal-A
      x x y
      (id-arr A x)
      f
      f
      (id-comp-witness A x y f)
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
  (A : U)
  (triangle : Δ² -> A)
  : Δ¹×Δ¹ -> A
  := \ (t , s) ->                   -- two copies of the triangle along the common diagonal edge.
    recOR (t <= s |-> triangle (s , t) ,
        s <= t |-> triangle (t , s))
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
  <text x="90" y="110" transform="rotate(45, 90, 110)" fill="red">Segal-comp</text>
  <text x="100" y="190">g</text>
  <text x="15" y="100">f</text>
</svg>

```rzk
#def Segal-comp-witness-square
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : Δ¹×Δ¹ -> A
  := unfolding-square A (Segal-comp-witness A is-segal-A x y z f g)
```

The `Segal-comp-witness-square` as an arrow in the arrow type:

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
#def Segal-arr-in-arr
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : hom (arr A) f g
  := \ t -> \ s -> (Segal-comp-witness-square A is-segal-A x y z f g) (t , s)
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
#def Segal-associativity-witness
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : hom2 (arr A) f g h
      (Segal-arr-in-arr A is-segal-A w x y f g)
      (Segal-arr-in-arr A is-segal-A x y z g h)
      (Segal-comp (arr A) (Segal-arrow-types extext A is-segal-A)
      f g h
      (Segal-arr-in-arr A is-segal-A w x y f g)
      (Segal-arr-in-arr A is-segal-A x y z g h))
  := (Segal-comp-witness (arr A) (Segal-arrow-types extext A is-segal-A)
      f g h
      (Segal-arr-in-arr A is-segal-A w x y f g)
      (Segal-arr-in-arr A is-segal-A x y z g h))
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

The `Segal-associativity-witness` curries to define a diagram $Δ²×Δ¹ → A$. The
`Segal-associativity-tetrahedron` is extracted via the middle-simplex map
$((t , s) , r) ↦ ((t , r) , s)$ from $Δ³$ to $Δ²×Δ¹$.

```rzk
#def Segal-associativity-tetrahedron
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : Δ³ -> A
  := \ ((t , s) , r) ->
    (Segal-associativity-witness extext A is-segal-A w x y z f g h) (t , r) s
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
`Segal-associativity-tetrahedron`.

```rzk
#def Segal-triple-composite
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : hom A w z
  :=
    \ t ->
    ( Segal-associativity-tetrahedron extext A is-segal-A w x y z f g h)
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
#def Segal-left-associativity-witness
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : hom2 A w y z
    (Segal-comp A is-segal-A w x y f g)
    h
    (Segal-triple-composite extext A is-segal-A w x y z f g h)
  := \ (t , s) ->
    (Segal-associativity-tetrahedron extext A is-segal-A w x y z f g h) ((t , t) , s)
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
#def Segal-right-associativity-witness
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : hom2 A w x z
    f
    (Segal-comp A is-segal-A x y z g h)
    (Segal-triple-composite extext A is-segal-A w x y z f g h)
  :=
    \ (t , s) ->
    ( Segal-associativity-tetrahedron extext A is-segal-A w x y z f g h)
      ((t , s) , s)
```

```rzk
#def Segal-left-associativity
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : (Segal-comp A is-segal-A w y z (Segal-comp A is-segal-A w x y f g) h) =
      (Segal-triple-composite extext A is-segal-A w x y z f g h)
  := Segal-comp-uniqueness
        A is-segal-A w y z (Segal-comp A is-segal-A w x y f g) h
        (Segal-triple-composite extext A is-segal-A w x y z f g h)
        (Segal-left-associativity-witness extext A is-segal-A w x y z f g h)

#def Segal-right-associativity
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : (Segal-comp A is-segal-A w x z f (Segal-comp A is-segal-A x y z g h)) =
      (Segal-triple-composite extext A is-segal-A w x y z f g h)
  := Segal-comp-uniqueness
        A is-segal-A w x z f (Segal-comp A is-segal-A x y z g h)
        (Segal-triple-composite extext A is-segal-A w x y z f g h)
        (Segal-right-associativity-witness extext A is-segal-A w x y z f g h)

#def Segal-associativity
  (extext : ExtExt)
  (A : U)
  (is-segal-A : is-segal A)
  (w x y z : A)
  (f : hom A w x)
  (g : hom A x y)
  (h : hom A y z)
  : (Segal-comp A is-segal-A w y z (Segal-comp A is-segal-A w x y f g) h) =
      (Segal-comp A is-segal-A w x z f (Segal-comp A is-segal-A x y z g h))
  := zig-zag-concat (hom A w z)
      (Segal-comp A is-segal-A w y z (Segal-comp A is-segal-A w x y f g) h)
      (Segal-triple-composite extext A is-segal-A w x y z f g h)
      (Segal-comp A is-segal-A w x z f (Segal-comp A is-segal-A x y z g h))
      (Segal-left-associativity extext A is-segal-A w x y z f g h)
      (Segal-right-associativity extext A is-segal-A w x y z f g h)


#def Segal-postcomp
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : (z : A) -> (hom A z x) -> (hom A z y)
  := \ z -> \ g -> (Segal-comp A is-segal-A z x y g f)

#def Segal-precomp
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : (z : A) -> (hom A y z) -> (hom A x z)
  := \ z -> \ g -> (Segal-comp A is-segal-A x y z f g)
```

## Homotopies

We may define a "homotopy" to be a path between parallel arrows. In a Segal
type, homotopies are equivalent to terms in hom2 types involving an identity
arrow.

```rzk
#def homotopy-to-hom2
  (A : U)
  (x y : A)
  (f g : hom A x y)
  (p : f = g)
  : (hom2 A x x y (id-arr A x) f g)
  := idJ (hom A x y , f ,
          \ g' p' -> (hom2 A x x y (id-arr A x) f g') ,
          (id-comp-witness A x y f) , g , p)

#def homotopy-to-hom2-total-map
  (A : U)
  (x y : A)
  (f : hom A x y)
  : (Σ (g : hom A x y) , f = g) ->
      (Σ (g : hom A x y) , (hom2 A x x y (id-arr A x) f g))
  := \ (g , p) -> (g , homotopy-to-hom2 A x y f g p)

#def Segal-homotopy-to-hom2-total-map-is-equiv
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : is-equiv
      (Σ (g : hom A x y) , f = g)
      (Σ (g : hom A x y) , (hom2 A x x y (id-arr A x) f g))
      (homotopy-to-hom2-total-map A x y f)
  := areContr-is-equiv
        (Σ (g : hom A x y) , f = g)
        (Σ (g : hom A x y) , (hom2 A x x y (id-arr A x) f g))
        (is-contr-based-paths (hom A x y) f)
        (is-segal-A x x y (id-arr A x) f)
        (homotopy-to-hom2-total-map A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def Eq-Segal-homotopy-hom2
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f h : hom A x y)
  : Equiv (f = h) (hom2 A x x y (id-arr A x) f h)
  :=
    ( ( homotopy-to-hom2 A x y f h) ,
      ( total-equiv-family-of-equiv
        ( hom A x y)
        ( \ k -> (f = k))
        ( \ k -> (hom2 A x x y (id-arr A x) f k))
        ( homotopy-to-hom2 A x y f)
        ( Segal-homotopy-to-hom2-total-map-is-equiv A is-segal-A x y f)
        ( h)))
```

A dual notion of homotopy can be defined similarly.

```rzk
#def homotopy-to-hom2'
  (A : U)
  (x y : A)
  (f g : hom A x y)
  (p : f = g)
  : (hom2 A x y y f (id-arr A y) g)
  := idJ (hom A x y , f ,
          \ g' p' -> (hom2 A x y y f (id-arr A y) g') ,
          (comp-id-witness A x y f) , g , p)

#def homotopy-to-hom2'-total-map
  (A : U)
  (x y : A)
  (f : hom A x y)
  : (Σ (g : hom A x y) , f = g) ->
      (Σ (g : hom A x y) , (hom2 A x y y f (id-arr A y) g))
  := \ (g , p) -> (g , homotopy-to-hom2' A x y f g p)

#def Segal-homotopy-to-hom2'-total-map-is-equiv
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : is-equiv
      (Σ (g : hom A x y) , f = g)
      (Σ (g : hom A x y) , (hom2 A x y y f (id-arr A y) g))
      (homotopy-to-hom2'-total-map A x y f)
  := areContr-is-equiv
        (Σ (g : hom A x y) , f = g)
        (Σ (g : hom A x y) , (hom2 A x y y f (id-arr A y) g))
        (is-contr-based-paths (hom A x y) f)
        (is-segal-A x y y f (id-arr A y))
        (homotopy-to-hom2'-total-map A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def Eq-Segal-homotopy-hom2'
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f h : hom A x y)
  : Equiv (f = h) (hom2 A x y y f (id-arr A y) h)
  :=
    ( ( homotopy-to-hom2' A x y f h) ,
      ( total-equiv-family-of-equiv
        ( hom A x y)
        ( \ k -> (f = k))
        ( \ k -> (hom2 A x y y f (id-arr A y) k))
        ( homotopy-to-hom2' A x y f)
        ( Segal-homotopy-to-hom2'-total-map-is-equiv A is-segal-A x y f)
        ( h)))
```

More generally, a homotopy between a composite and another map is equivalent to
the data provided by a commutative triangle with that boundary.

```rzk
#def Segal-eq-to-hom2
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (h : hom A x z)
  (p : (Segal-comp A is-segal-A x y z f g) = h)
  : (hom2 A x y z f g h)
  := idJ (hom A x z , (Segal-comp A is-segal-A x y z f g) ,
          \ h' p' -> (hom2 A x y z f g h') ,
          Segal-comp-witness A is-segal-A x y z f g , h , p)

#def Segal-eq-to-hom2-total-map
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : (Σ (h : hom A x z) , (Segal-comp A is-segal-A x y z f g) = h) ->
      (Σ (h : hom A x z) , (hom2 A x y z f g h))
  := \ (h , p) -> (h , Segal-eq-to-hom2 A is-segal-A x y z f g h p)

#def Segal-eq-to-hom2-total-map-is-equiv
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  : is-equiv
      (Σ (h : hom A x z) , (Segal-comp A is-segal-A x y z f g) = h)
      (Σ (h : hom A x z) , (hom2 A x y z f g h))
      (Segal-eq-to-hom2-total-map A is-segal-A x y z f g)
  := areContr-is-equiv
        (Σ (h : hom A x z) , (Segal-comp A is-segal-A x y z f g) = h)
        (Σ (h : hom A x z) , (hom2 A x y z f g h))
        (is-contr-based-paths (hom A x z) (Segal-comp A is-segal-A x y z f g) )
        (is-segal-A x y z f g)
        (Segal-eq-to-hom2-total-map A is-segal-A x y z f g)
```

```rzk title="RS17, Proposition 5.12"
#def Eq-Segal-eq-hom2
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f : hom A x y)
  (g : hom A y z)
  (k : hom A x z)
  : Equiv ((Segal-comp A is-segal-A x y z f g) = k) (hom2 A x y z f g k)
  := (Segal-eq-to-hom2 A is-segal-A x y z f g k ,
    total-equiv-family-of-equiv (hom A x z)
      (\ m -> (Segal-comp A is-segal-A x y z f g) = m)
      (\ m -> hom2 A x y z f g m)
      (Segal-eq-to-hom2 A is-segal-A x y z f g)
      (Segal-eq-to-hom2-total-map-is-equiv A is-segal-A x y z f g)
      k)
```

Homotopies form a congruence, meaning that homotopies are respected by
composition:

```rzk title="RS17, Proposition 5.13"
#def Segal-homotopy-congruence
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f g : hom A x y)
  (h k : hom A y z)
  (p : f = g)
  (q : h = k)
  : (Segal-comp A is-segal-A x y z f h) = (Segal-comp A is-segal-A x y z g k)
  :=
    idJ
      ( ( hom A y z),
        ( h),
        ( \ k' q' ->
          (Segal-comp A is-segal-A x y z f h) =
          (Segal-comp A is-segal-A x y z g k')),
        ( idJ
          ( ( hom A x y ),
            ( f),
            ( \ g' p' ->
              (Segal-comp A is-segal-A x y z f h) =
              (Segal-comp A is-segal-A x y z g' h)),
            ( refl),
            ( g),
            (p))),
        ( k),
        ( q))

-- As a special case of the above:
#def Segal-homotopy-postwhisker
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f g : hom A x y)
  (h : hom A y z)
  (p : f = g)
  : (Segal-comp A is-segal-A x y z f h) = (Segal-comp A is-segal-A x y z g h)
  := Segal-homotopy-congruence A is-segal-A x y z f g h h p refl

-- As a special case of the above:
#def Segal-homotopy-prewhisker
  (A : U)
  (is-segal-A : is-segal A)
  (w x y : A)
  (k : hom A w x)
  (f g : hom A x y)
  (p : f = g)
  : (Segal-comp A is-segal-A w x y k f) = (Segal-comp A is-segal-A w x y k g)
  := Segal-homotopy-congruence A is-segal-A w x y k k f g refl p
```

```rzk title="RS17, Proposition 5.14(a)"
#def Segal-homotopy-postwhisker-is-ap
  (A : U)
  (is-segal-A : is-segal A)
  (x y z : A)
  (f g : hom A x y)
  (h : hom A y z)
  (p : f = g)
  : (Segal-homotopy-postwhisker A is-segal-A x y z f g h p) =
    ap (hom A x y) (hom A x z) f g (\ k -> Segal-comp A is-segal-A x y z k h) p
  := idJ (hom A x y , f , \ g' p' -> (Segal-homotopy-postwhisker A is-segal-A x y z f g' h p') =
    ap (hom A x y) (hom A x z) f g' (\ k -> Segal-comp A is-segal-A x y z k h) p' , refl , g , p)
```

```rzk title="RS17, Proposition 5.14(b)"
#def Segal-homotopy-prewhisker-is-ap
  (A : U)
  (is-segal-A : is-segal A)
  (w x y : A)
  (k : hom A w x)
  (f g : hom A x y)
  (p : f = g)
  : (Segal-homotopy-prewhisker A is-segal-A w x y k f g p) =
    ap (hom A x y) (hom A w y) f g (Segal-comp A is-segal-A w x y k) p
  := idJ (hom A x y , f , \ g' p' -> (Segal-homotopy-prewhisker A is-segal-A w x y k f g' p') =
    ap (hom A x y) (hom A w y) f g' (Segal-comp A is-segal-A w x y k) p' , refl , g , p)

#section is-segal-Unit

#variable extext : ExtExt

#def iscontr-Unit : is-contr Unit := (unit , \ _ -> refl)

#def is-contr-Δ²→Unit uses (extext)
  : is-contr (Δ² -> Unit)
  := (\ _ -> unit , \ k -> eq-ext-htpy extext
    (2 * 2) Δ² (\ _ -> BOT)
    (\ _ -> Unit) (\ _ -> recBOT)
    (\ _ -> unit) k
    (\ _ -> refl)
    )

#def is-segal-Unit uses (extext)
  : is-segal Unit
  := \ x y z f g -> is-retract-of-is-contr-is-contr
    (Σ (h : hom Unit x z) , hom2 Unit x y z f g h)
    (Δ² -> Unit)
    (\ (_ , k) -> k , (\ k -> (\ t -> k (t , t) , k) , \ _ -> refl))
    is-contr-Δ²→Unit

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
