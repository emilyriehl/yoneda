# Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sections, retractions, and equivalences

```rzk
#section is-equiv

#variables A B : U

#def witness-section
  ( f : A → B)
  ( s : B → A)
  : U
  := (homotopy B B (comp B A B f s) (identity B))

#def has-section
  ( f : A → B)
  : U
  := Σ (s : B → A) , (witness-section f s)

#def witness-retraction
  ( f : A → B)
  ( r : B → A)
  : U
  := (homotopy A A (comp A B A r f) (identity A))

#def has-retraction
  ( f : A → B)
  : U
  := Σ (r : B → A) , (witness-retraction f r)
```

We define equivalences to be bi-invertible maps.

```rzk
#def is-equiv
  ( f : A → B)
  : U
  := product (has-retraction f) (has-section f)

#end is-equiv
```

## Equivalence data

```rzk
#section equivalence-data

#variables A B : U
#variable f : A → B
#variable is-equiv-f : is-equiv A B f

#def section-is-equiv uses (f)
  : B → A
  := first (second is-equiv-f)

#def retraction-is-equiv uses (f)
  : B → A
  := first (first is-equiv-f)
```

```rzk title="The homotopy between the section and retraction of an equivalence"
#def homotopy-section-retraction-is-equiv uses (f)
  : homotopy B A section-is-equiv retraction-is-equiv
  :=
    concat-homotopy B A
      ( section-is-equiv)
      ( triple-comp B A B A retraction-is-equiv f section-is-equiv)
      ( retraction-is-equiv)
      ( rev-homotopy B A
        ( triple-comp B A B A retraction-is-equiv f section-is-equiv)
        ( section-is-equiv)
        ( prewhisker-homotopy B A A
          ( comp A B A retraction-is-equiv f)
          ( identity A)
          ( second (first is-equiv-f))
          ( section-is-equiv)))
      ( postwhisker-homotopy B B A
        ( comp B A B f section-is-equiv)
        ( identity B)
        ( second (second is-equiv-f))
        ( retraction-is-equiv))

#end equivalence-data
```

## Invertible maps

The following type of more coherent equivalences is not a proposition.

```rzk
#def has-inverse
  ( A B : U)
  ( f : A → B)
  : U
  :=
    Σ ( g : B → A)
    , ( product
        ( homotopy A A (comp A B A g f) (identity A))
        ( homotopy B B (comp B A B f g) (identity B)))
```

## Equivalences are invertible maps

```rzk title="Invertible maps are equivalences"
#def is-equiv-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : is-equiv A B f
  :=
    ( ( first has-inverse-f , first (second has-inverse-f))
    , ( first has-inverse-f , second (second has-inverse-f)))
```

```rzk title="Equivalences are invertible"
#def has-inverse-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : has-inverse A B f
  :=
    ( section-is-equiv A B f is-equiv-f
    , ( concat-homotopy A A
        ( comp A B A (section-is-equiv A B f is-equiv-f) f)
        ( comp A B A (retraction-is-equiv A B f is-equiv-f) f)
        ( identity A)
        ( prewhisker-homotopy A B A
          ( section-is-equiv A B f is-equiv-f)
          ( retraction-is-equiv A B f is-equiv-f)
          ( homotopy-section-retraction-is-equiv A B f is-equiv-f)
          ( f))
        ( second (first is-equiv-f))
    , ( second (second is-equiv-f))))
```

## Invertible map data

```rzk
#section has-inverse-data

#variables A B : U
#variable f : A → B
#variable has-inverse-f : has-inverse A B f
```

```rzk title="The inverse of a map with an inverse"
#def map-inverse-has-inverse uses (f)
  : B → A
  := first (has-inverse-f)
```

The following are some iterated composites associated to a pair of invertible
maps.

```rzk
#def retraction-composite-has-inverse uses (B has-inverse-f)
  : A → A
  := comp A B A map-inverse-has-inverse f

#def section-composite-has-inverse uses (A has-inverse-f)
  : B → B
  := comp B A B f map-inverse-has-inverse
```

This composite is parallel to `#!rzk f`; we won't need the dual notion.

```rzk
#def triple-composite-has-inverse uses (has-inverse-f)
  : A → B
  := triple-comp A B A B f map-inverse-has-inverse f
```

This composite is also parallel to `#!rzk f`; again we won't need the dual
notion.

```rzk
#def quintuple-composite-has-inverse uses (has-inverse-f)
  : A → B
  := \ a → f (map-inverse-has-inverse (f (map-inverse-has-inverse (f a))))

#end has-inverse-data
```

## Composing equivalences

The type of equivalences between types uses `#!rzk is-equiv` rather than
`#!rzk has-inverse`.

```rzk
#def Equiv
  ( A B : U)
  : U
  := Σ (f : A → B) , (is-equiv A B f)
```

The data of an equivalence is not symmetric so we promote an equivalence to an
invertible map to prove symmetry:

```rzk
#def inv-equiv
  ( A B : U)
  ( e : Equiv A B)
  : Equiv B A
  :=
    ( first (has-inverse-is-equiv A B (first e) (second e))
    , ( ( first e
        , second (second (has-inverse-is-equiv A B (first e) (second e))))
      , ( first e
      , first (second (has-inverse-is-equiv A B (first e) (second e))))))
```

```rzk
#def section-inv-equiv
  ( A B : U)
  ( e : Equiv A B)
  : ( witness-section A B (first e) (first (inv-equiv A B e)))
  := (second (first (second (inv-equiv A B e))))
```

```rzk
#def retraction-inv-equiv
  ( A B : U)
  ( e : Equiv A B)
  : ( witness-retraction A B (first e) (first (inv-equiv A B e)))
  := (second (second (second (inv-equiv A B e))))
```

```rzk title="Composition of equivalences in diagrammatic order"
#def equiv-comp
  ( A B C : U)
  ( A≃B : Equiv A B)
  ( B≃C : Equiv B C)
  : Equiv A C
  :=
    ( ( \ a → first B≃C (first A≃B a))
    , ( ( ( \ c → first (first (second A≃B)) (first (first (second (B≃C))) c))
        , ( \ a →
            concat A
              ( first
                ( first (second A≃B))
                ( first
                  ( first (second B≃C))
                  ( first B≃C (first A≃B a))))
              ( first (first (second A≃B)) (first A≃B a))
              ( a)
              ( ap B A
                ( first (first (second B≃C)) (first B≃C (first A≃B a)))
                ( first A≃B a)
                ( first (first (second A≃B)))
                ( second (first (second B≃C)) (first A≃B a)))
              ( second (first (second A≃B)) a)))
      , ( ( \ c →
          first
            ( second (second A≃B))
            ( first (second (second (B≃C))) c))
        , ( \ c →
            concat C
              ( first B≃C
                ( first A≃B
                  ( first
                    ( second (second A≃B))
                    ( first (second (second B≃C)) c))))
              ( first B≃C (first (second (second B≃C)) c))
              ( c)
              ( ap B C
                ( first A≃B
                  ( first
                    ( second (second A≃B))
                    ( first (second (second B≃C)) c)))
                ( first (second (second B≃C)) c)
                ( first B≃C)
                ( second
                  ( second (second A≃B))
                  ( first (second (second B≃C)) c)))
              ( second (second (second B≃C)) c)))))
```

Now we compose the functions that are equivalences.

```rzk
#def is-equiv-comp
  ( A B C : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( g : B → C)
  ( is-equiv-g : is-equiv B C g)
  : is-equiv A C (comp A B C g f)
  :=
    ( ( comp C B A
        ( retraction-is-equiv A B f is-equiv-f)
        ( retraction-is-equiv B C g is-equiv-g)
      , ( \ a →
          concat A
            ( retraction-is-equiv A B f is-equiv-f
              ( retraction-is-equiv B C g is-equiv-g (g (f a))))
            ( retraction-is-equiv A B f is-equiv-f (f a))
            ( a)
            ( ap B A
              ( retraction-is-equiv B C g is-equiv-g (g (f a)))
              ( f a)
              ( retraction-is-equiv A B f is-equiv-f)
              ( second (first is-equiv-g) (f a)))
            ( second (first is-equiv-f) a)))
    , ( comp C B A
        ( section-is-equiv A B f is-equiv-f)
        ( section-is-equiv B C g is-equiv-g)
      , ( \ c →
          concat C
            ( g (f (first (second is-equiv-f) (first (second is-equiv-g) c))))
            ( g (first (second is-equiv-g) c))
            ( c)
            ( ap B C
              ( f (first (second is-equiv-f) (first (second is-equiv-g) c)))
              ( first (second is-equiv-g) c)
              ( g)
              ( second (second is-equiv-f) (first (second is-equiv-g) c)))
            ( second (second is-equiv-g) c))))
```

```rzk title="Right cancellation of equivalences in diagrammatic order"
#def equiv-right-cancel
  ( A B C : U)
  ( A≃C : Equiv A C)
  ( B≃C : Equiv B C)
  : Equiv A B
  := equiv-comp A C B (A≃C) (inv-equiv B C B≃C)
```

```rzk title="Left cancellation of equivalences in diagrammatic order"
#def equiv-left-cancel
  ( A B C : U)
  ( A≃B : Equiv A B)
  ( A≃C : Equiv A C)
  : Equiv B C
  := equiv-comp B A C (inv-equiv A B A≃B) (A≃C)
```

```rzk title="A composition of three equivalences"
#def equiv-triple-comp
  ( A B C D : U)
  ( A≃B : Equiv A B)
  ( B≃C : Equiv B C)
  ( C≃D : Equiv C D)
  : Equiv A D
  := equiv-comp A B D (A≃B) (equiv-comp B C D B≃C C≃D)

#def is-equiv-triple-comp
  ( A B C D : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( g : B → C)
  ( is-equiv-g : is-equiv B C g)
  ( h : C → D)
  ( is-equiv-h : is-equiv C D h)
  : is-equiv A D (triple-comp A B C D h g f)
  :=
    is-equiv-comp A B D
      ( f)
      ( is-equiv-f)
      ( comp B C D h g)
      ( is-equiv-comp B C D g is-equiv-g h is-equiv-h)
```

## Equivalences and homotopy

If a map is homotopic to an equivalence it is an equivalence.

```rzk
#def is-equiv-homotopy
  ( A B : U)
  ( f g : A → B)
  ( H : homotopy A B f g)
  ( is-equiv-g : is-equiv A B g)
  : is-equiv A B f
  :=
    ( ( ( first (first is-equiv-g))
      , ( \ a →
          concat A
            ( first (first is-equiv-g) (f a))
            ( first (first is-equiv-g) (g a))
            ( a)
            ( ap B A (f a) (g a) (first (first is-equiv-g)) (H a))
            ( second (first is-equiv-g) a)))
    , ( ( first (second is-equiv-g))
      , ( \ b →
          concat B
            ( f (first (second is-equiv-g) b))
            ( g (first (second is-equiv-g) b))
            ( b)
            ( H (first (second is-equiv-g) b))
            ( second (second is-equiv-g) b))))

#def is-equiv-rev-homotopy
  ( A B : U)
  ( f g : A → B)
  ( H : homotopy A B f g)
  ( is-equiv-f : is-equiv A B f)
  : is-equiv A B g
  := is-equiv-homotopy A B g f (rev-homotopy A B f g H) is-equiv-f
```

## Function extensionality

By path induction, an identification between functions defines a homotopy.

```rzk
#def htpy-eq
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  ( p : f = g)
  : ( x : X) → (f x = g x)
  :=
    ind-path
      ( ( x : X) → A x)
      ( f)
      ( \ g' p' → (x : X) → (f x = g' x))
      ( \ x → refl)
      ( g)
      ( p)
```

The function extensionality axiom asserts that this map defines a family of
equivalences.

```rzk title="The type that encodes the function extensionality axiom"
#def FunExt
  : U
  :=
    ( X : U)
  → ( A : X → U)
  → ( f : (x : X) → A x)
  → ( g : (x : X) → A x)
  → is-equiv (f = g) ((x : X) → f x = g x) (htpy-eq X A f g)
```

In the formalisations below, some definitions will assume function
extensionality:

```rzk
#assume funext : FunExt
```

Whenever a definition (implicitly) uses function extensionality, we write
`#!rzk uses (funext)`. In particular, the following definitions rely on function
extensionality:

```rzk title="The equivalence provided by function extensionality"
#def equiv-FunExt uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  : Equiv (f = g) ((x : X) → f x = g x)
  := (htpy-eq X A f g , funext X A f g)
```

In particular, function extensionality implies that homotopies give rise to
identifications. This defines `#!rzk eq-htpy` to be the retraction to
`#!rzk htpy-eq`.

```rzk
#def eq-htpy uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  : ( ( x : X) → f x = g x) → (f = g)
  := first (first (funext X A f g))
```

Using function extensionality, a fiberwise equivalence defines an equivalence of
dependent function types.

```rzk
#def equiv-function-equiv-family uses (funext)
  ( X : U)
  ( A B : X → U)
  ( famequiv : (x : X) → Equiv (A x) (B x))
  : Equiv ((x : X) → A x) ((x : X) → B x)
  :=
    ( ( \ a x → first (famequiv x) (a x))
    , ( ( ( \ b x → first (first (second (famequiv x))) (b x))
        , ( \ a →
            eq-htpy
              X A
              ( \ x →
                first
                  ( first (second (famequiv x)))
                  ( first (famequiv x) (a x)))
              ( a)
              ( \ x → second (first (second (famequiv x))) (a x))))
      , ( ( \ b x → first (second (second (famequiv x))) (b x))
        , ( \ b →
            eq-htpy
              X B
              ( \ x →
                first (famequiv x) (first (second (second (famequiv x))) (b x)))
              ( b)
              ( \ x → second (second (second (famequiv x))) (b x))))))
```

## Embeddings

```rzk
#def is-emb
  ( A B : U)
  ( f : A → B)
  : U
  := (x : A) → (y : A) → is-equiv (x = y) (f x = f y) (ap A B x y f)

#def Emb
  ( A B : U)
  : U
  := (Σ (f : A → B) , is-emb A B f)

#def is-emb-is-inhabited-emb
  ( A B : U)
  ( f : A → B)
  ( e : A → is-emb A B f)
  : is-emb A B f
  := \ x y → e x x y

#def inv-ap-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( x y : A)
  ( p : f x = f y)
  : ( x = y)
  := first (first (is-emb-f x y)) p
```

## Reversal is an equivalence

```rzk
#def has-retraction-rev
  ( A : U)
  ( y : A)
  : ( x : A) → has-retraction (x = y) (y = x) (rev A x y)
  :=
    \ x →
    ( ( rev A y x)
    , ( \ p →
        ind-path
          ( A)
          ( x)
          ( \ y' p' →
            ( comp
              ( x = y') (y' = x) (x = y') (rev A y' x) (rev A x y') (p'))
            =_{x = y'}
            ( p'))
            ( refl)
            ( y)
            ( p)))

#def has-section-rev
  ( A : U)
  ( y x : A)
  : has-section (x = y) (y = x) (rev A x y)
  :=
    ( ( rev A y x)
    , ( ind-path
        ( A)
        ( y)
        ( \ x' p' →
          ( comp
            ( y = x') (x' = y) (y = x') (rev A x' y) (rev A y x') (p'))
          =_{y = x'}
          ( p'))
        ( refl)
        ( x)))

#def is-equiv-rev
  ( A : U)
  ( x y : A)
  : is-equiv (x = y) (y = x) (rev A x y)
  := ((has-retraction-rev A y x) , (has-section-rev A y x))
```
