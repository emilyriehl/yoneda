# 4. Half Adjoint Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Half adjoint equivalences

We'll require a more coherent notion of equivalence. Namely, the notion of
**half adjoint equivalences**.

```rzk
#def is-half-adjoint-equiv
  ( A B : U)
  ( f : A → B)
  : U
  :=
    Σ ( has-inverse-f : (has-inverse A B f)) ,
      ( ( a : A) →
        ( second (second has-inverse-f) (f a)) =
        ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( a)
          ( f)
          ( first (second has-inverse-f) a)))
```

By function extensionality, the previous definition coincides with the following
one:

```rzk
#def is-half-adjoint-equiv'
  (A B : U)
  (f : A → B)
  : U
  :=
    Σ ( has-inverse-f : (has-inverse A B f)) ,
      ( ( a : A) →
        ( second (second has-inverse-f) (f a)) =
          ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( a)
          ( f)
          ( first (second has-inverse-f) a)))
```

## Coherence data from an invertible map

To promote an invertible map to a half adjoint equivalence we keep one homotopy
and discard the other.

```rzk
#def has-inverse-kept-htpy
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : homotopy A A
    ( retraction-composite-has-inverse A B f has-inverse-f) (identity A)
  := ( first (second has-inverse-f))

#def has-inverse-discarded-htpy
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : homotopy B B
    ( section-composite-has-inverse A B f has-inverse-f) (identity B)
  := (second (second has-inverse-f))
```

The required coherence will be built by transforming an instance of the
following naturality square.

```rzk
#section has-inverse-coherence

#variables A B : U
#variable f : A → B
#variable has-inverse-f : has-inverse A B f
#variable a : A

#def has-inverse-discarded-naturality-square
  : concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( triple-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
    ( has-inverse-discarded-htpy A B f has-inverse-f (f a)) =
    concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
      ( triple-composite-has-inverse A B f has-inverse-f a)
      ( f a)
      ( has-inverse-discarded-htpy A B f has-inverse-f
        ( triple-composite-has-inverse A B f has-inverse-f a))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
        f (has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    nat-htpy A B
    ( triple-composite-has-inverse A B f has-inverse-f)
    ( f)
    ( \ x → has-inverse-discarded-htpy A B f has-inverse-f (f x))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( a)
    ( has-inverse-kept-htpy A B f has-inverse-f a)
```

We build a path that will be whiskered into the naturality square above:

```rzk
#def has-inverse-cocone-homotopy-coherence
  : has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a) =
    ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a)
  :=
    cocone-naturality-coherence
      ( A)
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f)
      ( a)

#def has-inverse-ap-cocone-homotopy-coherence
  : ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a)) =
    ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    ap-htpy A B
      ( retraction-composite-has-inverse A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( retraction-composite-has-inverse A B f has-inverse-f a)
      ( f)
      ( has-inverse-kept-htpy A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
        ( retraction-composite-has-inverse A B f has-inverse-f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-cocone-homotopy-coherence)

#def has-inverse-cocone-coherence
  : ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a)) =
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( triple-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    concat
      ( quintuple-composite-has-inverse A B f has-inverse-f a =
        triple-composite-has-inverse A B f has-inverse-f a)
      ( ap A B
        ( retraction-composite-has-inverse A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a))
        ( retraction-composite-has-inverse A B f has-inverse-f a)
        ( f)
        ( has-inverse-kept-htpy A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a)))
      ( ap A B
        ( retraction-composite-has-inverse A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a))
        ( retraction-composite-has-inverse A B f has-inverse-f a)
        ( f)
        ( ap A A
          ( retraction-composite-has-inverse A B f has-inverse-f a) a
          ( retraction-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a)))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
        ( triple-composite-has-inverse A B f has-inverse-f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-ap-cocone-homotopy-coherence)
      ( rev-ap-comp A A B
        ( retraction-composite-has-inverse A B f has-inverse-f a) a
        ( retraction-composite-has-inverse A B f has-inverse-f)
        ( f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
```

This morally gives the half adjoint inverse coherence. It just requires
rotation.

```rzk
#def has-inverse-replaced-naturality-square
  : concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( ap A B
      ( retraction-composite-has-inverse A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( retraction-composite-has-inverse A B f has-inverse-f a)
      ( f)
      ( has-inverse-kept-htpy A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a)))
    ( has-inverse-discarded-htpy A B f has-inverse-f (f a)) =
    concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( has-inverse-discarded-htpy A B f has-inverse-f
      ( triple-composite-has-inverse A B f has-inverse-f a))
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    concat
      ( quintuple-composite-has-inverse A B f has-inverse-f a = f a)
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a))
          ( retraction-composite-has-inverse A B f has-inverse-f a) f
          ( has-inverse-kept-htpy A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a)))
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
          ( triple-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a))
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a) (f a)
        ( has-inverse-discarded-htpy A B f has-inverse-f
          ( triple-composite-has-inverse A B f has-inverse-f a))
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
          ( has-inverse-kept-htpy A B f has-inverse-f a)))
      ( concat-eq-left B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a))
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( f)
          ( has-inverse-kept-htpy A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a)))
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
          ( triple-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a))
        ( has-inverse-cocone-coherence)
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( has-inverse-discarded-naturality-square)
```

This will replace the discarded homotopy.

```rzk
#def has-inverse-corrected-htpy
  : homotopy B B (section-composite-has-inverse A B f has-inverse-f) (\ b → b)
  :=
    \ b →
      concat B
        ( (section-composite-has-inverse A B f has-inverse-f) b)
        ( (section-composite-has-inverse A B f has-inverse-f)
          ((section-composite-has-inverse A B f has-inverse-f) b))
        ( b)
        ( rev B
          ( (section-composite-has-inverse A B f has-inverse-f)
            ((section-composite-has-inverse A B f has-inverse-f) b))
          ( (section-composite-has-inverse A B f has-inverse-f) b)
          ( has-inverse-discarded-htpy A B f has-inverse-f
            ((section-composite-has-inverse A B f has-inverse-f) b)))
        ( concat B
          ( (section-composite-has-inverse A B f has-inverse-f)
            ((section-composite-has-inverse A B f has-inverse-f) b))
          ( (section-composite-has-inverse A B f has-inverse-f) b)
          ( b)
          ( ap A B
            ( (retraction-composite-has-inverse A B f has-inverse-f)
              (map-inverse-has-inverse A B f has-inverse-f b))
            ( map-inverse-has-inverse A B f has-inverse-f b) f
            ( (first (second has-inverse-f))
              (map-inverse-has-inverse A B f has-inverse-f b)))
          ( (has-inverse-discarded-htpy A B f has-inverse-f b)))
```

The following is the half adjoint coherence.

```rzk
#def has-inverse-coherence
  : ( has-inverse-corrected-htpy (f a)) =
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    triangle-rotation B
      ( quintuple-composite-has-inverse A B f has-inverse-f a)
      ( triple-composite-has-inverse A B f has-inverse-f a)
      ( f a)
      ( concat B
        ( (section-composite-has-inverse A B f has-inverse-f)
          ((section-composite-has-inverse A B f has-inverse-f) (f a)))
        ( (section-composite-has-inverse A B f has-inverse-f) (f a))
        ( f a)
        ( ap A B
          ( (retraction-composite-has-inverse A B f has-inverse-f)
            (map-inverse-has-inverse A B f has-inverse-f (f a)))
          ( map-inverse-has-inverse A B f has-inverse-f (f a))
            ( f)
            ( (first (second has-inverse-f))
              (map-inverse-has-inverse A B f has-inverse-f (f a))))
        ( (has-inverse-discarded-htpy A B f has-inverse-f (f a))))
      ( has-inverse-discarded-htpy A B f has-inverse-f
        ( triple-composite-has-inverse A B f has-inverse-f a))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-replaced-naturality-square)
```

```rzk
#end has-inverse-coherence
```

## Invertible maps are half adjoint equivalences

To promote an invertible map to a half adjoint equivalence we change the data of
the invertible map by discarding the homotopy and replacing it with a corrected
one.

```rzk
#def corrected-has-inverse-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : has-inverse A B f
  :=
    ( map-inverse-has-inverse A B f has-inverse-f ,
      ( has-inverse-kept-htpy A B f has-inverse-f ,
        has-inverse-corrected-htpy A B f has-inverse-f))
```

```rzk title="Invertible maps are half adjoint equivalences!"
#def is-half-adjoint-equiv-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : is-half-adjoint-equiv A B f
  :=
    ( corrected-has-inverse-has-inverse A B f has-inverse-f ,
      has-inverse-coherence A B f has-inverse-f)
```

```rzk title="Equivalences are half adjoint equivalences!"
#def is-half-adjoint-equiv-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-half-adjoint-equiv A B f
  :=
    is-half-adjoint-equiv-has-inverse A B f
      ( has-inverse-is-equiv A B f is-equiv-f)
```

## Equivalences of identity types

We use the notion of half adjoint equivalence to prove that equivalent types
have equivalent identity types.

```rzk
#section equiv-identity-types-equiv

#variables A B : U
#variable f : A → B
#variable is-HAE-f : is-half-adjoint-equiv A B f

#def iff-ap-is-half-adjoint-equiv
  ( x y : A)
  : iff (x = y) (f x = f y)
  :=
    ( ap A B x y f ,
      \ q →
      triple-concat A
        ( x)
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
        ( y)
        ( rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
          ( (first (second (first is-HAE-f))) x))
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q)
        ( (first (second (first is-HAE-f))) y))

#def has-retraction-ap-is-half-adjoint-equiv
  (x y : A)
  : has-retraction (x = y) (f x = f y) (ap A B x y f)
  :=
    ( second (iff-ap-is-half-adjoint-equiv x y) ,
      \ p →
          idJ
          ( A ,
            x ,
            \ y' p' →
              ( second (iff-ap-is-half-adjoint-equiv x y')) (ap A B x y' f p') =
              p' ,
            ( rev-refl-id-triple-concat A
              ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x
              ( (first (second (first is-HAE-f))) x)) ,
            y ,
            p))

#def ap-triple-concat-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) =
    (triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      ( ap A B x ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) f
        ( rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
          ( (first (second (first is-HAE-f))) x)))
      ( ap A B
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
        ( (first (second (first is-HAE-f))) y)))
  :=
    ap-triple-concat A B
      ( x)
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
      ( y)
      ( f)
      ( rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
        ( (first (second (first is-HAE-f))) x))
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q)
      ( (first (second (first is-HAE-f))) y)

#def ap-rev-triple-concat-eq-first-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
    ( f y)
    ( ap A B x ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) f
      (rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
        ( (first (second (first is-HAE-f))) x)))
    ( ap A B
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
    ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
      ( (first (second (first is-HAE-f))) y)) =
    triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
        ( (first (second (first is-HAE-f))) x)))
    ( ap A B
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
    ( ap A B
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
      ( y)
      ( f)
      ( (first (second (first is-HAE-f))) y))
  :=
    triple-concat-eq-first B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
    ( f y)
    ( ap A B
      ( x) ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) f
      ( rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
        ( (first (second (first is-HAE-f))) x)))
    ( rev B (f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
        ( (first (second (first is-HAE-f))) x)))
    ( ap A B
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
      ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
    ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
      ( (first (second (first is-HAE-f))) y))
    ( ap-rev A B (retraction-composite-has-inverse A B f (first is-HAE-f) x) x f
      ( (first (second (first is-HAE-f))) x))

#def ap-ap-triple-concat-eq-first-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : (triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      ( rev B
        ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x))
        ( f x)
        ( ap A B
          ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
          ( (first (second (first is-HAE-f))) x)))
      ( ap A B
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
        ( (first (second (first is-HAE-f))) y))) =
    ( triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      ( rev B
        ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
          ( (first (second (first is-HAE-f))) x)))
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-HAE-f)) q)
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y
        ( f) ((first (second (first is-HAE-f))) y)))
  :=
    triple-concat-eq-second B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      ( rev B ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
          ( (first (second (first is-HAE-f))) x)))
      ( ap A B
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
        ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
      ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-HAE-f)) q)
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
        ( (first (second (first is-HAE-f))) y))
      ( rev-ap-comp B A B (f x) (f y)
        ( map-inverse-has-inverse A B f (first is-HAE-f)) f q)

-- This needs to be reversed later.
#def triple-concat-higher-homotopy-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      ( rev B ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
        ( (second (second (first is-HAE-f))) (f x)))
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-HAE-f)) q)
      ( (second (second (first is-HAE-f))) (f y)) =
    triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
      ( f y)
      (rev B (f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
        (ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f ((first (second (first is-HAE-f))) x)))
        (ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-HAE-f)) q)
        (ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f ((first (second (first is-HAE-f))) y))
  :=
    triple-concat-higher-homotopy A B
      ( triple-composite-has-inverse A B f (first is-HAE-f)) f
      ( \ a → (((second (second (first is-HAE-f)))) (f a)))
      ( \ a →
        ( ap A B (retraction-composite-has-inverse A B f (first is-HAE-f) a) a f
          ( ((first (second (first is-HAE-f)))) a)))
      ( second is-HAE-f)
      ( x)
      ( y)
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-HAE-f)) q)

#def triple-concat-nat-htpy-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
      ( ((second (second (first is-HAE-f)))) (f x)))
    ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-HAE-f)) q)
    ( ((second (second (first is-HAE-f)))) (f y))
    = ap B B (f x) (f y) (identity B) q
  :=
    triple-concat-nat-htpy B B
      ( section-composite-has-inverse A B f (first is-HAE-f))
      ( identity B)
      ( (second (second (first is-HAE-f))))
      ( f x)
      ( f y)
      q

#def zag-zig-concat-triple-concat-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
        ( (first (second (first is-HAE-f))) x)))
    ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-HAE-f)) q)
    ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
      ( (first (second (first is-HAE-f))) y)) =
    ap B B (f x) (f y) (identity B) q
  :=
    zag-zig-concat (f x = f y)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
            ( (first (second (first is-HAE-f))) x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-HAE-f)) q)
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y
          f ((first (second (first is-HAE-f))) y)))
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x))
          ( f x)
          ( ((second (second (first is-HAE-f)))) (f x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-HAE-f)) q)
        ( ((second (second (first is-HAE-f)))) (f y)))
      ( ap B B (f x) (f y) (identity B) q)
      ( triple-concat-higher-homotopy-is-half-adjoint-equiv x y q)
      ( triple-concat-nat-htpy-is-half-adjoint-equiv x y q)

#def triple-concat-reduction-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap B B (f x) (f y) (identity B) q = q
  := ap-id B (f x) (f y) q

#def section-htpy-ap-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) = q
  :=
    alternating-quintuple-concat (f x = f y)
      ( ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q))
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
        ( f y)
        ( ap A B x ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) f
          ( rev A (retraction-composite-has-inverse A B f (first is-HAE-f) x) x
            ( (first (second (first is-HAE-f))) x)))
        ( ap A B
          ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
          ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) f
          ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
          ( (first (second (first is-HAE-f))) y)))
      ( ap-triple-concat-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x)) (f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
            ( (first (second (first is-HAE-f))) x)))
        ( ap A B
          ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f x))
          ( (map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) f
          ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-HAE-f)) q))
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y f
          ( (first (second (first is-HAE-f))) y)))
      ( ap-rev-triple-concat-eq-first-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-HAE-f) x))
          ( f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f x)) x f
            ( (first (second (first is-HAE-f))) x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-HAE-f)) q)
        ( ap A B ((map-inverse-has-inverse A B f (first is-HAE-f)) (f y)) y
          f ((first (second (first is-HAE-f))) y)))
      ( ap-ap-triple-concat-eq-first-is-half-adjoint-equiv x y q)
      ( ap B B (f x) (f y) (identity B) q)
      ( zag-zig-concat-triple-concat-is-half-adjoint-equiv x y q)
      ( q)
      ( triple-concat-reduction-is-half-adjoint-equiv x y q)

#def has-section-ap-is-half-adjoint-equiv uses (is-HAE-f)
  ( x y : A)
  : has-section (x = y) (f x = f y) (ap A B x y f)
  :=
    ( second (iff-ap-is-half-adjoint-equiv x y) ,
      section-htpy-ap-is-half-adjoint-equiv x y)

#def is-equiv-ap-is-half-adjoint-equiv uses (is-HAE-f)
  ( x y : A)
  : is-equiv (x = y) (f x = f y) (ap A B x y f)
  :=
    ( has-retraction-ap-is-half-adjoint-equiv x y ,
      has-section-ap-is-half-adjoint-equiv x y)
#end equiv-identity-types-equiv

#def is-equiv-ap-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( x y : A)
  : is-equiv (x = y) (f x = f y) (ap A B x y f)
  :=
    is-equiv-ap-is-half-adjoint-equiv A B f
    ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f) x y

#def Eq-ap-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( x y : A)
  : Equiv (x = y) (f x = f y)
  := (ap A B x y f , is-equiv-ap-is-equiv A B f is-equiv-f x y)
```
