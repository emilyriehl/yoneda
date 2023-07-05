# 4. Half Adjoint Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Half adjoint equivalences

```rzk
-- We'll require a more coherent notion of equivalence
#def is-half-adjoint-equiv
  (A B : U)
  (f : A -> B)
  : U
  :=
    Σ (fhasinverse : (has-inverse A B f)) ,
      (a : A) ->
        ((second (second fhasinverse)) (f a)) =
        (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
          ( f) (((first (second fhasinverse))) a))

-- By function extensionality, the previous definition coincides with the
-- following one:
#def is-half-adjoint-equiv'
  (A B : U)
  (f : A -> B)
  : U
  := Σ (fhasinverse : (has-inverse A B f)) ,
      ( homotopy-prewhisker A B B
        ( has-inverse-section-composite A B f fhasinverse)
        ( identity B)
        ( second (second fhasinverse)) f =
      ( homotopy-postwhisker A A B
        ( has-inverse-retraction-composite A B f fhasinverse)
        ( identity A)
        ( first (second fhasinverse)) f))
```

## Coherence data from an invertible map

To promote an invertible map to a half adjoint equivalence we keep one homotopy
and discard the other.

```rzk
#def has-inverse-kept-htpy
  (A B : U)
  (f : A -> B)
  (fhasinverse : has-inverse A B f)
  : homotopy A A
    ( has-inverse-retraction-composite A B f fhasinverse) (identity A)
  := (first (second fhasinverse))

#def has-inverse-discarded-htpy
  (A B : U)
  (f : A -> B)
  (fhasinverse : has-inverse A B f)
  : homotopy B B
    ( has-inverse-section-composite A B f fhasinverse) (identity B)
  := (second (second fhasinverse))
```

The required coherence will be built by transforming an instance of the
following naturality square.

```rzk
#section has-inverse-coherence

#variables A B : U
#variable f : A -> B
#variable fhasinverse : has-inverse A B f
#variable a : A

#def has-inverse-discarded-naturality-square
  : concat B
    ( has-inverse-quintuple-composite A B f fhasinverse a)
    ( has-inverse-triple-composite A B f fhasinverse a)
    ( f a)
    ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
      ( has-inverse-triple-composite A B f fhasinverse)
      ( has-inverse-kept-htpy A B f fhasinverse a))
    ( has-inverse-discarded-htpy A B f fhasinverse (f a)) =
    concat B
    ( has-inverse-quintuple-composite A B f fhasinverse a)
      ( has-inverse-triple-composite A B f fhasinverse a)
      ( f a)
      ( has-inverse-discarded-htpy A B f fhasinverse
        ( has-inverse-triple-composite A B f fhasinverse a))
      ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
        f (has-inverse-kept-htpy A B f fhasinverse a))
  :=
    nat-htpy A B
    ( has-inverse-triple-composite A B f fhasinverse)
    ( f)
    ( \ x -> has-inverse-discarded-htpy A B f fhasinverse (f x))
    ( has-inverse-retraction-composite A B f fhasinverse a)
    ( a)
    ( has-inverse-kept-htpy A B f fhasinverse a)

-- building a path that will be whiskered into the naturality square above
#def has-inverse-cocone-homotopy-coherence
  : has-inverse-kept-htpy A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a) =
    ap A A (has-inverse-retraction-composite A B f fhasinverse a) a
      ( has-inverse-retraction-composite A B f fhasinverse)
      ( has-inverse-kept-htpy A B f fhasinverse a)
  :=
    cocone-naturality-coherence
      ( A)
      ( has-inverse-retraction-composite A B f fhasinverse)
      ( has-inverse-kept-htpy A B f fhasinverse)
      ( a)

#def has-inverse-ap-cocone-homotopy-coherence
  : ap A B
    ( has-inverse-retraction-composite A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a))
    ( has-inverse-retraction-composite A B f fhasinverse a)
    ( f)
    ( has-inverse-kept-htpy A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a)) =
    ap A B
    ( has-inverse-retraction-composite A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a))
    ( has-inverse-retraction-composite A B f fhasinverse a)
    ( f)
    ( ap A A (has-inverse-retraction-composite A B f fhasinverse a) a
      ( has-inverse-retraction-composite A B f fhasinverse)
      ( has-inverse-kept-htpy A B f fhasinverse a))
  :=
    ap-htpy A B
      ( has-inverse-retraction-composite A B f fhasinverse
        ( has-inverse-retraction-composite A B f fhasinverse a))
      ( has-inverse-retraction-composite A B f fhasinverse a)
      ( f)
      ( has-inverse-kept-htpy A B f fhasinverse
        ( has-inverse-retraction-composite A B f fhasinverse a))
      ( ap A A (has-inverse-retraction-composite A B f fhasinverse a) a
        ( has-inverse-retraction-composite A B f fhasinverse)
        ( has-inverse-kept-htpy A B f fhasinverse a))
      ( has-inverse-cocone-homotopy-coherence)

#def has-inverse-cocone-coherence
  : ap A B
    ( has-inverse-retraction-composite A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a))
    ( has-inverse-retraction-composite A B f fhasinverse a)
    ( f)
    ( has-inverse-kept-htpy A B f fhasinverse
      ( has-inverse-retraction-composite A B f fhasinverse a)) =
    ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
      ( has-inverse-triple-composite A B f fhasinverse)
      ( has-inverse-kept-htpy A B f fhasinverse a))
  :=
    concat
      ( has-inverse-quintuple-composite A B f fhasinverse a =
        has-inverse-triple-composite A B f fhasinverse a)
      ( ap A B
        ( has-inverse-retraction-composite A B f fhasinverse
          ( has-inverse-retraction-composite A B f fhasinverse a))
        ( has-inverse-retraction-composite A B f fhasinverse a)
        ( f)
        ( has-inverse-kept-htpy A B f fhasinverse
          ( has-inverse-retraction-composite A B f fhasinverse a)))
      ( ap A B
        ( has-inverse-retraction-composite A B f fhasinverse
          ( has-inverse-retraction-composite A B f fhasinverse a))
        ( has-inverse-retraction-composite A B f fhasinverse a)
        ( f)
        ( ap A A
          ( has-inverse-retraction-composite A B f fhasinverse a) a
          ( has-inverse-retraction-composite A B f fhasinverse)
          ( has-inverse-kept-htpy A B f fhasinverse a)))
      ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
        ( has-inverse-triple-composite A B f fhasinverse)
        ( has-inverse-kept-htpy A B f fhasinverse a))
      ( has-inverse-ap-cocone-homotopy-coherence)
      ( rev-ap-comp A A B
        ( has-inverse-retraction-composite A B f fhasinverse a) a
        ( has-inverse-retraction-composite A B f fhasinverse)
        ( f)
        ( has-inverse-kept-htpy A B f fhasinverse a))

-- This morally gives the half adjoint inverse coherence.
-- It just requires rotation.
#def has-inverse-replaced-naturality-square
  : concat B
    ( has-inverse-quintuple-composite A B f fhasinverse a)
    ( has-inverse-triple-composite A B f fhasinverse a)
    ( f a)
    ( ap A B
      ( has-inverse-retraction-composite A B f fhasinverse
        ( has-inverse-retraction-composite A B f fhasinverse a))
      ( has-inverse-retraction-composite A B f fhasinverse a)
      ( f)
      ( has-inverse-kept-htpy A B f fhasinverse
        ( has-inverse-retraction-composite A B f fhasinverse a)))
    ( has-inverse-discarded-htpy A B f fhasinverse (f a)) =
    concat B
    ( has-inverse-quintuple-composite A B f fhasinverse a)
    ( has-inverse-triple-composite A B f fhasinverse a)
    ( f a)
    ( has-inverse-discarded-htpy A B f fhasinverse
      ( has-inverse-triple-composite A B f fhasinverse a))
    ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f
      ( has-inverse-kept-htpy A B f fhasinverse a))
  :=
    concat (has-inverse-quintuple-composite A B f fhasinverse a = f a)
      ( concat B
        ( has-inverse-quintuple-composite A B f fhasinverse a)
        ( has-inverse-triple-composite A B f fhasinverse a)
        ( f a)
        ( ap A B
          ( has-inverse-retraction-composite A B f fhasinverse
            ( has-inverse-retraction-composite A B f fhasinverse a))
          ( has-inverse-retraction-composite A B f fhasinverse a) f
          ( has-inverse-kept-htpy A B f fhasinverse
            ( has-inverse-retraction-composite A B f fhasinverse a)))
        ( has-inverse-discarded-htpy A B f fhasinverse (f a)))
      ( concat B
        ( has-inverse-quintuple-composite A B f fhasinverse a)
        ( has-inverse-triple-composite A B f fhasinverse a)
        ( f a)
        ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
          ( has-inverse-triple-composite A B f fhasinverse)
          ( has-inverse-kept-htpy A B f fhasinverse a))
        ( has-inverse-discarded-htpy A B f fhasinverse (f a)))
      ( concat B
        ( has-inverse-quintuple-composite A B f fhasinverse a)
        ( has-inverse-triple-composite A B f fhasinverse a) (f a)
        ( has-inverse-discarded-htpy A B f fhasinverse
          ( has-inverse-triple-composite A B f fhasinverse a))
        ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f
          ( has-inverse-kept-htpy A B f fhasinverse a)))
      ( homotopy-concat B
        ( has-inverse-quintuple-composite A B f fhasinverse a)
        ( has-inverse-triple-composite A B f fhasinverse a)
        ( f a)
        ( ap A B
          ( has-inverse-retraction-composite A B f fhasinverse
            ( has-inverse-retraction-composite A B f fhasinverse a))
          ( has-inverse-retraction-composite A B f fhasinverse a)
          ( f)
          ( has-inverse-kept-htpy A B f fhasinverse
            ( has-inverse-retraction-composite A B f fhasinverse a)))
        ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
          ( has-inverse-triple-composite A B f fhasinverse)
          ( has-inverse-kept-htpy A B f fhasinverse a))
        ( has-inverse-cocone-coherence)
        ( has-inverse-discarded-htpy A B f fhasinverse (f a)))
      ( has-inverse-discarded-naturality-square)

-- This will replace the discarded homotopy
#def has-inverse-corrected-htpy
  : homotopy B B (has-inverse-section-composite A B f fhasinverse) (\ b -> b)
  :=
    \ b ->
      concat B
        ( (has-inverse-section-composite A B f fhasinverse) b)
        ( (has-inverse-section-composite A B f fhasinverse)
          ((has-inverse-section-composite A B f fhasinverse) b))
        ( b)
        ( rev B
          ( (has-inverse-section-composite A B f fhasinverse)
            ((has-inverse-section-composite A B f fhasinverse) b))
          ( (has-inverse-section-composite A B f fhasinverse) b)
          ( has-inverse-discarded-htpy A B f fhasinverse
            ((has-inverse-section-composite A B f fhasinverse) b)))
        ( concat B
          ( (has-inverse-section-composite A B f fhasinverse)
            ((has-inverse-section-composite A B f fhasinverse) b))
          ( (has-inverse-section-composite A B f fhasinverse) b)
          ( b)
          ( ap A B
            ( (has-inverse-retraction-composite A B f fhasinverse)
              (has-inverse-inverse A B f fhasinverse b))
            ( has-inverse-inverse A B f fhasinverse b) f
            ( (first (second fhasinverse))
              (has-inverse-inverse A B f fhasinverse b)))
          ( (has-inverse-discarded-htpy A B f fhasinverse b)))

-- this is the half adjoint coherence
#def has-inverse-coherence
  : ( has-inverse-corrected-htpy (f a)) =
    ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f
      ( has-inverse-kept-htpy A B f fhasinverse a))
  :=
    triangle-rotation B
      ( has-inverse-quintuple-composite A B f fhasinverse a)
      ( has-inverse-triple-composite A B f fhasinverse a)
      ( f a)
      ( concat B
        ( (has-inverse-section-composite A B f fhasinverse)
          ((has-inverse-section-composite A B f fhasinverse) (f a)))
        ( (has-inverse-section-composite A B f fhasinverse) (f a))
        ( f a)
        ( ap A B
          ( (has-inverse-retraction-composite A B f fhasinverse)
            (has-inverse-inverse A B f fhasinverse (f a)))
          ( has-inverse-inverse A B f fhasinverse (f a))
            ( f)
            ( (first (second fhasinverse))
              (has-inverse-inverse A B f fhasinverse (f a))))
        ( (has-inverse-discarded-htpy A B f fhasinverse (f a))))
      ( has-inverse-discarded-htpy A B f fhasinverse
        ( has-inverse-triple-composite A B f fhasinverse a))
      ( ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f
        ( has-inverse-kept-htpy A B f fhasinverse a))
      ( has-inverse-replaced-naturality-square)

#end has-inverse-coherence
```

## Invertible maps are half adjoint equivalences

To promote an invertible map to a half adjoint equivalence we change the data of
the invertible map by replacing the discarded homotopy with the corrected one.

```rzk
#def corrected-has-inverse-has-inverse
  (A B : U)
  (f : A -> B)
  (fhasinverse : has-inverse A B f)
  : has-inverse A B f
  :=
    ( has-inverse-inverse A B f fhasinverse ,
      ( has-inverse-kept-htpy A B f fhasinverse ,
        has-inverse-corrected-htpy A B f fhasinverse))

-- Invertible maps are half adjoint equivalences!
#def is-half-adjoint-equiv-has-inverse
  (A B : U)
  (f : A -> B)
  (fhasinverse : has-inverse A B f)
  : is-half-adjoint-equiv A B f
  :=
    ( corrected-has-inverse-has-inverse A B f fhasinverse ,
      has-inverse-coherence A B f fhasinverse)

-- Equivalences are half adjoint equivalences!
#def is-half-adjoint-equiv-is-equiv
  (A B : U)
  (f : A -> B)
  (fisequiv : is-equiv A B f)
  : is-half-adjoint-equiv A B f
  :=
    is-half-adjoint-equiv-has-inverse A B f
      ( has-inverse-is-equiv A B f fisequiv)
```

## Equivalences of identity types

We use the notion of half adjoint equivalence to prove that equivalent types
have equivalent identity types.

```rzk
#section equiv-identity-types-equiv

#variables A B : U
#variable f : A -> B
#variable fisHAE : is-half-adjoint-equiv A B f

#def iff-ap-is-half-adjoint-equiv
  (x y : A)
  : iff (x = y) (f x = f y)
  :=
    (ap A B x y f ,
      \ q ->
        triple-concat A
          ( x)
          ( (has-inverse-inverse A B f (first fisHAE)) (f x))
          ( (has-inverse-inverse A B f (first fisHAE)) (f y))
          ( y)
          ( rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
            ( (first (second (first fisHAE))) x))
          ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q)
          ( (first (second (first fisHAE))) y))

#def has-retraction-ap-is-half-adjoint-equiv
  (x y : A)
  : has-retraction (x = y) (f x = f y) (ap A B x y f)
  :=
    ( second (iff-ap-is-half-adjoint-equiv x y) ,
      \ p ->
          idJ
          ( A ,
            x ,
            \ y' p' ->
              ( second (iff-ap-is-half-adjoint-equiv x y')) (ap A B x y' f p') =
              p' ,
            ( rev-refl-id-triple-concat A
              ( (has-inverse-inverse A B f (first fisHAE)) (f x)) x
              ( (first (second (first fisHAE))) x)) ,
            y ,
            p))

#def ap-triple-concat-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) =
    (triple-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      ( ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
        ( rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
          ( (first (second (first fisHAE))) x)))
      ( ap A B
        ( (has-inverse-inverse A B f (first fisHAE)) (f x))
        ( (has-inverse-inverse A B f (first fisHAE)) (f y))
        ( f)
        ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
        ( (first (second (first fisHAE))) y)))
  :=
    ap-triple-concat A B
      ( x)
      ( (has-inverse-inverse A B f (first fisHAE)) (f x))
      ( (has-inverse-inverse A B f (first fisHAE)) (f y))
      ( y)
      ( f)
      ( rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
        ( (first (second (first fisHAE))) x))
      ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q)
      ( (first (second (first fisHAE))) y)

#def ap-rev-homotopy-triple-concat-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
    ( f y)
    ( ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
      (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
        ( (first (second (first fisHAE))) x)))
    ( ap A B
      ( (has-inverse-inverse A B f (first fisHAE)) (f x))
      ( (has-inverse-inverse A B f (first fisHAE)) (f y))
      ( f)
      ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
    ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
      ( (first (second (first fisHAE))) y)) =
    triple-concat B
    ( f x)
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
    ( f y)
    ( rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
        ( (first (second (first fisHAE))) x)))
    ( ap A B
      ( (has-inverse-inverse A B f (first fisHAE)) (f x))
      ( (has-inverse-inverse A B f (first fisHAE)) (f y))
      ( f)
      ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
    ( ap A B
      ( (has-inverse-inverse A B f (first fisHAE)) (f y))
      ( y)
      ( f)
      ( (first (second (first fisHAE))) y))
  :=
    homotopy-triple-concat B
    ( f x)
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
    ( f y)
    ( ap A B
      ( x) ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
      ( rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
        ( (first (second (first fisHAE))) x)))
    ( rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
        ( (first (second (first fisHAE))) x)))
    ( ap A B
      ( (has-inverse-inverse A B f (first fisHAE)) (f x))
      ( (has-inverse-inverse A B f (first fisHAE)) (f y))
      ( f)
      ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
    ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
      ( (first (second (first fisHAE))) y))
    ( ap-rev A B (has-inverse-retraction-composite A B f (first fisHAE) x) x f
      ( (first (second (first fisHAE))) x))

#def ap-ap-homotopy-triple-concat-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : (triple-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      ( rev B
        ( f (has-inverse-retraction-composite A B f (first fisHAE) x))
        ( f x)
        ( ap A B
          ( (has-inverse-inverse A B f (first fisHAE)) (f x)) x f
          ( (first (second (first fisHAE))) x)))
      ( ap A B
        ( (has-inverse-inverse A B f (first fisHAE)) (f x))
        ( (has-inverse-inverse A B f (first fisHAE)) (f y))
        ( f)
        ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
        ( (first (second (first fisHAE))) y))) =
    ( triple-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      ( rev B
        ( f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
          ( (first (second (first fisHAE))) x)))
      ( ap B B (f x) (f y)
        ( has-inverse-section-composite A B f (first fisHAE)) q)
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y
        ( f) ((first (second (first fisHAE))) y)))
  :=
    triple-homotopy-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      ( rev B ( f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
          ( (first (second (first fisHAE))) x)))
      ( ap A B
        ( (has-inverse-inverse A B f (first fisHAE)) (f x))
        ( (has-inverse-inverse A B f (first fisHAE)) (f y))
        ( f)
        ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
      ( ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
        ( (first (second (first fisHAE))) y))
      ( rev-ap-comp B A B (f x) (f y)
        ( has-inverse-inverse A B f (first fisHAE)) f q)

-- This needs to be reversed later.
#def triple-concat-higher-homotopy-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : triple-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      ( rev B ( f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        ( (second (second (first fisHAE))) (f x)))
      ( ap B B (f x) (f y)
        ( has-inverse-section-composite A B f (first fisHAE)) q)
      ( (second (second (first fisHAE))) (f y)) =
    triple-concat B
      ( f x)
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
      ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
      ( f y)
      (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y))
  :=
    triple-concat-higher-homotopy A B
      ( has-inverse-triple-composite A B f (first fisHAE)) f
      ( \ a -> (((second (second (first fisHAE)))) (f a)))
      ( \ a ->
        ( ap A B (has-inverse-retraction-composite A B f (first fisHAE) a) a f
          ( ((first (second (first fisHAE)))) a)))
      ( second fisHAE)
      ( x)
      ( y)
      ( ap B B (f x) (f y)
        ( has-inverse-section-composite A B f (first fisHAE)) q)

#def triple-concat-nat-htpy-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
    ( f y)
    ( rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
      ( ((second (second (first fisHAE)))) (f x)))
    ( ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
    ( ((second (second (first fisHAE)))) (f y))
    = ap B B (f x) (f y) (identity B) q
  :=
    triple-concat-nat-htpy B B
      ( has-inverse-section-composite A B f (first fisHAE))
      ( identity B)
      ( (second (second (first fisHAE))))
      ( f x)
      ( f y)
      q

#def zag-zig-concat-triple-concat-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
    ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
    ( f y)
    ( rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
      ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
        ( (first (second (first fisHAE))) x)))
    ( ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
    ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
      ( (first (second (first fisHAE))) y)) =
    ap B B (f x) (f y) (identity B) q
  :=
    zag-zig-concat (f x = f y)
      ( triple-concat B
        ( f x)
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        ( f y)
        ( rev B
          ( f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
          ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
            ( (first (second (first fisHAE))) x)))
        ( ap B B (f x) (f y)
          ( has-inverse-section-composite A B f (first fisHAE)) q)
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y
          f ((first (second (first fisHAE))) y)))
      ( triple-concat B
        ( f x)
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        ( f y)
        ( rev B
          ( f (has-inverse-retraction-composite A B f (first fisHAE) x))
          ( f x)
          ( ((second (second (first fisHAE)))) (f x)))
        ( ap B B (f x) (f y)
          ( has-inverse-section-composite A B f (first fisHAE)) q)
        ( ((second (second (first fisHAE)))) (f y)))
      ( ap B B (f x) (f y) (identity B) q)
      ( triple-concat-higher-homotopy-is-half-adjoint-equiv x y q)
      ( triple-concat-nat-htpy-is-half-adjoint-equiv x y q)

#def triple-concat-reduction-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : ap B B (f x) (f y) (identity B) q = q
  := ap-id B (f x) (f y) q

#def section-htpy-ap-is-half-adjoint-equiv
  (x y : A)
  (q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) = q
  :=
    alternating-quintuple-concat (f x = f y)
      ( ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q))
      ( triple-concat B
        ( f x)
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        ( f y)
        ( ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
          ( rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x
            ( (first (second (first fisHAE))) x)))
        ( ap A B
          ( (has-inverse-inverse A B f (first fisHAE)) (f x))
          ( (has-inverse-inverse A B f (first fisHAE)) (f y)) f
          ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
          ( (first (second (first fisHAE))) y)))
      ( ap-triple-concat-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        ( f y)
        ( rev B
          ( f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
          ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
            ( (first (second (first fisHAE))) x)))
        ( ap A B
          ( (has-inverse-inverse A B f (first fisHAE)) (f x))
          ( (has-inverse-inverse A B f (first fisHAE)) (f y)) f
          ( ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f
          ( (first (second (first fisHAE))) y)))
      ( ap-rev-homotopy-triple-concat-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        ( f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        ( f y)
        ( rev B
          ( f (has-inverse-retraction-composite A B f (first fisHAE) x))
          ( f x)
          ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f
            ( (first (second (first fisHAE))) x)))
        ( ap B B (f x) (f y)
          ( has-inverse-section-composite A B f (first fisHAE)) q)
        ( ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y
          f ((first (second (first fisHAE))) y)))
      ( ap-ap-homotopy-triple-concat-is-half-adjoint-equiv x y q)
      ( ap B B (f x) (f y) (identity B) q)
      ( zag-zig-concat-triple-concat-is-half-adjoint-equiv x y q)
      ( q)
      ( triple-concat-reduction-is-half-adjoint-equiv x y q)

#def has-section-ap-is-half-adjoint-equiv uses (fisHAE)
  (x y : A)
  : has-section (x = y) (f x = f y) (ap A B x y f)
  :=
    ( second (iff-ap-is-half-adjoint-equiv x y) ,
      section-htpy-ap-is-half-adjoint-equiv x y)

#def is-equiv-ap-is-half-adjoint-equiv uses (fisHAE)
  (x y : A)
  : is-equiv (x = y) (f x = f y) (ap A B x y f)
  :=
    ( has-retraction-ap-is-half-adjoint-equiv x y ,
      has-section-ap-is-half-adjoint-equiv x y)
#end equiv-identity-types-equiv

#def is-equiv-ap-is-equiv
  (A B : U)
  (f : A -> B)
  (fisequiv : is-equiv A B f)
  (x y : A)
  : is-equiv (x = y) (f x = f y) (ap A B x y f)
  :=
    is-equiv-ap-is-half-adjoint-equiv A B f
    ( is-half-adjoint-equiv-is-equiv A B f fisequiv) x y

#def Eq-ap-is-equiv
  (A B : U)
  (f : A -> B)
  (fisequiv : is-equiv A B f)
  (x y : A)
  : Equiv (x = y) (f x = f y)
  := (ap A B x y f , is-equiv-ap-is-equiv A B f fisequiv x y)
```
