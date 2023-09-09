# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on extension extensionality:

```rzk
#assume extext : ExtExt
```

## Isomorphisms

```rzk
#def has-retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  : U
  := ( comp-is-segal A is-segal-A x y x f g) =_{hom A x x} (id-hom A x)

#def Retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ ( g : hom A y x) , ( has-retraction-arrow A is-segal-A x y f g)

#def has-section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  : U
  := ( comp-is-segal A is-segal-A y x y h f) =_{hom A y y} (id-hom A y)

#def Section-arrow
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  : U
  := Σ (h : hom A y x) , (has-section-arrow A is-segal-A x y f h)

#def is-iso-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  :=
    product
    ( Retraction-arrow A is-segal-A x y f)
    ( Section-arrow A is-segal-A x y f)

#def Iso
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : U
  := Σ ( f : hom A x y) , is-iso-arrow A is-segal-A x y f

#def has-inverse-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  :=
    Σ ( g : hom A y x) ,
      product
      ( has-retraction-arrow A is-segal-A x y f g)
      ( has-section-arrow A is-segal-A x y f g)

#def is-iso-arrow-has-inverse-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( has-inverse-arrow A is-segal-A x y f) → (is-iso-arrow A is-segal-A x y f)
  :=
    ( \ (g , (p , q)) → ((g , p) , (g , q)))

#def has-inverse-arrow-is-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (is-iso-arrow A is-segal-A x y f) → (has-inverse-arrow A is-segal-A x y f)
  :=
    ( \ ((g , p) , (h , q)) →
      ( g ,
        ( p ,
          ( concat
            ( hom A y y)
            ( comp-is-segal A is-segal-A y x y g f)
            ( comp-is-segal A is-segal-A y x y h f)
            ( id-hom A y)
            ( postwhisker-homotopy-is-segal A is-segal-A y x y g h f
              ( alternating-quintuple-concat
                ( hom A y x)
                ( g)
                ( comp-is-segal A is-segal-A y y x (id-hom A y) g)
                ( rev
                  ( hom A y x)
                  ( comp-is-segal A is-segal-A y y x (id-hom A y) g)
                  ( g)
                  ( id-comp-is-segal A is-segal-A y x g))
                ( comp-is-segal A is-segal-A y y x
                  ( comp-is-segal A is-segal-A y x y h f) ( g))
                ( postwhisker-homotopy-is-segal A is-segal-A y y x
                  ( id-hom A y)
                  ( comp-is-segal A is-segal-A y x y h f)
                  ( g)
                  ( rev
                    ( hom A y y)
                    ( comp-is-segal A is-segal-A y x y h f)
                    ( id-hom A y)
                    ( q)))
                ( comp-is-segal A is-segal-A y x x
                  ( h)
                  ( comp-is-segal A is-segal-A x y x f g))
                ( associative-is-segal extext A is-segal-A y x y x h f g)
                ( comp-is-segal A is-segal-A y x x h (id-hom A x))
                ( prewhisker-homotopy-is-segal A is-segal-A y x x h
                  ( comp-is-segal A is-segal-A x y x f g)
                  ( id-hom A x) p)
                ( h)
                ( comp-id-is-segal A is-segal-A y x h)))
            ( q)))))

#def inverse-iff-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : iff (has-inverse-arrow A is-segal-A x y f) (is-iso-arrow A is-segal-A x y f)
  :=
    ( is-iso-arrow-has-inverse-arrow A is-segal-A x y f ,
      has-inverse-arrow-is-iso-arrow A is-segal-A x y f)

#def has-retraction-postcomp-has-retraction uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  : ( z : A) →
    has-retraction (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x g z) ,
        \ k →
      ( triple-concat
        ( hom A z x)
        ( comp-is-segal A is-segal-A z y x (comp-is-segal A is-segal-A z x y k f) g)
        ( comp-is-segal A is-segal-A z x x k (comp-is-segal A is-segal-A x y x f g))
        ( comp-is-segal A is-segal-A z x x k (id-hom A x))
        ( k)
        ( associative-is-segal extext A is-segal-A z x y x k f g)
        ( prewhisker-homotopy-is-segal A is-segal-A z x x k
          ( comp-is-segal A is-segal-A x y x f g) (id-hom A x) gg)
        ( comp-id-is-segal A is-segal-A z x k)))

#def has-section-postcomp-has-section uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : ( z : A) →
    has-section (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x h z) ,
        \ k →
        ( triple-concat
          ( hom A z y)
          ( comp-is-segal A is-segal-A z x y (comp-is-segal A is-segal-A z y x k h) f)
          ( comp-is-segal A is-segal-A z y y k (comp-is-segal A is-segal-A y x y h f))
          ( comp-is-segal A is-segal-A z y y k (id-hom A y))
          ( k)
          ( associative-is-segal extext A is-segal-A z y x y k h f)
          ( prewhisker-homotopy-is-segal A is-segal-A z y y k
            ( comp-is-segal A is-segal-A y x y h f) (id-hom A y) hh)
          ( comp-id-is-segal A is-segal-A z y k)))

#def is-equiv-postcomp-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : (z : A) →
    is-equiv (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( has-retraction-postcomp-has-retraction A is-segal-A x y f g gg z) ,
      ( has-section-postcomp-has-section A is-segal-A x y f h hh z))

#def has-retraction-precomp-has-section uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : (z : A) →
    has-retraction (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x h z) ,
        \ k →
        ( triple-concat
          ( hom A y z)
          ( comp-is-segal A is-segal-A y x z h (comp-is-segal A is-segal-A x y z f k))
          ( comp-is-segal A is-segal-A y y z (comp-is-segal A is-segal-A y x y h f) k)
          ( comp-is-segal A is-segal-A y y z (id-hom A y) k)
          ( k)
          ( rev
            ( hom A y z)
            ( comp-is-segal A is-segal-A y y z
              ( comp-is-segal A is-segal-A y x y h f) k)
            ( comp-is-segal A is-segal-A y x z
              h (comp-is-segal A is-segal-A x y z f k))
            ( associative-is-segal extext A is-segal-A y x y z h f k))
          ( postwhisker-homotopy-is-segal A is-segal-A y y z
            ( comp-is-segal A is-segal-A y x y h f)
            ( id-hom A y) k hh)
          ( id-comp-is-segal A is-segal-A y z k)
        )
    )

#def has-section-precomp-has-retraction uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  : (z : A) →
    has-section (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x g z) ,
        \ k →
        ( triple-concat
          ( hom A x z)
          ( comp-is-segal A is-segal-A x y z f (comp-is-segal A is-segal-A y x z g k))
          ( comp-is-segal A is-segal-A x x z (comp-is-segal A is-segal-A x y x f g) k)
          ( comp-is-segal A is-segal-A x x z (id-hom A x) k)
          ( k)
          ( rev
            ( hom A x z)
            ( comp-is-segal A is-segal-A x x z
              ( comp-is-segal A is-segal-A x y x f g) k)
            ( comp-is-segal A is-segal-A x y z
              f (comp-is-segal A is-segal-A y x z g k))
            ( associative-is-segal extext A is-segal-A x y x z f g k))
          ( postwhisker-homotopy-is-segal A is-segal-A x x z
            ( comp-is-segal A is-segal-A x y x f g)
            ( id-hom A x)
            ( k)
            ( gg))
          ( id-comp-is-segal A is-segal-A x z k)))

#def is-equiv-precomp-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : (z : A) →
    is-equiv (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
      ( ( has-retraction-precomp-has-section A is-segal-A x y f h hh z) ,
        ( has-section-precomp-has-retraction A is-segal-A x y f g gg z))

#def is-contr-Retraction-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (Retraction-arrow A is-segal-A x y f)
  :=
    ( is-contr-map-is-equiv
      ( hom A y x)
      ( hom A x x)
      ( precomp-is-segal A is-segal-A x y f x)
      ( is-equiv-precomp-is-iso A is-segal-A x y f g gg h hh x))
    ( id-hom A x)

#def is-contr-Section-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (Section-arrow A is-segal-A x y f)
  :=
    ( is-contr-map-is-equiv
      ( hom A y x)
      ( hom A y y)
      ( postcomp-is-segal A is-segal-A x y f y)
      ( is-equiv-postcomp-is-iso A is-segal-A x y f g gg h hh y))
    ( id-hom A y)

#def is-contr-is-iso-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (is-iso-arrow A is-segal-A x y f)
  :=
    ( is-contr-product
      ( Retraction-arrow A is-segal-A x y f)
      ( Section-arrow A is-segal-A x y f)
      ( is-contr-Retraction-arrow-is-iso A is-segal-A x y f g gg h hh)
      ( is-contr-Section-arrow-is-iso A is-segal-A x y f g gg h hh))

#def is-prop-is-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (is-prop (is-iso-arrow A is-segal-A x y f))
  :=
    ( is-prop-is-contr-is-inhabited
      ( is-iso-arrow A is-segal-A x y f)
      ( \ is-isof →
        ( is-contr-is-iso-arrow-is-iso A is-segal-A x y f
          ( first (first is-isof))
          ( second (first is-isof))
          ( first (second is-isof))
          ( second (second is-isof)))))

#def iso-id-arrow
  (A : U)
  (is-segal-A : is-segal A)
  : (x : A) → Iso A is-segal-A x x
  :=
    \ x →
    (
    (id-hom A x) ,
    (
    (
      (id-hom A x) ,
      (id-comp-is-segal A is-segal-A x x (id-hom A x))
    ) ,
    (
      (id-hom A x) ,
      (id-comp-is-segal A is-segal-A x x (id-hom A x))
    )
      )
  )

#def iso-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : (x = y) → Iso A is-segal-A x y
  :=
    \ p →
    ind-path
      ( A)
      ( x)
      ( \ y' p' → Iso A is-segal-A x y')
      ( iso-id-arrow A is-segal-A x)
      ( y)
      ( p)

#def is-rezk
  (A : U)
  : U
  :=
    Σ ( is-segal-A : is-segal A) ,
      (x : A) → (y : A) →
        is-equiv (x = y) (Iso A is-segal-A x y) (iso-eq A is-segal-A x y)
```

## Uniqueness of initial and final objects

In a Segal type, initial objects are isomorphic.

```rzk
#def iso-initial
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-initial-a : is-initial A a)
  ( is-initial-b : is-initial A b)
  : Iso A is-segal-A a b
  :=
    ( first (is-initial-a b) ,
      ( ( first (is-initial-b a) ,
          eq-is-contr
            ( hom A a a)
            ( is-initial-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-initial-a b))
              ( first (is-initial-b a)))
            ( id-hom A a)) ,
        ( first (is-initial-b a) ,
          eq-is-contr
            ( hom A b b)
            ( is-initial-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-initial-b a))
              ( first (is-initial-a b)))
            ( id-hom A b))))
```

In a Segal type, final objects are isomorphic.

```rzk
#def iso-final
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-final-a : is-final A a)
  ( is-final-b : is-final A b)
  ( iso : Iso A is-segal-A a b)
  : Iso A is-segal-A a b
  :=
    ( first (is-final-b a) ,
      ( ( first (is-final-a b) ,
          eq-is-contr
            ( hom A a a)
            ( is-final-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-final-b a))
              ( first (is-final-a b)))
            ( id-hom A a)) ,
        ( first (is-final-a b) ,
          eq-is-contr
            ( hom A b b)
            ( is-final-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-final-a b))
              ( first (is-final-b a)))
            ( id-hom A b))))
```
