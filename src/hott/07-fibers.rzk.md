# Fibers

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Fibers

The homotopy fiber of a map is the following type:

```rzk title="The fiber of a map"
#def fib
  ( A B : U)
  ( f : A → B)
  ( b : B)
  : U
  := Σ (a : A) , (f a) = b
```

```rzk title="The total space of a family"
#def total-type
  ( A : U)
  ( P : A → U)
  : U
  := Σ (a : A) , P a
```

We calculate the transport of (a , q) : fib b along p : a = a':

```rzk
#def transport-in-fiber
  ( A B : U)
  ( f : A → B)
  ( b : B)
  ( a a' : A)
  ( u : (f a) = b)
  ( p : a = a')
  : ( transport A (\ x → (f x) = b) a a' p u)
  = ( concat B (f a') (f a) b (ap A B a' a f (rev A a a' p)) u)
  :=
    ind-path
      ( A)
      ( a)
      ( \ a'' p' →
        ( transport (A) (\ x → (f x) = b) (a) (a'') (p') (u))
      = ( concat (B) (f a'') (f a) (b) (ap A B a'' a f (rev A a a'' p')) (u)))
      ( rev
        ( ( f a) = b) (concat B (f a) (f a) b refl u) (u)
        ( left-unit-concat B (f a) b u))
      ( a')
      ( p)
```

## Contractible maps

A map is contractible just when its fibers are contractible.

```rzk title="Contractible maps"
#def is-contr-map
  ( A B : U)
  ( f : A → B)
  : U
  := (b : B) → is-contr (fib A B f b)
```

Contractible maps are equivalences:

```rzk
#section is-contr-map-is-equiv

#variables A B : U
#variable f : A → B
#variable is-contr-f : is-contr-map A B f
```

```rzk title="The inverse to a contractible map"
#def is-contr-map-inverse
  : B → A
  := \ b → first (center-contraction (fib A B f b) (is-contr-f b))

#def has-section-is-contr-map
  : has-section A B f
  :=
    ( is-contr-map-inverse
    , \ b → second (center-contraction (fib A B f b) (is-contr-f b)))

#def is-contr-map-data-in-fiber uses (is-contr-f)
  ( a : A)
  : fib A B f (f a)
  := (is-contr-map-inverse (f a) , (second has-section-is-contr-map) (f a))

#def is-contr-map-path-in-fiber
  ( a : A)
  : ( is-contr-map-data-in-fiber a) =_{fib A B f (f a)} (a , refl)
  :=
    eq-is-contr
      ( fib A B f (f a))
      ( is-contr-f (f a))
      ( is-contr-map-data-in-fiber a)
      ( a , refl)

#def is-contr-map-has-retraction uses (is-contr-f)
  : has-retraction A B f
  :=
    ( is-contr-map-inverse
    , \ a → (ap (fib A B f (f a)) A
                ( is-contr-map-data-in-fiber a)
                ( ( a , refl))
                ( \ u → first u)
                ( is-contr-map-path-in-fiber a)))

#def is-equiv-is-contr-map uses (is-contr-f)
  : is-equiv A B f
  := (is-contr-map-has-retraction , has-section-is-contr-map)

#end is-contr-map-is-equiv
```

## Half adjoint equivalences are contractible

We now show that half adjoint equivalences are contractible maps.

```rzk title="If f is a half adjoint equivalence, its fibers are inhabited"
#def is-split-surjection-is-half-adjoint-equiv
  ( A B : U)
  ( f : A → B)
  ( is-hae-f : is-half-adjoint-equiv A B f)
  ( b : B)
  : fib A B f b
  :=
    ( ( map-inverse-has-inverse A B f (first is-hae-f)) b
    , ( second (second (first is-hae-f))) b)
```

It takes much more work to construct the contracting homotopy. The base path of
this homotopy is straightforward.

```rzk
#section half-adjoint-equivalence-fiber-data

#variables A B : U
#variable f : A → B
#variable is-hae-f : is-half-adjoint-equiv A B f
#variable b : B
#variable z : fib A B f b

#def base-path-fib-is-half-adjoint-equiv
  : ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) = (first z)
  :=
    concat A
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( first z)
      ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
        ( rev B (f (first z)) b (second z)))
      ( ( first (second (first is-hae-f))) (first z))
```

Specializing the above to `#!rzk isHAE-fib-base-path`:

```rzk
#def transport-base-path-fib-is-half-adjoint-equiv
  : transport A (\ x → (f x) = b)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
      ( base-path-fib-is-half-adjoint-equiv)
      ( ( second (second (first is-hae-f))) b)
  = concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
          ( rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
            ( base-path-fib-is-half-adjoint-equiv)))
      ( ( second (second (first is-hae-f))) b)
  :=
    transport-in-fiber A B f b
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
      ( ( second (second (first is-hae-f))) b)
      ( base-path-fib-is-half-adjoint-equiv)

#def rev-coherence-base-path-fib-is-half-adjoint-equiv
  : rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
      ( base-path-fib-is-half-adjoint-equiv)
  = concat A
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
        ( ( first (second (first is-hae-f))) (first z)))
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
          ( rev B (f (first z)) b (second z))))
  :=
    rev-concat A
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( first z)
      ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
        ( rev B (f (first z)) b (second z)))
      ( ( first (second (first is-hae-f))) (first z))

#def compute-rev-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
      ( rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
        ( base-path-fib-is-half-adjoint-equiv)))
    ( ( second (second (first is-hae-f))) b)
  = concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
      ( concat A
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z)))
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
            ( rev B (f (first z)) b (second z))))))
    ( ( second (second (first is-hae-f))) b)
  :=
    concat-eq-left B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
          ( base-path-fib-is-half-adjoint-equiv)))
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( concat A
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z)))
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( ap-eq A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
          ( base-path-fib-is-half-adjoint-equiv))
        ( concat A
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z)))
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z)))))
        ( rev-coherence-base-path-fib-is-half-adjoint-equiv))
      ( ( second (second (first is-hae-f))) b)

#def compute-ap-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
      ( concat A
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z)))
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
            ( rev B (f (first z)) b (second z))))))
    ( ( second (second (first is-hae-f))) b)
  = concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( ( second (second (first is-hae-f))) b)
  :=
    concat-eq-left B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( concat A
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z)))
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( ap-concat A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z)))
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
            ( rev B (f (first z)) b (second z)))))
      ( ( second (second (first is-hae-f))) b)

#def compute-rev-ap-rev-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
            ( rev B (f (first z)) b (second z))))))
    ( ( second (second (first is-hae-f))) b)
  = concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z) ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( ap B A (f (first z)) b
            ( map-inverse-has-inverse A B f (first is-hae-f))
            ( second z))))
      ( ( second (second (first is-hae-f))) b)
  :=
    concat-eq-left B
      ( f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( ap B A
            ( f (first z)) b (map-inverse-has-inverse A B f (first is-hae-f))
            ( second z))))
      ( concat-eq-right B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z)))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) f
          ( ap B A (f (first z)) b
            ( map-inverse-has-inverse A B f (first is-hae-f)) (second z)))
        ( ap-eq A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b
              ( f (first z))
              ( map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))
          ( ap B A
            ( f (first z))
            ( b)
            ( map-inverse-has-inverse A B f (first is-hae-f))
            ( second z))
          ( rev-ap-rev B A (f (first z)) b
            ( map-inverse-has-inverse A B f (first is-hae-f)) (second z))))
      ( ( second (second (first is-hae-f))) b)

#def compute-ap-ap-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z) ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( f)
        ( ap B A (f (first z)) b
          ( map-inverse-has-inverse A B f (first is-hae-f))
          ( second z))))
    ( ( second (second (first is-hae-f))) b)
  = concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z) ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z)))
    ( ( second (second (first is-hae-f))) b)
  :=
    concat-eq-left B
    ( f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( f)
        ( ap B A
          ( f (first z)) b
          ( map-inverse-has-inverse A B f (first is-hae-f)) (second z))))
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z)))
    ( concat-eq-right B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
        ( f)
        ( ap B A (f (first z)) b
          ( map-inverse-has-inverse A B f (first is-hae-f)) (second z)))
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z))
      ( rev-ap-comp B A B
        ( f (first z))
        ( b)
        ( map-inverse-has-inverse A B f (first is-hae-f))
        ( f)
        ( second z)))
    ( ( second (second (first is-hae-f))) b)

#def compute-assoc-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z)))
    ( ( second (second (first is-hae-f))) b)
  = concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z))
      ( ( second (second (first is-hae-f))) b))
  :=
    associative-concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( ap B B (f (first z)) b
      ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
      ( second z))
    ( ( second (second (first is-hae-f))) b)

#def compute-nat-transport-base-path-fib-is-half-adjoint-equiv
  : concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( ap B B (f (first z)) b
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( second z))
      ( ( second (second (first is-hae-f))) b))
  = concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( b)
      ( ( second (second (first is-hae-f))) (f (first z)))
      ( ap B B (f (first z)) b (identity B) (second z)))
  :=
    concat-eq-right B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( b)
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( b)
        ( ap B B
          ( f (first z))
          ( b)
          ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
          ( second z))
        ( ( second (second (first is-hae-f))) b))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( ap B B (f (first z)) b (identity B) (second z)))
      ( nat-htpy B B
        ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
        ( identity B)
        ( second (second (first is-hae-f)))
        ( f (first z))
        ( b)
        ( second z))

#def compute-ap-id-transport-base-path-fib-is-half-adjoint-equiv
  : concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( b)
      ( ( second (second (first is-hae-f))) (f (first z)))
      ( ap B B (f (first z)) b (identity B) (second z)))
  = concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( b)
      ( ( second (second (first is-hae-f))) (f (first z)))
      ( second z))
  :=
    concat-eq-right B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( b)
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( ap B B (f (first z)) b (identity B) (second z)))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( second z))
      ( concat-eq-right B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( ap B B (f (first z)) b (identity B) (second z))
        ( second z)
        ( ap-id B (f (first z)) b (second z)))

#def compute-reassoc-transport-base-path-fib-is-half-adjoint-equiv
  : concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( concat B
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( b)
      ( ( second (second (first is-hae-f))) (f (first z)))
      ( second z))
  = concat B (f (first z)) (f (first z)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ( second (second (first is-hae-f))) (f (first z))))
      ( second z)
  :=
    rev-associative-concat B
    ( f (first z))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
    ( f (first z))
    ( b)
    ( ap A B
      ( first z)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
      ( f)
      ( rev A
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( first z)
        ( ( first (second (first is-hae-f))) (first z))))
    ( ( second (second (first is-hae-f))) (f (first z)))
    ( second z)

#def compute-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f (first z)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ( second (second (first is-hae-f))) (f (first z))))
    ( second z)
  = concat B (f (first z)) (f (first z)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
          ( first z) f
          ( ( ( first (second (first is-hae-f)))) (first z))))
      ( second z)
  :=
    concat-eq-left B (f (first z)) (f (first z)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ( second (second (first is-hae-f))) (f (first z))))
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
        ( first z)
        ( f)
        ( ( first (second (first is-hae-f))) (first z))))
      ( concat-eq-right B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( ap A B
          ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
          ( first z) f
          ( ( ( first (second (first is-hae-f)))) (first z)))
        ( ( second is-hae-f) (first z)))
      ( second z)

#def reduction-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv
  : concat B (f (first z)) (f (first z)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( ap A B
        ( first z) ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
        ( first z) f
        ( ( ( first (second (first is-hae-f)))) (first z))))
    ( second z)
  = concat B (f (first z)) (f (first z)) b (refl) (second z)
  :=
    concat-eq-left B (f (first z)) (f (first z)) b
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( f (first z))
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( ap A B
        ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
        ( first z) f
        ( ( ( first (second (first is-hae-f)))) (first z))))
    ( refl)
    ( concat-ap-rev-ap-id A B
      ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
      ( first z)
      ( f)
      ( ( ( first (second (first is-hae-f)))) (first z)))
    ( second z)

#def final-reduction-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv uses (A)
  : concat B (f (first z)) (f (first z)) b (refl) (second z) = second z
  := left-unit-concat B (f (first z)) b (second z)

#def path-transport-base-path-fib-is-half-adjoint-equiv
  : transport A (\ x → (f x) = b)
    ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
    ( base-path-fib-is-half-adjoint-equiv)
    ( ( second (second (first is-hae-f))) b) = second z
  :=
    alternating-12ary-concat ((f (first z)) = b)
    ( transport A (\ x → (f x) = b)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
      ( base-path-fib-is-half-adjoint-equiv)
      ( ( second (second (first is-hae-f))) b))
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( rev A ((map-inverse-has-inverse A B f (first is-hae-f)) b) (first z)
          ( base-path-fib-is-half-adjoint-equiv)))
      ( ( second (second (first is-hae-f))) b))
    ( transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( ap A B (first z) ((map-inverse-has-inverse A B f (first is-hae-f)) b) f
        ( concat A
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z)))
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( ( second (second (first is-hae-f))) b))
    ( compute-rev-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
      ( b)
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( ap B A b (f (first z)) (map-inverse-has-inverse A B f (first is-hae-f))
              ( rev B (f (first z)) b (second z))))))
      ( ( second (second (first is-hae-f))) b))
    ( compute-ap-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
          f
          ( ap B A (f (first z)) b
            ( map-inverse-has-inverse A B f (first is-hae-f)) (second z))))
      ( ( second (second (first is-hae-f))) b))
    ( compute-rev-ap-rev-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B (f (first z)) (f ((map-inverse-has-inverse A B f (first is-hae-f)) b)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap B B (f (first z)) b
          ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
          ( second z)))
      ( ( second (second (first is-hae-f))) b))
    ( compute-ap-ap-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( b)
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) b))
        ( b)
        ( ap B B
          ( f (first z)) (b)
          ( comp B A B f (map-inverse-has-inverse A B f (first is-hae-f)))
          ( second z))
        ( ( second (second (first is-hae-f))) b)))
    ( compute-assoc-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( b)
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
        ( f)
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) (first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( ap B B (f (first z)) b (identity B) (second z))))
    ( compute-nat-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B
      ( f (first z))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
      ( b)
      ( ap A B
        ( first z)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))) f
        ( rev A
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( first z)
          ( ( first (second (first is-hae-f))) (first z))))
      ( concat B
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( b)
        ( ( second (second (first is-hae-f))) (f (first z)))
        ( second z)))
    ( compute-ap-id-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B (f (first z)) (f (first z)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ( second (second (first is-hae-f))) (f (first z))))
        ( second z))
    ( compute-reassoc-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B (f (first z)) (f (first z)) b
      ( concat B
        ( f (first z))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f (first z))))
        ( f (first z))
        ( ap A B
          ( first z)
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
          ( f)
          ( rev A
            ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f (first z)))
            ( first z)
            ( ( first (second (first is-hae-f))) (first z))))
        ( ap A B
          ( retraction-composite-has-inverse A B f (first is-hae-f) (first z))
          ( first z) f
          ( ( first (second (first is-hae-f))) (first z))))
      ( second z))
    ( compute-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv)
    ( concat B (f (first z)) (f (first z)) b (refl) (second z))
    ( reduction-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv)
    ( second z)
    ( final-reduction-half-adjoint-equiv-transport-base-path-fib-is-half-adjoint-equiv)
```

Finally, we may define the contracting homotopy:

```rzk
#def contraction-fib-is-half-adjoint-equiv
  : ( is-split-surjection-is-half-adjoint-equiv A B f is-hae-f b) = z
  :=
    path-of-pairs-pair-of-paths A
    ( \ x → (f x) = b)
    ( ( map-inverse-has-inverse A B f (first is-hae-f)) b)
    ( first z)
    ( base-path-fib-is-half-adjoint-equiv)
    ( ( second (second (first is-hae-f))) b)
    ( second z)
    ( path-transport-base-path-fib-is-half-adjoint-equiv)

#end half-adjoint-equivalence-fiber-data
```

Half adjoint equivalences define contractible maps:

```rzk
#def is-contr-map-is-half-adjoint-equiv
  ( A B : U)
  ( f : A → B)
  ( is-hae-f : is-half-adjoint-equiv A B f)
  : is-contr-map A B f
  :=
    \ b →
    ( is-split-surjection-is-half-adjoint-equiv A B f is-hae-f b
    , contraction-fib-is-half-adjoint-equiv A B f is-hae-f b)
```

## Equivalences are contractible maps

```rzk
#def is-contr-map-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-contr-map A B f
  :=
    \ b →
    ( is-split-surjection-is-half-adjoint-equiv A B f
      ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f) b
    , \ z → contraction-fib-is-half-adjoint-equiv A B f
        ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f) b z)

#def is-contr-map-iff-is-equiv
  ( A B : U)
  ( f : A → B)
  : iff (is-contr-map A B f) (is-equiv A B f)
  := (is-equiv-is-contr-map A B f , is-contr-map-is-equiv A B f)
```
