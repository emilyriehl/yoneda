# 6. Fibers

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Fibers

The homotopy fiber of a map is the following type:

```rzk
-- The fiber of a map
#def fib
    (A B : U)
    (f : A -> B)
    (b : B)
    : U
    := ∑ (a : A), (f a) = b

-- We calculate the transport of (a, q) : fib b along p : a = a'
#def transport-in-fiber
    (A B : U)
    (f : A -> B)
    (b : B)
    (a a' : A)
    (u : (f a) = b)
    (p : a = a')
    : (transport A (\x -> (f x) = b) a a' p u) =
        (concat B (f a') (f a) b (ap A B a' a f (rev A a a' p)) u)
    := idJ(A, a, \a'' p' -> (transport A (\x -> (f x) = b) a a'' p' u) =
        (concat B (f a'') (f a) b (ap A B a'' a f (rev A a a'' p')) u),
        (rev ((f a) = b) (concat B (f a) (f a) b refl u) u (refl-concat B (f a) b u)), a', p)

```

## Contractible maps

A map is contractible just when its fibers are contractible.

```rzk
-- Contractible maps
#def is-contr-map
    (A B : U)
    (f : A -> B)
    : U
    := (b : B) -> is-contr (fib A B f b)
```

Contractible maps are equivalences:

```rzk
#section is-equiv-is-contr-map

#variables A B : U
#variable f : A -> B
#variable fiscontr : is-contr-map A B f

-- The inverse to a contractible map
#def is-contr-map-inverse
    : B -> A
    := \b -> first(contraction-center (fib A B f b) (fiscontr b))

#def is-contr-map-has-section
    : has-section A B f
    := (is-contr-map-inverse, \b -> second(contraction-center (fib A B f b) (fiscontr b)))

#def is-contr-map-data-in-fiber uses (fiscontr)
    (a : A)
    : fib A B f (f a)
    := (is-contr-map-inverse (f a), (second is-contr-map-has-section) (f a))

#def is-contr-map-path-in-fiber
    (a : A)
    : (is-contr-map-data-in-fiber a) =_{fib A B f (f a)} (a, refl)
    := contractible-connecting-htpy (fib A B f (f a)) (fiscontr (f a)) (is-contr-map-data-in-fiber a) (a, refl)

#def is-contr-map-has-retraction uses (fiscontr)
    : has-retraction A B f
    := (is-contr-map-inverse,
        \a -> (ap (fib A B f (f a)) A (is-contr-map-data-in-fiber a) ((a, refl))
                (\u -> first u) (is-contr-map-path-in-fiber a)))

#def is-contr-map-is-equiv uses (fiscontr)
    : is-equiv A B f
    := (is-contr-map-has-retraction, is-contr-map-has-section)

#end is-equiv-is-contr-map
```

## Half adjoint equivalences are contractible.

We now show that half adjoint equivalences are contractible maps.

```rzk
-- If f is a half adjoint equivalence, its fibers are inhabited.
#def isHAE-isSurj
    (A B : U)
    (f : A -> B)
    (fisHAE : is-half-adjoint-equiv A B f)             -- first fisHAE : has-inverse A B f
    (b : B)
    : fib A B f b
    := ((has-inverse-inverse A B f (first fisHAE)) b, (second (second (first fisHAE))) b)
```

It takes much more work to construct the contracting homotopy. The bath path of
this homotopy is straightforward.

```rzk
#section half-adjoint-equivalence-fiber-data

#variables A B : U
#variable f : A -> B
#variable fisHAE : is-half-adjoint-equiv A B f
#variable b : B
#variable z : fib A B f b

#def isHAE-fib-base-path
    : ((has-inverse-inverse A B f (first fisHAE)) b) = (first z)
    := concat A
        ((has-inverse-inverse A B f (first fisHAE)) b)
        ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
        (first z)
        (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
            (rev B (f (first z)) b (second z)))
        ((first (second (first fisHAE))) (first z))

-- Specializing the above to isHAE-fib-base-path
#def isHAE-fib-base-path-transport
    : (transport A (\x -> (f x) = b)
        ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
        (isHAE-fib-base-path )
        ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
                (isHAE-fib-base-path ))) ((second (second (first fisHAE))) b))
    := transport-in-fiber A B f b ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
        ((second (second (first fisHAE))) b)
        (isHAE-fib-base-path )

#def isHAE-fib-base-path-rev-coherence
    : rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z) (isHAE-fib-base-path ) =
        concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))
    := rev-concat A
        ((has-inverse-inverse A B f (first fisHAE)) b)
        ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
        (first z)
        (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
            (rev B (f (first z)) b (second z)))
        ((first (second (first fisHAE))) (first z))

#def isHAE-fib-base-path-transport-rev-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
                (isHAE-fib-base-path ))) ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
                (isHAE-fib-base-path )))
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (ap-htpy A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z) (isHAE-fib-base-path ))
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))
            (isHAE-fib-base-path-rev-coherence ))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-ap-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (ap-concat
            A B
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-rev-ap-rev-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                ))
        (concat-homotopy B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b) f (rev A ((has-inverse-inverse A B f (first fisHAE)) b) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE)) (rev B (f (first z)) b (second z)))))
             (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b) f (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z)))
            (ap-htpy A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) b) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE)) (rev B (f (first z)) b (second z))))
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                (rev-ap-rev B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE))  (second z)))
            )
            ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-ap-ap-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                ))
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z)))
        (concat-homotopy B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                )
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
            (rev-ap-comp B A B (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) f (second z)))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-assoc-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b)))
    := concat-assoc B
        (f (first z))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
        (f ((has-inverse-inverse A B f (first fisHAE)) b))
        b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-nat-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b))) =
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z))))
    := concat-homotopy B
        (f (first z))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
        b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))
        (nat-htpy B B
            (composition B A B f (has-inverse-inverse A B f (first fisHAE)))
            (identity B)
            (second (second (first fisHAE)))
            (f (first z))
            b
            (second z))

#def isHAE-fib-base-path-transport-ap-id-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))) =
        (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z)))
    := concat-homotopy B
        (f (first z))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
        b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z))
        (concat-homotopy B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z))
            (second z)
            (ap-id B (f (first z)) b (second z)))

#def isHAE-fib-base-path-transport-reassoc-calculation
    : (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z))) =
        (concat B (f (first z)) (f (first z)) b
            (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z))
    := assoc-concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        ((second (second (first fisHAE))) (f (first z)))
        (second z)

#def isHAE-fib-base-path-transport-HAE-calculation
    : (concat B (f (first z)) (f (first z)) b
            (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z)) =
            (concat B (f (first z)) (f (first z)) b
            (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f
                (((first (second (first fisHAE)))) (first z))))
            (second z))
    := homotopy-concat B (f (first z)) (f (first z)) b
        (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
        (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f
                (((first (second (first fisHAE)))) (first z))))
        (concat-homotopy B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
        (f (first z))
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (((second (second (first fisHAE)))) (f (first z)))
        (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f (((first (second (first fisHAE)))) (first z)))
        ((second fisHAE) (first z)))
        (second z)

#def isHAE-fib-base-path-transport-HAE-reduction
    : (concat B (f (first z)) (f (first z)) b
        (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f
                (((first (second (first fisHAE)))) (first z))))
            (second z)) =
    (concat B (f (first z)) (f (first z)) b (refl) (second z))
    := homotopy-concat B (f (first z)) (f (first z)) b
        (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f
                (((first (second (first fisHAE)))) (first z))))
        (refl)
        (concat-ap-rev-ap-id A B
            (has-inverse-retraction-composite A B f (first fisHAE) (first z))
            (first z)
            f
            (((first (second (first fisHAE)))) (first z)))
        (second z)

#def isHAE-fib-base-path-transport-HAE-final-reduction uses (A)
    : (concat B (f (first z)) (f (first z)) b (refl) (second z)) = (second z)
    := refl-concat B (f (first z)) b (second z)

#def isHAE-fib-base-path-transport-path
    : (transport A (\x -> (f x) = b)
        ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
        (isHAE-fib-base-path )
        ((second (second (first fisHAE))) b)) = (second z)
    := 12ary-concat-alternating ((f (first z)) = b)
    (transport A (\x -> (f x) = b)
        ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
        (isHAE-fib-base-path )
        ((second (second (first fisHAE))) b))
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (rev A ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
                (isHAE-fib-base-path ))) ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) b) f
            (concat A
            (first z)
            ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
            ((has-inverse-inverse A B f (first fisHAE)) b)
            (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z)))
            (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-rev-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (rev A
                ((has-inverse-inverse A B f (first fisHAE)) b)
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                (ap B A b (f (first z)) (has-inverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-ap-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B
                ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))
                ((has-inverse-inverse A B f (first fisHAE)) b)
                f
                (ap B A (f (first z)) b (has-inverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-rev-ap-rev-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) b)) b
        (concat B
            (f (first z))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-ap-ap-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f ((has-inverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (has-inverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b)))
    (isHAE-fib-base-path-transport-assoc-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z))))
    (isHAE-fib-base-path-transport-nat-calculation )
    (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) b
        (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z))))
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z)))
    (isHAE-fib-base-path-transport-ap-id-calculation )
    (concat B (f (first z)) (f (first z)) b
            (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z))
    (isHAE-fib-base-path-transport-reassoc-calculation )
    (concat B (f (first z)) (f (first z)) b
            (concat B (f (first z)) (f ((has-inverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((has-inverse-inverse A B f (first fisHAE)) (f (first z))) (first z)
                ((first (second (first fisHAE))) (first z))))
            (ap A B (has-inverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f
                (((first (second (first fisHAE)))) (first z))))
            (second z))
    (isHAE-fib-base-path-transport-HAE-calculation )
    (concat B (f (first z)) (f (first z)) b (refl) (second z))
    (isHAE-fib-base-path-transport-HAE-reduction )
    (second z)
    (isHAE-fib-base-path-transport-HAE-final-reduction )
```

Finally, we may define the contracting homotopy:

```rzk
#def isHAE-fib-contracting-homotopy
    : (isHAE-isSurj A B f fisHAE b) = z
    := path-of-pairs-pair-of-paths A (\x -> (f x) = b)
        ((has-inverse-inverse A B f (first fisHAE)) b) (first z)
        (isHAE-fib-base-path )
        ((second (second (first fisHAE))) b)
        (second z)
        (isHAE-fib-base-path-transport-path )

#end half-adjoint-equivalence-fiber-data
```

Half adjoint equivalences define contractible maps:

```rzk
#def isHAE-is-contr-map
    (A B : U)
    (f : A -> B)
    (fisHAE : is-half-adjoint-equiv A B f)
    : is-contr-map A B f
    := \b -> (isHAE-isSurj A B f fisHAE b, \z -> isHAE-fib-contracting-homotopy A B f fisHAE b z)
```

## Equivalences are contractible maps

```rzk
#def is-equiv-is-contr-map
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    : is-contr-map A B f
    := \b -> (isHAE-isSurj A B f (is-equiv-is-half-adjoint-equiv A B f fisequiv) b,
                \z -> isHAE-fib-contracting-homotopy A B f (is-equiv-is-half-adjoint-equiv A B f fisequiv) b z)

#def is-contr-map-iff-is-equiv
    (A B : U)
    (f : A -> B)
    : iff (is-contr-map A B f) (is-equiv A B f)
    := (is-contr-map-is-equiv A B f, is-equiv-is-contr-map A B f)
```

## Fiber of total map

We now calculate the fiber of the map on total spaces associated to a family of
maps.

```rzk
#def family-of-maps-total-map
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    : (∑ (x : A), B x) -> (∑ (x : A), C x)      -- the induced map on total spaces
    := \z -> (first z, f (first z) (second z))

#def total-map-to-fiber
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : fib (B (first w)) (C (first w)) (f (first w)) (second w) ->
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
    := \(b, p) -> ((first w, b),  sigma-path-fibered-path A C (first w) (f (first w) b) (second w) p)

#def total-map-from-fiber
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w) ->
        fib (B (first w)) (C (first w)) (f (first w)) (second w)
    := \(z, p) -> idJ((∑ (x : A), C x), ((family-of-maps-total-map A B C f) z), \w' p' -> fib (B (first w')) (C (first w')) (f (first w')) (second w'), (((second z), refl)), w, p)

#def total-map-to-fiber-retraction
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : has-retraction
        (fib (B (first w)) (C (first w)) (f (first w)) (second w))
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
        (total-map-to-fiber A B C f w)
    := (total-map-from-fiber A B C f w,
        \(b, p) -> idJ((C (first w)), (f (first w) b), \w1 p' -> ((total-map-from-fiber A B C f ((first w, w1))) ((total-map-to-fiber A B C f (first w, w1)) (b, p')))
            =_{(fib (B (first w)) (C (first w)) (f (first w)) (w1))} (b, p'), refl, (second w), p))

#def total-map-to-fiber-section
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : has-section
        (fib (B (first w)) (C (first w)) (f (first w)) (second w))
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
        (total-map-to-fiber A B C f w)
    := (total-map-from-fiber A B C f w,
            \(z, p) -> idJ((∑ (x : A), C x), ((first z, f (first z) (second z))), \w' p' ->
            ((total-map-to-fiber A B C f w') ((total-map-from-fiber A B C f w') (z, p')))
                =_{(fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w')} (z, p'), refl, w, p))

#def total-map-to-fiber-is-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : is-equiv
        (fib (B (first w)) (C (first w)) (f (first w)) (second w))
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
        (total-map-to-fiber A B C f w)
    := (total-map-to-fiber-retraction A B C f w, total-map-to-fiber-section A B C f w)

#def total-map-fiber-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (w : (∑ (x : A), C x))
    : Eq (fib (B (first w)) (C (first w)) (f (first w)) (second w))
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
    := (total-map-to-fiber A B C f w, total-map-to-fiber-is-equiv A B C f w)
```

## Families of equivalences

A family of equivalences induces an equivalence on total spaces and conversely.
It will be easiest to work with the incoherent notion of two-sided-inverses.

```rzk
#def invertible-family-total-inverse
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> has-inverse (B a) (C a) (f a))   -- an invertible family of maps
    : (∑ (x : A), C x) -> (∑ (x : A), B x)      -- the inverse map on total spaces
    := \(a, c) -> (a, (has-inverse-inverse (B a) (C a) (f a) (invfamily a)) c)

#def invertible-family-total-retraction
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> has-inverse (B a) (C a) (f a))   -- an invertible family of maps
    : has-retraction (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily,
        \(a, b) -> (sigma-path-fibered-path A B a ((has-inverse-inverse (B a) (C a) (f a) (invfamily a)) (f a b)) b
        ((first (second (invfamily a))) b)))

#def invertible-family-total-section
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> has-inverse (B a) (C a) (f a))   -- an invertible family of maps
    : has-section (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily,
        \(a, c) -> (sigma-path-fibered-path A C a (f a ((has-inverse-inverse (B a) (C a) (f a) (invfamily a)) c)) c
        ((second (second (invfamily a))) c)))

#def invertible-family-total-invertible
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> has-inverse (B a) (C a) (f a))   -- an invertible family of maps
    : has-inverse (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily,
        (second (invertible-family-total-retraction A B C f invfamily),
        second (invertible-family-total-section A B C f invfamily) ))

#def family-of-equiv-total-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                        -- a family of maps
    (familyequiv : (a : A) -> is-equiv (B a) (C a) (f a))   -- a family of equivalences
    : is-equiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := has-inverse-is-equiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
        (invertible-family-total-invertible A B C f
            (\a -> is-equiv-has-inverse (B a) (C a) (f a) (familyequiv a)))

#def family-Eq-total-Eq
    (A : U)
    (B C : A -> U)
    (familyeq : (a : A) -> Eq (B a) (C a))       -- a family of equivalences
    : Eq (∑ (x : A), B x) (∑ (x : A), C x)
    := (family-of-maps-total-map A B C (\a -> first (familyeq a)),
    family-of-equiv-total-equiv A B C (\a -> first (familyeq a)) (\a -> second (familyeq a)))
```

The one-way result: that a family of equivalence gives an invertible map (and
thus an equivalence) on total spaces.

```rzk
#def family-of-equiv-total-invertible
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (familyequiv : (a : A) -> is-equiv (B a) (C a) (f a))    -- a family of equivalences
    : has-inverse (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := invertible-family-total-invertible A B C f (\a -> is-equiv-has-inverse (B a) (C a) (f a) (familyequiv a))
```

For the converse, we make use of our calculation on fibers. The first
implication could be proven similarly.

```rzk
#def total-contr-map-family-of-contr-maps
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (totalcontrmap : is-contr-map (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    (a : A)
    : is-contr-map (B a) (C a) (f a)
    := \c -> is-equiv-toContr-is-contr
                (fib (B a) (C a) (f a) c)
                (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) ((a, c)))
                (total-map-fiber-equiv A B C f ((a, c)))
                (totalcontrmap ((a, c)))

#def total-equiv-family-of-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (totalequiv : is-equiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    (a : A)
    : is-equiv (B a) (C a) (f a)
    := is-contr-map-is-equiv (B a) (C a) (f a)
        (total-contr-map-family-of-contr-maps A B C f
            (is-equiv-is-contr-map (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
                totalequiv)
            a)
```

In summary, a family of maps is an equivalence iff the map on total spaces is an
equivalence.

```rzk
#def total-equiv-iff-family-of-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    : iff ((a : A) -> is-equiv (B a) (C a) (f a)) (is-equiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    := (family-of-equiv-total-equiv A B C f, total-equiv-family-of-equiv A B C f)
```

## Codomain based path spaces

```rzk
#def rev-is-eq
    (A : U)
    (x y : A)
    : Eq (x = y) (y = x)
    := (rev A x y, ((rev A y x, rev-rev A x y),(rev A y x, rev-rev A y x)))

-- An equivalence between the based path spaces.
#def based-paths-Eq
    (A : U)
    (a : A)
    : Eq (∑ (x : A), x = a) (∑ (x : A), a = x)
    := family-Eq-total-Eq A (\x -> x = a) (\x -> a = x)(\x -> rev-is-eq A x a)

-- Codomain based path spaces are contractible
#def codomain-based-paths-contractible
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : is-contr (∑ (x : A), x = a)
    := is-equiv-toContr-is-contr (∑ (x : A), x = a) (∑ (x : A), a = x)
        (based-paths-Eq A a)
        (based-paths-contractible A a)
```

## Pullback of a type family

A family of types over B pulls back along any function f : A -> B to define a
family of types over A.

```rzk
#def pullback
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    : A -> U
    := \a -> C (f a)
```

The pullback of a family along homotopic maps is equivalent.

```rzk
#def pullback-homotopy
    (A B : U)
    (f g : A -> B)
    (alpha : homotopy A B f g)
    (C : B -> U)
    (a : A)
    : (pullback A B f C a) -> (pullback A B g C a)
    := \c -> transport B C (f a) (g a) (alpha a) c

#def pullback-homotopy-inverse
    (A B : U)
    (f g : A -> B)
    (alpha : homotopy A B f g)
    (C : B -> U)
    (a : A)
    : (pullback A B g C a) -> (pullback A B f C a)
    := \c -> transport B C (g a) (f a) (rev B (f a) (g a) (alpha a)) c

#def pullback-homotopy-has-retraction
    (A B : U)
    (f g : A -> B)
    (alpha : homotopy A B f g)
    (C : B -> U)
    (a : A)
    : has-retraction (pullback A B f C a) (pullback A B g C a) (pullback-homotopy A B f g alpha C a)
    := (pullback-homotopy-inverse A B f g alpha C a, \c -> concat (pullback A B f C a)
        (transport B C (g a) (f a) (rev B (f a) (g a) (alpha a)) (transport B C (f a) (g a) (alpha a) c))
        (transport B C (f a) (f a) (concat B (f a) (g a) (f a) (alpha a) (rev B (f a) (g a) (alpha a))) c)
        c
        (transport-concat-rev B C (f a) (g a) (f a) (alpha a) (rev B (f a) (g a) (alpha a)) c)
        (transport2 B C (f a) (f a) (concat B (f a) (g a) (f a) (alpha a) (rev B (f a) (g a) (alpha a))) refl (right-inverse B (f a) (g a) (alpha a)) c))

#def pullback-homotopy-has-section
    (A B : U)
    (f g : A -> B)
    (alpha : homotopy A B f g)
    (C : B -> U)
    (a : A)
    : has-section (pullback A B f C a) (pullback A B g C a) (pullback-homotopy A B f g alpha C a)
    := (pullback-homotopy-inverse A B f g alpha C a, \c -> concat (pullback A B g C a)
        (transport B C (f a) (g a) (alpha a) (transport B C (g a) (f a) (rev B (f a) (g a) (alpha a)) c))
        (transport B C (g a) (g a) (concat B (g a) (f a) (g a) (rev B (f a) (g a) (alpha a)) (alpha a)) c)
        c
        (transport-concat-rev B C (g a) (f a) (g a) (rev B (f a) (g a) (alpha a)) (alpha a) c)
        (transport2 B C (g a) (g a) (concat B (g a) (f a) (g a) (rev B (f a) (g a) (alpha a)) (alpha a)) refl (left-inverse B (f a) (g a) (alpha a)) c))

#def pullback-homotopy-is-equiv
    (A B : U)
    (f g : A -> B)
    (alpha : homotopy A B f g)
    (C : B -> U)
    (a : A)
    : is-equiv (pullback A B f C a) (pullback A B g C a) (pullback-homotopy A B f g alpha C a)
    := (pullback-homotopy-has-retraction A B f g alpha C a, pullback-homotopy-has-section A B f g alpha C a)
```

The total space of a pulled back family of types maps to the original total
space.

```rzk
#def pullback-comparison-map
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    : (∑(a : A), (pullback A B f C) a) -> (∑(b : B), C b)
    := \(a, c) -> (f a, c)
```

Now we show that if a family is pulled back along an equivalence, the total
spaces are equivalent by proving that the comparison is a contractible map. For
this, we first prove that each fiber is equivalent to a fiber of the original
map.

```rzk
#def pullback-comparison-fiber
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    : U
    := fib (∑(a : A), (pullback A B f C) a) (∑(b : B), C b) (pullback-comparison-map A B f C) z

#def pullback-comparison-fiber-to-fiber
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    : (pullback-comparison-fiber A B f C z) -> (fib A B f (first z))
    := \(w, p) -> idJ((∑(b : B), C b), (pullback-comparison-map A B f C w), \z' p' -> (fib A B f (first z')), (first w, refl), z, p)

#def from-base-fiber-to-pullback-comparison-fiber
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (b : B)
    : (fib A B f b) -> (c : C b) -> (pullback-comparison-fiber A B f C (b, c))
    := \(a, p) -> idJ(B, f a, \b' p' -> (c : C b') -> (pullback-comparison-fiber A B f C ((b', c))), \c -> ((a, c), refl), b, p)

#def pullback-comparison-fiber-to-fiber-inv
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    : (fib A B f (first z)) -> (pullback-comparison-fiber A B f C z)
    := \(a, p) -> from-base-fiber-to-pullback-comparison-fiber A B f C (first z) (a, p) (second z)

#def pullback-comparison-fiber-to-fiber-retracting-homotopy
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    ((w, p) : pullback-comparison-fiber A B f C z)
    : ((pullback-comparison-fiber-to-fiber-inv A B f C z) ((pullback-comparison-fiber-to-fiber A B f C z) (w, p))) =_{(pullback-comparison-fiber A B f C z)} (w, p)
    := idJ((∑(b : B), C b), (pullback-comparison-map A B f C w), \z' p' ->  ((pullback-comparison-fiber-to-fiber-inv A B f C z') ((pullback-comparison-fiber-to-fiber A B f C z') (w, p'))) =_{(pullback-comparison-fiber A B f C z')} (w, p'), refl, z, p)

#def pullback-comparison-fiber-to-fiber-section-homotopy-map
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (b : B)
    ((a, p) : fib A B f b)
    : (c : C b) -> ((pullback-comparison-fiber-to-fiber A B f C (b, c)) ((pullback-comparison-fiber-to-fiber-inv A B f C (b, c))  (a, p))) =_{(fib A B f b)} (a, p)
    := idJ(B, f a, \b' p' -> (c : C b') -> ((pullback-comparison-fiber-to-fiber A B f C (b', c)) ((pullback-comparison-fiber-to-fiber-inv A B f C (b', c))  (a, p'))) =_{(fib A B f b')} (a, p'), \c -> refl, b, p)

#def pullback-comparison-fiber-to-fiber-section-homotopy
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    ((a, p) : fib A B f (first z))
    : ((pullback-comparison-fiber-to-fiber A B f C z) ((pullback-comparison-fiber-to-fiber-inv A B f C z)  (a, p))) =_{(fib A B f (first z))} (a, p)
    := pullback-comparison-fiber-to-fiber-section-homotopy-map A B f C (first z) (a, p) (second z)

#def pullback-comparison-fiber-Eq
    (A B : U)
    (f : A -> B)
    (C : B -> U)
    (z : ∑(b : B), C b)
    : Eq (pullback-comparison-fiber A B f C z) (fib A B f (first z))
    := (pullback-comparison-fiber-to-fiber A B f C z,
        ((pullback-comparison-fiber-to-fiber-inv A B f C z,
        pullback-comparison-fiber-to-fiber-retracting-homotopy A B f C z),
        (pullback-comparison-fiber-to-fiber-inv A B f C z,
         pullback-comparison-fiber-to-fiber-section-homotopy A B f C z)))
```

As a corollary, we show that pullback along an equivalence induces an
equivalence of total spaces.

```rzk
#def pullback-is-equiv-total-eq
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    (C : B -> U)
    : Eq (∑(a : A), (pullback A B f C) a) (∑(b : B), C b)
    := (pullback-comparison-map A B f C,
        is-contr-map-is-equiv
            (∑(a : A), (pullback A B f C) a)
            (∑(b : B), C b)
            (pullback-comparison-map A B f C)
            (\z -> (is-equiv-toContr-is-contr
                        (pullback-comparison-fiber A B f C z)
                        (fib A B f (first z))
                        (pullback-comparison-fiber-Eq A B f C z)
                        (is-equiv-is-contr-map A B f fisequiv (first z)))))
```

## Fundamental theorem of identity types

```rzk
#section fundamental-thm-id-types

#variable A : U
#variable a : A
#variable B : A -> U
#variable f : (x : A) -> (a = x) -> B x

#def fund-id-fam-of-eqs-implies-sum-over-codomain-contr
  : ((x : A) -> (is-equiv (a = x) (B x) (f x))) -> (is-contr (∑(x : A), B x))
  :=  (
        \familyequiv -> (equiv-with-contractible-domain-implies-contractible-codomain (∑(x : A), a = x) (∑(x : A), B x)
        ((family-of-maps-total-map A (\x -> (a = x)) B f), (has-inverse-is-equiv (∑(x : A), a = x) (∑(x : A), B x) (family-of-maps-total-map A (\x -> (a = x)) B f)
        (family-of-equiv-total-invertible A (\x -> (a = x)) B f familyequiv)
        )
        )
        (based-paths-contractible A a)
        )
  )

#def fund-id-sum-over-codomain-contr-implies-fam-of-eqs
  : (is-contr (∑(x : A), B x)) -> ((x : A) -> (is-equiv (a = x) (B x) (f x)))
  :=  (
        \Biscontr -> (\x -> (total-equiv-family-of-equiv
        A
        (\x' -> (a = x'))
        B
        f
       (areContr-is-equiv (∑(x' : A), (a = x')) (∑(x' : A), (B x')) (based-paths-contractible A a) Biscontr (family-of-maps-total-map A (\x' -> (a = x')) B f) )
        x
         )
      )
  )

-- This allows us to apply "based path induction"
-- to a family satisfying the fundamental theorem.
-- Please suggest a better name.
#def ind-based-path
  (familyequiv : (z : A) -> (is-equiv (a = z) (B z) (f z)))
  (P : (z : A) -> B z -> U)
  (p0 : P a (f a refl))
  (x : A)
  (p : B x)
  : P x p
  :=
    (ind-sing
      ( ∑(x : A), B x)
      ( a, f a refl)
      ( \ (x', p') -> P x' p')
      ( contr-implies-singleton-induction-pointed
        ( ∑(x : A), B x)
        ( fund-id-fam-of-eqs-implies-sum-over-codomain-contr familyequiv)
        ( \ (x', p') -> P x' p'))) p0 (x, p)

#end fundamental-thm-id-types
```

```rzk
#def equivalence-to-embedding
  (A B : U)
  (e : A -> B)
  (eisequiv : is-equiv A B e)
  : (Emb A B) -- For all x, y in A, ap_{e,x,y} is an equivalence
  := (e,
      \x -> \y ->
          (fund-id-sum-over-codomain-contr-implies-fam-of-eqs
          -- By the fundamental theorem of identity types, it will suffice to show contractibility of sigma_{t : A} e x = e t
          -- for the family of maps ap_e, which is of type (\t:A) -> (x = t) -> (e x = e t)
          A
          x
          (\t -> (e x = e t))
          (\t -> (ap A B x t e)) -- the family of maps ap_e
        ((is-equiv-toContr-is-contr
        -- Contractibility of sigma_{t : A} e x = e t will follow since total(\t -> rev B (e x) = (e t)), mapping from sigma_{t : A} e x = e t to sigma_{t : A} e t = e x
        -- is an equivalence, and sigma_{t : A} e t = e x ~ fib(e, e x) is contractible since e is an equivalence.
            (∑(y' : A), (e x = e y')) -- source type
            (∑(y' : A), (e y' = e x)) -- target type
        (
         -- total map as equivalence
        (family-of-maps-total-map A (\y' -> (e x) = (e y')) (\y' -> (e y') = (e x)) (\y' -> (rev B (e x) (e y')))), -- a) total map

        ( -- b) proof that total map is equivalence
          (first
            (total-equiv-iff-family-of-equiv A (\y' -> (e x) = (e y')) (\y' -> (e y') = (e x)) (\y' -> (rev B (e x) (e y'))))
          )
           (\y' -> (rev-is-equiv B (e x) (e y')))
        )
        )

        ( -- fiber of e at e(x) is contractible
          (is-equiv-is-contr-map A B e eisequiv) (e x)
        )
      )
  )
  )(y) -- evaluate at y
  )

#def equivalence-is-embedding
  (A B : U)
  (e : A -> B)
  (eisequiv : is-equiv A B e)
  : is-emb A B e
  := (second (equivalence-to-embedding A B e eisequiv))
```

## 2-of-3 for equivalences

```rzk
-- It might be better to redo this without appealing to results about
-- embeddings so that this could go earlier.
#def RightCancel-is-equiv
  (A B C : U)
  (f : A -> B)
  (g : B -> C)
  (gisequiv : is-equiv B C g)
  (gfisequiv : is-equiv A C (composition A B C g f))
  : is-equiv A B f
  := ((composition B C A
        (is-equiv-retraction A C (composition A B C g f) gfisequiv) g,
        (second (first gfisequiv))),
      (composition B C A
        (is-equiv-section A C (composition A B C g f) gfisequiv) g,
      \b -> inv-ap-is-emb
                B C g (equivalence-is-embedding B C g gisequiv)
                (f ((is-equiv-section A C (composition A B C g f) gfisequiv) (g b)))
                b
                ((second (second gfisequiv)) (g b))
      ))

#def LeftCancel-is-equiv
  (A B C : U)
  (f : A -> B)
  (fisequiv : is-equiv A B f)
  (g : B -> C)
  (gfisequiv : is-equiv A C (composition A B C g f))
  : is-equiv B C g
  := ((composition C A B
        f (is-equiv-retraction A C (composition A B C g f) gfisequiv),
        \b -> triple-concat B
                (f ((is-equiv-retraction A C (composition A B C g f) gfisequiv) (g b)))
                (f ((is-equiv-retraction A C (composition A B C g f) gfisequiv) (g (f ((is-equiv-section A B f fisequiv) b)))))
                (f ((is-equiv-section A B f fisequiv) b))
                b
                (ap B B
                  b
                  (f ((is-equiv-section A B f fisequiv) b))
                  (\b0 -> (f ((is-equiv-retraction A C (composition A B C g f) gfisequiv) (g b0))))
                  (rev B (f ((is-equiv-section A B f fisequiv) b)) b  ((second (second fisequiv)) b)))
                ((homotopy-whisker B A A B
                  (\a -> (is-equiv-retraction A C (composition A B C g f) gfisequiv) (g (f a)))
                  (\a -> a)
                  (second (first gfisequiv))
                  (is-equiv-section A B f fisequiv)
                  f) b)
                ((second (second fisequiv)) b)
      )
      ,
      (composition C A B
        f (is-equiv-section A C (composition A B C g f) gfisequiv),
        (second (second gfisequiv))
      )
    )
```

## Maps over product types

For later use, we specialize the previous results to the case of a family of
types over a product type.

```rzk
#section fibered-map-over-product

#variables A A' B B' : U
#variable C : A -> B -> U
#variable C' : A' -> B' -> U
#variable f : A -> A'
#variable g : B -> B'
#variable h : (a : A) -> (b : B) -> (c : C a b) -> C' (f a) (g b)

#def total-map-fibered-map-over-product
  : (∑ (a : A), (∑ (b : B), C a b)) -> (∑ (a' : A'), (∑ (b' : B'), C' a' b'))
  := \(a, (b, c)) -> (f a, (g b, h a b c))

#def pullback-is-equiv-base-is-equiv-total-is-equiv
  (totalisequiv : is-equiv
                    (∑(a : A), (∑ (b : B), C a b))
                    (∑ (a' : A'), (∑ (b' : B'), C' a' b'))
                    total-map-fibered-map-over-product)
  (fisequiv : is-equiv A A' f)
  : is-equiv (∑ (a : A), (∑ (b : B), C a b))
            (∑ (a : A), (∑ (b' : B'), C' (f a) b'))
            (\(a, (b, c)) -> (a, (g b, h a b c)))
  := RightCancel-is-equiv
      (∑(a : A), (∑ (b : B), C a b))
      (∑ (a : A), (∑ (b' : B'), C' (f a) b'))
      (∑ (a' : A'), (∑ (b' : B'), C' a' b'))
      (\(a, (b, c)) -> (a, (g b, h a b c)))
      (\(a, (b', c')) -> (f a, (b', c')))
      (second (pullback-is-equiv-total-eq
                A
                A'
                f
                fisequiv
                (\a' -> (∑ (b' : B'), C' a' b'))))
      totalisequiv

#def pullback-is-equiv-bases-are-equiv-total-is-equiv
  (totalisequiv : is-equiv
                    (∑(a : A), (∑ (b : B), C a b))
                    (∑ (a' : A'), (∑ (b' : B'), C' a' b'))
                    total-map-fibered-map-over-product)
  (fisequiv : is-equiv A A' f)
  (gisequiv : is-equiv B B' g)
  : is-equiv (∑ (a : A), (∑ (b : B), C a b))
            (∑ (a : A), (∑ (b : B), C' (f a) (g b)))
            (\(a, (b, c)) -> (a, (b, h a b c)))
  := RightCancel-is-equiv
      (∑ (a : A), (∑ (b : B), C a b))
      (∑ (a : A), (∑ (b : B), C' (f a) (g b)))
      (∑ (a : A), (∑ (b' : B'), C' (f a) b'))
      (\(a, (b, c)) -> (a, (b, h a b c)))
      (\(a, (b, c)) -> (a, (g b, c)))
      (family-of-equiv-total-equiv A
        (\a -> (∑ (b : B), C' (f a) (g b)))
        (\a -> (∑ (b' : B'), C' (f a) b'))
        (\a (b, c) -> (g b, c))
        (\a -> (second (pullback-is-equiv-total-eq
                B
                B'
                g
                gisequiv
                (\b' -> C' (f a) b')))))
      (pullback-is-equiv-base-is-equiv-total-is-equiv totalisequiv fisequiv)

#def fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
  (totalisequiv : is-equiv
                    (∑(a : A), (∑ (b : B), C a b))
                    (∑ (a' : A'), (∑ (b' : B'), C' a' b'))
                    total-map-fibered-map-over-product)
  (fisequiv : is-equiv A A' f)
  (gisequiv : is-equiv B B' g)
  (a0 : A)
  (b0 : B)
  : is-equiv (C a0 b0) (C' (f a0) (g b0)) (h a0 b0)
  := total-equiv-family-of-equiv B
      (\b -> C a0 b)
      (\b -> C' (f a0) (g b))
      (\b c -> h a0 b c)
      (total-equiv-family-of-equiv
        A
        (\a -> (∑ (b : B), C a b))
        (\a -> (∑ (b : B), C' (f a) (g b)))
        (\a (b, c) -> (b, h a b c))
        (pullback-is-equiv-bases-are-equiv-total-is-equiv totalisequiv fisequiv gisequiv)
        a0)
      b0

#end fibered-map-over-product
```
