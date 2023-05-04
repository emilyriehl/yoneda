# 7. Fibers

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
```

## Contractible maps

A map is contractible iff its fibers are contractible.

```rzk
-- Contractible maps
#def isContr-map
    (A B : U)
    (f : A -> B)
    : U
    := (b : B) -> isContr (fib A B f b)
```

Contractible maps are equivalences:

```rzk
-- The inverse to a contractible map
#def isContr-map-inverse
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    : B -> A
    := \b -> first(contraction-center (fib A B f b) (fiscontr b))

#def isContr-map-hasSection
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    : hasSection A B f
    := (isContr-map-inverse A B f fiscontr, \b -> second(contraction-center (fib A B f b) (fiscontr b)))

#def isContr-map-data-in-fiber
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    (a : A)
    : fib A B f (f a)
    := ((isContr-map-inverse A B f fiscontr) (f a), (second (isContr-map-hasSection A B f fiscontr)) (f a))

#def isContr-map-path-in-fiber
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    (a : A)
    : (isContr-map-data-in-fiber A B f fiscontr a) =_{fib A B f (f a)} (a, refl)
    := contractible-connecting-htpy (fib A B f (f a)) (fiscontr (f a)) (isContr-map-data-in-fiber A B f fiscontr a) (a, refl)

#def isContr-map-hasRetraction
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    : hasRetraction A B f    
    := (isContr-map-inverse A B f fiscontr, 
        \a -> (ap (fib A B f (f a)) A (isContr-map-data-in-fiber A B f fiscontr a) ((a, refl)) 
                (\u -> first u) (isContr-map-path-in-fiber A B f fiscontr a)))

#def isContr-map-isEquiv
    (A B : U)
    (f : A -> B)
    (fiscontr : isContr-map A B f)
    : isEquiv A B f
    := (isContr-map-hasRetraction A B f fiscontr, isContr-map-hasSection A B f fiscontr)
```

## Half adjoint equivalences are contractible.

We now show that half adjoint equivalences are contractible maps. 

```rzk
-- If f is a half adjoint equivalence, its fibers are inhabited.
#def isHAE-isSurj
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    : fib A B f b
    := ((hasInverse-inverse A B f (first fisHAE)) b, (second (second (first fisHAE))) b)
```

It takes much more work to construct the contracting homotopy. The bath path of this homotopy is straightforward.

```rzk
#def isHAE-fib-base-path
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : ((hasInverse-inverse A B f (first fisHAE)) b) = (first z)
    := concat A 
        ((hasInverse-inverse A B f (first fisHAE)) b) 
        ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
        (first z)
        (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
            (rev B (f (first z)) b (second z)))
        ((first (second (first fisHAE))) (first z))

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

-- Specializing the above to isHAE-fib-base-path
#def isHAE-fib-base-path-transport
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (transport A (\x -> (f x) = b) 
        ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
        (isHAE-fib-base-path A B f fisHAE b z)
        ((second (second (first fisHAE))) b)) = 
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
                (isHAE-fib-base-path A B f fisHAE b z))) ((second (second (first fisHAE))) b))
    := transport-in-fiber A B f b ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
        ((second (second (first fisHAE))) b)
        (isHAE-fib-base-path A B f fisHAE b z)

#def isHAE-fib-base-path-rev-coherence
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) (isHAE-fib-base-path A B f fisHAE b z) = 
        concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))
    := rev-concat A 
        ((hasInverse-inverse A B f (first fisHAE)) b) 
        ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
        (first z)
        (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
            (rev B (f (first z)) b (second z)))
        ((first (second (first fisHAE))) (first z))

#def isHAE-fib-base-path-transport-rev-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
                (isHAE-fib-base-path A B f fisHAE b z))) ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b))    
    := homotopy-concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
                (isHAE-fib-base-path A B f fisHAE b z)))
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (ap-htpy A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f
            (rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) (isHAE-fib-base-path A B f fisHAE b z))
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))
            (isHAE-fib-base-path-rev-coherence A B f fisHAE b z))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-ap-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (ap-concat
            A B
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            f
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-rev-ap-rev-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b)) = 
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                ))
        (concat-homotopy B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) f (rev A ((hasInverse-inverse A B f (first fisHAE)) b) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE)) (rev B (f (first z)) b (second z)))))
             (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) f (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z)))
            (ap-htpy A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) b) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE)) (rev B (f (first z)) b (second z))))
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                (rev-ap-rev B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE))  (second z)))
            )
            ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-ap-ap-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b)) = 
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b))
    := homotopy-concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                ))
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z)))
        (concat-homotopy B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                )
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
            (rev-ap-comp B A B (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) f (second z)))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-assoc-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b)) =
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b)))
    := concat-assoc B 
        (f (first z)) 
        (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
        (f ((hasInverse-inverse A B f (first fisHAE)) b)) 
        b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
        ((second (second (first fisHAE))) b)

#def isHAE-fib-base-path-transport-nat-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b))) =
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z))))
    := concat-homotopy B 
        (f (first z)) 
        (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        b 
        (concat B 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))
        (nat-htpy B B
            (composition B A B f (hasInverse-inverse A B f (first fisHAE)))
            (identity B)
            (second (second (first fisHAE)))
            (f (first z))
            b
            (second z))    

#def isHAE-fib-base-path-transport-ap-id-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))) = 
        (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z)))
    := concat-homotopy B 
        (f (first z)) 
        (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        b 
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z)))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z))
        (concat-homotopy B 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            ((second (second (first fisHAE))) (f (first z)))
            b
            (ap B B (f (first z)) b (identity B) (second z))
            (second z)
            (ap-id B (f (first z)) b (second z)))
            
#def isHAE-fib-base-path-transport-reassoc-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z))) = 
        (concat B (f (first z)) (f (first z)) b 
            (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z))
    := assoc-concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z)) b
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        ((second (second (first fisHAE))) (f (first z)))
        (second z)        

#def isHAE-fib-base-path-transport-HAE-calculation
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f (first z)) b 
            (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z)) = 
            (concat B (f (first z)) (f (first z)) b 
            (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f 
                (((first (second (first fisHAE)))) (first z))))
            (second z))
    := homotopy-concat B (f (first z)) (f (first z)) b
        (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
        (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f 
                (((first (second (first fisHAE)))) (first z))))     
        (concat-homotopy B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (f (first z))
        (((second (second (first fisHAE)))) (f (first z)))
        (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f (((first (second (first fisHAE)))) (first z)))
        ((second fisHAE) (first z)))                     
        (second z)

#def isHAE-fib-base-path-transport-HAE-reduction
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f (first z)) b 
        (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f 
                (((first (second (first fisHAE)))) (first z))))
            (second z)) =    
    (concat B (f (first z)) (f (first z)) b (refl) (second z))   
    := homotopy-concat B (f (first z)) (f (first z)) b
        (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f 
                (((first (second (first fisHAE)))) (first z))))
        (refl)
        (concat-ap-rev-ap-id A B 
            (hasInverse-retraction-composite A B f (first fisHAE) (first z)) 
            (first z) 
            f 
            (((first (second (first fisHAE)))) (first z)))
        (second z)

#def isHAE-fib-base-path-transport-HAE-final-reduction
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (concat B (f (first z)) (f (first z)) b (refl) (second z)) = (second z)
    := refl-concat B (f (first z)) b (second z)

#def isHAE-fib-base-path-transport-path 
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (transport A (\x -> (f x) = b) 
        ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
        (isHAE-fib-base-path A B f fisHAE b z)
        ((second (second (first fisHAE))) b)) = (second z)
    := 12ary-concat-alternating ((f (first z)) = b)
    (transport A (\x -> (f x) = b) 
        ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
        (isHAE-fib-base-path A B f fisHAE b z)
        ((second (second (first fisHAE))) b))
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
                (isHAE-fib-base-path A B f fisHAE b z))) ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport A B f fisHAE b z)
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) b) f 
            (concat A 
            (first z) 
            ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
            ((hasInverse-inverse A B f (first fisHAE)) b) 
            (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z)))
            (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z)))))) ((second (second (first fisHAE))) b))    
    (isHAE-fib-base-path-transport-rev-calculation A B f fisHAE b z)
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (rev A 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                (ap B A b (f (first z)) (hasInverse-inverse A B f (first fisHAE))
                    (rev B (f (first z)) b (second z))))))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-ap-calculation A B f fisHAE b z)
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B 
                ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) 
                ((hasInverse-inverse A B f (first fisHAE)) b) 
                f
                (ap B A (f (first z)) b (hasInverse-inverse A B f (first fisHAE)) (second z))
                ))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-rev-ap-rev-calculation A B f fisHAE b z) 
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) b)) b 
        (concat B 
            (f (first z)) 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z)))
        ((second (second (first fisHAE))) b))
    (isHAE-fib-base-path-transport-ap-ap-calculation A B f fisHAE b z) 
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B 
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f ((hasInverse-inverse A B f (first fisHAE)) b))
            b
            (ap B B (f (first z)) b (composition B A B f (hasInverse-inverse A B f (first fisHAE))) (second z))
            ((second (second (first fisHAE))) b)))
    (isHAE-fib-base-path-transport-assoc-calculation A B f fisHAE b z)
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (ap B B (f (first z)) b (identity B) (second z))))
    (isHAE-fib-base-path-transport-nat-calculation A B f fisHAE b z)   
    (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) b 
        (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
        (concat B
            (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) 
            (f (first z))
            b
            ((second (second (first fisHAE))) (f (first z)))
            (second z)))
    (isHAE-fib-base-path-transport-ap-id-calculation A B f fisHAE b z)
    (concat B (f (first z)) (f (first z)) b 
            (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
             ((second (second (first fisHAE))) (f (first z))))
            (second z))
    (isHAE-fib-base-path-transport-reassoc-calculation A B f fisHAE b z)   
    (concat B (f (first z)) (f (first z)) b 
            (concat B (f (first z)) (f ((hasInverse-inverse A B f (first fisHAE)) (f (first z)))) (f (first z))
            (ap A B (first z) ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) f
                (rev A ((hasInverse-inverse A B f (first fisHAE)) (f (first z))) (first z) 
                ((first (second (first fisHAE))) (first z))))
            (ap A B (hasInverse-retraction-composite A B f (first fisHAE) (first z)) (first z) f 
                (((first (second (first fisHAE)))) (first z))))
            (second z))
    (isHAE-fib-base-path-transport-HAE-calculation A B f fisHAE b z)
    (concat B (f (first z)) (f (first z)) b (refl) (second z))   
    (isHAE-fib-base-path-transport-HAE-reduction A B f fisHAE b z)
    (second z)
    (isHAE-fib-base-path-transport-HAE-final-reduction A B f fisHAE b z)
```

Finally, we may define the contracting homotopy:

```rzk
#def isHAE-fib-contracting-homotopy
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f)             -- first fisHAE : hasInverse A B f
    (b : B)
    (z : fib A B f b)
    : (isHAE-isSurj A B f fisHAE b) = z
    := pair-of-paths-to-path-of-pairs A (\x -> (f x) = b) 
        ((hasInverse-inverse A B f (first fisHAE)) b) (first z) 
        (isHAE-fib-base-path A B f fisHAE b z)
        ((second (second (first fisHAE))) b)
        (second z)
        (isHAE-fib-base-path-transport-path A B f fisHAE b z)
```

Half adjoint equivalences define contractible maps:

```rzk
#def isHAE-isContr-map
    (A B : U)
    (f : A -> B)
    (fisHAE : isHalfAdjointEquiv A B f) 
    : isContr-map A B f
    := \b -> (isHAE-isSurj A B f fisHAE b, \z -> isHAE-fib-contracting-homotopy A B f fisHAE b z)
```

## Equivalences are contractible maps

```rzk
#def isEquiv-isContr-map
    (A B : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f) 
    : isContr-map A B f
    := \b -> (isHAE-isSurj A B f (isEquiv-isHalfAdjointEquiv A B f fisequiv) b, 
                \z -> isHAE-fib-contracting-homotopy A B f (isEquiv-isHalfAdjointEquiv A B f fisequiv) b z)

#def isContr-map-iff-isEquiv
    (A B : U)
    (f : A -> B)
    : iff (isContr-map A B f) (isEquiv A B f)
    := (isContr-map-isEquiv A B f, isEquiv-isContr-map A B f)
```

## Fiber of total map

We now calculate the fiber of the map on total spaces associated to a family of maps.

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
    := \(b, p) -> ((first w, b),  fibered-path-to-sigma-path A C (first w) (f (first w) b) (second w) p)

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
    : hasRetraction 
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
    : hasSection 
        (fib (B (first w)) (C (first w)) (f (first w)) (second w))
        (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w)
        (total-map-to-fiber A B C f w)
    := (total-map-from-fiber A B C f w, 
            \(z, p) -> idJ((∑ (x : A), C x), ((first z, f (first z) (second z))), \w' p' -> 
            ((total-map-to-fiber A B C f w') ((total-map-from-fiber A B C f w') (z, p'))) 
                =_{(fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) w')} (z, p'), refl, w, p))

#def total-map-to-fiber-isEquiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps    
    (w : (∑ (x : A), C x))
    : isEquiv 
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
    := (total-map-to-fiber A B C f w, total-map-to-fiber-isEquiv A B C f w)
```

## Families of equivalences

A family of equivalences induces an equivalence on total spaces and conversely. It will be easiest to work with the incoherent notion of two-sided-inverses.

```rzk
#def invertible-family-total-inverse
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> hasInverse (B a) (C a) (f a))   -- an invertible family of maps
    : (∑ (x : A), C x) -> (∑ (x : A), B x)      -- the inverse map on total spaces
    := \(a, c) -> (a, (hasInverse-inverse (B a) (C a) (f a) (invfamily a)) c)

#def invertible-family-total-retraction
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> hasInverse (B a) (C a) (f a))   -- an invertible family of maps
    : hasRetraction (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily, 
        \(a, b) -> (fibered-path-to-sigma-path A B a ((hasInverse-inverse (B a) (C a) (f a) (invfamily a)) (f a b)) b 
        ((first (second (invfamily a))) b)))

#def invertible-family-total-section
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> hasInverse (B a) (C a) (f a))   -- an invertible family of maps
    : hasSection (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily, 
        \(a, c) -> (fibered-path-to-sigma-path A C a (f a ((hasInverse-inverse (B a) (C a) (f a) (invfamily a)) c)) c 
        ((second (second (invfamily a))) c)))

#def invertible-family-total-invertible
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))             -- a family of maps
    (invfamily : (a : A) -> hasInverse (B a) (C a) (f a))   -- an invertible family of maps
    : hasInverse (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := (invertible-family-total-inverse A B C f invfamily, 
        (second (invertible-family-total-retraction A B C f invfamily), 
        second (invertible-family-total-section A B C f invfamily) ))

#def family-of-equiv-total-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                        -- a family of maps
    (familyequiv : (a : A) -> isEquiv (B a) (C a) (f a))   -- a family of equivalences
    : isEquiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := hasInverse-isEquiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
        (invertible-family-total-invertible A B C f 
            (\a -> isEquiv-hasInverse (B a) (C a) (f a) (familyequiv a)))

#def family-Eq-total-Eq
    (A : U)
    (B C : A -> U)
    (familyeq : (a : A) -> Eq (B a) (C a))       -- a family of equivalences
    : Eq (∑ (x : A), B x) (∑ (x : A), C x) 
    := (family-of-maps-total-map A B C (\a -> first (familyeq a)), 
    family-of-equiv-total-equiv A B C (\a -> first (familyeq a)) (\a -> second (familyeq a)))
```

The one-way result: that a family of equivalence gives an invertible map (and thus an equivalence) on total spaces.

```rzk
#def family-of-equiv-total-invertible
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (familyequiv : (a : A) -> isEquiv (B a) (C a) (f a))    -- a family of equivalences
    : hasInverse (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
    := invertible-family-total-invertible A B C f (\a -> isEquiv-hasInverse (B a) (C a) (f a) (familyequiv a))
```

For the converse, we make use of our calculation on fibers. The first implication could be proven similarly.

```rzk
#def total-contr-map-family-of-contr-maps
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (totalcontrmap : isContr-map (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    (a : A)
    : isContr-map (B a) (C a) (f a) 
    := \c -> isEquiv-toContr-isContr 
                (fib (B a) (C a) (f a) c)
                (fib (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f) ((a, c)))
                (total-map-fiber-equiv A B C f ((a, c)))
                (totalcontrmap ((a, c)))

#def total-equiv-family-of-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    (totalequiv : isEquiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    (a : A)
    : isEquiv (B a) (C a) (f a) 
    := isContr-map-isEquiv (B a) (C a) (f a) 
        (total-contr-map-family-of-contr-maps A B C f 
            (isEquiv-isContr-map (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f)
                totalequiv)
            a)
```

In summary, a family of maps is an equivalence iff the map on total spaces is an equivalence.
```rzk
#def total-equiv-iff-family-of-equiv
    (A : U)
    (B C : A -> U)
    (f : (a : A) -> (B a) -> (C a))                         -- a family of maps
    : iff ((a : A) -> isEquiv (B a) (C a) (f a)) (isEquiv (∑ (x : A), B x) (∑ (x : A), C x) (family-of-maps-total-map A B C f))
    := (family-of-equiv-total-equiv A B C f, total-equiv-family-of-equiv A B C f)
```