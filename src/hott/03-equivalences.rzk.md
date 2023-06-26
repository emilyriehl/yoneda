# 3. Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sections, retractions, and equivalences

```rzk
#section is-equiv

#variables A B : U

#def hasSection
    (f : A -> B)
    : U
    := ∑ (s : B -> A), homotopy B B (composition B A B f s)(identity B)

#def hasRetraction
    (f : A -> B)
    : U
    := ∑ (r : B -> A), homotopy A A (composition A B A r f)(identity A)

-- equivalences are bi-invertible maps
#def isEquiv
    (f : A -> B)
    : U
    := prod (hasRetraction f) (hasSection f)

#end is-equiv
```

## Equivalence data

```rzk
#section equivalence-data

#variables A B : U
#variable f : A -> B
#variable fisequiv : isEquiv A B f

#def isEquiv-section uses (f)
    : B -> A
    := (first (second fisequiv))

#def isEquiv-retraction uses (f)
    : B -> A
    := (first (first fisequiv))

-- the homotopy between the section and retraction of an equivalence
#def isEquiv-htpic-inverses uses (f)
    : homotopy B A isEquiv-section isEquiv-retraction
    := homotopy-composition B A
            (isEquiv-section)
            (triple-composition B A B A isEquiv-retraction f isEquiv-section)
            (isEquiv-retraction)
            (homotopy-rev B A
                (triple-composition B A B A isEquiv-retraction f isEquiv-section)
                isEquiv-section
                (homotopy-prewhisker B A A
                    (composition A B A isEquiv-retraction f)
                    (identity A)
                    (second (first fisequiv))
                    isEquiv-section))
            (homotopy-postwhisker B B A
                (composition B A B f isEquiv-section)
                (identity B)
                (second (second fisequiv))
                isEquiv-retraction)

#end equivalence-data
```

## Invertible maps

```rzk
-- the following type of more coherent equivalences is not a proposition
#def hasInverse
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (g : B -> A),    -- A two-sided inverse
        (prod
            (homotopy A A (composition A B A g f)(identity A))    -- The retracting homotopy
            (homotopy B B (composition B A B f g)(identity B)))   -- The section homotopy
```

## Equivalences are invertible maps

```rzk
-- invertible maps are equivalences
#def hasInverse-isEquiv
    (A B : U)
    (f : A -> B)
    (fhasinverse : hasInverse A B f)
    : isEquiv A B f
  := ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

-- equivalences are invertible
#def isEquiv-hasInverse
    (A B : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    : hasInverse A B f
    := (isEquiv-section A B f fisequiv,
            (homotopy-composition A A
                (composition A B A (isEquiv-section A B f fisequiv) f)
                (composition A B A (isEquiv-retraction A B f fisequiv) f)
                (identity A)
                    (homotopy-prewhisker A B A
                        (isEquiv-section A B f fisequiv)
                        (isEquiv-retraction A B f fisequiv)
                        (isEquiv-htpic-inverses A B f fisequiv)
                        f)
                    (second (first fisequiv)) ,
            second (second  fisequiv)))
```

## Invertible map data

```rzk
#section has-inverse-data

#variables A B : U
#variable f : A -> B
#variable fhasinverse : hasInverse A B f

-- The inverse of a map with an inverse
#def hasInverse-inverse uses (f)
    : B -> A
    := first (fhasinverse)

-- Some iterated composites associated to a pair of invertible maps.
#def hasInverse-retraction-composite uses (B fhasinverse)
    : A -> A
    := composition A B A hasInverse-inverse f

#def hasInverse-section-composite uses (A fhasinverse)
    : B -> B
    := composition B A B f hasInverse-inverse

-- This composite is parallel to f; we won't need the dual notion.
#def hasInverse-triple-composite uses (fhasinverse)
    : A -> B
    := triple-composition A B A B f hasInverse-inverse f

-- This composite is also parallel to f; again we won't need the dual notion.
#def hasInverse-quintuple-composite uses (fhasinverse)
    : A -> B
    := \a -> f (hasInverse-inverse (f (hasInverse-inverse (f a))))
#end has-inverse-data
```

## Half adjoint equivalences

```rzk
-- We'll require a more coherent notion of equivalence
#def isHalfAdjointEquiv
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (hasInverse A B f)),
            (a : A) -> (((second (second fhasinverse))) (f a)) =
                        (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (((first (second fhasinverse))) a))

-- By function extensionality, the previous definition coincides with the following one:
#def ALTisHalfAdjointEquiv
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (hasInverse A B f)),
            ((homotopy-prewhisker A B B
                (hasInverse-section-composite A B f fhasinverse) (identity B) (second (second fhasinverse)) f)
            = ((homotopy-postwhisker A A B
                (hasInverse-retraction-composite A B f fhasinverse) (identity A) (first (second fhasinverse)) f)))
```

## Coherence data from an invertible map

```rzk
-- To promote an invertible map to a half adjoint equivalence we keep one homotopy and discard the other
#def hasInverse-kept-htpy
    (A B : U)
    (f : A -> B)
    (fhasinverse : hasInverse A B f)
    : homotopy A A (hasInverse-retraction-composite A B f fhasinverse) (identity A)
    := (first (second fhasinverse))

#def hasInverse-discarded-htpy
    (A B : U)
    (f : A -> B)
    (fhasinverse : hasInverse A B f)
    : homotopy B B (hasInverse-section-composite A B f fhasinverse) (identity B)
    := (second (second fhasinverse))

#section has-inverse-coherence

#variables A B : U
#variable f : A -> B
#variable fhasinverse : hasInverse A B f
#variable a : A

-- the required coherence will be built by transforming an instance of this naturality square
#def hasInverse-discarded-naturality-square
    : concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse)(hasInverse-kept-htpy A B f fhasinverse a))
            (hasInverse-discarded-htpy A B f fhasinverse (f a))
                =
            concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := nat-htpy A B (hasInverse-triple-composite A B f fhasinverse) f
            (\x -> hasInverse-discarded-htpy A B f fhasinverse (f x))
            (hasInverse-retraction-composite A B f fhasinverse a) (a) (hasInverse-kept-htpy A B f fhasinverse a)

-- building a path that will be whiskered into the naturality square above
#def hasInverse-cocone-homotopy-coherence
    : (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
            = ap A A (hasInverse-retraction-composite A B f fhasinverse a) a
                (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)
    := cocone-naturality-coherence A (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse) a

#def hasInverse-ap-cocone-homotopy-coherence
    : ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
            (hasInverse-retraction-composite A B f fhasinverse a)
            f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
        = ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                 (hasInverse-retraction-composite A B f fhasinverse a) f
                 (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
    := ap-htpy A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
            (hasInverse-retraction-composite A B f fhasinverse a) f
            (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a
                    (hasInverse-retraction-composite A B f fhasinverse)
                    (hasInverse-kept-htpy A B f fhasinverse a))
            hasInverse-cocone-homotopy-coherence

#def hasInverse-cocone-coherence
    : ap A B
            (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
            (hasInverse-retraction-composite A B f fhasinverse a)
                f
                (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
            =
        (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a
            (hasInverse-triple-composite A B f fhasinverse)
            (hasInverse-kept-htpy A B f fhasinverse a))
    := concat ((hasInverse-quintuple-composite A B f fhasinverse a) = (hasInverse-triple-composite A B f fhasinverse a))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                (hasInverse-retraction-composite A B f fhasinverse a) f
                (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse)
                (hasInverse-kept-htpy A B f fhasinverse a))
            hasInverse-ap-cocone-homotopy-coherence
            (rev-ap-comp A A B (hasInverse-retraction-composite A B f fhasinverse a) a
                (hasInverse-retraction-composite A B f fhasinverse)
                f
                (hasInverse-kept-htpy A B f fhasinverse a))

-- this morally gives the half adjoint inverse coherence; it just requires rotation
#def hasInverse-replaced-naturality-square
    : concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                (hasInverse-retraction-composite A B f fhasinverse a) f
                (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
            (hasInverse-discarded-htpy A B f fhasinverse (f a))
                =
        concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := concat ((hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (f a))
            (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) (hasInverse-retraction-composite A B f fhasinverse a) f
                (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
                (hasInverse-discarded-htpy A B f fhasinverse (f a)))
            (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
                (hasInverse-discarded-htpy A B f fhasinverse (f a)))
            (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
                (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a))
                (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a)))
            (homotopy-concat B
                (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
                (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse)
                    (hasInverse-kept-htpy A B f fhasinverse a))
                hasInverse-cocone-coherence
                (hasInverse-discarded-htpy A B f fhasinverse (f a)))
            hasInverse-discarded-naturality-square

-- This will replace the discarded homotopy
#def hasInverse-corrected-htpy
    : homotopy B B (hasInverse-section-composite A B f fhasinverse) (\b -> b)
    := \b -> concat B
                ((hasInverse-section-composite A B f fhasinverse) b)
                ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
                b
                (rev B ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
                ((hasInverse-section-composite A B f fhasinverse) b)
                (hasInverse-discarded-htpy A B f fhasinverse ((hasInverse-section-composite A B f fhasinverse) b)))
                (concat B
                    ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
                    ((hasInverse-section-composite A B f fhasinverse) b)
                    b
                    (ap A B ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse b))
                        (hasInverse-inverse A B f fhasinverse b) f
                        ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse b)))
                    ((hasInverse-discarded-htpy A B f fhasinverse b)))

-- this is the half adjoint coherence
#def hasInverse-coherence
    : (hasInverse-corrected-htpy (f a))
                = (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := triangle-rotation B
            (hasInverse-quintuple-composite A B f fhasinverse a)(hasInverse-triple-composite A B f fhasinverse a) (f a)
            (concat B
                ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) (f a)))
                ((hasInverse-section-composite A B f fhasinverse) (f a))
                (f a)
            (ap A B
                ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse (f a)))
                (hasInverse-inverse A B f fhasinverse (f a))
                f ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse (f a))))
            ((hasInverse-discarded-htpy A B f fhasinverse (f a))))
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a)) hasInverse-replaced-naturality-square
#end has-inverse-coherence
```

## Invertible maps are half adjoint equivalences

```rzk
-- to promote an invertible map to a half adjoint equivalence we change the data of the invertible map by replacing the discarded homotopy with the corrected one.
#def hasInverse-correctedhasInverse
    (A B : U)
    (f : A -> B)
    (fhasinverse : hasInverse A B f)
    : hasInverse A B f
    := (hasInverse-inverse A B f fhasinverse, (hasInverse-kept-htpy A B f fhasinverse, hasInverse-corrected-htpy A B f fhasinverse))

-- Invertible maps are half adjoint equivalences!
#def hasInverse-isHalfAdjointEquiv
    (A B : U)
    (f : A -> B)
    (fhasinverse : hasInverse A B f)
    : isHalfAdjointEquiv A B f
    := (hasInverse-correctedhasInverse A B f fhasinverse, hasInverse-coherence A B f fhasinverse)

-- Equivalences are half adjoint equivalences!
#def isEquiv-isHalfAdjointEquiv
    (A B : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    : isHalfAdjointEquiv A B f
    := hasInverse-isHalfAdjointEquiv A B f (isEquiv-hasInverse A B f fisequiv)
```

## Composing equivalences

```rzk
-- The type of equivalences between types uses the propositional notion isEquiv rather than the incoherent hasInverse.
#def Eq
    (A B : U)
    : U
    :=  ∑ (f : A -> B), ((isEquiv A) B) f

-- The data of an equivalence is not symmetric so we promote an equivalence to an invertible map to prove symmetry
#def sym_Eq
    (A B : U)
    (e : Eq A B)
    : Eq B A
    := (first (isEquiv-hasInverse A B (first e) (second e)) ,
            (( first e ,
                second (second (isEquiv-hasInverse A B (first e) (second e))) ) ,
            ( first e ,
                first (second (isEquiv-hasInverse A B (first e) (second e))) ) ))

-- Composition of equivalences in diagrammatic order.
#def compose_Eq
    (A B C : U)
    (A=B : Eq A B)
    (B=C : Eq B C)
    : Eq A C
    := (\a -> (first B=C) ((first A=B) a), -- the composite equivalence
             ((\c -> (first (first (second A=B))) ((first (first (second (B=C)))) c),
            (\a ->
                concat A
                ((first (first (second A=B))) ((first (first (second B=C))) ((first B=C) ((first A=B) a))))
                ((first (first (second A=B))) ((first A=B) a))
                a
                (ap B A
                    ((first (first (second B=C))) ((first B=C) ((first A=B) a))) -- should be inferred
                    ((first A=B) a) -- should be inferred
                    (first (first (second A=B)))
                    ((second (first (second B=C))) ((first A=B) a)))
                ((second (first (second A=B))) a))),
                    (\c -> (first (second (second A=B))) ((first (second (second (B=C)))) c),
            (\c ->
                concat C
                ((first B=C) ((first A=B) ((first (second (second A=B))) ((first (second (second B=C))) c))))
                ((first B=C) ((first (second (second B=C))) c))
                c
                (ap B C
                    ((first A=B) ((first (second (second A=B))) ((first (second (second B=C))) c))) -- should be inferred
                    ((first (second (second B=C))) c) -- should be inferred
                    (first B=C)
                    ((second (second (second A=B))) ((first (second (second B=C))) c)))
                ((second (second (second B=C))) c)))))

-- now we compose the functions that are equivalences
#def compose_isEquiv
    (A B C : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (g : B -> C)
    (gisequiv : isEquiv B C g)
    : isEquiv A C (composition A B C g f)
    := ((composition C B A (isEquiv-retraction A B f fisequiv) (isEquiv-retraction B C g gisequiv),
        \a ->
            concat A
            ((isEquiv-retraction A B f fisequiv) ((isEquiv-retraction B C g gisequiv) (g (f a))))
            ((isEquiv-retraction A B f fisequiv) (f a))
            a
            (ap B A
                ((isEquiv-retraction B C g gisequiv) (g (f a))) -- should be inferred
                (f a) -- should be inferred
                (isEquiv-retraction A B f fisequiv)
                ((second (first gisequiv)) (f a)))
            ((second (first fisequiv)) a)),
        (composition C B A (isEquiv-section A B f fisequiv) (isEquiv-section B C g gisequiv),
        \c ->
            concat C
            (g (f ((first (second fisequiv)) ((first (second gisequiv)) c))))
            (g ((first (second gisequiv)) c))
            c
            (ap B C
                (f ((first (second fisequiv)) ((first (second gisequiv)) c))) -- should be inferred
                ((first (second gisequiv)) c) -- should be inferred
                g
               ((second (second fisequiv)) ((first (second gisequiv)) c)))
            ((second (second gisequiv)) c)))

-- Right cancellation of equivalences in diagrammatic order.
#def RightCancel_Eq
    (A B C : U)
    (A=C : Eq A C)
    (B=C : Eq B C)
    : Eq A B
    := compose_Eq A C B (A=C) (sym_Eq B C B=C)

-- Left cancellation of equivalences in diagrammatic order.
#def LeftCancel_Eq
    (A B C : U)
    (A=B : Eq A B)
    (A=C : Eq A C)
    : Eq B C
    := compose_Eq B A C (sym_Eq A B A=B) (A=C)

-- a composition of three equivalences
#def triple_compose_Eq
    (A B C D : U)
    (A=B : Eq A B)
    (B=C : Eq B C)
    (C=D : Eq C D)
    : Eq A D
    := compose_Eq A B D (A=B) (compose_Eq B C D B=C C=D)

#def triple_compose_isEquiv
    (A B C D : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (g : B -> C)
    (gisequiv : isEquiv B C g)
    (h : C -> D)
    (hisequiv : isEquiv C D h)
    : isEquiv A D (triple-composition A B C D h g f)
    := compose_isEquiv A B D f fisequiv (composition B C D h g) (compose_isEquiv B C D g gisequiv h hisequiv)
```

## Equivalences and homotopy

If a map is homotopic to an equivalence it is an equivalence.

```rzk
#def isEquiv-homotopic-isEquiv
    (A B : U)
    (f g : A -> B)
    (H : homotopy A B f g)
    (gisequiv : isEquiv A B g)
    : isEquiv A B f
    := ((first (first gisequiv),
        \a -> concat A
            ((first (first gisequiv)) (f a))
            ((first (first gisequiv)) (g a))
            a
            (ap B A (f a) (g a) (first (first gisequiv)) (H a))
            ((second (first gisequiv)) a))
        ,(first (second gisequiv),
        \b -> concat B
            (f ((first (second gisequiv)) b))
            (g ((first (second gisequiv)) b))
            b
            (H ((first (second gisequiv)) b))
            ((second (second gisequiv)) b)
            ))
```

## Equivalences of identity types

Equivalent types have equivalent identity types.

```rzk
#section equiv-identity-types-equiv

#variables A B : U
#variable f : A -> B
#variable fisHAE : isHalfAdjointEquiv A B f

#def iff-ap-isHalfAdjointEquiv
    (x y : A)
    : iff (x = y) (f x = f y)
    := (ap A B x y f , \q ->
        triple-concat A x ((hasInverse-inverse A B f (first fisHAE)) (f x))
            ((hasInverse-inverse A B f (first fisHAE)) (f y)) y
            (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x))
            (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q)
            ((first (second (first fisHAE))) y))

#def hasRetraction-ap-isHalfAdjointEquiv
    (x y : A)
    : hasRetraction (x = y) (f x = f y) (ap A B x y f)
    := (second (iff-ap-isHalfAdjointEquiv x y), \p ->
            idJ(A, x,
                \y' p' ->
                    (second (iff-ap-isHalfAdjointEquiv x y')) (ap A B x y' f p') = p',
                (rev-refl-id-triple-concat A ((hasInverse-inverse A B f (first fisHAE)) (f x)) x
                    ((first (second (first fisHAE))) x)),
                    y, p))

#def ap-triple-concat-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : ap A B x y f ((second (iff-ap-isHalfAdjointEquiv x y)) q) =
        (triple-concat B
            (f x)
            (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
            (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
            (f y)
            (ap A B x ((hasInverse-inverse A B f (first fisHAE)) (f x)) f
            (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
            (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
                ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
            (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := ap-triple-concat A B
                x ((hasInverse-inverse A B f (first fisHAE)) (f x))
                ((hasInverse-inverse A B f (first fisHAE)) (f y)) y
                f
                (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x))
                (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q)
                ((first (second (first fisHAE))) y)

#def ap-rev-homotopy-triple-concat-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (ap A B x ((hasInverse-inverse A B f (first fisHAE)) (f x)) f
        (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
        ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
        ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := homotopy-triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (ap A B x ((hasInverse-inverse A B f (first fisHAE)) (f x)) f
        (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
        ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y))
        (ap-rev A B (hasInverse-retraction-composite A B f (first fisHAE) x) x f ((first (second (first fisHAE))) x))

#def ap-ap-homotopy-triple-concat-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
        ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := triple-homotopy-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
            ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y))
        (rev-ap-comp B A B (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) f q)

-- This needs to be reversed later.
#def triple-concat-higher-homotopy-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y))) =
    (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := triple-concat-higher-homotopy A B
        (hasInverse-triple-composite A B f (first fisHAE)) f (\a -> (((second (second (first fisHAE)))) (f a))) (\a -> (ap A B (hasInverse-retraction-composite A B f (first fisHAE) a) a f (((first (second (first fisHAE)))) a)))
        (second fisHAE)
        x y (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)

#def triple-concat-nat-htpy-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y)))
    = ap B B (f x) (f y) (identity B) q
    := triple-concat-nat-htpy B B (hasInverse-section-composite A B f (first fisHAE)) (identity B)
        ((second (second (first fisHAE)))) (f x) (f y) q

#def zag-zig-concat-triple-concat-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = ap B B (f x) (f y) (identity B) q
    := zag-zig-concat (f x = f y)
        (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y)))
        (ap B B (f x) (f y) (identity B) q)
        (triple-concat-higher-homotopy-isHalfAdjointEquiv x y q)
        (triple-concat-nat-htpy-isHalfAdjointEquiv x y q)

#def triple-concat-reduction-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : ap B B (f x) (f y) (identity B) q = q
    := ap-id B (f x) (f y) q

#def section-htpy-ap-isHalfAdjointEquiv
    (x y : A)
    (q : f x = f y)
    : ap A B x y f ((second (iff-ap-isHalfAdjointEquiv x y)) q) = q
    := quintuple-concat-alternating (f x = f y)
        (ap A B x y f ((second (iff-ap-isHalfAdjointEquiv x y)) q))
        (triple-concat B
            (f x)
            (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
            (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
            (f y)
            (ap A B x ((hasInverse-inverse A B f (first fisHAE)) (f x)) f
            (rev A (hasInverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
            (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
                ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
            (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-triple-concat-isHalfAdjointEquiv x y q)
        (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x))
        ((hasInverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (hasInverse-inverse A B f (first fisHAE)) q))
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-rev-homotopy-triple-concat-isHalfAdjointEquiv x y q)
        (triple-concat B
        (f x)
        (f ((hasInverse-inverse A B f (first fisHAE)) (f x)))
        (f ((hasInverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (hasInverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (hasInverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((hasInverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-ap-homotopy-triple-concat-isHalfAdjointEquiv x y q)
        (ap B B (f x) (f y) (identity B) q)
        (zag-zig-concat-triple-concat-isHalfAdjointEquiv x y q)
        q
        (triple-concat-reduction-isHalfAdjointEquiv x y q)

#def hasSection-ap-isHalfAdjointEquiv uses (fisHAE)
    (x y : A)
    : hasSection (x = y) (f x = f y) (ap A B x y f)
    := (second (iff-ap-isHalfAdjointEquiv x y), section-htpy-ap-isHalfAdjointEquiv x y)

#def isEquiv-ap-isHalfAdjointEquiv uses (fisHAE)
    (x y : A)
    : isEquiv (x = y) (f x = f y) (ap A B x y f)
    := (hasRetraction-ap-isHalfAdjointEquiv x y, hasSection-ap-isHalfAdjointEquiv x y)
#end equiv-identity-types-equiv

#def isEquiv-ap-isEquiv
    (A B : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (x y : A)
    : isEquiv (x = y) (f x = f y)(ap A B x y f)
    := isEquiv-ap-isHalfAdjointEquiv A B f (isEquiv-isHalfAdjointEquiv A B f fisequiv) x y

#def Eq-ap-isEquiv
    (A B : U)
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (x y : A)
    : Eq (x = y) (f x = f y)
    := (ap A B x y f, isEquiv-ap-isEquiv A B f fisequiv x y)
```

```rzk
#def rev-Retraction
    (A : U)
    (y : A)
    : (x : A) -> hasRetraction (x = y) (y = x) ((\p -> ((rev A x y) p)))
    := \x ->
       ((rev A y x), \p -> idJ(A, x, \y' p' -> ((composition (x = y') (y' = x) (x = y') (rev A y' x) (rev A x y'))(p') =_{x = y'} p'), refl, y, p))

#def rev-Section
    (A : U)
    (y : A)
    : (x : A) -> hasSection (x = y) (y = x) ((\p -> ((rev A x y) p)))
    := \x ->
       ((rev A y x), \p -> idJ(A, y, \x' p' -> ((composition (y = x') (x' = y) (y = x') (rev A x' y) (rev A y x'))(p') =_{y = x'} p'), refl, x, p))

#def rev-isEquiv
    (A : U)
    (x y : A)
    : isEquiv (x = y) (y = x) (rev A x y)
    := ((rev-Retraction A y x), (rev-Section A y x))
```


## Function extensionality

By path induction, an identification between functions defines a homotopy

```rzk
#def htpy-eq
    (X : U)
    (A : X -> U)
    (f g : (x : X) -> A x)
    (p : f = g)
    : (x : X) -> (f x = g x)
    := idJ((x : X) -> A x, f, \g' p' -> (x : X) -> (f x = g' x), \x -> refl, g, p)
```

The function extensionality axiom asserts that this map defines a family of
equivalences.

```rzk
-- The type that encodes the function extensionality axiom.
#def FunExt : U
    := (X : U) -> (A : X -> U) ->
    (f : (x : X) -> A x) -> (g : (x : X) -> A x) ->
        isEquiv (f = g)((x : X) -> f x = g x)(htpy-eq X A f g)

-- The equivalence provided by function extensionality.
#def FunExtEq
    (funext : FunExt)
    (X : U)
    (A : X -> U)
    (f g : (x : X) -> A x)
    : Eq (f = g) ((x : X) -> f x = g x)
    := (htpy-eq X A f g, funext X A f g)

-- In particular, function extensionality implies that homotopies give rise to identifications. This definition defines eq-htpy to be the retraction to htpy-eq.
#def eq-htpy
    (funext : FunExt)
    (X : U)
    (A : X -> U)
    (f g : (x : X) -> A x)
    : ((x : X) -> f x = g x) -> (f = g)
    := first (first (funext X A f g))

-- Using function extensionality, a fiberwise equivalence defines an equivalence of dependent function types
#def fibered-Eq-function-Eq
    (funext : FunExt)
    (X : U)
    (A B : X -> U)
    (fibequiv : (x : X) -> Eq (A x) (B x))
    : Eq ((x : X) -> A x) ((x : X) -> B x)
    := ((\a -> \x -> (first (fibequiv x)) (a x)),
            (((\b -> \x -> (first (first (second (fibequiv x)))) (b x)),
                \a -> eq-htpy funext X A (\x -> (first (first (second (fibequiv x)))) ((first (fibequiv x)) (a x))) a (\x -> (second (first (second (fibequiv x)))) (a x))),
           ((\b -> \x -> (first (second (second (fibequiv x)))) (b x)),
            (\b -> eq-htpy funext X B (\x -> (first (fibequiv x)) ((first (second (second (fibequiv x)))) (b x))) b (\x -> (second (second (second (fibequiv x)))) (b x))))))
```

```

```

## Embeddings

```rzk
#def isEmb
  (A B : U)
  (f : A -> B)
  : U
  := (x : A) -> (y : A) -> isEquiv (x = y) (f x = f y) (ap A B x y f)

#def Emb
  (A B : U)
  : U
  := (∑ (f : A -> B), isEmb A B f)

#def inhabited-emb-implies-emb
  (A B : U)
  (f : A -> B)
  (e : A -> isEmb A B f)
  : isEmb A B f
  := \x -> \y -> e x x y
```

```rzk
#def final-projection-of-path-types-of-Unit-has-retr
    (x y : Unit)
    : hasRetraction (x = y) Unit (final-projection (x = y))
    :=
    (\a -> refl, \p -> idJ(Unit, x, \y' p' -> refl =_{x = y'} p', refl, y, p))

#def final-projection-of-path-types-of-Unit-has-sec
    (x y : Unit)
    : hasSection (x = y) Unit (final-projection (x = y))
    :=
    (\a -> refl, \a -> refl)

#def final-projection-of-path-types-of-Unit-isEquiv
    (x y : Unit)
    : isEquiv (x = y) Unit (final-projection (x = y))
    :=
    ((final-projection-of-path-types-of-Unit-has-retr x y), (final-projection-of-path-types-of-Unit-has-sec x y))

```
