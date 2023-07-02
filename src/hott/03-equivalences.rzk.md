# 3. Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sections, retractions, and equivalences

```rzk
#section is-equiv

#variables A B : U

#def has-section
    (f : A -> B)
    : U
    := ∑ (s : B -> A), homotopy B B (composition B A B f s)(identity B)

#def has-retraction
    (f : A -> B)
    : U
    := ∑ (r : B -> A), homotopy A A (composition A B A r f)(identity A)

-- equivalences are bi-invertible maps
#def is-equiv
    (f : A -> B)
    : U
    := prod (has-retraction f) (has-section f)

#end is-equiv
```

## Equivalence data

```rzk
#section equivalence-data

#variables A B : U
#variable f : A -> B
#variable fisequiv : is-equiv A B f

#def is-equiv-section uses (f)
    : B -> A
    := (first (second fisequiv))

#def is-equiv-retraction uses (f)
    : B -> A
    := (first (first fisequiv))

-- the homotopy between the section and retraction of an equivalence
#def is-equiv-htpic-inverses uses (f)
    : homotopy B A is-equiv-section is-equiv-retraction
    := homotopy-composition B A
            (is-equiv-section)
            (triple-composition B A B A is-equiv-retraction f is-equiv-section)
            (is-equiv-retraction)
            (homotopy-rev B A
                (triple-composition B A B A is-equiv-retraction f is-equiv-section)
                is-equiv-section
                (homotopy-prewhisker B A A
                    (composition A B A is-equiv-retraction f)
                    (identity A)
                    (second (first fisequiv))
                    is-equiv-section))
            (homotopy-postwhisker B B A
                (composition B A B f is-equiv-section)
                (identity B)
                (second (second fisequiv))
                is-equiv-retraction)

#end equivalence-data
```

## Invertible maps

```rzk
-- the following type of more coherent equivalences is not a proposition
#def has-inverse
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
#def has-inverse-is-equiv
    (A B : U)
    (f : A -> B)
    (fhasinverse : has-inverse A B f)
    : is-equiv A B f
  := ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

-- equivalences are invertible
#def is-equiv-has-inverse
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    : has-inverse A B f
    := (is-equiv-section A B f fisequiv,
            (homotopy-composition A A
                (composition A B A (is-equiv-section A B f fisequiv) f)
                (composition A B A (is-equiv-retraction A B f fisequiv) f)
                (identity A)
                    (homotopy-prewhisker A B A
                        (is-equiv-section A B f fisequiv)
                        (is-equiv-retraction A B f fisequiv)
                        (is-equiv-htpic-inverses A B f fisequiv)
                        f)
                    (second (first fisequiv)) ,
            second (second  fisequiv)))
```

## Invertible map data

```rzk
#section has-inverse-data

#variables A B : U
#variable f : A -> B
#variable fhasinverse : has-inverse A B f

-- The inverse of a map with an inverse
#def has-inverse-inverse uses (f)
    : B -> A
    := first (fhasinverse)

-- Some iterated composites associated to a pair of invertible maps.
#def has-inverse-retraction-composite uses (B fhasinverse)
    : A -> A
    := composition A B A has-inverse-inverse f

#def has-inverse-section-composite uses (A fhasinverse)
    : B -> B
    := composition B A B f has-inverse-inverse

-- This composite is parallel to f; we won't need the dual notion.
#def has-inverse-triple-composite uses (fhasinverse)
    : A -> B
    := triple-composition A B A B f has-inverse-inverse f

-- This composite is also parallel to f; again we won't need the dual notion.
#def has-inverse-quintuple-composite uses (fhasinverse)
    : A -> B
    := \a -> f (has-inverse-inverse (f (has-inverse-inverse (f a))))
#end has-inverse-data
```

## Half adjoint equivalences

```rzk
-- We'll require a more coherent notion of equivalence
#def is-half-adjoint-equiv
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (has-inverse A B f)),
            (a : A) -> (((second (second fhasinverse))) (f a)) =
                        (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (((first (second fhasinverse))) a))

-- By function extensionality, the previous definition coincides with the following one:
#def is-half-adjoint-equiv'
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (has-inverse A B f)),
            ((homotopy-prewhisker A B B
                (has-inverse-section-composite A B f fhasinverse) (identity B) (second (second fhasinverse)) f)
            = ((homotopy-postwhisker A A B
                (has-inverse-retraction-composite A B f fhasinverse) (identity A) (first (second fhasinverse)) f)))
```

## Coherence data from an invertible map

```rzk
-- To promote an invertible map to a half adjoint equivalence we keep one homotopy and discard the other
#def has-inverse-kept-htpy
    (A B : U)
    (f : A -> B)
    (fhasinverse : has-inverse A B f)
    : homotopy A A (has-inverse-retraction-composite A B f fhasinverse) (identity A)
    := (first (second fhasinverse))

#def has-inverse-discarded-htpy
    (A B : U)
    (f : A -> B)
    (fhasinverse : has-inverse A B f)
    : homotopy B B (has-inverse-section-composite A B f fhasinverse) (identity B)
    := (second (second fhasinverse))

#section has-inverse-coherence

#variables A B : U
#variable f : A -> B
#variable fhasinverse : has-inverse A B f
#variable a : A

-- the required coherence will be built by transforming an instance of this naturality square
#def has-inverse-discarded-naturality-square
    : concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
            (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-triple-composite A B f fhasinverse)(has-inverse-kept-htpy A B f fhasinverse a))
            (has-inverse-discarded-htpy A B f fhasinverse (f a))
                =
            concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
            (has-inverse-discarded-htpy A B f fhasinverse (has-inverse-triple-composite A B f fhasinverse a))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (has-inverse-kept-htpy A B f fhasinverse a))
    := nat-htpy A B (has-inverse-triple-composite A B f fhasinverse) f
            (\x -> has-inverse-discarded-htpy A B f fhasinverse (f x))
            (has-inverse-retraction-composite A B f fhasinverse a) (a) (has-inverse-kept-htpy A B f fhasinverse a)

-- building a path that will be whiskered into the naturality square above
#def has-inverse-cocone-homotopy-coherence
    : (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
            = ap A A (has-inverse-retraction-composite A B f fhasinverse a) a
                (has-inverse-retraction-composite A B f fhasinverse) (has-inverse-kept-htpy A B f fhasinverse a)
    := cocone-naturality-coherence A (has-inverse-retraction-composite A B f fhasinverse) (has-inverse-kept-htpy A B f fhasinverse) a

#def has-inverse-ap-cocone-homotopy-coherence
    : ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
            (has-inverse-retraction-composite A B f fhasinverse a)
            f (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
        = ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                 (has-inverse-retraction-composite A B f fhasinverse a) f
                 (ap A A (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-retraction-composite A B f fhasinverse) (has-inverse-kept-htpy A B f fhasinverse a))
    := ap-htpy A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
            (has-inverse-retraction-composite A B f fhasinverse a) f
            (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                (ap A A (has-inverse-retraction-composite A B f fhasinverse a) a
                    (has-inverse-retraction-composite A B f fhasinverse)
                    (has-inverse-kept-htpy A B f fhasinverse a))
            has-inverse-cocone-homotopy-coherence

#def has-inverse-cocone-coherence
    : ap A B
            (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
            (has-inverse-retraction-composite A B f fhasinverse a)
                f
                (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
            =
        (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a
            (has-inverse-triple-composite A B f fhasinverse)
            (has-inverse-kept-htpy A B f fhasinverse a))
    := concat ((has-inverse-quintuple-composite A B f fhasinverse a) = (has-inverse-triple-composite A B f fhasinverse a))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                (has-inverse-retraction-composite A B f fhasinverse a) f (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a)))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                (has-inverse-retraction-composite A B f fhasinverse a) f
                (ap A A (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-retraction-composite A B f fhasinverse) (has-inverse-kept-htpy A B f fhasinverse a)))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-triple-composite A B f fhasinverse)
                (has-inverse-kept-htpy A B f fhasinverse a))
            has-inverse-ap-cocone-homotopy-coherence
            (rev-ap-comp A A B (has-inverse-retraction-composite A B f fhasinverse a) a
                (has-inverse-retraction-composite A B f fhasinverse)
                f
                (has-inverse-kept-htpy A B f fhasinverse a))

-- this morally gives the half adjoint inverse coherence; it just requires rotation
#def has-inverse-replaced-naturality-square
    : concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
            (ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                (has-inverse-retraction-composite A B f fhasinverse a) f
                (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a)))
            (has-inverse-discarded-htpy A B f fhasinverse (f a))
                =
        concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
            (has-inverse-discarded-htpy A B f fhasinverse (has-inverse-triple-composite A B f fhasinverse a))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (has-inverse-kept-htpy A B f fhasinverse a))
    := concat ((has-inverse-quintuple-composite A B f fhasinverse a) =_{B} (f a))
            (concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a)) (has-inverse-retraction-composite A B f fhasinverse a) f
                (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a)))
                (has-inverse-discarded-htpy A B f fhasinverse (f a)))
            (concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-triple-composite A B f fhasinverse) (has-inverse-kept-htpy A B f fhasinverse a))
                (has-inverse-discarded-htpy A B f fhasinverse (f a)))
            (concat B (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
                (has-inverse-discarded-htpy A B f fhasinverse (has-inverse-triple-composite A B f fhasinverse a))
                (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (has-inverse-kept-htpy A B f fhasinverse a)))
            (homotopy-concat B
                (has-inverse-quintuple-composite A B f fhasinverse a) (has-inverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (has-inverse-retraction-composite A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a))
                    (has-inverse-retraction-composite A B f fhasinverse a) f (has-inverse-kept-htpy A B f fhasinverse (has-inverse-retraction-composite A B f fhasinverse a)))
                (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a (has-inverse-triple-composite A B f fhasinverse)
                    (has-inverse-kept-htpy A B f fhasinverse a))
                has-inverse-cocone-coherence
                (has-inverse-discarded-htpy A B f fhasinverse (f a)))
            has-inverse-discarded-naturality-square

-- This will replace the discarded homotopy
#def has-inverse-corrected-htpy
    : homotopy B B (has-inverse-section-composite A B f fhasinverse) (\b -> b)
    := \b -> concat B
                ((has-inverse-section-composite A B f fhasinverse) b)
                ((has-inverse-section-composite A B f fhasinverse) ((has-inverse-section-composite A B f fhasinverse) b))
                b
                (rev B ((has-inverse-section-composite A B f fhasinverse) ((has-inverse-section-composite A B f fhasinverse) b))
                ((has-inverse-section-composite A B f fhasinverse) b)
                (has-inverse-discarded-htpy A B f fhasinverse ((has-inverse-section-composite A B f fhasinverse) b)))
                (concat B
                    ((has-inverse-section-composite A B f fhasinverse) ((has-inverse-section-composite A B f fhasinverse) b))
                    ((has-inverse-section-composite A B f fhasinverse) b)
                    b
                    (ap A B ((has-inverse-retraction-composite A B f fhasinverse) (has-inverse-inverse A B f fhasinverse b))
                        (has-inverse-inverse A B f fhasinverse b) f
                        ((first (second fhasinverse)) (has-inverse-inverse A B f fhasinverse b)))
                    ((has-inverse-discarded-htpy A B f fhasinverse b)))

-- this is the half adjoint coherence
#def has-inverse-coherence
    : (has-inverse-corrected-htpy (f a))
                = (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (has-inverse-kept-htpy A B f fhasinverse a))
    := triangle-rotation B
            (has-inverse-quintuple-composite A B f fhasinverse a)(has-inverse-triple-composite A B f fhasinverse a) (f a)
            (concat B
                ((has-inverse-section-composite A B f fhasinverse) ((has-inverse-section-composite A B f fhasinverse) (f a)))
                ((has-inverse-section-composite A B f fhasinverse) (f a))
                (f a)
            (ap A B
                ((has-inverse-retraction-composite A B f fhasinverse) (has-inverse-inverse A B f fhasinverse (f a)))
                (has-inverse-inverse A B f fhasinverse (f a))
                f ((first (second fhasinverse)) (has-inverse-inverse A B f fhasinverse (f a))))
            ((has-inverse-discarded-htpy A B f fhasinverse (f a))))
            (has-inverse-discarded-htpy A B f fhasinverse (has-inverse-triple-composite A B f fhasinverse a))
            (ap A B (has-inverse-retraction-composite A B f fhasinverse a) a f (has-inverse-kept-htpy A B f fhasinverse a)) has-inverse-replaced-naturality-square
#end has-inverse-coherence
```

## Invertible maps are half adjoint equivalences

```rzk
-- to promote an invertible map to a half adjoint equivalence we change the data of the invertible map by replacing the discarded homotopy with the corrected one.
#def has-inverse-correctedhas-inverse
    (A B : U)
    (f : A -> B)
    (fhasinverse : has-inverse A B f)
    : has-inverse A B f
    := (has-inverse-inverse A B f fhasinverse, (has-inverse-kept-htpy A B f fhasinverse, has-inverse-corrected-htpy A B f fhasinverse))

-- Invertible maps are half adjoint equivalences!
#def has-inverse-is-half-adjoint-equiv
    (A B : U)
    (f : A -> B)
    (fhasinverse : has-inverse A B f)
    : is-half-adjoint-equiv A B f
    := (has-inverse-correctedhas-inverse A B f fhasinverse, has-inverse-coherence A B f fhasinverse)

-- Equivalences are half adjoint equivalences!
#def is-equiv-is-half-adjoint-equiv
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    : is-half-adjoint-equiv A B f
    := has-inverse-is-half-adjoint-equiv A B f (is-equiv-has-inverse A B f fisequiv)
```

## Composing equivalences

```rzk
-- The type of equivalences between types uses the propositional notion is-equiv rather than the incoherent has-inverse.
#def Eq
    (A B : U)
    : U
    :=  ∑ (f : A -> B), ((is-equiv A) B) f

-- The data of an equivalence is not symmetric so we promote an equivalence to an invertible map to prove symmetry
#def inv-equiv
    (A B : U)
    (e : Eq A B)
    : Eq B A
    := (first (is-equiv-has-inverse A B (first e) (second e)) ,
            (( first e ,
                second (second (is-equiv-has-inverse A B (first e) (second e))) ) ,
            ( first e ,
                first (second (is-equiv-has-inverse A B (first e) (second e))) ) ))

-- Composition of equivalences in diagrammatic order.
#def comp-equiv
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
#def compose-is-equiv
    (A B C : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    (g : B -> C)
    (gisequiv : is-equiv B C g)
    : is-equiv A C (composition A B C g f)
    := ((composition C B A (is-equiv-retraction A B f fisequiv) (is-equiv-retraction B C g gisequiv),
        \a ->
            concat A
            ((is-equiv-retraction A B f fisequiv) ((is-equiv-retraction B C g gisequiv) (g (f a))))
            ((is-equiv-retraction A B f fisequiv) (f a))
            a
            (ap B A
                ((is-equiv-retraction B C g gisequiv) (g (f a))) -- should be inferred
                (f a) -- should be inferred
                (is-equiv-retraction A B f fisequiv)
                ((second (first gisequiv)) (f a)))
            ((second (first fisequiv)) a)),
        (composition C B A (is-equiv-section A B f fisequiv) (is-equiv-section B C g gisequiv),
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
#def right-cancel-equiv
    (A B C : U)
    (A=C : Eq A C)
    (B=C : Eq B C)
    : Eq A B
    := comp-equiv A C B (A=C) (inv-equiv B C B=C)

-- Left cancellation of equivalences in diagrammatic order.
#def left-cancel-equiv
    (A B C : U)
    (A=B : Eq A B)
    (A=C : Eq A C)
    : Eq B C
    := comp-equiv B A C (inv-equiv A B A=B) (A=C)

-- a composition of three equivalences
#def triple-comp-equiv
    (A B C D : U)
    (A=B : Eq A B)
    (B=C : Eq B C)
    (C=D : Eq C D)
    : Eq A D
    := comp-equiv A B D (A=B) (comp-equiv B C D B=C C=D)

#def triple-compose-is-equiv
    (A B C D : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    (g : B -> C)
    (gisequiv : is-equiv B C g)
    (h : C -> D)
    (hisequiv : is-equiv C D h)
    : is-equiv A D (triple-composition A B C D h g f)
    := compose-is-equiv A B D f fisequiv (composition B C D h g) (compose-is-equiv B C D g gisequiv h hisequiv)
```

## Equivalences and homotopy

If a map is homotopic to an equivalence it is an equivalence.

```rzk
#def is-equiv-homotopic-is-equiv
    (A B : U)
    (f g : A -> B)
    (H : homotopy A B f g)
    (gisequiv : is-equiv A B g)
    : is-equiv A B f
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

#def is-equiv-rev-homotopic-is-equiv
    (A B : U)
    (f g : A -> B)
    (H : homotopy A B f g)
    (fisequiv : is-equiv A B f)
    : is-equiv A B g
    := is-equiv-homotopic-is-equiv A B g f (homotopy-rev A B f g H) fisequiv
```

## Equivalences of identity types

Equivalent types have equivalent identity types.

```rzk
#section equiv-identity-types-equiv

#variables A B : U
#variable f : A -> B
#variable fisHAE : is-half-adjoint-equiv A B f

#def iff-ap-is-half-adjoint-equiv
    (x y : A)
    : iff (x = y) (f x = f y)
    := (ap A B x y f , \q ->
        triple-concat A x ((has-inverse-inverse A B f (first fisHAE)) (f x))
            ((has-inverse-inverse A B f (first fisHAE)) (f y)) y
            (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x))
            (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q)
            ((first (second (first fisHAE))) y))

#def has-retraction-ap-is-half-adjoint-equiv
    (x y : A)
    : has-retraction (x = y) (f x = f y) (ap A B x y f)
    := (second (iff-ap-is-half-adjoint-equiv x y), \p ->
            idJ(A, x,
                \y' p' ->
                    (second (iff-ap-is-half-adjoint-equiv x y')) (ap A B x y' f p') = p',
                (rev-refl-id-triple-concat A ((has-inverse-inverse A B f (first fisHAE)) (f x)) x
                    ((first (second (first fisHAE))) x)),
                    y, p))

#def ap-triple-concat-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) =
        (triple-concat B
            (f x)
            (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
            (f y)
            (ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
            (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
            (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
                ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
            (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := ap-triple-concat A B
                x ((has-inverse-inverse A B f (first fisHAE)) (f x))
                ((has-inverse-inverse A B f (first fisHAE)) (f y)) y
                f
                (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x))
                (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q)
                ((first (second (first fisHAE))) y)

#def ap-rev-homotopy-triple-concat-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
        (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
        ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
        ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := homotopy-triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
        (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
        ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y))
        (ap-rev A B (has-inverse-retraction-composite A B f (first fisHAE) x) x f ((first (second (first fisHAE))) x))

#def ap-ap-homotopy-triple-concat-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
        ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := triple-homotopy-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
            ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y))
        (rev-ap-comp B A B (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) f q)

-- This needs to be reversed later.
#def triple-concat-higher-homotopy-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y))) =
    (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    := triple-concat-higher-homotopy A B
        (has-inverse-triple-composite A B f (first fisHAE)) f (\a -> (((second (second (first fisHAE)))) (f a))) (\a -> (ap A B (has-inverse-retraction-composite A B f (first fisHAE) a) a f (((first (second (first fisHAE)))) a)))
        (second fisHAE)
        x y (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)

#def triple-concat-nat-htpy-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y)))
    = ap B B (f x) (f y) (identity B) q
    := triple-concat-nat-htpy B B (has-inverse-section-composite A B f (first fisHAE)) (identity B)
        ((second (second (first fisHAE)))) (f x) (f y) q

#def zag-zig-concat-triple-concat-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
    = ap B B (f x) (f y) (identity B) q
    := zag-zig-concat (f x = f y)
        (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
            (((second (second (first fisHAE)))) (f x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (((second (second (first fisHAE)))) (f y)))
        (ap B B (f x) (f y) (identity B) q)
        (triple-concat-higher-homotopy-is-half-adjoint-equiv x y q)
        (triple-concat-nat-htpy-is-half-adjoint-equiv x y q)

#def triple-concat-reduction-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : ap B B (f x) (f y) (identity B) q = q
    := ap-id B (f x) (f y) q

#def section-htpy-ap-is-half-adjoint-equiv
    (x y : A)
    (q : f x = f y)
    : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) = q
    := quintuple-concat-alternating (f x = f y)
        (ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q))
        (triple-concat B
            (f x)
            (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
            (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
            (f y)
            (ap A B x ((has-inverse-inverse A B f (first fisHAE)) (f x)) f
            (rev A (has-inverse-retraction-composite A B f (first fisHAE) x) x ((first (second (first fisHAE))) x)))
            (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
                ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
            (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-triple-concat-is-half-adjoint-equiv x y q)
        (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x))
        ((has-inverse-inverse A B f (first fisHAE)) (f y)) f (ap B A (f x) (f y) (has-inverse-inverse A B f (first fisHAE)) q))
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-rev-homotopy-triple-concat-is-half-adjoint-equiv x y q)
        (triple-concat B
        (f x)
        (f ((has-inverse-inverse A B f (first fisHAE)) (f x)))
        (f ((has-inverse-inverse A B f (first fisHAE)) (f y)))
        (f y)
        (rev B (f (has-inverse-retraction-composite A B f (first fisHAE) x)) (f x)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f x)) x f ((first (second (first fisHAE))) x)))
        (ap B B (f x) (f y) (has-inverse-section-composite A B f (first fisHAE)) q)
        (ap A B ((has-inverse-inverse A B f (first fisHAE)) (f y)) y f ((first (second (first fisHAE))) y)))
        (ap-ap-homotopy-triple-concat-is-half-adjoint-equiv x y q)
        (ap B B (f x) (f y) (identity B) q)
        (zag-zig-concat-triple-concat-is-half-adjoint-equiv x y q)
        q
        (triple-concat-reduction-is-half-adjoint-equiv x y q)

#def has-section-ap-is-half-adjoint-equiv uses (fisHAE)
    (x y : A)
    : has-section (x = y) (f x = f y) (ap A B x y f)
    := (second (iff-ap-is-half-adjoint-equiv x y), section-htpy-ap-is-half-adjoint-equiv x y)

#def is-equiv-ap-is-half-adjoint-equiv uses (fisHAE)
    (x y : A)
    : is-equiv (x = y) (f x = f y) (ap A B x y f)
    := (has-retraction-ap-is-half-adjoint-equiv x y, has-section-ap-is-half-adjoint-equiv x y)
#end equiv-identity-types-equiv

#def is-equiv-ap-is-equiv
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    (x y : A)
    : is-equiv (x = y) (f x = f y)(ap A B x y f)
    := is-equiv-ap-is-half-adjoint-equiv A B f (is-equiv-is-half-adjoint-equiv A B f fisequiv) x y

#def Eq-ap-is-equiv
    (A B : U)
    (f : A -> B)
    (fisequiv : is-equiv A B f)
    (x y : A)
    : Eq (x = y) (f x = f y)
    := (ap A B x y f, is-equiv-ap-is-equiv A B f fisequiv x y)
```

```rzk
#def rev-Retraction
    (A : U)
    (y : A)
    : (x : A) -> has-retraction (x = y) (y = x) ((\p -> ((rev A x y) p)))
    := \x ->
       ((rev A y x), \p -> idJ(A, x, \y' p' -> ((composition (x = y') (y' = x) (x = y') (rev A y' x) (rev A x y'))(p') =_{x = y'} p'), refl, y, p))

#def rev-Section
    (A : U)
    (y : A)
    : (x : A) -> has-section (x = y) (y = x) ((\p -> ((rev A x y) p)))
    := \x ->
       ((rev A y x), \p -> idJ(A, y, \x' p' -> ((composition (y = x') (x' = y) (y = x') (rev A x' y) (rev A y x'))(p') =_{y = x'} p'), refl, x, p))

#def rev-is-equiv
    (A : U)
    (x y : A)
    : is-equiv (x = y) (y = x) (rev A x y)
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
        is-equiv (f = g)((x : X) -> f x = g x)(htpy-eq X A f g)

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

## Embeddings

```rzk
#def is-emb
  (A B : U)
  (f : A -> B)
  : U
  := (x : A) -> (y : A) -> is-equiv (x = y) (f x = f y) (ap A B x y f)

#def Emb
  (A B : U)
  : U
  := (∑ (f : A -> B), is-emb A B f)

#def inhabited-emb-implies-emb
  (A B : U)
  (f : A -> B)
  (e : A -> is-emb A B f)
  : is-emb A B f
  := \x -> \y -> e x x y

#def inv-ap-is-emb
  (A B : U)
  (f : A -> B)
  (fisemb : is-emb A B f)
  (x y : A)
  (p : f x = f y)
  : (x = y)
  := (first (first (fisemb x y))) p
```

## Identity types of unit types

```rzk
#def terminal-map-of-path-types-of-Unit-has-retr
    (x y : Unit)
    : has-retraction (x = y) Unit (terminal-map (x = y))
    :=
    (\a -> refl, \p -> idJ(Unit, x, \y' p' -> refl =_{x = y'} p', refl, y, p))

#def terminal-map-of-path-types-of-Unit-has-sec
    (x y : Unit)
    : has-section (x = y) Unit (terminal-map (x = y))
    :=
    (\a -> refl, \a -> refl)

#def terminal-map-of-path-types-of-Unit-is-equiv
    (x y : Unit)
    : is-equiv (x = y) Unit (terminal-map (x = y))
    :=
    ((terminal-map-of-path-types-of-Unit-has-retr x y), (terminal-map-of-path-types-of-Unit-has-sec x y))

```
