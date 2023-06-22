# 5. Contractible

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Contractible types

```rzk
-- contractible types
#def isContr (A : U) : U
  := ∑ (x : A), (y : A) -> x = y
```

## Contractible type data

```rzk
#section contractible-data

#variable A : U
#variable Aiscontr : isContr A

#def contraction-center
  : A
  := (first Aiscontr)

-- The path from the contraction center to any point.
#def contracting-htpy
  : (z : A) -> contraction-center = z
  := second Aiscontr

#def contracting-htpy-realigned uses (Aiscontr)
  : (z : A) -> contraction-center = z
  := \z -> (concat A contraction-center contraction-center z 
          (rev A contraction-center contraction-center (contracting-htpy contraction-center))
          (contracting-htpy z)
          )

-- A path between an arbitrary pair of types in a contractible type.
#def contractible-connecting-htpy uses (Aiscontr)
  (x y : A)
  : x = y
  := zag-zig-concat A x contraction-center y (contracting-htpy x) (contracting-htpy y)

#end contractible-data
```

## Characterization of contractibility

A type is contractible if and only if its final projection is an equivalence.

```rzk

#def final-proj-is-equiv
  (A : U)
  : U
  := isEquiv A Unit (final-projection A)

#def contr-implies-final-proj-is-equiv-retr
  (A : U)
  (AisContr : isContr A)
  : hasRetraction A Unit (final-projection A)
  :=
    (const Unit A (contraction-center A AisContr), \y -> (contracting-htpy A AisContr) y)

#def contr-implies-final-proj-is-equiv-sec
  (A : U)
  (AisContr : isContr A)
  : hasSection A Unit (final-projection A)
  :=  (const Unit A (contraction-center A AisContr), \z -> refl)

#def contr-implies-final-proj-is-equiv
  (A : U)
  (AisContr : isContr A)
  : isEquiv A Unit (final-projection A)
  := (contr-implies-final-proj-is-equiv-retr A AisContr, contr-implies-final-proj-is-equiv-sec A AisContr)

#def final-proj-is-equiv-implies-contr
  (A : U)
  (e : final-proj-is-equiv A)
  : isContr A
  := ( (first (first e)) unit, (second (first e)))

#def contr-iff-final-proj-is-equiv
  (A : U)
  : iff (isContr A) (final-proj-is-equiv A)
  :=  ((contr-implies-final-proj-is-equiv A), (final-proj-is-equiv-implies-contr A))
```

## Retracts of contractible types

A retract of contractible types is contractible.

```rzk
-- A type that records a proof that A is a retract of B.
-- Very similar to hasRetraction.
#def isRetract
  (A B : U)
  : U
  := ∑ (s : A -> B), hasRetraction A B s

#section retraction-data

#variables A B : U
#variable AretractB : isRetract A B

#def isRetract-section
  : A -> B
  := first AretractB

#def isRetract-retraction
  : B -> A
  := first (second AretractB)

#def isRetract-homotopy
  : homotopy A A (composition A B A isRetract-retraction isRetract-section)(identity A)
  := second (second AretractB)

-- If A is a retract of a contractible type it has a term.
#def isRetract-ofContr-isInhabited uses (AretractB)
  (Biscontr : isContr B)
  : A
  := isRetract-retraction (contraction-center B Biscontr)

-- If A is a retract of a contractible type it has a contracting homotopy.
#def isRetract-ofContr-hasHtpy uses (AretractB)
  (Biscontr : isContr B)
  (a : A)
  : (isRetract-ofContr-isInhabited Biscontr) = a
  := concat
      A
      (isRetract-ofContr-isInhabited Biscontr)
      ((composition A B A isRetract-retraction isRetract-section) a)
      a
      (ap B A (contraction-center B Biscontr) (isRetract-section a) isRetract-retraction
        (contracting-htpy B Biscontr (isRetract-section a)))
      (isRetract-homotopy a)

-- If A is a retract of a contractible type it is contractible.
#def isRetract-ofContr-isContr uses (AretractB)
  (Biscontr : isContr B)
  : isContr A
  := (isRetract-ofContr-isInhabited Biscontr, isRetract-ofContr-hasHtpy Biscontr)

#end retraction-data
```

## Functions between contractible types

A function between contractible types is an equivalence

```rzk
#def areContr-isEquiv
    (A B : U)
    (Aiscontr : isContr A)
    (Biscontr : isContr B)
    (f : A -> B)
    : isEquiv A B f
    := ((\b -> contraction-center A Aiscontr,
        \a -> contracting-htpy A Aiscontr a),
       (\b -> contraction-center A Aiscontr,
        \b -> contractible-connecting-htpy B Biscontr (f (contraction-center A Aiscontr)) b))
```

A type equivalent to a contractible type is contractible.

```rzk
#def isEquiv-toContr-isContr
    (A B : U)
    (e : Eq A B)
    (Biscontr : isContr B)
    : isContr A
    := isRetract-ofContr-isContr A B
        (first e, first (second e))
        Biscontr
```

## Based path spaces

For example, we prove that based path spaces are contractible.

```rzk
-- Transport in the space of paths starting at a is concatenation.
#def concat-as-based-transport
    (A : U)             -- The ambient type.
    (a x y : A)         -- The basepoint and two other points.
    (p : a = x)         -- An element of the based path space.
    (q : x = y)         -- A path in the base.
    : (transport A (\z -> (a = z)) x y q p) = (concat A a x y p q)
    := idJ(A, x, \y' q' -> (transport A (\z -> (a = z)) x y' q' p) = (concat A a x y' p q'), refl, y, q)

-- The center of contraction in the based path space is (a, refl)
#def based-paths-center
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : ∑ (x : A), a = x
    := (a, refl)

-- The contracting homotopy.
#def based-paths-contracting-homotopy
    (A : U)                     -- The ambient type.
    (a : A)                     -- The basepoint.
    (p : ∑ (x : A), a = x)      -- Another based path.
    : (based-paths-center A a) =_{∑ (x : A), a = x} p
    := path-of-pairs-pair-of-paths A (\z -> a = z) a (first p) (second p) (refl) (second p)
        (concat (a = (first p))
        (transport A (\z -> (a = z)) a (first p) (second p) (refl))
        (concat A a a (first p) (refl) (second p))
        (second p)
        (concat-as-based-transport A a a (first p) (refl) (second p))
        (refl-concat A a (first p) (second p)))

-- Based path spaces are contractible
#def based-paths-contractible
    (A : U)         -- The ambient type.
    (a : A)         -- The basepoint.
    : isContr (∑ (x : A), a = x)
    := (based-paths-center A a, based-paths-contracting-homotopy A a)
```

## Contractible products

```rzk
#def isContr-product
  (A B : U)
  (AisContr : isContr A)
  (BisContr : isContr B)
  : isContr (prod A B)
  := ((first AisContr, first BisContr), \p ->
    path-product A B
      (first AisContr) (first p)
      (first BisContr) (second p)
      (second AisContr (first p))
      (second BisContr (second p))
      )

#def first-isContr-product
  (A B : U)
  (AxBisContr : isContr (prod A B))
  : isContr A
  := (first (first AxBisContr), \a ->
    first-path-product A B
      (first AxBisContr)
      (a, second (first AxBisContr))
      (second AxBisContr (a, second (first AxBisContr))))

#def first-isContr-sigma
  (A : U)
  (B : A -> U)
  (b : (a : A) -> B a)
  (ABisContr : isContr (∑ (a : A), B a))
  : isContr A
  := (first (first ABisContr), \a ->
        first-path-sigma A B
          (first ABisContr)
          (a, b a)
          (second ABisContr (a, b a)))
```

## Singleton induction

A type is contractible if and only if it has singleton induction.

```rzk
#def ev-pt
  (A : U)
  (a : A)
  (B : A -> U)
  : ((x : A) -> B x) -> B a
  := \f -> f a

#def has-singleton-induction-pointed
  (A : U)
  (a : A)
  (B : A -> U)
  : U
  := hasSection ((x : A) -> B x) (B a) (ev-pt A a B)

#def has-singleton-induction
  (A : U)
  : U
  := ∑ (a : A), (B : A -> U) -> (has-singleton-induction-pointed A a B)

#def ind-sing
  (A : U)
  (a : A)
  (B : A -> U)
  (AhasSingInd : has-singleton-induction-pointed A a B)
  : (B a) -> ((x : A) -> B x)
  := (first AhasSingInd)

#def comp-sing
  (A : U)
  (a : A)
  (B : A -> U)
  (AhasSingInd : has-singleton-induction-pointed A a B)
  : (homotopy (B a) (B a) (composition (B a) ((x : A) -> B x) (B a) (ev-pt A a B) (ind-sing A a B AhasSingInd)) (identity (B a)))
  := (second AhasSingInd)

```

## Propositions

A type is a proposition when its identity types are contractible.

```rzk
#def isProp
  (A : U)
  : U
  := (a : A) -> (b : A) -> isContr(a = b)

-- Alternative characterizations: definitions

#def all-elements-equal
  (A : U)
  : U
  := (a : A) -> (b : A) -> (a = b)

#def inhabited-implies-contractible
  (A : U)
  : U
  := A -> isContr A

#def final-proj-is-embedding
  (A : U)
  : U
  := isEmb A Unit (final-projection A)

-- Alternative characterizations: proofs

#def prop-implies-all-elements-equal
  (A : U)
  (AisProp : isProp A)
  : all-elements-equal A
  := \a -> \b -> (first (AisProp a b))

#def all-elements-equal-implies-inhabited-implies-contractible
  (A : U)
  (AhasAllEltsEqual : all-elements-equal A)
  : inhabited-implies-contractible A
  := \a -> (a, AhasAllEltsEqual a)

```

#def inhabited-implies-contractible-implies-final-proj-is-embedding (A : U)
(AhasAllEltsEqual : all-elements-equal A) : final-proj-is-embedding A :=

#def unit-loop-final-projection-sec : hasSection (unit = unit) Unit
(final-projection (unit = unit)) := (\z -> refl\_{unit}, (identity Unit))

#def unit-center (x : Unit) : (x = unit) := refl

#def inhabited-implies-contractible-implies-final-proj-is-embedding (A : U) (f :
inhabited-implies-contractible A) : final-proj-is-embedding A
