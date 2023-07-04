# 6. Contractible

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Contractible types

```rzk
-- contractible types
#def is-contr (A : U) : U
  := Σ (x : A), (y : A) -> x = y
```

## Contractible type data

```rzk
#section contractible-data

#variable A : U
#variable Aiscontr : is-contr A

#def contraction-center
  : A
  := (first Aiscontr)

-- The path from the contraction center to any point.
#def contracting-htpy
  : (z : A) -> contraction-center = z
  := second Aiscontr

#def contracting-htpy-realigned uses (Aiscontr)
  : (z : A) -> contraction-center = z
  :=
    \ z ->
      ( concat A contraction-center contraction-center z
          (rev A contraction-center contraction-center
            ( contracting-htpy contraction-center))
          (contracting-htpy z))

#def contracting-htpy-realigned-path uses (Aiscontr)
  : (contracting-htpy-realigned contraction-center) = refl
  :=
    ( left-inverse A contraction-center contraction-center
      ( contracting-htpy contraction-center))

-- A path between an arbitrary pair of types in a contractible type.
#def contractible-connecting-htpy uses (Aiscontr)
  (x y : A)
  : x = y
  :=
    zag-zig-concat A x contraction-center y
    ( contracting-htpy x) (contracting-htpy y)

#end contractible-data
```

## Unit type

The prototypical contractible type is the unit type, which is built-in to rzk.

```rzk
#def ind-unit
  (C : Unit -> U)
  (C-unit : C unit)
  (x : Unit)
  : C x
  := C-unit

#def is-prop-unit
  (x y : Unit)
  : x = y
  := refl

-- Terminal projection as a constant map
#def terminal-map
  (A : U)
  : A -> Unit
  := constant A Unit unit
```

## Identity types of unit types

```rzk
#def terminal-map-of-path-types-of-Unit-has-retr
  (x y : Unit)
  : has-retraction (x = y) Unit (terminal-map (x = y))
  :=
    ( \ a -> refl,
      \ p -> idJ (Unit, x, \ y' p' -> refl =_{x = y'} p', refl, y, p))

#def terminal-map-of-path-types-of-Unit-has-sec
  (x y : Unit)
  : has-section (x = y) Unit (terminal-map (x = y))
  := ( \ a -> refl, \ a -> refl)

#def terminal-map-of-path-types-of-Unit-is-equiv
  (x y : Unit)
  : is-equiv (x = y) Unit (terminal-map (x = y))
  :=
    ( terminal-map-of-path-types-of-Unit-has-retr x y,
      terminal-map-of-path-types-of-Unit-has-sec x y)
```

## Characterization of contractibility

A type is contractible if and only if its terminal map is an equivalence.

```rzk

#def terminal-map-is-equiv
  (A : U)
  : U
  := is-equiv A Unit (terminal-map A)

#def contr-implies-terminal-map-is-equiv-retr
  (A : U)
  (AisContr : is-contr A)
  : has-retraction A Unit (terminal-map A)
  :=
    ( constant Unit A (contraction-center A AisContr),
      \ y -> (contracting-htpy A AisContr) y)

#def contr-implies-terminal-map-is-equiv-sec
  (A : U)
  (AisContr : is-contr A)
  : has-section A Unit (terminal-map A)
  :=  (constant Unit A (contraction-center A AisContr), \ z -> refl)

#def contr-implies-terminal-map-is-equiv
  (A : U)
  (AisContr : is-contr A)
  : is-equiv A Unit (terminal-map A)
  :=
    ( contr-implies-terminal-map-is-equiv-retr A AisContr,
      contr-implies-terminal-map-is-equiv-sec A AisContr)

#def terminal-map-is-equiv-implies-contr
  (A : U)
  (e : terminal-map-is-equiv A)
  : is-contr A
  := ((first (first e)) unit, (second (first e)))

#def contr-iff-terminal-map-is-equiv
  (A : U)
  : iff (is-contr A) (terminal-map-is-equiv A)
  :=
    ( (contr-implies-terminal-map-is-equiv A),
      (terminal-map-is-equiv-implies-contr A))

#def equiv-with-contractible-domain-implies-contractible-codomain
  (A B : U)
  (f : Equiv A B)
  (Aiscontr : is-contr A)
  : is-contr B
  := (terminal-map-is-equiv-implies-contr B
      (second
      (comp-equiv B A Unit
        (inv-equiv A B f)
        (terminal-map A, (contr-implies-terminal-map-is-equiv A Aiscontr)))))

#def equiv-with-contractible-codomain-implies-contractible-domain
  (A B : U)
  (f : Equiv A B)
  (Biscontr : is-contr B)
  : is-contr A
  :=
    ( equiv-with-contractible-domain-implies-contractible-codomain B A
      ( inv-equiv A B f) Biscontr)

#def equiv-then-domain-contractible-iff-codomain-contractible
  (A B : U)
  (f : Equiv A B)
  : (iff (is-contr A) (is-contr B))
  :=
    ( \ Aiscontr ->
      ( equiv-with-contractible-domain-implies-contractible-codomain
        A B f Aiscontr),
      \ Biscontr ->
      ( equiv-with-contractible-codomain-implies-contractible-domain
        A B f Biscontr))

#def path-types-of-Unit-are-contractible
  (x y : Unit)
  : is-contr (x = y)
  :=
    ( terminal-map-is-equiv-implies-contr
      ( x = y) (terminal-map-of-path-types-of-Unit-is-equiv x y))
```

## Retracts of contractible types

A retract of contractible types is contractible.

```rzk
-- A type that records a proof that A is a retract of B.
-- Very similar to has-retraction.
#def is-retract-of
  (A B : U)
  : U
  := Σ (s : A -> B), has-retraction A B s

#section retraction-data

#variables A B : U
#variable AretractB : is-retract-of A B

#def is-retract-of-section
  : A -> B
  := first AretractB

#def is-retract-of-retraction
  : B -> A
  := first (second AretractB)

#def is-retract-of-homotopy
  : homotopy A A (composition A B A is-retract-of-retraction is-retract-of-section) (identity A)
  := second (second AretractB)

-- If A is a retract of a contractible type it has a term.
#def is-retract-of-is-contr-isInhabited uses (AretractB)
  (Biscontr : is-contr B)
  : A
  := is-retract-of-retraction (contraction-center B Biscontr)

-- If A is a retract of a contractible type it has a contracting homotopy.
#def is-retract-of-is-contr-hasHtpy uses (AretractB)
  (Biscontr : is-contr B)
  (a : A)
  : (is-retract-of-is-contr-isInhabited Biscontr) = a
  := concat
      A
      (is-retract-of-is-contr-isInhabited Biscontr)
      ((composition A B A is-retract-of-retraction is-retract-of-section) a)
      a
      (ap B A (contraction-center B Biscontr) (is-retract-of-section a)
        ( is-retract-of-retraction)
        ( contracting-htpy B Biscontr (is-retract-of-section a)))
      (is-retract-of-homotopy a)

-- If A is a retract of a contractible type it is contractible.
#def is-retract-of-is-contr-is-contr uses (AretractB)
  (Biscontr : is-contr B)
  : is-contr A
  :=
    ( is-retract-of-is-contr-isInhabited Biscontr,
      is-retract-of-is-contr-hasHtpy Biscontr)

#end retraction-data
```

## Functions between contractible types

A function between contractible types is an equivalence

```rzk
#def areContr-is-equiv
  (A B : U)
  (Aiscontr : is-contr A)
  (Biscontr : is-contr B)
  (f : A -> B)
  : is-equiv A B f
  :=
    ( ( \ b -> contraction-center A Aiscontr,
        \ a -> contracting-htpy A Aiscontr a),
      ( \ b -> contraction-center A Aiscontr,
        \ b -> contractible-connecting-htpy B Biscontr
                (f (contraction-center A Aiscontr)) b))
```

A type equivalent to a contractible type is contractible.

```rzk
#def is-contr-is-equiv-to-contr
  (A B : U)
  (e : Equiv A B)
  (Biscontr : is-contr B)
  : is-contr A
  :=
    is-retract-of-is-contr-is-contr A B (first e, first (second e)) Biscontr

#def is-contr-is-equiv-from-contr
  (A B : U)
  (e : Equiv A B)
  (Aiscontr : is-contr A)
  : is-contr B
  := is-retract-of-is-contr-is-contr B A
      ( first (second (second e)), (first e, second (second (second e))))
      ( Aiscontr)
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
  :=
    idJ (
      A,
      x,
      \ y' q' ->
        ( transport A (\z -> (a = z)) x y' q' p) = (concat A a x y' p q'),
      refl,
      y,
      q)

-- The center of contraction in the based path space is (a, refl)
#def based-paths-center
  (A : U)         -- The ambient type.
  (a : A)         -- The basepoint.
  : Σ (x : A), a = x
  := (a, refl)

-- The contracting homotopy.
#def based-paths-contracting-homotopy
  (A : U)                     -- The ambient type.
  (a : A)                     -- The basepoint.
  (p : Σ (x : A), a = x)      -- Another based path.
  : (based-paths-center A a) =_{Σ (x : A), a = x} p
  :=
    path-of-pairs-pair-of-paths
      A ( \ z -> a = z) a (first p) (second p) (refl) (second p)
        (concat
          ( a = (first p))
          ( transport A (\z -> (a = z)) a (first p) (second p) (refl))
          ( concat A a a (first p) (refl) (second p))
          ( second p)
          ( concat-as-based-transport A a a (first p) (refl) (second p))
          ( refl-concat A a (first p) (second p)))

-- Based path spaces are contractible
#def is-contr-based-paths
  (A : U)         -- The ambient type.
  (a : A)         -- The basepoint.
  : is-contr (Σ (x : A), a = x)
  := (based-paths-center A a, based-paths-contracting-homotopy A a)
```

## Contractible products

```rzk
#def is-contr-product
  (A B : U)
  (AisContr : is-contr A)
  (BisContr : is-contr B)
  : is-contr (prod A B)
  :=
    ( (first AisContr, first BisContr),
      \ p -> path-product A B
              ( first AisContr) (first p)
              ( first BisContr) (second p)
              ( second AisContr (first p))
              ( second BisContr (second p)))

#def first-is-contr-product
  (A B : U)
  (AxBisContr : is-contr (prod A B))
  : is-contr A
  :=
    ( first (first AxBisContr),
      \ a -> first-path-product A B
              ( first AxBisContr)
              ( a, second (first AxBisContr))
              ( second AxBisContr (a, second (first AxBisContr))))

#def first-is-contr-sigma
  (A : U)
  (B : A -> U)
  (b : (a : A) -> B a)
  (ABisContr : is-contr (Σ (a : A), B a))
  : is-contr A
  :=
    ( first (first ABisContr),
      \ a -> first-path-sigma A B
              ( first ABisContr)
              ( a, b a)
              ( second ABisContr (a, b a)))
```

## Singleton induction

A type is contractible if and only if it has singleton induction.

```rzk
#def ev-pt
  (A : U)
  (a : A)
  (B : A -> U)
  : ((x : A) -> B x) -> B a
  := \ f -> f a

#def has-singleton-induction-pointed
  (A : U)
  (a : A)
  (B : A -> U)
  : U
  := has-section ((x : A) -> B x) (B a) (ev-pt A a B)

#def has-singleton-induction-pointed-structure
  (A : U)
  (a : A)
  : U
  := (B : A -> U) -> has-section ((x : A) -> B x) (B a) (ev-pt A a B)

#def has-singleton-induction
  (A : U)
  : U
  := Σ (a : A), (B : A -> U) -> (has-singleton-induction-pointed A a B)

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

#def contr-implies-singleton-induction-ind
  (A : U)
  (Aiscontr : is-contr A)
  : (has-singleton-induction A)
  :=
    ( ( contraction-center A Aiscontr),
      \ B ->
        ( ( \ b x ->
                ( transport A B
                  ( contraction-center A Aiscontr) x
                  ( contracting-htpy-realigned A Aiscontr x) b)),
          ( \ b ->
                ( ap
                  ( (contraction-center A Aiscontr) =
                    (contraction-center A Aiscontr))
                  ( B (contraction-center A Aiscontr))
                  ( contracting-htpy-realigned A Aiscontr
                    ( contraction-center A Aiscontr))
                  refl_{(contraction-center A Aiscontr)}
                  ( \ p ->
                    ( transport-loop A B (contraction-center A Aiscontr) b p))
                  ( contracting-htpy-realigned-path A Aiscontr)))))

#def contr-implies-singleton-induction-pointed
  (A : U)
  (Aiscontr : is-contr A)
  (B : A -> U)
  : has-singleton-induction-pointed A (contraction-center A Aiscontr) B
  := (second (contr-implies-singleton-induction-ind A Aiscontr)) B

#def singleton-induction-ind-implies-contr
  (A : U)
  (a : A)
  (f : has-singleton-induction-pointed-structure A a)
  : (is-contr A)
  := (  a, (first (f (  \ x -> a = x))) (refl_{a}))
```
