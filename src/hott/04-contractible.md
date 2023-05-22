# 4. Contractible

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

-- A path between an arbitrary pair of types in a contractible type.
#def contractible-connecting-htpy uses (Aiscontr)
  (x y : A) 
  : x = y
  := zag-zig-concat A x contraction-center y (contracting-htpy x) (contracting-htpy y)  

#end contractible-data
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
