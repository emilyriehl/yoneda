# 3. Contractible

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
#def contraction-center (A : U) (Aiscontr : isContr A) : A
  := (first Aiscontr)

-- The path from the contraction center to any point.
#def contracting-htpy 
  (A : U) 
  (Aiscontr : isContr A) 
  : (z : A) -> (contraction-center A Aiscontr) = z
  := second Aiscontr

-- A path between an arbitrary pair of types in a contractible type.
#def contractible-connecting-htpy 
  (A : U)
  (Aiscontr : isContr A)
  (x y : A) 
  : x = y
  := zag-zig-concat A x (contraction-center A Aiscontr) y (contracting-htpy A Aiscontr x) (contracting-htpy A Aiscontr y)  
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

#def isRetract-section
  (A B : U)
  (AretractB : isRetract A B)
  : A -> B
  := first AretractB

#def isRetract-retraction
  (A B : U)
  (AretractB : isRetract A B)
  : B -> A
  := first (second AretractB)

#def isRetract-homotopy
  (A B : U)
  (AretractB : isRetract A B)
  : homotopy A A (composition A B A (isRetract-retraction A B AretractB) (isRetract-section A B AretractB))(identity A)
  := second (second AretractB)

-- If A is a retract of a contractible type it has a term.
#def isRetract-ofContr-isInhabited
  (A B : U)
  (AretractB : isRetract A B)
  (Biscontr : isContr B)
  : A
  := (isRetract-retraction A B AretractB)(contraction-center B Biscontr)

-- If A is a retract of a contractible type it has a contracting homotopy.
#def isRetract-ofContr-hasHtpy
  (A B : U)
  (AretractB : isRetract A B)
  (Biscontr : isContr B)
  (a : A)
  : (isRetract-ofContr-isInhabited A B AretractB Biscontr) = a
  := concat
      A
      (isRetract-ofContr-isInhabited A B AretractB Biscontr)
      ((composition A B A (isRetract-retraction A B AretractB) (isRetract-section A B AretractB)) a)
      a
      (ap B A (contraction-center B Biscontr) ((isRetract-section A B AretractB) a) (isRetract-retraction A B AretractB)
        (contracting-htpy B Biscontr ((isRetract-section A B AretractB) a)))
      ((isRetract-homotopy A B AretractB) a)

-- If A is a retract of a contractible type it is contractible.
#def isRetract-ofContr-isContr
  (A B : U)
  (AretractB : isRetract A B)
  (Biscontr : isContr B)
  : isContr A
  := (isRetract-ofContr-isInhabited A B AretractB Biscontr, isRetract-ofContr-hasHtpy A B AretractB Biscontr) 
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


