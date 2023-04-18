# 2. Contractible

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