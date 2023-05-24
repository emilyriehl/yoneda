# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#def isRetr
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    (g : hom A y x)
    : U
    := (Segal-comp A AisSegal x y x f g) =_{hom A x x} (id-arr A x)

#def Retr
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (g : hom A y x), (isRetr A AisSegal x y f g)

#def isSec
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    (h : hom A y x)
    : U
    := (Segal-comp A AisSegal x y x f h) =_{hom A x x} (id-arr A x)

#def Sec
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (h : hom A y x), (isSec A AisSegal x y f h)

#def isIso
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := prod (Retr A AisSegal x y f) (Sec A AisSegal x y f)

#def isBiinvertible
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (g : hom A y x), prod (isRetr A AisSegal x y f g) (isSec A AisSegal x y f g)

#def biinv-iso
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : (isBiinvertible A AisSegal x y f) -> (isIso A AisSegal x y f)
    := (\(g, (p, q)) -> ((g, p), (g, q)))
```
