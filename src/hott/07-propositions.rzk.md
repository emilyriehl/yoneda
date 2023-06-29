# 7. Propositions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Propositions

A type is a proposition when its identity types are contractible.

```rzk
#def isProp
  (A : U)
  : U
  := (a : A) -> (b : A) -> isContr(a = b)

#def Unit-isProp
  : isProp Unit
  := \x -> \y -> (path-types-of-Unit-are-contractible x y)
```

## Alternative characterizations: definitions

```rzk
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
```

## Alternative characterizations: proofs

```rzk
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

#def inhabited-implies-contractible-implies-if-inhabited-then-final-proj-is-embedding
  (A : U)
  (c : inhabited-implies-contractible A)
  : A -> (final-proj-is-embedding A)
  := \x ->
  (equivalence-is-embedding A Unit (final-projection A)
      (contr-implies-final-proj-is-equiv A (c x))
  )

#def inhabited-implies-contractible-implies-final-proj-is-embedding
  (A : U)
  (c : inhabited-implies-contractible A)
  : (final-proj-is-embedding A)
  :=
  (inhabited-emb-implies-emb A Unit (final-projection A)
    (inhabited-implies-contractible-implies-if-inhabited-then-final-proj-is-embedding A c)
  )

#def final-proj-is-embedding-implies-proposition
  (A : U)
  (f : final-proj-is-embedding A)
  : isProp A
  := \x -> \y -> (isEquiv-toContr-isContr (x = y) (unit = unit) ((ap A Unit x y (final-projection A)), (f x y)) (path-types-of-Unit-are-contractible unit unit))

#def contractible-if-inhabited-implies-proposition
  (A : U)
  (c : inhabited-implies-contractible A)
  : isProp A
  := (final-proj-is-embedding-implies-proposition A (inhabited-implies-contractible-implies-final-proj-is-embedding A c))

```
