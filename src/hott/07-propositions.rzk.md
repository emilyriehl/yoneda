# 7. Propositions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Propositions

A type is a proposition when its identity types are contractible.

```rzk
#def is-prop
  (A : U)
  : U
  := (a : A) -> (b : A) -> is-contr(a = b)

#def Unit-is-prop
  : is-prop Unit
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
  := A -> is-contr A

#def terminal-map-is-embedding
  (A : U)
  : U
  := is-emb A Unit (terminal-map A)
```

## Alternative characterizations: proofs

```rzk
#def prop-implies-all-elements-equal
  (A : U)
  (AisProp : is-prop A)
  : all-elements-equal A
  := \a -> \b -> (first (AisProp a b))

#def all-elements-equal-implies-inhabited-implies-contractible
  (A : U)
  (AhasAllEltsEqual : all-elements-equal A)
  : inhabited-implies-contractible A
  := \a -> (a, AhasAllEltsEqual a)

#def inhabited-implies-contractible-implies-if-inhabited-then-terminal-map-is-embedding
  (A : U)
  (c : inhabited-implies-contractible A)
  : A -> (terminal-map-is-embedding A)
  := \x ->
  (equivalence-is-embedding A Unit (terminal-map A)
      (contr-implies-terminal-map-is-equiv A (c x))
  )

#def inhabited-implies-contractible-implies-terminal-map-is-embedding
  (A : U)
  (c : inhabited-implies-contractible A)
  : (terminal-map-is-embedding A)
  :=
  (inhabited-emb-implies-emb A Unit (terminal-map A)
    (inhabited-implies-contractible-implies-if-inhabited-then-terminal-map-is-embedding A c)
  )

#def terminal-map-is-embedding-implies-proposition
  (A : U)
  (f : terminal-map-is-embedding A)
  : is-prop A
  := \x -> \y -> (is-equiv-toContr-is-contr (x = y) (unit = unit) ((ap A Unit x y (terminal-map A)), (f x y)) (path-types-of-Unit-are-contractible unit unit))

#def contractible-if-inhabited-implies-proposition
  (A : U)
  (c : inhabited-implies-contractible A)
  : is-prop A
  := (terminal-map-is-embedding-implies-proposition A (inhabited-implies-contractible-implies-terminal-map-is-embedding A c))

```
