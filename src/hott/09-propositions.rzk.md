# 9. Propositions

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
  := (a : A) → (b : A) → is-contr (a = b)

#def is-prop-Unit
  : is-prop Unit
  := \ x y → (path-types-of-Unit-are-contractible x y)
```

## Alternative characterizations: definitions

```rzk
#def all-elements-equal
  (A : U)
  : U
  := (a : A) → (b : A) → (a = b)

#def is-contr-is-inhabited
  (A : U)
  : U
  := A → is-contr A

#def is-emb-terminal-map
  (A : U)
  : U
  := is-emb A Unit (terminal-map A)
```

## Alternative characterizations: proofs

```rzk
#def all-elements-equal-is-prop
  ( A : U)
  ( is-prop-A : is-prop A)
  : all-elements-equal A
  := \ a b → (first (is-prop-A a b))

#def is-contr-is-inhabited-all-elements-equal
  ( A : U)
  ( all-elements-equal-A : all-elements-equal A)
  : is-contr-is-inhabited A
  := \ a → (a , all-elements-equal-A a)

#def terminal-map-is-emb-is-inhabited-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : A → (is-emb-terminal-map A)
  :=
    \ x →
      ( is-emb-is-equiv A Unit (terminal-map A)
        ( contr-implies-terminal-map-is-equiv A (c x)))

#def terminal-map-is-emb-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : (is-emb-terminal-map A)
  :=
    ( is-emb-is-inhabited-emb A Unit (terminal-map A)
      ( terminal-map-is-emb-is-inhabited-is-contr-is-inhabited A c))

#def is-prop-is-emb-terminal-map
  ( A : U)
  ( f : is-emb-terminal-map A)
  : is-prop A
  :=
    \ x y →
      ( is-contr-is-equiv-to-contr (x = y) (unit = unit)
        ( (ap A Unit x y (terminal-map A)) , (f x y))
        ( path-types-of-Unit-are-contractible unit unit))

#def is-prop-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : is-prop A
  :=
    ( is-prop-is-emb-terminal-map A
      ( terminal-map-is-emb-is-contr-is-inhabited A c))
```
