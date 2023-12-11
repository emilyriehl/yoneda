# Contractible types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Contractible types

```rzk title="The type of contractibility proofs"
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
```

## Contractible type data

```rzk
#section contractible-data

#variable A : U
#variable is-contr-A : is-contr A

#def center-contraction
  : A
  := (first is-contr-A)
```

```rzk title="The path from the contraction center to any point"
#def homotopy-contraction
  : ( z : A) → center-contraction = z
  := second is-contr-A

#def realign-homotopy-contraction uses (is-contr-A)
  : ( z : A) → center-contraction = z
  :=
    \ z →
      ( concat A center-contraction center-contraction z
          ( rev A center-contraction center-contraction
            ( homotopy-contraction center-contraction))
          ( homotopy-contraction z))

#def path-realign-homotopy-contraction uses (is-contr-A)
  : ( realign-homotopy-contraction center-contraction) = refl
  :=
    ( left-inverse-concat A center-contraction center-contraction
      ( homotopy-contraction center-contraction))
```

```rzk title="A path between any pair of terms in a contractible type"
#def eq-is-contr uses (is-contr-A)
  ( x y : A)
  : x = y
  :=
    zag-zig-concat A x center-contraction y
      ( homotopy-contraction x) (homotopy-contraction y)

#end contractible-data
```

## Unit type

The prototypical contractible type is the unit type, which is built-in to rzk.

```rzk
#def ind-unit
  ( C : Unit → U)
  ( C-unit : C unit)
  ( x : Unit)
  : C x
  := C-unit

#def is-prop-unit
  ( x y : Unit)
  : x = y
  := refl
```

```rzk title="The terminal projection as a constant map"
#def terminal-map
  ( A : U)
  : A → Unit
  := constant A Unit unit
```

## Identity types of unit types

```rzk
#def terminal-map-of-path-types-of-Unit-has-retr
  ( x y : Unit)
  : has-retraction (x = y) Unit (terminal-map (x = y))
  :=
    ( \ a → refl
    , \ p → ind-path (Unit) (x) (\ y' p' → refl =_{x = y'} p') (refl) (y) (p))

#def terminal-map-of-path-types-of-Unit-has-sec
  ( x y : Unit)
  : has-section (x = y) Unit (terminal-map (x = y))
  := (\ a → refl , \ a → refl)

#def terminal-map-of-path-types-of-Unit-is-equiv
  ( x y : Unit)
  : is-equiv (x = y) Unit (terminal-map (x = y))
  :=
    ( terminal-map-of-path-types-of-Unit-has-retr x y
    , terminal-map-of-path-types-of-Unit-has-sec x y)
```

## Characterization of contractibility

A type is contractible if and only if its terminal map is an equivalence.

```rzk
#def terminal-map-is-equiv
  ( A : U)
  : U
  := is-equiv A Unit (terminal-map A)

#def contr-implies-terminal-map-is-equiv-retr
  ( A : U)
  ( is-contr-A : is-contr A)
  : has-retraction A Unit (terminal-map A)
  :=
    ( constant Unit A (center-contraction A is-contr-A)
    , \ y → (homotopy-contraction A is-contr-A) y)

#def contr-implies-terminal-map-is-equiv-sec
  ( A : U)
  ( is-contr-A : is-contr A)
  : has-section A Unit (terminal-map A)
  := (constant Unit A (center-contraction A is-contr-A) , \ z → refl)

#def contr-implies-terminal-map-is-equiv
  ( A : U)
  ( is-contr-A : is-contr A)
  : is-equiv A Unit (terminal-map A)
  :=
    ( contr-implies-terminal-map-is-equiv-retr A is-contr-A
    , contr-implies-terminal-map-is-equiv-sec A is-contr-A)

#def terminal-map-is-equiv-implies-contr
  ( A : U)
  ( e : terminal-map-is-equiv A)
  : is-contr A
  := ((first (first e)) unit , (second (first e)))

#def contr-iff-terminal-map-is-equiv
  ( A : U)
  : iff (is-contr A) (terminal-map-is-equiv A)
  :=
    ( ( contr-implies-terminal-map-is-equiv A)
    , ( terminal-map-is-equiv-implies-contr A))

#def equiv-with-contractible-domain-implies-contractible-codomain
  ( A B : U)
  ( f : Equiv A B)
  ( is-contr-A : is-contr A)
  : is-contr B
  :=
    ( terminal-map-is-equiv-implies-contr B
      ( second
        ( equiv-comp B A Unit
          ( inv-equiv A B f)
          ( ( terminal-map A)
          , ( contr-implies-terminal-map-is-equiv A is-contr-A)))))

#def equiv-with-contractible-codomain-implies-contractible-domain
  ( A B : U)
  ( f : Equiv A B)
  ( is-contr-B : is-contr B)
  : is-contr A
  :=
    ( equiv-with-contractible-domain-implies-contractible-codomain B A
      ( inv-equiv A B f) is-contr-B)

#def equiv-then-domain-contractible-iff-codomain-contractible
  ( A B : U)
  ( f : Equiv A B)
  : ( iff (is-contr A) (is-contr B))
  :=
    ( \ is-contr-A →
      ( equiv-with-contractible-domain-implies-contractible-codomain
        A B f is-contr-A)
    , \ is-contr-B →
      ( equiv-with-contractible-codomain-implies-contractible-domain
        A B f is-contr-B))

#def path-types-of-Unit-are-contractible
  ( x y : Unit)
  : is-contr (x = y)
  :=
    ( terminal-map-is-equiv-implies-contr
      ( x = y) (terminal-map-of-path-types-of-Unit-is-equiv x y))
```

## Retracts of contractible types

A retract of contractible types is contractible.

```rzk title="The type of proofs that A is a retract of B"
#def is-retract-of
  ( A B : U)
  : U
  := Σ (s : A → B) , has-retraction A B s

#section retraction-data

#variables A B : U
#variable is-retract-of-A-B : is-retract-of A B

#def is-retract-of-section
  : A → B
  := first is-retract-of-A-B

#def is-retract-of-retraction
  : B → A
  := first (second is-retract-of-A-B)

#def is-retract-of-homotopy
  : homotopy A A (comp A B A is-retract-of-retraction is-retract-of-section) (identity A)
  := second (second is-retract-of-A-B)
```

```rzk title="If A is a retract of a contractible type it has a term"
#def is-retract-of-is-contr-isInhabited uses (is-retract-of-A-B)
  ( is-contr-B : is-contr B)
  : A
  := is-retract-of-retraction (center-contraction B is-contr-B)
```

```rzk title="If A is a retract of a contractible type it has a contracting homotopy"
#def is-retract-of-is-contr-hasHtpy uses (is-retract-of-A-B)
  ( is-contr-B : is-contr B)
  ( a : A)
  : ( is-retract-of-is-contr-isInhabited is-contr-B) = a
  :=
    concat
      ( A)
      ( is-retract-of-is-contr-isInhabited is-contr-B)
      ( ( comp A B A is-retract-of-retraction is-retract-of-section) a)
      ( a)
      ( ap B A (center-contraction B is-contr-B) (is-retract-of-section a)
        ( is-retract-of-retraction)
        ( homotopy-contraction B is-contr-B (is-retract-of-section a)))
      ( is-retract-of-homotopy a)
```

```rzk title="If A is a retract of a contractible type it is contractible"
#def is-contr-is-retract-of-is-contr uses (is-retract-of-A-B)
  ( is-contr-B : is-contr B)
  : is-contr A
  :=
    ( is-retract-of-is-contr-isInhabited is-contr-B
    , is-retract-of-is-contr-hasHtpy is-contr-B)
```

```rzk
#end retraction-data
```

## Functions between contractible types

```rzk title="Any function between contractible types is an equivalence"
#def is-equiv-are-contr
  ( A B : U)
  ( is-contr-A : is-contr A)
  ( is-contr-B : is-contr B)
  ( f : A → B)
  : is-equiv A B f
  :=
    ( ( \ b → center-contraction A is-contr-A
      , \ a → homotopy-contraction A is-contr-A a)
    , ( \ b → center-contraction A is-contr-A
      , \ b → eq-is-contr B is-contr-B
                ( f (center-contraction A is-contr-A)) b))
```

```rzk title="A type equivalent to a contractible type is contractible"
#def is-contr-equiv-is-contr'
  ( A B : U)
  ( e : Equiv A B)
  ( is-contr-B : is-contr B)
  : is-contr A
  :=
    is-contr-is-retract-of-is-contr A B (first e , first (second e)) is-contr-B

#def is-contr-equiv-is-contr
  ( A B : U)
  ( e : Equiv A B)
  ( is-contr-A : is-contr A)
  : is-contr B
  :=
    is-contr-is-retract-of-is-contr B A
      ( first (second (second e)) , (first e , second (second (second e))))
      ( is-contr-A)
```

## Based path spaces

For example, we prove that based path spaces are contractible.

```rzk title="Transport in the space of paths starting at a is concatenation"
#def concat-as-based-transport
  ( A : U)
  ( a x y : A)
  ( p : a = x)
  ( q : x = y)
  : ( transport A (\ z → (a = z)) x y q p) = (concat A a x y p q)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' q' →
        ( transport A (\ z → (a = z)) x y' q' p) = (concat A a x y' p q'))
      ( refl)
      ( y)
      ( q)
```

The center of contraction in the based path space is `#!rzk (a , refl)`.

```rzk title="The center of contraction in the based path space"
#def center-based-paths
  ( A : U)
  ( a : A)
  : Σ ( x : A) , (a = x)
  := (a , refl)
```

```rzk title="The contracting homotopy in the based path space"
#def contraction-based-paths
  ( A : U)
  ( a : A)
  ( p : Σ (x : A) , a = x)
  : ( center-based-paths A a) = p
  :=
    path-of-pairs-pair-of-paths
      A (\ z → a = z) a (first p) (second p) (refl) (second p)
      ( concat
        ( a = (first p))
        ( transport A (\ z → (a = z)) a (first p) (second p) (refl))
        ( concat A a a (first p) (refl) (second p))
        ( second p)
        ( concat-as-based-transport A a a (first p) (refl) (second p))
        ( left-unit-concat A a (first p) (second p)))
```

```rzk title="Based path spaces are contractible"
#def is-contr-based-paths
  ( A : U)
  ( a : A)
  : is-contr (Σ (x : A) , a = x)
  := (center-based-paths A a , contraction-based-paths A a)
```

## Contractible products

```rzk
#def is-contr-product
  ( A B : U)
  ( is-contr-A : is-contr A)
  ( is-contr-B : is-contr B)
  : is-contr (product A B)
  :=
    ( ( first is-contr-A , first is-contr-B)
    , \ p → path-product A B
              ( first is-contr-A) (first p)
              ( first is-contr-B) (second p)
              ( second is-contr-A (first p))
              ( second is-contr-B (second p)))

#def first-is-contr-product
  ( A B : U)
  ( AxB-is-contr : is-contr (product A B))
  : is-contr A
  :=
    ( first (first AxB-is-contr)
    , \ a → first-path-product A B
              ( first AxB-is-contr)
              ( a , second (first AxB-is-contr))
              ( second AxB-is-contr (a , second (first AxB-is-contr))))

#def is-contr-base-is-contr-Σ
  ( A : U)
  ( B : A → U)
  ( b : (a : A) → B a)
  ( is-contr-AB : is-contr (Σ (a : A) , B a))
  : is-contr A
  :=
    ( first (first is-contr-AB)
    , \ a → first-path-Σ A B
              ( first is-contr-AB)
              ( a , b a)
              ( second is-contr-AB (a , b a)))
```

## Singleton induction

A type is contractible if and only if it has singleton induction.

```rzk
#def ev-pt
  ( A : U)
  ( a : A)
  ( B : A → U)
  : ( ( x : A) → B x) → B a
  := \ f → f a

#def has-singleton-induction-pointed
  ( A : U)
  ( a : A)
  ( B : A → U)
  : U
  := has-section ((x : A) → B x) (B a) (ev-pt A a B)

#def has-singleton-induction-pointed-structure
  ( A : U)
  ( a : A)
  : U
  := (B : A → U) → has-section ((x : A) → B x) (B a) (ev-pt A a B)

#def has-singleton-induction
  ( A : U)
  : U
  := Σ (a : A) , (B : A → U) → (has-singleton-induction-pointed A a B)

#def ind-sing
  ( A : U)
  ( a : A)
  ( B : A → U)
  ( singleton-ind-A : has-singleton-induction-pointed A a B)
  : ( B a) → ((x : A) → B x)
  := (first singleton-ind-A)

#def compute-ind-sing
  ( A : U)
  ( a : A)
  ( B : A → U)
  ( singleton-ind-A : has-singleton-induction-pointed A a B)
  : ( homotopy
      ( B a)
      ( B a)
      ( comp
        ( B a)
        ( ( x : A) → B x)
        ( B a)
        ( ev-pt A a B)
        ( ind-sing A a B singleton-ind-A))
      ( identity (B a)))
  := (second singleton-ind-A)

#def contr-implies-singleton-induction-ind
  ( A : U)
  ( is-contr-A : is-contr A)
  : ( has-singleton-induction A)
  :=
    ( ( center-contraction A is-contr-A)
    , \ B →
        ( ( \ b x →
                ( transport A B
                  ( center-contraction A is-contr-A) x
                  ( realign-homotopy-contraction A is-contr-A x) b))
        , ( \ b →
                ( ap
                  ( ( center-contraction A is-contr-A)
                  = ( center-contraction A is-contr-A))
                  ( B (center-contraction A is-contr-A))
                  ( realign-homotopy-contraction A is-contr-A
                    ( center-contraction A is-contr-A))
                  refl_{(center-contraction A is-contr-A)}
                  ( \ p →
                    ( transport-loop A B (center-contraction A is-contr-A) b p))
                  ( path-realign-homotopy-contraction A is-contr-A)))))

#def contr-implies-singleton-induction-pointed
  ( A : U)
  ( is-contr-A : is-contr A)
  ( B : A → U)
  : has-singleton-induction-pointed A (center-contraction A is-contr-A) B
  := (second (contr-implies-singleton-induction-ind A is-contr-A)) B

#def singleton-induction-ind-implies-contr
  ( A : U)
  ( a : A)
  ( f : has-singleton-induction-pointed-structure A a)
  : ( is-contr A)
  := (a , (first (f (\ x → a = x))) (refl_{a}))
```
