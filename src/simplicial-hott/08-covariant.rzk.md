# Covariantly functorial type families

These formalisations correspond to Section 8 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the notion of contractible types.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `5-segal-types.md` - We make use of the notion of Segal types and their
  structures.

Some of the definitions in this file rely on extension extensionality:

```rzk
#assume extext : ExtExt
```

## Dependent hom types

In a type family over a base type, there is a dependent hom type of arrows that
live over a specified arrow in the base type.

```rzk title="RS17, Section 8 Prelim"
#def dhom
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( u : C x)
  ( v : C y)
  : U
  := ( t : Δ¹) → C (f t) [
        t ≡ 0₂ ↦ u ,
        t ≡ 1₂ ↦ v
    ]
```

It will be convenient to collect together dependent hom types with fixed domain
but varying codomain.

```rzk
#def dhom-from
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( u : C x)
  : U
  := ( Σ (v : C y) , dhom A x y f C u v)
```

There is also a type of dependent commutative triangles over a base commutative
triangle.

```rzk
#def dhom2
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( α : hom2 A x y z f g h)
  ( C : A → U)
  ( u : C x)
  ( v : C y)
  ( w : C z)
  ( ff : dhom A x y f C u v)
  ( gg : dhom A y z g C v w)
  ( hh : dhom A x z h C u w)
  : U
  :=
    ( (t1 , t2) : Δ²) → C (α (t1 , t2)) [
        t2 ≡ 0₂ ↦ ff t1 ,
        t1 ≡ 1₂ ↦ gg t2 ,
        t2 ≡ t1 ↦ hh t2
      ]
```

## Covariant families

A family of types over a base type is covariant if every arrow in the base has a
unique lift with specified domain.

```rzk title="RS17, Definition 8.2"
#def is-covariant
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom A x y) → (u : C x) →
      is-contr (dhom-from A x y f C u)
```

```rzk title="The type of covariant families over a fixed type"
#def covariant-family (A : U) : U
  := ( Σ (C : (A → U)) , is-covariant A C)
```

The notion of having a unique lift with a fixed domain may also be expressed by
contractibility of the type of extensions along the domain inclusion into the
1-simplex.

```rzk
#def has-unique-fixed-domain-lifts
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom A x y) → (u : C x) →
      is-contr ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u ])
```

These two notions of covariance are equivalent because the two types of lifts of
a base arrow with fixed domain are equivalent. Note that this is not quite an
instance of Theorem 4.4 but its proof, with a very small modification, works
here.

```rzk
#def equiv-lifts-with-fixed-domain
  ( A : U)
  ( C : A → U)
  ( x y : A)
  ( f : hom A x y)
  ( u : C x)
  : Equiv
      ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u ])
      (dhom-from A x y f C u)
  :=
    ( \ h → (h 1₂ , \ t → h t) ,
      ( ( \ fg t → (second fg) t , \ h → refl) ,
        ( ( \ fg t → (second fg) t , \ h → refl))))
```

By the equivalence-invariance of contractibility, this proves the desired
logical equivalence

```rzk title="RS17, Proposition 8.4"
#def has-unique-fixed-domain-lifts-iff-is-covariant
  ( A : U)
  ( C : A → U)
  : iff
      ( has-unique-fixed-domain-lifts A C)
      ( is-covariant A C)
  :=
    ( \ C-has-unique-lifts x y f u →
      is-contr-is-equiv-from-contr
        ( (t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u ])
        ( dhom-from A x y f C u)
        ( equiv-lifts-with-fixed-domain A C x y f u)
        ( C-has-unique-lifts x y f u),
      \ C-is-covariant x y f u →
      is-contr-is-equiv-to-contr
        ( (t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u ])
        ( dhom-from A x y f C u)
        ( equiv-lifts-with-fixed-domain A C x y f u)
        ( C-is-covariant x y f u))
```

## Representable covariant families

If A is a Segal type and a : A is any term, then hom A a defines a covariant
family over A, and conversely if this family is covariant for every a : A, then
A must be a Segal type. The proof involves a rather lengthy composition of
equivalences.

```rzk
#def dhom-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  ( v : hom A a y)
  : U
  := dhom A x y f (\ z → hom A a z) u v
```

By uncurrying (RS 4.2) we have an equivalence:

```rzk
#def uncurried-dhom-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  ( v : hom A a y)
  : Equiv
    ( dhom-representable A a x y f u v)
    ( ((t , s) : Δ¹×Δ¹) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ])
  :=
    curry-uncurry 2 2 Δ¹ ∂Δ¹ Δ¹ ∂Δ¹ (\ t s → A)
    ( \ (t , s) →
      recOR
        ( (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ))

#def dhom-from-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : U
  := dhom-from A x y f (\ z → hom A a z) u
```

By uncurrying (RS 4.2) we have an equivalence:

```rzk
#def uncurried-dhom-from-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( dhom-from-representable A a x y f u)
    ( Σ (v : hom A a y) , (((t , s) : Δ¹×Δ¹) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
  :=
    total-equiv-family-equiv
      ( hom A a y)
      ( \ v → dhom-representable A a x y f u v)
      ( \ v →
        (((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
      ( \ v → uncurried-dhom-representable A a x y f u v)

#def square-to-hom2-pushout
  ( A : U)
  ( w x y z : A)
  ( u : hom A w x)
  ( f : hom A x z)
  ( g : hom A w y)
  ( v : hom A y z)
  : ( ((t , s) : Δ¹×Δ¹) → A [(t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ g t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) →
      ( Σ (d : hom A w z) , product (hom2 A w x z u f d) (hom2 A w y z g v d))
  :=
    \ sq →
    ( ( \ t → sq (t , t)) , (\ (t , s) → sq (s , t) , \ (t , s) → sq (t , s)))

#def hom2-pushout-to-square
  ( A : U)
  ( w x y z : A)
  ( u : hom A w x)
  ( f : hom A x z)
  ( g : hom A w y)
  ( v : hom A y z)
  : ( Σ (d : hom A w z) , product (hom2 A w x z u f d) (hom2 A w y z g v d)) →
      ( ((t , s) : Δ¹×Δ¹) → A [
                      (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ g t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ])
  :=
    \ (d , (α1 , α2)) (t , s) →
      recOR (t ≤ s ↦ α1 (s , t) ,
             s ≤ t ↦ α2 (t , s))

#def Eq-square-hom2-pushout
  ( A : U)
  ( w x y z : A)
  ( u : hom A w x)
  ( f : hom A x z)
  ( g : hom A w y)
  ( v : hom A y z)
  : Equiv
    ( ((t , s) : Δ¹×Δ¹) → A [(t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ g t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ])
    ( Σ (d : hom A w z) , product (hom2 A w x z u f d) (hom2 A w y z g v d))
  :=
    ( square-to-hom2-pushout A w x y z u f g v ,
      ( ( hom2-pushout-to-square A w x y z u f g v , \ sq → refl) ,
        ( hom2-pushout-to-square A w x y z u f g v , \ αs → refl)))

#def representable-dhom-from-uncurry-hom2
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( Σ (v : hom A a y) ,
      ( ((t , s) : Δ¹×Δ¹) → A [
                      (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( Σ (v : hom A a y) ,
      ( Σ (d : hom A a y) ,
        product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
  :=
    total-equiv-family-equiv
    ( hom A a y)
    ( \ v →
      ( ((t , s) : Δ¹×Δ¹) → A [
                      (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( \ v →
      ( Σ (d : hom A a y) ,
        product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
    ( \ v → Eq-square-hom2-pushout A a x a y u f (id-hom A a) v)

#def representable-dhom-from-hom2
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( Σ (v : hom A a y) ,
        product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
  :=
    equiv-triple-comp
    ( dhom-from-representable A a x y f u)
    ( Σ (v : hom A a y) ,
      ( ((t , s) : Δ¹×Δ¹) → A [
                      (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( Σ (v : hom A a y) ,
      ( Σ (d : hom A a y) ,
        product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
    ( Σ (d : hom A a y) ,
      ( Σ (v : hom A a y) ,
      product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
    ( uncurried-dhom-from-representable A a x y f u)
    ( representable-dhom-from-uncurry-hom2 A a x y f u)
    ( fubini-Σ (hom A a y) (hom A a y)
      ( \ v d → product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))

#def representable-dhom-from-hom2-dist
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( product
        ( hom2 A a x y u f d)
        ( Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d)))
  :=
    equiv-right-cancel
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( product
        ( hom2 A a x y u f d)
        ( Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d)))
    ( Σ (d : hom A a y) ,
      ( Σ (v : hom A a y) ,
        product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
    ( representable-dhom-from-hom2 A a x y f u)
    ( total-equiv-family-equiv
      ( hom A a y)
      ( \ d →
        ( product
          ( hom2 A a x y u f d)
          ( Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d)))
      ( \ d →
        ( Σ (v : hom A a y) ,
          product (hom2 A a x y u f d) (hom2 A a a y (id-hom A a) v d)))
      ( \ d →
        ( distributive-product-Σ (hom2 A a x y u f d) (hom A a y)
          ( \ v → hom2 A a a y (id-hom A a) v d))))
```

Now we introduce the hypothesis that A is Segal type.

```rzk
#def representable-dhom-from-path-space-Segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
  :=
    equiv-right-cancel
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
    ( Σ (d : hom A a y) ,
      ( product
        ( hom2 A a x y u f d)
        ( Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d)))
    ( representable-dhom-from-hom2-dist A a x y f u)
    ( total-equiv-family-equiv
      ( hom A a y)
      ( \ d → (product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
      ( \ d →
        ( product
          ( hom2 A a x y u f d)
          ( Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d)))
      ( \ d →
        ( total-equiv-family-equiv
          ( hom2 A a x y u f d)
          ( \ α → (Σ (v : hom A a y) , (v = d)))
          ( \ α → (Σ (v : hom A a y) , hom2 A a a y (id-hom A a) v d))
          ( \ α →
            ( total-equiv-family-equiv
              ( hom A a y)
              ( \ v → (v = d))
              ( \ v → hom2 A a a y (id-hom A a) v d)
              ( \ v → (Eq-Segal-homotopy-hom2 A is-segal-A a y v d)))))))


#def codomain-based-paths-contraction
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  ( d : hom A a y)
  : Equiv
    ( product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d)))
    ( hom2 A a x y u f d)
  :=
    equiv-projection-contractible-fibers
      ( hom2 A a x y u f d)
      ( \ α → (Σ (v : hom A a y) , (v = d)))
      ( \ α → is-contr-codomain-based-paths (hom A a y) d)

#def is-segal-representable-dhom-from-hom2
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv (dhom-from-representable A a x y f u)
    (Σ (d : hom A a y) , (hom2 A a x y u f d))
  :=
    equiv-comp
    ( dhom-from-representable A a x y f u)
    ( Σ (d : hom A a y) ,
      ( product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d))))
    ( Σ (d : hom A a y) , (hom2 A a x y u f d))
    ( representable-dhom-from-path-space-Segal A is-segal-A a x y f u)
    ( total-equiv-family-equiv
      ( hom A a y)
      ( \ d → product (hom2 A a x y u f d) (Σ (v : hom A a y) , (v = d)))
      ( \ d → hom2 A a x y u f d)
      ( \ d → codomain-based-paths-contraction A a x y f u d))

#def is-segal-representable-dhom-from-contractible
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : is-contr (dhom-from-representable A a x y f u)
  :=
    is-contr-is-equiv-to-contr
      ( dhom-from-representable A a x y f u)
      ( Σ (d : hom A a y) , (hom2 A a x y u f d))
      ( is-segal-representable-dhom-from-hom2 A is-segal-A a x y f u)
      ( is-segal-A a x y u f)
```

Finally, we see that covariant hom families in a Segal type are covariant.

```rzk title="RS17, Proposition 8.13(<-)"
#def is-segal-representable-is-covariant
  (A : U)
  (is-segal-A : is-segal A)
  (a : A)
  : is-covariant A (\ x → hom A a x)
  :=
    \ x y f u →
    is-segal-representable-dhom-from-contractible A is-segal-A a x y f u
```

The proof of the claimed converse result given in the original source is
circular - using Proposition 5.10, which holds only for Segal types - so instead
we argue as follows:

```rzk title="RS17, Proposition 8.13(→)"
#def representable-is-covariant-is-segal
  ( A : U)
  ( corepresentable-family-is-covariant : (a : A) →
    is-covariant A (\ x → hom A a x))
  : is-segal A
  :=
    \ x y z f g →
    is-contr-base-is-contr-Σ
    ( Σ (h : hom A x z) , hom2 A x y z f g h)
    ( \ hk → Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v (first hk))
    ( \ hk → (first hk , \ (t , s) → first hk s))
    ( is-contr-is-equiv-to-contr
      ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
        Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v (first hk))
      ( dhom-from-representable A x y z g f)
      ( inv-equiv
        ( dhom-from-representable A x y z g f)
        ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
          Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v (first hk))
        ( equiv-comp
          ( dhom-from-representable A x y z g f)
          ( Σ (h : hom A x z) ,
            ( product
              ( hom2 A x y z f g h)
              ( Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v h)))
          ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
            Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v (first hk))
          ( representable-dhom-from-hom2-dist A x y z g f)
          ( associative-Σ
            ( hom A x z)
            ( \ h → hom2 A x y z f g h)
            ( \ h _ → Σ (v : hom A x z) , hom2 A x x z (id-hom A x) v h))))
      ( corepresentable-family-is-covariant x y z g f))
```

While not needed to prove Proposition 8.13, it is interesting to observe that
the dependent hom types in a representable family can be understood as extension
types as follows.

```rzk
#def cofibration-union-test
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( ((t , s) : ∂□) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ])
    ( ((t , s) : 2 × 2 | (t ≡ 1₂) ∧ (Δ¹ s)) → A
      [ (t ≡ 1₂) ∧ (s ≡ 0₂) ↦ a ,
        (t ≡ 1₂) ∧ (s ≡ 1₂) ↦ y ])
  :=
    cofibration-union (2 × 2)
    ( \ (t , s) → (t ≡ 1₂) ∧ Δ¹ s)
    ( \ (t , s) →
      (t ≡ 0₂) ∧ (Δ¹ s) ∨ (Δ¹ t) ∧ (s ≡ 0₂) ∨ (Δ¹ t) ∧ (s ≡ 1₂))
    ( \ (t , s) → A)
    ( \ (t , s) →
      recOR
        ( (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t))

#def base-hom-rewriting
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    (((t , s) : 2 × 2 | (t ≡ 1₂) ∧ (Δ¹ s)) → A
      [ (t ≡ 1₂) ∧ (s ≡ 0₂) ↦ a ,
        (t ≡ 1₂) ∧ (s ≡ 1₂) ↦ y ])
    (hom A a y)
  :=
    ( \ v → (\ r → v ((1₂ , r))) ,
      ( ( \ v → \ (t , s) → v s ,
          \ v → refl) ,
        ( \ v → \ (t , s) → v s ,
          \ v → refl)))

#def base-hom-expansion
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( ((t , s) : ∂□) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t])
    ( hom A a y)
  :=
    equiv-comp
    ( ((t , s) : ∂□) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ] )
    ( ((t , s) : 2 × 2 | (t ≡ 1₂) ∧ (Δ¹ s)) → A
      [ (t ≡ 1₂) ∧ (s ≡ 0₂) ↦ a ,
        (t ≡ 1₂) ∧ (s ≡ 1₂) ↦ y ])
    ( hom A a y)
    ( cofibration-union-test A a x y f u)
    ( base-hom-rewriting A a x y f u)

#def representable-dhom-from-expansion
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( Σ (sq : ((t , s) : ∂□) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) ,
        (((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ (sq (1₂ , s)) ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( Σ (v : hom A a y) ,
      (((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
  :=
    total-equiv-pullback-is-equiv
    ( ((t , s) : ∂□) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ] )
    ( hom A a y)
    ( first (base-hom-expansion A a x y f u))
    ( second (base-hom-expansion A a x y f u))
    ( \ v →
      ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))

#def representable-dhom-from-composite-expansion
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv (dhom-from-representable A a x y f u)
      ( Σ (sq : ((t , s) : ∂□) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) ,
        ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ (sq (1₂ , s)) ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
  :=
    equiv-right-cancel
    ( dhom-from-representable A a x y f u)
    ( Σ (sq : ((t , s) : ∂□) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) ,
        ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ (sq (1₂ , s)) ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( Σ (v : hom A a y) , (((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( uncurried-dhom-from-representable A a x y f u)
    ( representable-dhom-from-expansion A a x y f u)

#def representable-dhom-from-cofibration-composition
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
    ( ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t] )
    ( Σ (sq : ((t , s) : ∂□) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) ,
        (((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ (sq (1₂ , s)) ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
  :=
    cofibration-composition (2 × 2) Δ¹×Δ¹ ∂□
    ( \ (t , s) →
      (t ≡ 0₂) ∧ (Δ¹ s) ∨ (Δ¹ t) ∧ (s ≡ 0₂) ∨ (Δ¹ t) ∧ (s ≡ 1₂))
    ( \ ts → A)
    ( \ (t , s) →
      recOR ( (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t))

#def representable-dhom-from-as-extension-type
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A a x)
  : Equiv
      ( dhom-from-representable A a x y f u)
      ( ((t , s) : Δ¹×Δ¹) → A
              [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t] )
  :=
    equiv-right-cancel
    ( dhom-from-representable A a x y f u)
    ( ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t] )
    ( Σ (sq : ((t , s) : ∂□) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]) ,
        ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ (sq (1₂ , s)) ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ a ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ f t ]))
    ( representable-dhom-from-composite-expansion A a x y f u)
    ( representable-dhom-from-cofibration-composition A a x y f u)
```

## Covariant lifts, transport, and uniqueness

In a covariant family C over a base type A , a term u : C x may be transported
along an arrow f : hom A x y to give a term in C y.

```rzk title="RS17, covariant transport from beginning of Section 8.2"
#def covariant-transport
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
   : C y
   :=
    first (contraction-center (dhom-from A x y f C u) (is-covariant-C x y f u))
```

```rzk title="RS17, covariant lift from beginning of Section 8.2"
#def covariant-lift
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
  : ( dhom A x y f C u (covariant-transport A x y f C is-covariant-C u))
  :=
    second (contraction-center (dhom-from A x y f C u) (is-covariant-C x y f u))

#def covariant-uniqueness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
  ( lift : dhom-from A x y f C u)
  : ( covariant-transport A x y f C is-covariant-C u) = (first lift)
  :=
    first-path-Σ
    ( C y)
    ( \ v → dhom A x y f C u v)
    ( contraction-center (dhom-from A x y f C u) (is-covariant-C x y f u))
    ( lift)
    ( contracting-htpy (dhom-from A x y f C u) (is-covariant-C x y f u) lift)
```

## Covariant functoriality

The covariant transport operation defines a covariantly functorial action of
arrows in the base on terms in the fibers. In particular, there is an identity
transport law.

```rzk
#def id-dhom
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( u : C x)
  : dhom A x x (id-hom A x) C u u
  := \ t → u
```

```rzk title="RS17, Proposition 8.16, Part 2, Covariant families preserve identities"
#def id-arr-covariant-transport
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( u : C x)
  : ( covariant-transport A x x (id-hom A x) C is-covariant-C u) = u
  :=
    covariant-uniqueness
      A x x (id-hom A x) C is-covariant-C u (u , id-dhom A x C u)
```

## Natural transformations

A fiberwise map between covariant families is automatically "natural" commuting
with the covariant lifts.

```rzk title="RS17, Proposition 8.17, Covariant naturality"
#def covariant-fiberwise-transformation-application
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( ϕ : (z : A) → C z → D z)
  ( u : C x)
  : dhom-from A x y f D (ϕ x u)
  :=
    ( ϕ y (covariant-transport A x y f C is-covariant-C u) ,
      \ t → ϕ (f t) (covariant-lift A x y f C is-covariant-C u t))

#def naturality-covariant-fiberwise-transformation
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C D : A → U)
  ( is-covariant-C : is-covariant A C)
  ( is-covariant-D : is-covariant A D)
  ( ϕ : (z : A) → C z → D z)
  ( u : C x)
  : ( covariant-transport A x y f D is-covariant-D (ϕ x u)) =
    ( ϕ y (covariant-transport A x y f C is-covariant-C u))
  :=
    covariant-uniqueness A x y f D is-covariant-D (ϕ x u)
      ( covariant-fiberwise-transformation-application
          A x y f C D is-covariant-C ϕ u)
```

## Covariant equivalence

A family of types that is equivalent to a covariant family is itself covariant.

To prove this we first show that the corresponding types of lifts with fixed
domain are equivalent:

```rzk
#def equiv-covariant-total-dhom
  ( A : U)
  ( C : A → U)
  ( x y : A)
  ( f : hom A x y)
  : Equiv
    ( (t : Δ¹) → C (f t))
    ( Σ (u : C x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))
  :=
    ( \ h → (h 0₂ , \ t → h t) ,
      ( ( \ k t → (second k) t , \ h → refl) ,
        ( ( \ k t → (second k) t , \ h → refl))))
```

```rzk
#section dhom-from-equivalence

#variable A : U
#variables B C : A → U
#variable equiv-BC : (a : A) → Equiv (B a) (C a)
#variables x y : A
#variable f : hom A x y

#def equiv-total-dhom-equiv uses (A x y)
  : Equiv ( (t : Δ¹) → B (f t)) ((t : Δ¹) → C (f t))
  :=
    equiv-extension-equiv-fibered
      ( extext)
      ( 2)
      ( Δ¹)
      ( \ t → B (f t))
      ( \ t → C (f t))
      ( \ t → equiv-BC (f t))

#def equiv-total-covariant-dhom-equiv uses (extext equiv-BC)
  : Equiv
    ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
    ( Σ (u : C x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))
  :=
    equiv-triple-comp
    ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
    ( (t : Δ¹) → B (f t))
    ( (t : Δ¹) → C (f t))
    ( Σ (u : C x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))
    ( inv-equiv
      ( (t : Δ¹) → B (f t))
      ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
      ( equiv-covariant-total-dhom A B x y f))
    ( equiv-total-dhom-equiv)
    ( equiv-covariant-total-dhom A C x y f)

#def equiv-pullback-total-covariant-dhom-equiv uses (A y)
  : Equiv
    ( Σ (i : B x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i]))
    ( Σ (u : C x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))
  :=
    total-equiv-pullback-is-equiv
      ( B x)
      ( C x)
      ( first (equiv-BC x))
      ( second (equiv-BC x))
      ( \ u → ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))

#def is-equiv-to-pullback-total-covariant-dhom-equiv uses (extext A y)
  : is-equiv
    ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
    ( Σ (i : B x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i]))
    ( \ (i, h) → (i, \ t → (first (equiv-BC (f t))) (h t)))
  :=
    is-equiv-right-factor
    ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
    ( Σ (i : B x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i]))
    ( Σ (u : C x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ u]))
    ( \ (i, h) → (i, \ t → (first (equiv-BC (f t))) (h t)))
    ( first (equiv-pullback-total-covariant-dhom-equiv))
    ( second (equiv-pullback-total-covariant-dhom-equiv))
    ( second (equiv-total-covariant-dhom-equiv))

#def equiv-to-pullback-total-covariant-dhom-equiv uses (extext A y)
  : Equiv
    ( Σ (i : B x), ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i]))
    ( Σ (i : B x), ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i]))
  :=
    ( \ (i, h) → (i, \ t → (first (equiv-BC (f t))) (h t)),
      is-equiv-to-pullback-total-covariant-dhom-equiv)

#def family-equiv-dhom-family-equiv uses (extext A y)
  (i : B x)
  : Equiv
    ( (t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i])
    ( (t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i])
  :=
    family-equiv-total-equiv
    ( B x)
    ( \ii → ((t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ ii]))
    ( \ii → ((t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) ii]))
    ( \ii h t → (first (equiv-BC (f t))) (h t))
    ( is-equiv-to-pullback-total-covariant-dhom-equiv)
    ( i)

#end dhom-from-equivalence
```

Now we introduce the hypothesis that $C$ is covariant in the form of
`has-unique-fixed-domain-lifts`.

```rzk
#def equiv-has-unique-fixed-domain-lifts uses (extext)
  ( A : U)
  ( B C : A → U)
  ( equiv-BC : (a : A) → Equiv (B a) (C a))
  ( has-unique-fixed-domain-lifts-C :
    has-unique-fixed-domain-lifts A C)
  : has-unique-fixed-domain-lifts A B
  :=
    \ x y f i →
    is-contr-is-equiv-to-contr
    ( (t : Δ¹) → B (f t) [ t ≡ 0₂ ↦ i])
    ( (t : Δ¹) → C (f t) [ t ≡ 0₂ ↦ (first (equiv-BC x)) i])
    ( family-equiv-dhom-family-equiv A B C equiv-BC x y f i)
    ( has-unique-fixed-domain-lifts-C x y f ((first (equiv-BC x)) i))

#def equiv-is-covariant uses (extext)
  ( A : U)
  ( B C : A → U)
  ( equiv-BC : (a : A) → Equiv (B a) (C a))
  ( is-covariant-C : is-covariant A C)
  : is-covariant A B
  :=
    ( first (has-unique-fixed-domain-lifts-iff-is-covariant A B))
      ( equiv-has-unique-fixed-domain-lifts
        A B C equiv-BC
        ( (second (has-unique-fixed-domain-lifts-iff-is-covariant A C))
          is-covariant-C))
```

## Contravariant families

A family of types over a base type is contravariant if every arrow in the base
has a unique lift with specified codomain.

```rzk
#def dhom-to
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( v : C y)
  : U
  := ( Σ (u : C x) , dhom A x y f C u v)
```

```rzk title="RS17, Definition 8.2, dual form"
#def is-contravariant
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom A x y) → (v : C y) →
      is-contr (dhom-to A x y f C v)
```

```rzk title="The type of contravariant families over a fixed type"
#def contravariant-family (A : U) : U
  := ( Σ (C : A → U) , is-contravariant A C)
```

The notion of having a unique lift with a fixed codomain may also be expressed
by contractibility of the type of extensions along the codomain inclusion into
the 1-simplex.

```rzk
#def has-unique-fixed-codomain-lifts
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom A x y) → (v : C y) →
      is-contr ((t : Δ¹) → C (f t) [ t ≡ 1₂ ↦ v ])
```

These two notions of covariance are equivalent because the two types of lifts of
a base arrow with fixed codomain are equivalent. Note that this is not quite an
instance of Theorem 4.4 but its proof, with a very small modification, works
here.

```rzk
#def equiv-lifts-with-fixed-codomain
  ( A : U)
  ( C : A → U)
  ( x y : A)
  ( f : hom A x y)
  ( v : C y)
  : Equiv
      ( (t : Δ¹) → C (f t) [ t ≡ 1₂ ↦ v ])
      ( dhom-to A x y f C v)
  :=
    ( \ h → (h 0₂ , \ t → h t) ,
      ( ( \ fg t → (second fg) t , \ h → refl) ,
        ( ( \ fg t → (second fg) t , \ h → refl))))
```

By the equivalence-invariance of contractibility, this proves the desired
logical equivalence

```rzk title="RS17, Proposition 8.4"
#def has-unique-fixed-codomain-lifts-iff-is-contravariant
  ( A : U)
  ( C : A → U)
  : iff
      ( has-unique-fixed-codomain-lifts A C)
      ( is-contravariant A C)
  :=
    ( \ C-has-unique-lifts x y f v →
      is-contr-is-equiv-from-contr
        ( (t : Δ¹) → C (f t) [ t ≡ 1₂ ↦ v ])
        ( dhom-to A x y f C v)
        ( equiv-lifts-with-fixed-codomain A C x y f v)
        ( C-has-unique-lifts x y f v),
      \ is-contravariant-C x y f v →
      is-contr-is-equiv-to-contr
        ( (t : Δ¹) → C (f t) [ t ≡ 1₂ ↦ v ])
        ( dhom-to A x y f C v)
        ( equiv-lifts-with-fixed-codomain A C x y f v)
        ( is-contravariant-C x y f v))
```

## Representable contravariant families

If A is a Segal type and a : A is any term, then the family \ x → hom A x a
defines a contravariant family over A , and conversely if this family is
contravariant for every a : A , then A must be a Segal type. The proof involves
a rather lengthy composition of equivalences.

```rzk
#def dhom-contra-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A x a)
  ( v : hom A y a)
  : U
  := dhom A x y f (\ z → hom A z a) u v
```

By uncurrying (RS 4.2) we have an equivalence:

```rzk
#def uncurried-dhom-contra-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( u : hom A x a)
  ( v : hom A y a)
  : Equiv
    ( dhom-contra-representable A a x y f u v)
    ( ((t , s) : Δ¹×Δ¹) → A [
                      (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ])
  := curry-uncurry 2 2 Δ¹ ∂Δ¹ Δ¹ ∂Δ¹ (\ t s → A)
    (\ (t , s) → recOR ((t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ))

#def dhom-to-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : U
  := dhom-to A x y f (\ z → hom A z a) v
```

By uncurrying (RS 4.2) we have an equivalence:

```rzk
#def uncurried-dhom-to-representable
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( dhom-to-representable A a x y f v)
    ( Σ (u : hom A x a) ,
        (((t , s) : Δ¹×Δ¹) → A
                    [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ]))
  :=
    total-equiv-family-equiv
    ( hom A x a)
    ( \ u → dhom-contra-representable A a x y f u v)
    ( \ u →
      (((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ]))
    ( \ u → uncurried-dhom-contra-representable A a x y f u v)

#def representable-dhom-to-uncurry-hom2
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( Σ (u : hom A x a) , (((t , s) : Δ¹×Δ¹) → A
                    [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ]))
    ( Σ (u : hom A x a) ,
      (Σ (d : hom A x a) ,
        product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d) ))
  :=
    total-equiv-family-equiv (hom A x a)
    ( \ u →
      (((t , s) : Δ¹×Δ¹) → A
                    [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ]))
    ( \ u →
      (Σ (d : hom A x a) ,
          product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d) ))
    ( \ u → Eq-square-hom2-pushout A x a y a u (id-hom A a) f v)

#def representable-dhom-to-hom2
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) ,
      (Σ (u : hom A x a) ,
        product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d) ))
  :=
    equiv-triple-comp
    ( dhom-to-representable A a x y f v)
    ( Σ (u : hom A x a) ,
        (((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ u s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ v s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ f t ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ a ]))
    ( Σ (u : hom A x a ) ,
      (Σ (d : hom A x a) ,
        product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d)))
    ( Σ (d : hom A x a ) ,
      (Σ (u : hom A x a) ,
        product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d)))
    ( uncurried-dhom-to-representable A a x y f v)
    ( representable-dhom-to-uncurry-hom2 A a x y f v)
    ( fubini-Σ (hom A x a) (hom A x a)
      (\ u d → product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d)))

#def representable-dhom-to-hom2-swap
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) , (Σ (u : hom A x a) ,
      product (hom2 A x y a f v d) (hom2 A x a a u (id-hom A a) d) ))
  := equiv-comp
      ( dhom-to-representable A a x y f v)
      ( Σ (d : hom A x a) , (Σ (u : hom A x a) ,
        product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d) ))
      ( Σ (d : hom A x a) , (Σ (u : hom A x a) ,
        product (hom2 A x y a f v d) (hom2 A x a a u (id-hom A a) d) ))
      ( representable-dhom-to-hom2 A a x y f v)
      ( total-equiv-family-equiv (hom A x a)
        (\ d → (Σ (u : hom A x a) ,
          product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d) ))
        (\ d → (Σ (u : hom A x a) ,
          product (hom2 A x y a f v d) (hom2 A x a a u (id-hom A a) d) ))
        (\ d → total-equiv-family-equiv (hom A x a)
          (\ u → product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d))
          (\ u → product (hom2 A x y a f v d) (hom2 A x a a u (id-hom A a) d))
          (\ u →
            sym-product (hom2 A x a a u (id-hom A a) d) (hom2 A x y a f v d))))

#def representable-dhom-to-hom2-dist
  ( A : U)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
      ( dhom-to-representable A a x y f v)
      ( Σ (d : hom A x a ) ,
        ( product
          ( hom2 A x y a f v d)
          ( Σ (u : hom A x a ) , hom2 A x a a u (id-hom A a) d)))
  :=
    equiv-right-cancel
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a ) ,
      ( product
        ( hom2 A x y a f v d)
        ( Σ (u : hom A x a ) , hom2 A x a a u (id-hom A a) d)))
    ( Σ (d : hom A x a) ,
      ( Σ (u : hom A x a) ,
        product
        ( hom2 A x y a f v d)
        ( hom2 A x a a u (id-hom A a) d)))
    ( representable-dhom-to-hom2-swap A a x y f v)
    ( total-equiv-family-equiv (hom A x a)
      ( \ d →
        ( product
          ( hom2 A x y a f v d)
          ( Σ (u : hom A x a ) , hom2 A x a a u (id-hom A a) d)))
      ( \ d →
        ( Σ (u : hom A x a) ,
          product (hom2 A x y a f v d) (hom2 A x a a u (id-hom A a) d) ))
      ( \ d →
        ( distributive-product-Σ
          ( hom2 A x y a f v d)
          ( hom A x a)
          ( \ u → hom2 A x a a u (id-hom A a) d))))
```

Now we introduce the hypothesis that A is Segal type.

```rzk
#def representable-dhom-to-path-space-Segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) ,
      ( product (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
  :=
    equiv-right-cancel
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) ,
      ( product (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
    ( Σ (d : hom A x a) ,
      ( product
        ( hom2 A x y a f v d)
        ( Σ (u : hom A x a) , (hom2 A x a a u (id-hom A a) d))))
    ( representable-dhom-to-hom2-dist A a x y f v)
    ( total-equiv-family-equiv (hom A x a)
      ( \ d → (product (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
      ( \ d →
        ( product
          ( hom2 A x y a f v d)
          ( Σ (u : hom A x a) , hom2 A x a a u (id-hom A a) d)))
      ( \ d →
        ( total-equiv-family-equiv
          ( hom2 A x y a f v d)
          ( \ α → (Σ (u : hom A x a) , (u = d)))
          ( \ α → (Σ (u : hom A x a) , hom2 A x a a u (id-hom A a) d))
          ( \ α →
          ( total-equiv-family-equiv
            ( hom A x a)
            ( \ u → (u = d))
            ( \ u → hom2 A x a a u (id-hom A a) d)
            ( \ u → (Eq-Segal-homotopy-hom2' A is-segal-A x a u d)))))))

#def is-segal-representable-dhom-to-hom2
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : Equiv
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) , (hom2 A x y a f v d))
  :=
    equiv-comp
    ( dhom-to-representable A a x y f v)
    ( Σ (d : hom A x a) ,
      ( product (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d))))
    ( Σ (d : hom A x a) ,
      ( hom2 A x y a f v d))
    ( representable-dhom-to-path-space-Segal A is-segal-A a x y f v)
    ( total-equiv-family-equiv
      ( hom A x a)
      ( \ d → product (hom2 A x y a f v d) (Σ (u : hom A x a) , (u = d)))
      ( \ d → hom2 A x y a f v d)
      ( \ d → codomain-based-paths-contraction A x y a v f d))

#def is-segal-representable-dhom-to-contractible
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a x y : A)
  ( f : hom A x y)
  ( v : hom A y a)
  : is-contr (dhom-to-representable A a x y f v)
  :=
    is-contr-is-equiv-to-contr
      ( dhom-to-representable A a x y f v)
      ( Σ (d : hom A x a) , (hom2 A x y a f v d))
      ( is-segal-representable-dhom-to-hom2 A is-segal-A a x y f v)
      ( is-segal-A x y a f v)
```

Finally, we see that contravariant hom families in a Segal type are
contravariant.

```rzk title="RS17, Proposition 8.13(<-), dual"
#def is-segal-representable-is-contravariant
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a : A)
  : is-contravariant A (\ x → hom A x a)
  :=
    \ x y f v →
      is-segal-representable-dhom-to-contractible A is-segal-A a x y f v
```

The proof of the claimed converse result given in the original source is
circular - using Proposition 5.10, which holds only for Segal types - so instead
we argue as follows:

```rzk title="RS17, Proposition 8.13(→), dual"
#def representable-is-contravariant-is-segal
  ( A : U)
  ( representable-family-is-contravariant : (a : A) →
    is-contravariant A (\ x → hom A x a))
  : is-segal A
  :=
    \ x y z f g →
      is-contr-base-is-contr-Σ
      ( Σ (h : hom A x z) , hom2 A x y z f g h)
      ( \ hk → Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) (first hk))
      ( \ hk → (first hk , \ (t , s) → first hk t))
      ( is-contr-is-equiv-to-contr
        ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
          Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) (first hk))
        ( dhom-to-representable A z x y f g)
        ( inv-equiv
          ( dhom-to-representable A z x y f g)
          ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
            Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) (first hk))
          ( equiv-comp
            ( dhom-to-representable A z x y f g)
            ( Σ (h : hom A x z) ,
              ( product
                ( hom2 A x y z f g h)
                ( Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) h)))
            ( Σ (hk : Σ (h : hom A x z) , hom2 A x y z f g h) ,
              Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) (first hk))
            ( representable-dhom-to-hom2-dist A z x y f g)
            ( associative-Σ
              ( hom A x z)
              ( \ h → hom2 A x y z f g h)
              ( \ h _ → Σ (u : hom A x z) , hom2 A x z z u (id-hom A z) h))))
              ( representable-family-is-contravariant z x y f g))
```

## Contravariant lifts, transport, and uniqueness

In a contravariant family C over a base type A, a term v : C y may be
transported along an arrow f : hom A x y to give a term in C x.

```rzk title="RS17, contravariant transport from beginning of Section 8.2"
#def contravariant-transport
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( v : C y)
   : C x
   := first
        ( contraction-center (dhom-to A x y f C v) (is-contravariant-C x y f v))
```

```rzk title="RS17, contravariant lift from beginning of Section 8.2"
#def contravariant-lift
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( v : C y)
  : ( dhom A x y f C (contravariant-transport A x y f C is-contravariant-C v) v)
  :=
    second
      ( contraction-center (dhom-to A x y f C v) (is-contravariant-C x y f v))

#def contravariant-uniqueness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( v : C y)
  ( lift : dhom-to A x y f C v)
  : ( contravariant-transport A x y f C is-contravariant-C v) = (first lift)
  :=
    first-path-Σ
    ( C x)
    ( \ u → dhom A x y f C u v)
    ( contraction-center
      ( dhom-to A x y f C v)
      ( is-contravariant-C x y f v))
    ( lift)
    ( contracting-htpy (dhom-to A x y f C v) (is-contravariant-C x y f v) lift)
```

## Contravariant functoriality

The contravariant transport operation defines a comtravariantly functorial
action of arrows in the base on terms in the fibers. In particular, there is an
identity transport law.

```rzk title="RS17, Proposition 8.16, Part 2, dual, Contravariant families preserve identities"
#def id-arr-contravariant-transport
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( u : C x)
  : ( contravariant-transport A x x (id-hom A x) C is-contravariant-C u) = u
  :=
    contravariant-uniqueness A x x (id-hom A x) C is-contravariant-C u
      ( u , id-dhom A x C u)
```

## Contravariant natural transformations

A fiberwise map between contrvariant families is automatically "natural"
commuting with the contravariant lifts.

```rzk title="RS17, Proposition 8.17, dual, Contravariant naturality"
#def contravariant-fiberwise-transformation-application
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C D : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( ϕ : (z : A) → C z → D z)
  ( v : C y)
  : dhom-to A x y f D (ϕ y v)
  :=
    ( ϕ x (contravariant-transport A x y f C is-contravariant-C v) ,
      \ t → ϕ (f t) (contravariant-lift A x y f C is-contravariant-C v t))

#def naturality-contravariant-fiberwise-transformation
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( C D : A → U)
  ( is-contravariant-C : is-contravariant A C)
  ( is-contravariant-D : is-contravariant A D)
  ( ϕ : (z : A) → C z → D z)
  ( v : C y)
  : ( contravariant-transport A x y f D is-contravariant-D (ϕ y v)) =
    ( ϕ x (contravariant-transport A x y f C is-contravariant-C v))
  :=
    contravariant-uniqueness A x y f D is-contravariant-D (ϕ y v)
    ( contravariant-fiberwise-transformation-application
      A x y f C D is-contravariant-C ϕ v)
```
