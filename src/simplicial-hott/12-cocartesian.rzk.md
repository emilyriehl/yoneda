# Cocartesian families

These formalizations capture cocartesian families as treated in BW23.

The goal, for now, is not to give a general structural account as in the paper
but rather to provide the definitions and results that are necessary to prove
the cocartesian Yoneda Lemma.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use the fubini theorem and extension
  extensionality.
- `5-segal-types.md` - We make heavy use of the notion of Segal types
- `10-rezk-types.md`- We use Rezk types.

## (Iso-)Inner families

This is a (tentative and redundant) definition of (iso-)inner families. In the
future, hopefully, these can be replaced by instances of orthogonal and LARI
families.

```rzk
#def is-inner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-segal B) (is-segal (Σ (b : B) , P b)))
    ( (b : B) → (is-segal (P b)))

#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-rezk B) (is-rezk (Σ (b : B) , P b)))
    ( (b : B) → (is-rezk (P b)))
```

## Dependent composition

In an inner family, we can dependently compose arrows. To make this precise,
some coherence seems to be needed going through the axiom of choice for extension types.

```rzk
#def axiom-choice-dhom
  ( B : U)
  ( a b : B)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  : Equiv
    ( hom (total-type B P) (a, x) (b, y))
    ( Σ ( u' : hom B a b) ,
        ( dhom B a b u' P x y)
    )
  :=
  ( axiom-choice 
    2 
    Δ¹
    ∂Δ¹
    ( \ t → B)
    ( \ t → \ c → (P c)) 
    ( \ t → recOR(t ≡ 0₂ ↦ a , t ≡ 1₂ ↦ b))
    ( \ t → recOR(t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y))
  )

#def inv-axiom-choice-dhom
  ( B : U)
  ( a b : B)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  : Equiv
    ( Σ ( u' : hom B a b) ,
        ( dhom B a b u' P x y)
    )
    ( hom (total-type B P) (a, x) (b, y))
  :=
    ( inv-equiv
      ( hom (total-type B P) (a, x) (b, y))
      ( Σ ( u' : hom B a b) ,
          ( dhom B a b u' P x y)
      )
      ( axiom-choice-dhom B a b P x y)
    )

#def axiom-choice-hom2
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( w : hom B a c)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  ( h : dhom B a c w P x z)
  : Equiv
    ( hom2 (total-type B P) (a, x) (b, y) (c, z) (\t -> (u t, f t)) (\t -> (v t, g t)) (\t -> (w t, h t)))
    ( Σ (α : hom2 B a b c u v w ) ,
        (dhom2 B a b c u v w α P x y z f g h)
    )
  :=
  ( axiom-choice 
    (2 × 2) 
    Δ²
    ∂Δ²
    ( \ (t, s) → B)
    ( \ (t, s) → \ k → (P k)) 
    ( \ (t, s) → recOR(s ≡ 0₂ ↦ u t, t ≡ 1₂ ↦ v s, s ≡ t ↦ w s))
    ( \ (t, s) → recOR(s ≡ 0₂ ↦ f t, t ≡ 1₂ ↦ g s, s ≡ t ↦ h s))
  )

#def dep-comp-is-inner-sigma
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : ( Σ ( w : hom B a c) , (dhom B a c w P x z) )
  :=
        (
        (first (axiom-choice-dhom B a c P x z))
        
        (comp-is-segal (total-type B P) (second (first is-inner-family-P))
        (a, x) (b, y) (c, z)
        ( (\t → (u t, f t)))
        ( (\t → (v t, g t)))
        )
        )

#def proj1-dep-comp-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom B a c
  := ( first (dep-comp-is-inner-sigma B a b c u v P is-inner-family-P x y z f g))

#def proj1-dep-comp-is-inner-alt
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : (hom B a c)
  := (first
      ( (first (axiom-choice-dhom B a c P x z))
        (comp-is-segal (total-type B P) is-segal-total-P
        (a, x) (b, y) (c, z)
        (\t → (u t, f t))
        (\t → (v t, g t))
        )
      )
  )


#def proj
  ( B : U)
  ( a b : B)
  ( u : hom B a b)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  ( f : dhom B a b u P x y)
  : (hom B a b)
  := (first
      ( (first (axiom-choice-dhom B a b P x y))
        ((\t → (u t, f t)))
      )
  )

#def proj-path
  ( B : U)
  ( a b : B)
  ( u : hom B a b)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  ( f : dhom B a b u P x y)
  : u = (proj B a b u P x y f)
  := refl

#def comp-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom (total-type B P) (a, x) (c, z)
  :=  (
    (first (inv-axiom-choice-dhom B a c P x z))
    (
     (first (axiom-choice-dhom B a c P x z))
      ( comp-is-segal (total-type B P) is-segal-total-P (a, x) (b, y) (c, z) 
     ((first (inv-axiom-choice-dhom B a b P x y))((\t -> u t, \t -> f t))) 
     ((first (inv-axiom-choice-dhom B b c P y z))((\t -> v t, \t -> g t)))
    )
    )
  )

#def comp2-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom2 (total-type B P) (a, x) (b, y) (c, z)
    ((first (inv-axiom-choice-dhom B a b P x y))((\t -> u t, \t -> f t))) 
    ((first (inv-axiom-choice-dhom B b c P y z))((\t -> v t, \t -> g t)))
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  := (witness-comp-is-segal (total-type B P) is-segal-total-P  (a, x) (b, y) (c, z)
    ((first (inv-axiom-choice-dhom B a b P x y))((\t -> u t, \t -> f t))) 
    ((first (inv-axiom-choice-dhom B b c P y z))((\t -> v t, \t -> g t)))
   )

#def proj2-comp-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : dhom B a c (first ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
  P x z
  := 
  (second ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  )
  )

#def hom2-base-hom2-total-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom2 B a b c u v
  (
  (first ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  )
  )
  )
  :=
    (ap-hom2
    (total-type B P)
    B
    (proj-base B P)
    (a, x) (b, y) (c, z)
    ((first (inv-axiom-choice-dhom B a b P x y))((\t -> u t, \t -> f t))) 
    ((first (inv-axiom-choice-dhom B b c P y z))((\t -> v t, \t -> g t)))
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    (comp2-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    )

#def coherence-comp-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : (comp-is-segal B is-segal-B a b c u v)
    = (first ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  )
  )
  := 
    (uniqueness-comp-is-segal B is-segal-B a b c u v
     (first ((first (axiom-choice-dhom B a c P x z) )
      (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
      )
    )
    (hom2-base-hom2-total-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    )

#def dep-comp-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  (is-segal-B : is-segal B)
  (is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : dhom B a c (comp-is-segal B is-segal-B a b c u v) P x z 
  := 
  (transport
  
    (hom B a c)

    (\w -> dhom B a c w P x z)

    (first ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))

    (comp-is-segal B is-segal-B a b c u v)

    (rev (hom B a c)
       (comp-is-segal B is-segal-B a b c u v)
       (first ((first (axiom-choice-dhom B a c P x z) )
    (comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
     (coherence-comp-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    )
  
    (proj2-comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P
     x y z f g)

  )

```
      


## Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    (b'' : B) → (v : hom B b' b'') → (w : hom B b b'') →
      (sigma : hom2 B b b' b'' u v w) → (e'' : P b'') →
      (h : dhom B b b'' w P e e'') →
      is-contr
        ( Σ ( g : dhom B b' b'' v P e' e'') ,
          ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

```rzk
#def cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  : U
  := Σ (f : dhom B b b' u P e e'), (is-cocartesian-arrow B b b' u P e e' f)
```

## Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ (e' : P b') ,
      Σ (f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

## Cocartesian family

A family over cocartesian if it is isoinner and any arrow in
the has a cocartesian lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → ( b' : B) → ( u : hom B b b') →
      ( e : P b) → ( Σ (e' : P b'),
        ( Σ (f : dhom B b b' u P e e'), is-cocartesian-arrow B b b' u P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-cocartesian-lifts B P)
```
