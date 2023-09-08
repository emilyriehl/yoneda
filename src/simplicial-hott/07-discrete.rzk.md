# Discrete types

These formalisations correspond to Section 7 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/1-paths.md` - We require basic path algebra.
- `hott/4-equivalences.md` - We require the notion of equivalence between types.
- `3-simplicial-type-theory.md` — We rely on definitions of simplicies and their
  subshapes.
- `4-extension-types.md` — We use extension extensionality.
- `5-segal-types.md` - We use the notion of hom types.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## The definition

Discrete types are types in which the hom-types are canonically equivalent to
identity types.

```rzk title="RS17, Definition 7.1"
#def arr-eq
  (A : U)
  (x y : A)
  (p : x = y)
  : hom A x y
  := ind-path (A) (x) (\ y' → \ p' → hom A x y') ((id-hom A x)) (y) (p)

#def is-discrete
  (A : U)
  : U
  := (x : A) → (y : A) → is-equiv (x =_{A} y) (hom A x y) (arr-eq A x y)
```

## Families of discrete types

By function extensionality, the dependent function type associated to a family
of discrete types is discrete.

```rzk
#def equiv-discrete-family uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  ( f g : (x : X) → A x)
  : Equiv (f = g) (hom ((x : X) → A x) f g)
  :=
    equiv-triple-comp
      ( f = g)
      ( (x : X) → f x = g x)
      ( (x : X) → hom (A x) (f x) (g x))
      ( hom ((x : X) → A x) f g)
      ( equiv-FunExt funext X A f g)
      ( equiv-function-equiv-fibered funext X
        ( \ x → (f x = g x)) (\ x → hom (A x) (f x) (g x))
        ( \ x → (arr-eq (A x) (f x) (g x) , (is-discrete-A x (f x) (g x)))))
      ( flip-ext-fun-inv
        ( 2)
        ( Δ¹)
        ( ∂Δ¹)
        ( X)
        ( \ t x → A x)
        ( \ t x → recOR (t ≡ 0₂ ↦ f x , t ≡ 1₂ ↦ g x)))

#def equiv-discrete-family-map uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  ( f g : (x : X) → A x)
  ( h : f = g)
  : ( arr-eq ((x : X) → A x) f g h) =
    ( first (equiv-discrete-family X A is-discrete-A f g)) h
  :=
    ind-path
      ( (x : X) → A x)
      ( f)
      ( \ g' h' →
        arr-eq ((x : X) → A x) f g' h' =
        (first (equiv-discrete-family X A is-discrete-A f g')) h')
      ( refl)
      ( g)
      ( h)
```

```rzk title="RS17, Proposition 7.2"
#def is-discrete-dependent-function-discrete-family uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  : is-discrete ((x : X) → A x)
  :=
    \ f g →
    is-equiv-homotopy
      ( f = g)
      ( hom ((x : X) → A x) f g)
      ( arr-eq ((x : X) → A x) f g)
      ( first (equiv-discrete-family X A is-discrete-A f g))
      ( equiv-discrete-family-map X A is-discrete-A f g)
      ( second (equiv-discrete-family X A is-discrete-A f g))
```

By extension extensionality, an extension type into a family of discrete types
is discrete. Sinced fibered-Eq-extension-Equiv considers total extension types
only, extending from BOT, that's all we prove here for now.

```rzk
#def Eq-discrete-extension uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  ( f g : (t : ψ) → A t)
  : Equiv (f = g) (hom ((t : ψ) → A t) f g)
  :=
    equiv-triple-comp
      ( f = g)
      ( (t : ψ) → f t = g t)
      ( (t : ψ) → hom (A t) (f t) (g t))
      ( hom ((t : ψ) → A t) f g)
      ( equiv-ExtExt extext I ψ (\ _ → BOT) A (\ _ → recBOT) f g)
      ( equiv-extension-equiv-fibered
        ( extext)
        ( I)
        ( ψ)
        ( \ t → f t = g t)
        ( \ t → hom (A t) (f t) (g t))
        ( \ t → (arr-eq (A t) (f t) (g t) , (is-discrete-A t (f t) (g t)))))
      ( fubini
        ( I)
        ( 2)
        ( ψ)
        ( \ t → BOT)
        ( Δ¹)
        ( ∂Δ¹)
        ( \ t s → A t)
        ( \ (t , s) → recOR (s ≡ 0₂ ↦ f t , s ≡ 1₂ ↦ g t)))

#def Eq-discrete-extension-map uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  ( f g : (t : ψ) → A t)
  ( h : f = g)
  : arr-eq ((t : ψ) → A t) f g h =
    ( first (Eq-discrete-extension I ψ A is-discrete-A f g)) h
  :=
    ind-path
      ( (t : ψ) → A t)
      ( f)
      ( \ g' h' →
        ( arr-eq ((t : ψ) → A t) f g' h') =
        ( first (Eq-discrete-extension I ψ A is-discrete-A f g') h'))
      ( refl)
      ( g)
      ( h)
```

```rzk title="RS17, Proposition 7.2, for extension types"
#def is-discrete-extension-family uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  : is-discrete ((t : ψ) → A t)
  :=
    \ f g →
    is-equiv-homotopy
      ( f = g)
      ( hom ((t : ψ) → A t) f g)
      ( arr-eq ((t : ψ) → A t) f g)
      ( first (Eq-discrete-extension I ψ A is-discrete-A f g))
      ( Eq-discrete-extension-map I ψ A is-discrete-A f g)
      ( second (Eq-discrete-extension I ψ A is-discrete-A f g))
```

For instance, the arrow type of a discrete type is discrete.

```rzk
#def is-discrete-arr-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  : is-discrete (arr A)
  := is-discrete-extension-family 2 Δ¹ (\ _ → A) (\ _ → is-discrete-A)
```

## Discrete types are Segal types

Discrete types are automatically Segal types.

```rzk
#section discrete-arr-equivalences

#variable A : U
#variable is-discrete-A : is-discrete A
#variables x y z w : A
#variable f : hom A x y
#variable g : hom A z w

#def is-equiv-arr-eq-discrete uses (extext x y z w)
  : is-equiv (f =_{Δ¹ → A} g) (hom (arr A) f g) (arr-eq (arr A) f g)
  := (is-discrete-arr-is-discrete A is-discrete-A) f g

#def equiv-arr-eq-discrete uses (extext x y z w)
  : Equiv (f =_{Δ¹ → A} g) (hom (arr A) f g)
  := (arr-eq (arr A) f g ,
          (is-discrete-arr-is-discrete A is-discrete-A) f g)

#def equiv-square-hom-arr
  : Equiv
      ( hom (arr A) f g)
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( ((t , s) : Δ¹×Δ¹) → A
                [ t ≡ 0₂ ∧ Δ¹ s ↦ f s ,
                  t ≡ 1₂ ∧ Δ¹ s ↦ g s ,
                  Δ¹ t ∧ s ≡ 0₂ ↦ h t ,
                  Δ¹ t ∧ s ≡ 1₂ ↦ k t])))
  :=
    ( \ α →
      ( ( \ t → α t 0₂) ,
        ( ( \ t → α t 1₂) , (\ (t , s) → α t s))) ,
      ( ( ( \ σ → \ t → \ s → (second (second σ)) (t , s)) ,
          ( \ α → refl)) ,
        ( ( \ σ → \ t → \ s → (second (second σ)) (t , s)) ,
          ( \ σ → refl))))
```

The equivalence underlying `#!rzk equiv-arr-Σ-hom`:

```rzk
#def fibered-arr-free-arr
  : (arr A) → (Σ (u : A) , (Σ (v : A) , hom A u v))
  := \ k → (k 0₂ , (k 1₂ , k))

#def is-equiv-fibered-arr-free-arr
  : is-equiv (arr A) (Σ (u : A) , (Σ (v : A) , hom A u v)) (fibered-arr-free-arr)
  := is-equiv-arr-Σ-hom A

#def is-equiv-ap-fibered-arr-free-arr uses (w x y z)
  : is-equiv
      ( f =_{Δ¹ → A} g)
      ( fibered-arr-free-arr f = fibered-arr-free-arr g)
      ( ap
        ( arr A)
        ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
        ( f)
        ( g)
        ( fibered-arr-free-arr))
  :=
    is-emb-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
      ( fibered-arr-free-arr)
      ( is-equiv-fibered-arr-free-arr)
      ( f)
      ( g)

#def id-Eq-equiv-arr-Σ-hom uses (w x y z)
  : Equiv (f =_{Δ¹ → A} g) (fibered-arr-free-arr f = fibered-arr-free-arr g)
  :=
    equiv-ap-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
      ( fibered-arr-free-arr)
      ( is-equiv-fibered-arr-free-arr)
      ( f)
      ( g)

#def equiv-sigma-over-product-arr-eq
  : Equiv
      ( fibered-arr-free-arr f = fibered-arr-free-arr g)
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
  := equiv-Eq-Σ-over-product
      ( A) (A)
      ( hom A)
      ( fibered-arr-free-arr f)
      ( fibered-arr-free-arr g)

#def equiv-square-sigma-over-product uses (extext is-discrete-A)
  : Equiv
    ( Σ ( p : x = z) ,
        ( Σ (q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ((t , s) : Δ¹×Δ¹) → A
              [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ])))
  :=
    equiv-left-cancel
      ( f =_{Δ¹ → A} g)
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( ((t , s) : Δ¹×Δ¹) → A
                [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ])))
      ( equiv-comp
        ( f =_{Δ¹ → A} g)
        ( fibered-arr-free-arr f = fibered-arr-free-arr g)
        ( Σ ( p : x = z) ,
            ( Σ ( q : y = w) ,
                ( product-transport A A (hom A) x z y w p q f = g)))
        id-Eq-equiv-arr-Σ-hom
        equiv-sigma-over-product-arr-eq)
      ( equiv-comp
        ( f =_{Δ¹ → A} g)
        ( hom (arr A) f g)
        ( Σ ( h : hom A x z) ,
            ( Σ ( k : hom A y w) ,
                ( ((t , s) : Δ¹×Δ¹) → A
                  [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                    (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                    (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                    (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ])))
        ( equiv-arr-eq-discrete)
        ( equiv-square-hom-arr))
```

We close the section so we can use path induction.

```rzk
#end discrete-arr-equivalences
```

```rzk
#def fibered-map-square-sigma-over-product
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) →
    ( product-transport A A (hom A) x z y w p q f = g) →
    ( ((t , s) : Δ¹×Δ¹) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ (arr-eq A x z p) t ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ (arr-eq A y w q) t ])
  :=
    ind-path
      ( A)
      ( x)
      ( \ z' p' →
        ( g : hom A z' w) →
        ( product-transport A A (hom A) x z' y w p' q f = g) →
        ( ((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ (arr-eq A x z' p') t ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ (arr-eq A y w q) t ]))
      ( ind-path
        ( A)
        ( y)
        ( \ w' q' →
          ( g : hom A x w') →
          ( product-transport A A (hom A) x x y w' refl q' f = g) →
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ (arr-eq A y w' q') t ]))
        ( ind-path
            ( hom A x y)
            ( f)
            ( \ g' τ' →
              ( ((t , s) : Δ¹×Δ¹) → A
                [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g' s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
            ( \ (t , s) → f s))
        ( w)
        ( q))
      ( z)
      ( p)

#def square-sigma-over-product
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( ( p , (q , τ)) :
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g))))
  : Σ ( h : hom A x z) ,
      ( Σ ( k : hom A y w) ,
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ]))
  :=
    ( arr-eq A x z p ,
      ( arr-eq A y w q ,
        fibered-map-square-sigma-over-product
          ( A) (is-discrete-A)
          ( x) (y) (z) (w)
          ( f)
          ( p)
          ( q)
          ( g)
          ( τ)))

#def refl-refl-map-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f g : hom A x y)
  ( τ : product-transport A A (hom A) x x y y refl refl f = g)
  : ( first
      ( equiv-square-sigma-over-product A is-discrete-A x y x y f g)
      (refl , (refl , τ))) =
    ( square-sigma-over-product
      ( A) (is-discrete-A)
      ( x) (y) (x) (y)
      ( f) (g)
      ( refl , (refl , τ)))
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' τ' →
        ( first
          ( equiv-square-sigma-over-product A is-discrete-A x y x y f g')
          ( refl , (refl , τ'))) =
        ( square-sigma-over-product
          ( A) (is-discrete-A)
          ( x) (y) (x) (y)
          ( f) (g')
          ( refl , (refl , τ'))))
      ( refl)
      ( g)
      ( τ)

#def map-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) →
    ( τ : product-transport A A (hom A) x z y w p q f = g) →
    ( first
      ( equiv-square-sigma-over-product A is-discrete-A x y z w f g)
      ( p , (q , τ))) =
    ( square-sigma-over-product
        A is-discrete-A x y z w f g (p , (q , τ)))
  :=
    ind-path
      ( A)
      ( y)
      ( \ w' q' →
        ( g : hom A z w') →
        ( τ : product-transport A A (hom A) x z y w' p q' f = g) →
        ( first (equiv-square-sigma-over-product
                  A is-discrete-A x y z w' f g))
          ( p , (q' , τ)) =
        ( square-sigma-over-product A is-discrete-A x y z w' f g)
          ( p , (q' , τ)))
      ( ind-path
        ( A)
        ( x)
        ( \ z' p' →
          ( g : hom A z' y) →
          ( τ :
            product-transport A A (hom A) x z' y y p' refl f = g) →
          ( first
            ( equiv-square-sigma-over-product A is-discrete-A x y z' y f g)
            ( p' , (refl , τ))) =
          ( square-sigma-over-product A is-discrete-A x y z' y f g
            ( p' , (refl , τ))))
        ( refl-refl-map-equiv-square-sigma-over-product
            ( A) (is-discrete-A) (x) (y) (f))
        ( z)
        ( p))
      ( w)
      ( q)

#def is-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  : is-equiv
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ((t , s) : Δ¹×Δ¹) → A
              [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ])))
    ( square-sigma-over-product A is-discrete-A x y z w f g)
  :=
    is-equiv-rev-homotopy
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ((t , s) : Δ¹×Δ¹) → A
              [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t ])))
    ( first
      ( equiv-square-sigma-over-product A is-discrete-A x y z w f g))
    ( square-sigma-over-product A is-discrete-A x y z w f g)
    ( \ (p , (q , τ)) →
      map-equiv-square-sigma-over-product
        A is-discrete-A x y z w f p q g τ)
    ( second
      ( equiv-square-sigma-over-product A is-discrete-A x y z w f g))

#def is-equiv-fibered-map-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( p : x = z)
  ( q : y = w)
  : is-equiv
    ( product-transport A A (hom A) x z y w p q f = g)
    ( ((t , s) : Δ¹×Δ¹) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ (arr-eq A x z p) t ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ (arr-eq A y w q) t ])
    ( fibered-map-square-sigma-over-product A is-discrete-A x y z w f p q g)
  :=
    fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
      ( x = z)
      ( hom A x z)
      ( y = w)
      ( hom A y w)
      ( \ p' q' → (product-transport A A (hom A) x z y w p' q' f) = g)
      ( \ h' k' →
        ( ((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ h' t ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ k' t ]))
      ( arr-eq A x z)
      ( arr-eq A y w)
      ( \ p' q' →
        fibered-map-square-sigma-over-product
          ( A) (is-discrete-A)
          ( x) (y) (z) (w)
          ( f)
          ( p')
          ( q')
          ( g))
      ( is-equiv-square-sigma-over-product A is-discrete-A x y z w f g)
      ( is-discrete-A x z)
      ( is-discrete-A y w)
      ( p)
      ( q)

#def is-equiv-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  : is-equiv
    (f = g)
    ( ((t , s) : Δ¹×Δ¹) → A
      [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ])
    ( fibered-map-square-sigma-over-product
      A is-discrete-A x y x y f refl refl g)
  :=
    is-equiv-fibered-map-square-sigma-over-product
      A is-discrete-A x y x y f g refl refl
```

The previous calculations allow us to establish a family of equivalences:

```rzk
#def is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
    ( Σ (g : hom A x y) , f = g)
    ( Σ (g : hom A x y) ,
        ( ((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
    ( total-map-family-of-maps
      ( hom A x y)
      ( \ g → f = g)
      ( \ g →
        ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ])
      ( fibered-map-square-sigma-over-product
          A is-discrete-A x y x y f refl refl))
  :=
    family-of-equiv-total-equiv
      ( hom A x y)
      ( \ g → f = g)
      ( \ g →
        ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ])
      ( fibered-map-square-sigma-over-product
          A is-discrete-A x y x y f refl refl)
      ( \ g →
        is-equiv-fibered-map-square-sigma-over-product-refl-refl
          ( A) (is-discrete-A)
          ( x) (y)
          ( f) (g))

#def equiv-sum-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : Equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) ,
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
  :=
    ( ( total-map-family-of-maps
        ( hom A x y)
        ( \ g → f = g)
        ( \ g →
          ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ])
        ( fibered-map-square-sigma-over-product
            A is-discrete-A x y x y f refl refl)) ,
    is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl
      A is-discrete-A x y f)
```

Now using the equivalence on total spaces and the contractibility of based path
spaces, we conclude that the codomain extension type is contractible.

```rzk
#def is-contr-horn-refl-refl-extension-type uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr
    ( Σ ( g : hom A x y) ,
        ( ((t , s) : Δ¹×Δ¹) → A
          [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
  := is-contr-is-equiv-from-contr
      ( Σ ( g : hom A x y) , f = g)
      ( Σ ( g : hom A x y) ,
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
      ( equiv-sum-fibered-map-square-sigma-over-product-refl-refl
          A is-discrete-A x y f)
      ( is-contr-based-paths (hom A x y) f)
```

The extension types that appear in the Segal condition are retracts of this type
--- at least when the second arrow in the composable pair is an identity.

```rzk
#def triangle-to-square-section
  (A : U)
  (x y : A)
  (f g : hom A x y)
  (α : hom2 A x y y f (id-hom A y) g)
  : ((t , s) : Δ¹×Δ¹) → A
    [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
      (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
      (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
      (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]
  := \ (t , s) → recOR (t ≤ s ↦ α (s , t) , s ≤ t ↦ g s)

#def sigma-triangle-to-sigma-square-section
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (d , α) : Σ (d : hom A x y) , hom2 A x y y f (id-hom A y) d)
  : Σ ( g : hom A x y) ,
      ( ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ])
  := (d , triangle-to-square-section A x y f d α)

#def sigma-square-to-sigma-triangle-retraction
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (g , σ) :
    Σ (g : hom A x y) ,
      ( ((t , s) : Δ¹×Δ¹) → A
        [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
  : Σ (d : hom A x y) , hom2 A x y y f (id-hom A y) d
  := ((\ t → σ (t , t)) , (\ (t , s) → σ (s , t)))

#def sigma-triangle-to-sigma-square-retract
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : is-retract-of
      ( Σ (d : hom A x y) , hom2 A x y y f (id-hom A y) d)
      ( Σ (g : hom A x y) ,
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
  :=
    ( sigma-triangle-to-sigma-square-section A x y f ,
      ( sigma-square-to-sigma-triangle-retraction A x y f ,
        \ dα → refl ))
```

We can now verify the Segal condition in the case of composable pairs in which
the second arrow is an identity.

```rzk
#def is-contr-hom2-with-id-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr ( Σ (d : hom A x y) , hom2 A x y y f (id-hom A y) d)
  :=
    is-contr-is-retract-of-is-contr
      ( Σ ( d : hom A x y) , (hom2 A x y y f (id-hom A y) d))
      ( Σ ( g : hom A x y) ,
          ( ((t , s) : Δ¹×Δ¹) → A
            [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y ]))
      ( sigma-triangle-to-sigma-square-retract A x y f)
      ( is-contr-horn-refl-refl-extension-type A is-discrete-A x y f)
```

But since `#!rzk A` is discrete, its hom type family is equivalent to its
identity type family, and we can use "path induction" over arrows to reduce the
general case to the one just proven:

```rzk
#def is-contr-hom2-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : is-contr (Σ (h : hom A x z) , hom2 A x y z f g h)
  :=
    ind-based-path
      A
      y
      ( \ w → hom A y w)
      ( \ w → arr-eq A y w)
      ( is-discrete-A y)
      ( \ w d → is-contr ( Σ (h : hom A x w) , hom2 A x y w f d h))
      ( is-contr-hom2-with-id-is-discrete
          A is-discrete-A x y f)
      ( z)
      ( g)
```

Finally, we conclude:

```rzk title="RS17, Proposition 7.3"
#def is-segal-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  : is-segal A
  := is-contr-hom2-is-discrete A is-discrete-A
```
