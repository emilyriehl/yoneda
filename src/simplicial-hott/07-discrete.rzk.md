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

## The definition

Discrete types are types in which the hom-types are canonically equivalent to
identity types.

```rzk title="RS17, Definition 7.1"
#def arr-eq
  (A : U)             -- A type.
  (x y : A)           -- Two points of type A.
  (p : x = y)         -- A path p from x to y in A.
  : hom A x y         -- An arrow p from x to y in A.
  := idJ (A , x , \ y' -> \ p' -> hom A x y' , (id-arr A x) , y , p)

#def is-discrete
  (A : U)             -- A type.
  : U
  := (x : A) -> (y : A) -> is-equiv (x =_{A} y) (hom A x y) (arr-eq A x y)
```

## Families of discrete types

By function extensionality, the dependent function type associated to a family
of discrete types is discrete.

```rzk
#def equiv-discrete-family
  ( funext : FunExt)
  ( X : U)
  ( A : X -> U)
  ( Aisdiscrete : (x : X) -> is-discrete (A x))
  ( f g : (x : X) -> A x)
  : Equiv (f = g) (hom ((x : X) -> A x) f g)
  :=
    triple-comp-equiv
      ( f = g)
      ( (x : X) -> f x = g x)
      ( (x : X) -> hom (A x) (f x) (g x))
      ( hom ((x : X) -> A x) f g)
      ( FunExt-equiv funext X A f g)
      ( function-equiv-fibered-equiv funext X
        ( \ x -> (f x = g x)) (\ x -> hom (A x) (f x) (g x))
        ( \ x -> (arr-eq (A x) (f x) (g x) , (Aisdiscrete x (f x) (g x)))))
      ( flip-ext-fun-inv
        ( 2)
        ( Δ¹)
        ( ∂Δ¹)
        ( X)
        ( \ t x -> A x)
        ( \ t x -> recOR (t === 0_2 |-> f x , t === 1_2 |-> g x)))

#def equiv-discrete-family-map
  ( funext : FunExt)
  ( X : U)
  ( A : X -> U)
  ( Aisdiscrete : (x : X) -> is-discrete (A x))
  ( f g : (x : X) -> A x)
  ( h : f = g)
  : ( arr-eq ((x : X) -> A x) f g h) =
    ( first (equiv-discrete-family funext X A Aisdiscrete f g)) h
  :=
    idJ
    ( ( (x : X) -> A x) ,
      ( f) ,
      ( \ g' h' ->
        arr-eq ((x : X) -> A x) f g' h' =
        (first (equiv-discrete-family funext X A Aisdiscrete f g')) h') ,
      ( refl) ,
      ( g) ,
      ( h))
```

```rzk title="RS17, Proposition 7.2"
#def is-discrete-dependent-function-discrete-family
  ( funext : FunExt)
  ( X : U)
  ( A : X -> U)
  ( Aisdiscrete : (x : X) -> is-discrete (A x))
  : is-discrete ((x : X) -> A x)
  :=
    \ f g ->
    is-equiv-homotopic-is-equiv
      ( f = g)
      ( hom ((x : X) -> A x) f g)
      ( arr-eq ((x : X) -> A x) f g)
      ( first (equiv-discrete-family funext X A Aisdiscrete f g))
      ( equiv-discrete-family-map funext X A Aisdiscrete f g)
      ( second (equiv-discrete-family funext X A Aisdiscrete f g))
```

By extension extensionality, an extension type into a family of discrete types
is discrete. Sinced fibered-Eq-extension-Equiv considers total extension types
only, extending from BOT, that's all we prove here for now.

```rzk
#def Eq-discrete-extension
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( A : ψ -> U)
  ( Aisdiscrete : (t : ψ) -> is-discrete (A t))
  ( f g : (t : ψ) -> A t)
  : Equiv (f = g) (hom ((t : ψ) -> A t) f g)
  :=
    triple-comp-equiv
      ( f = g)
      ( (t : ψ) -> f t = g t)
      ( (t : ψ) -> hom (A t) (f t) (g t))
      ( hom ((t : ψ) -> A t) f g)
      ( ExtExtEquiv extext I ψ (\ t -> BOT) A (\ u -> recBOT) f g)
      ( fibered-Eq-extension-Equiv
        ( extext)
        ( I)
        ( ψ)
        ( \ t -> f t = g t)
        ( \ t -> hom (A t) (f t) (g t))
        ( \ t -> (arr-eq (A t) (f t) (g t) , (Aisdiscrete t (f t) (g t)))))
      ( fubini
        ( I)
        ( 2)
        ( ψ)
        ( \ t -> BOT)
        ( Δ¹)
        ( ∂Δ¹)
        ( \ t s -> A t)
        ( \ (t , s) -> recOR (s === 0_2 |-> f t , s === 1_2 |-> g t)))

#def Eq-discrete-extension-map
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : (t : I) -> TOPE)
  ( A : ψ -> U)
  ( Aisdiscrete : (t : ψ) -> is-discrete (A t))
  ( f g : (t : ψ) -> A t)
  ( h : f = g)
  : arr-eq ((t : ψ) -> A t) f g h =
    ( first (Eq-discrete-extension extext I ψ A Aisdiscrete f g)) h
  :=
    idJ
    ( ( (t : ψ) -> A t) ,
      ( f) ,
      ( \ g' h' ->
        ( arr-eq ((t : ψ) -> A t) f g' h') =
        ( first (Eq-discrete-extension extext I ψ A Aisdiscrete f g') h')) ,
      ( refl) ,
      ( g) ,
      ( h))
```

```rzk title="RS17, Proposition 7.2, for extension types"
#def is-discrete-extension-family
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : (t : I) -> TOPE)
  ( A : ψ -> U)
  ( Aisdiscrete : (t : ψ) -> is-discrete (A t))
  : is-discrete ((t : ψ) -> A t)
  :=
    \ f g ->
    is-equiv-homotopic-is-equiv
      ( f = g)
      ( hom ((t : ψ) -> A t) f g)
      ( arr-eq ((t : ψ) -> A t) f g)
      ( first (Eq-discrete-extension extext I ψ A Aisdiscrete f g))
      ( Eq-discrete-extension-map extext I ψ A Aisdiscrete f g)
      ( second (Eq-discrete-extension extext I ψ A Aisdiscrete f g))
```

For instance, the arrow type of a discrete type is discrete.

```rzk
#def is-discrete-arr-is-discrete
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  : is-discrete (arr A)
  := is-discrete-extension-family extext 2 Δ¹ (\ t -> A) (\ t -> Aisdiscrete)
```

## Discrete types are Segal types

Discrete types are automatically Segal types.

```rzk
#section discrete-arr-equivalences

#variable extext : ExtExt
#variable A : U
#variable Aisdiscrete : is-discrete A
#variables x y z w : A
#variable f : hom A x y
#variable g : hom A z w

#def is-equiv-arr-eq-discrete uses (x y z w)
  : is-equiv (f =_{Δ¹ -> A} g) (hom (arr A) f g) (arr-eq (arr A) f g)
  := (is-discrete-arr-is-discrete extext A Aisdiscrete) f g

#def equiv-arr-eq-discrete uses (x y z w)
  : Equiv (f =_{Δ¹ -> A} g) (hom (arr A) f g)
  := (arr-eq (arr A) f g ,
          (is-discrete-arr-is-discrete extext A Aisdiscrete) f g)

#def equiv-square-hom-arr
  : Equiv
      ( hom (arr A) f g)
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( { ((t , s) : 2 * 2) | Δ¹×Δ¹ (t, s) } -> A
                [ t === 0_2 /\ Δ¹ s |-> f s ,
                  t === 1_2 /\ Δ¹ s |-> g s ,
                  Δ¹ t /\ s === 0_2 |-> h t ,
                  Δ¹ t /\ s === 1_2 |-> k t])))
  :=
    ( \ α ->
      ( ( \ t -> α t 0_2) ,
        ( ( \ t -> α t 1_2) , (\ (t , s) -> α t s))) ,
      ( ( ( \ σ -> \ t -> \ s -> (second (second σ)) (t , s)) ,
          ( \ α -> refl)) ,
        ( ( \ σ -> \ t -> \ s -> (second (second σ)) (t , s)) ,
          ( \ σ -> refl))))

-- The equivalence underlying Eq-arr.
#def fibered-arr-free-arr
  : (arr A) -> (Σ (u : A) , (Σ (v : A) , hom A u v))
  := \ k -> (k 0_2 , (k 1_2 , k))

#def id-equiv-Eq-arr uses (w x y z)
  : is-equiv
      ( f =_{Δ¹ -> A} g)
      ( fibered-arr-free-arr f = fibered-arr-free-arr g)
      ( ap
        ( arr A)
        ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
        ( f)
        ( g)
        ( fibered-arr-free-arr))
  :=
    is-equiv-ap-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
      fibered-arr-free-arr
      ( second (Eq-arr A))
      ( f)
      ( g)

#def id-Eq-Eq-arr uses (w x y z)
  : Equiv (f =_{Δ¹ -> A} g) (fibered-arr-free-arr f = fibered-arr-free-arr g)
  :=
    Eq-ap-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v))) (fibered-arr-free-arr)
      ( second (Eq-arr A))
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

#def equiv-square-sigma-over-product uses (extext Aisdiscrete)
  : Equiv
      ( Σ ( p : x = z) ,
          ( Σ (q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
                [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                  ((t === 1_2) /\ Δ¹ s) |-> g s ,
                  (Δ¹ t /\ (s === 0_2)) |-> h t ,
                  (Δ¹ t /\ (s === 1_2)) |-> k t ])))
  :=
    left-cancel-equiv
      ( f =_{Δ¹ -> A} g)
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
                [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                  ((t === 1_2) /\ Δ¹ s) |-> g s ,
                  (Δ¹ t /\ (s === 0_2)) |-> h t ,
                  (Δ¹ t /\ (s === 1_2)) |-> k t ])))
      ( comp-equiv
        ( f =_{Δ¹ -> A} g)
        ( fibered-arr-free-arr f = fibered-arr-free-arr g)
        ( Σ ( p : x = z) ,
            ( Σ ( q : y = w) ,
                ( product-transport A A (hom A) x z y w p q f = g)))
        id-Eq-Eq-arr
        equiv-sigma-over-product-arr-eq)
      ( comp-equiv
        ( f =_{Δ¹ -> A} g)
        ( hom (arr A) f g)
        ( Σ ( h : hom A x z) ,
            ( Σ ( k : hom A y w) ,
                ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
                  [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                    ((t === 1_2) /\ Δ¹ s) |-> g s ,
                    (Δ¹ t /\ (s === 0_2)) |-> h t ,
                    (Δ¹ t /\ (s === 1_2)) |-> k t ])))
        ( equiv-arr-eq-discrete)
        ( equiv-square-hom-arr))

#end discrete-arr-equivalences

-- closing the section so I can use path induction
#def fibered-map-square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) ->
    ( product-transport A A (hom A) x z y w p q f = g) ->
    ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
      [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
        ((t === 1_2) /\ Δ¹ s) |-> g s ,
        (Δ¹ t /\ (s === 0_2)) |-> (arr-eq A x z p) t ,
        (Δ¹ t /\ (s === 1_2)) |-> (arr-eq A y w q) t ])
  :=
    idJ
    ( ( A) ,
      ( x) ,
      ( \ z' p' ->
        ( g : hom A z' w) ->
        ( product-transport A A (hom A) x z' y w p' q f = g) ->
        ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
          [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
            ((t === 1_2) /\ Δ¹ s) |-> g s ,
            (Δ¹ t /\ (s === 0_2)) |-> (arr-eq A x z' p') t ,
            (Δ¹ t /\ (s === 1_2)) |-> (arr-eq A y w q) t ])) ,
      ( idJ
        ( ( A) ,
          ( y) ,
          ( \ w' q' ->
            ( g : hom A x w') ->
            ( product-transport A A (hom A) x x y w' refl q' f = g) ->
            ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
              [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                ((t === 1_2) /\ Δ¹ s) |-> g s ,
                (Δ¹ t /\ (s === 0_2)) |-> x ,
                (Δ¹ t /\ (s === 1_2)) |-> (arr-eq A y w' q') t ])) ,
          ( \ g τ ->
            idJ
            ( ( hom A x y) ,
              ( f) ,
              ( \ g' τ' ->
                ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
                  [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                    ((t === 1_2) /\ Δ¹ s) |-> g' s ,
                    (Δ¹ t /\ (s === 0_2)) |-> x ,
                    (Δ¹ t /\ (s === 1_2)) |-> y ])),
              ( \ (t , s) -> f s) ,
              ( g) ,
              ( τ))),
          ( w) ,
          ( q))) ,
      ( z) ,
      ( p))

#def square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( ( p , (q , τ)) :
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g))))
  : Σ ( h : hom A x z) ,
      ( Σ ( k : hom A y w) ,
          ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> h t ,
              (Δ¹ t /\ (s === 1_2)) |-> k t ]))
  :=
    ( arr-eq A x z p ,
      ( arr-eq A y w q ,
        fibered-map-square-sigma-over-product
          ( extext)
          ( A) (Aisdiscrete)
          ( x) (y) (z) (w)
          ( f)
          ( p)
          ( q)
          ( g)
          ( τ)))

#def refl-refl-map-equiv-square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f g : hom A x y)
  ( τ : product-transport A A (hom A) x x y y refl refl f = g)
  : ( first
      ( equiv-square-sigma-over-product extext A Aisdiscrete x y x y f g)
      (refl , (refl , τ))) =
    ( square-sigma-over-product
      ( extext)
      ( A) (Aisdiscrete)
      ( x) (y) (x) (y)
      ( f) (g)
      ( refl , (refl , τ)))
  :=
    idJ
    ( ( hom A x y) ,
      ( f) ,
      ( \ g' τ' ->
        ( first
          ( equiv-square-sigma-over-product extext A Aisdiscrete x y x y f g')
          ( refl , (refl , τ'))) =
        ( square-sigma-over-product
          ( extext)
          ( A) (Aisdiscrete)
          ( x) (y) (x) (y)
          ( f) (g')
          ( refl , (refl , τ')))) ,
      ( refl) ,
      ( g) ,
      ( τ))

#def map-equiv-square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) ->
    ( τ : product-transport A A (hom A) x z y w p q f = g) ->
    ( first
      ( equiv-square-sigma-over-product extext A Aisdiscrete x y z w f g)
      ( p , (q , τ))) =
    ( square-sigma-over-product extext A Aisdiscrete x y z w f g (p , (q , τ)))
  :=
    idJ
    ( A ,
      y ,
      \ w' q' ->
        (g : hom A z w') ->
        (τ : product-transport A A (hom A) x z y w' p q' f = g) ->
        (first (equiv-square-sigma-over-product extext A Aisdiscrete x y z w' f g))
          (p , (q' , τ)) =
        (square-sigma-over-product extext A Aisdiscrete x y z w' f g) (p , (q' , τ)) ,
      idJ
      ( ( A) ,
        ( x) ,
        ( \ z' p' ->
          ( g : hom A z' y) ->
          ( τ :
            product-transport A A (hom A) x z' y y p' refl f = g) ->
          ( first
            ( equiv-square-sigma-over-product extext A Aisdiscrete x y z' y f g)
            ( p' , (refl , τ))) =
          ( square-sigma-over-product extext A Aisdiscrete x y z' y f g
            ( p' , (refl , τ)))) ,
        ( \ g τ ->
          refl-refl-map-equiv-square-sigma-over-product
            ( extext)
            ( A) (Aisdiscrete)
            ( x) (y)
            ( f) (g)
            ( τ)) ,
        ( z) ,
        ( p)) ,
      ( w) ,
      ( q))

#def is-equiv-square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  : is-equiv
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
              [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                ((t === 1_2) /\ Δ¹ s) |-> g s ,
                (Δ¹ t /\ (s === 0_2)) |-> h t ,
                (Δ¹ t /\ (s === 1_2)) |-> k t ])))
    ( square-sigma-over-product extext A Aisdiscrete x y z w f g)
  :=
    is-equiv-rev-homotopic-is-equiv
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
                [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
                  ((t === 1_2) /\ Δ¹ s) |-> g s ,
                  (Δ¹ t /\ (s === 0_2)) |-> h t ,
                  (Δ¹ t /\ (s === 1_2)) |-> k t ])))
      ( first (equiv-square-sigma-over-product extext A Aisdiscrete x y z w f g))
      ( square-sigma-over-product extext A Aisdiscrete x y z w f g)
      ( \ (p , (q , τ)) ->
        map-equiv-square-sigma-over-product extext A Aisdiscrete x y z w f p q g τ)
      ( second (equiv-square-sigma-over-product extext A Aisdiscrete x y z w f g))

#def is-equiv-fibered-map-square-sigma-over-product
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( p : x = z)
  ( q : y = w)
  : is-equiv
    ( product-transport A A (hom A) x z y w p q f = g)
    ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
      [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
        ((t === 1_2) /\ Δ¹ s) |-> g s ,
        (Δ¹ t /\ (s === 0_2)) |-> (arr-eq A x z p) t ,
        (Δ¹ t /\ (s === 1_2)) |-> (arr-eq A y w q) t ])
    ( fibered-map-square-sigma-over-product extext A Aisdiscrete x y z w f p q g)
  :=
    fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
      ( x = z)
      ( hom A x z)
      ( y = w)
      ( hom A y w)
      ( \ p' q' -> (product-transport A A (hom A) x z y w p' q' f) = g)
      ( \ h' k' ->
        ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
          [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
            ((t === 1_2) /\ Δ¹ s) |-> g s ,
            (Δ¹ t /\ (s === 0_2)) |-> h' t ,
            (Δ¹ t /\ (s === 1_2)) |-> k' t ]))
      ( arr-eq A x z)
      ( arr-eq A y w)
      ( \ p' q' ->
        fibered-map-square-sigma-over-product
          ( extext)
          ( A) (Aisdiscrete)
          ( x) (y) (z) (w)
          ( f)
          ( p')
          ( q')
          ( g))
      ( is-equiv-square-sigma-over-product extext A Aisdiscrete x y z w f g)
      ( Aisdiscrete x z)
      ( Aisdiscrete y w)
      ( p)
      ( q)

#def is-equiv-fibered-map-square-sigma-over-product-refl-refl
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  : is-equiv
    (f = g)
    ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
      [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
        ((t === 1_2) /\ Δ¹ s) |-> g s ,
        (Δ¹ t /\ (s === 0_2)) |-> x ,
        (Δ¹ t /\ (s === 1_2)) |-> y ])
    ( fibered-map-square-sigma-over-product
      extext A Aisdiscrete x y x y f refl refl g)
  :=
    is-equiv-fibered-map-square-sigma-over-product
      extext A Aisdiscrete x y x y f g refl refl
```

The previous calculations allow us to establish a family of equivalences:

```rzk
#def is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
    ( Σ (g : hom A x y) , f = g)
    ( Σ (g : hom A x y) ,
        ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
          [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
            ((t === 1_2) /\ Δ¹ s) |-> g s ,
            (Δ¹ t /\ (s === 0_2)) |-> x ,
            (Δ¹ t /\ (s === 1_2)) |-> y ]))
    ( total-map-family-of-maps
      ( hom A x y)
      ( \ g -> f = g)
      ( \ g ->
        { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
        [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
          ((t === 1_2) /\ Δ¹ s) |-> g s ,
          (Δ¹ t /\ (s === 0_2)) |-> x ,
          (Δ¹ t /\ (s === 1_2)) |-> y ])
      ( fibered-map-square-sigma-over-product
          extext A Aisdiscrete x y x y f refl refl))
  :=
    family-of-equiv-total-equiv
      ( hom A x y)
      ( \ g -> f = g)
      ( \ g ->
        { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
        [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
          ((t === 1_2) /\ Δ¹ s) |-> g s ,
          (Δ¹ t /\ (s === 0_2)) |-> x ,
          (Δ¹ t /\ (s === 1_2)) |-> y ])
      ( fibered-map-square-sigma-over-product
          extext A Aisdiscrete x y x y f refl refl)
      ( \ g ->
        is-equiv-fibered-map-square-sigma-over-product-refl-refl
          ( extext)
          ( A) (Aisdiscrete)
          ( x) (y)
          ( f) (g))

#def equiv-sum-fibered-map-square-sigma-over-product-refl-refl
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : Equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) ,
          ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> x ,
              (Δ¹ t /\ (s === 1_2)) |-> y ]))
  :=
    ( ( total-map-family-of-maps
        ( hom A x y)
        ( \ g -> f = g)
        ( \ g ->
          { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> x ,
              (Δ¹ t /\ (s === 1_2)) |-> y ])
        ( fibered-map-square-sigma-over-product
            extext A Aisdiscrete x y x y f refl refl)) ,
    is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl
      extext A Aisdiscrete x y f)
```

Now using the equivalence on total spaces and the contractibility of based path
spaces, we conclude that the codomain extension type is contractible.

```rzk
#def is-contr-horn-refl-refl-extension-type
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr
    ( Σ ( g : hom A x y) ,
        ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
          [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
            ((t === 1_2) /\ Δ¹ s) |-> g s ,
            (Δ¹ t /\ (s === 0_2)) |-> x ,
            (Δ¹ t /\ (s === 1_2)) |-> y ]))
  := is-contr-is-equiv-from-contr
      ( Σ ( g : hom A x y) , f = g)
      ( Σ ( g : hom A x y) ,
          ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> x ,
              (Δ¹ t /\ (s === 1_2)) |-> y ]))
      ( equiv-sum-fibered-map-square-sigma-over-product-refl-refl
          extext A Aisdiscrete x y f)
      ( is-contr-based-paths (hom A x y) f)
```

The extension types that appear in the Segal condition are retracts of this type
--- at least when the second arrow in the composable pair is an identity.

```rzk
#def triangle-to-square-section
  (A : U)
  (x y : A)
  (f g : hom A x y)
  (α : hom2 A x y y f (id-arr A y) g)
  : { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
    [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
      ((t === 1_2) /\ Δ¹ s) |-> g s ,
      (Δ¹ t /\ (s === 0_2)) |-> x ,
      (Δ¹ t /\ (s === 1_2)) |-> y ]
  := \ (t , s) -> recOR (t <= s |-> α (s , t) , s <= t |-> g s)

#def sigma-triangle-to-sigma-square-section
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (d , α) : Σ (d : hom A x y) , hom2 A x y y f (id-arr A y) d)
  : Σ ( g : hom A x y) ,
      ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
        [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
          ((t === 1_2) /\ Δ¹ s) |-> g s ,
          (Δ¹ t /\ (s === 0_2)) |-> x ,
          (Δ¹ t /\ (s === 1_2)) |-> y ])
  := (d , triangle-to-square-section A x y f d α)

#def sigma-square-to-sigma-triangle-retraction
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (g , σ) :
    Σ (g : hom A x y) ,
      ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
        [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
          ((t === 1_2) /\ Δ¹ s) |-> g s ,
          (Δ¹ t /\ (s === 0_2)) |-> x ,
          (Δ¹ t /\ (s === 1_2)) |-> y ]))
  : Σ (d : hom A x y) , hom2 A x y y f (id-arr A y) d
  := ((\ t -> σ (t , t)) , (\ (t , s) -> σ (s , t)))

#def sigma-triangle-to-sigma-square-retract
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : is-retract-of
      ( Σ (d : hom A x y) , hom2 A x y y f (id-arr A y) d)
      ( Σ (g : hom A x y) ,
          ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> x ,
              (Δ¹ t /\ (s === 1_2)) |-> y ]))
  :=
    ( sigma-triangle-to-sigma-square-section A x y f ,
      ( sigma-square-to-sigma-triangle-retraction A x y f ,
        \ dα -> refl ))
```

We can now verify the Segal condition in the case of composable pairs in which
the second arrow is an identity.

```rzk
#def is-contr-hom2-with-id-is-discrete
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr ( Σ (d : hom A x y) , hom2 A x y y f (id-arr A y) d)
  :=
    is-retract-of-is-contr-is-contr
      ( Σ ( d : hom A x y) , (hom2 A x y y f (id-arr A y) d))
      ( Σ ( g : hom A x y) ,
          ( { (t , s) : 2 * 2 | Δ¹×Δ¹ (t , s)} -> A
            [ ((t === 0_2) /\ Δ¹ s) |-> f s ,
              ((t === 1_2) /\ Δ¹ s) |-> g s ,
              (Δ¹ t /\ (s === 0_2)) |-> x ,
              (Δ¹ t /\ (s === 1_2)) |-> y ]))
      ( sigma-triangle-to-sigma-square-retract A x y f)
      ( is-contr-horn-refl-refl-extension-type extext A Aisdiscrete x y f)
```

But since `A` is discrete, its hom type family is equivalent to its identity
type family, and we can use "path induction" over arrows to reduce the general
case to the one just proven:

```rzk
#def is-contr-hom2-is-discrete
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : is-contr (Σ (h : hom A x z) , hom2 A x y z f g h)
  :=
    ind-based-path
      A
      y
      ( \ w -> hom A y w)
      ( \ w -> arr-eq A y w)
      ( Aisdiscrete y)
      ( \ w d -> is-contr ( Σ (h : hom A x w) , hom2 A x y w f d h))
      ( is-contr-hom2-with-id-is-discrete
          extext A Aisdiscrete x y f)
      ( z)
      ( g)
```

Finally, we conclude:

```rzk title="RS17, Proposition 7.3"
#def is-segal-is-discrete
  ( extext : ExtExt)
  ( A : U)
  ( Aisdiscrete : is-discrete A)
  : is-segal A
  := is-contr-hom2-is-discrete extext A Aisdiscrete
```
