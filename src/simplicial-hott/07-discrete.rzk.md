# Discrete types

These formalisations correspond to Section 7 of RS17 paper.

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

```rzk
-- [RS17, Definition 7.1]
#def arr-eq
  (A : U)             -- A type.
  (x y : A)           -- Two points of type A.
  (p : x = y)         -- A path p from x to y in A.
  : hom A x y         -- An arrow p from x to y in A.
  := idJ(A, x, \y' -> \p' -> hom A x y', (id-arr A x), y, p)

#def is-discrete
  (A : U)             -- A type.
  : U
  := (x : A) -> (y : A) -> isEquiv (x =_{A} y) (hom A x y) (arr-eq A x y)
```

## Families of discrete types

By function extensionality, the dependent function type associated to a family
of discrete types is discrete.

```rzk
#def equiv-discrete-family
  (funext : FunExt)
  (X : U)
  (A : X -> U)
  (Aisdiscrete : (x : X) -> is-discrete (A x))
  (f g : (x : X) -> A x)
  : Eq (f = g)(hom ((x : X) -> A x) f g)
  :=
    triple-comp-equiv
      ( f = g)
      ( (x : X) -> f x = g x)
      ( (x : X) -> hom (A x) (f x) (g x))
      ( hom ((x : X) -> A x) f g)
      ( FunExtEq funext X A f g)
      ( fibered-Eq-function-Eq funext X
        (\ x -> (f x = g x))(\x -> hom (A x) (f x) (g x))
        (\ x -> (arr-eq (A x) (f x) (g x),(Aisdiscrete x (f x) (g x)))))
      (flip-ext-fun-inv
        2
        Δ¹
        ∂Δ¹
        X
        ( \ t x -> A x)
        ( \ t x -> recOR (t === 0_2 |-> f x, t === 1_2 |-> g x)))

#def equiv-discrete-family-map
  (funext : FunExt)
  (X : U)
  (A : X -> U)
  (Aisdiscrete : (x : X) -> is-discrete (A x))
  (f g : (x : X) -> A x)
  (h : f = g)
  : arr-eq ((x : X) -> A x) f g h =
    (first (equiv-discrete-family funext X A Aisdiscrete f g)) h
  :=
    idJ(
      (x : X) -> A x,
      f,
      \ g' h' ->
        arr-eq ((x : X) -> A x) f g' h' =
        (first (equiv-discrete-family funext X A Aisdiscrete f g')) h',
      refl,
      g,
      h)

-- [RS17, Proposition 7.2]
#def is-discrete-dependent-function-discrete-family
  (funext : FunExt)
  (X : U)
  (A : X -> U)
  (Aisdiscrete : (x : X) -> is-discrete (A x))
  : is-discrete ((x : X) -> A x)
  := \ f g ->
      isEquiv-homotopic-isEquiv
        ( f = g)
        ( hom ((x : X) -> A x) f g)
        ( arr-eq ((x : X) -> A x) f g)
        ( first (equiv-discrete-family funext X A Aisdiscrete f g))
        ( equiv-discrete-family-map funext X A Aisdiscrete f g)
        ( second (equiv-discrete-family funext X A Aisdiscrete f g))
```

By extension extensionality, an extension type into a family of discrete types
is discrete. Sinced fibered-Eq-extension-Eq considers total extension types
only, extending from BOT, that's all we prove here for now.

```rzk
#def Eq-discrete-extension
  (extext : ExtExt) -- This proof uses extension extensionality.
  (I : CUBE) -- A cube.
  (ψ : I -> TOPE) -- A tope.
  (A : ψ -> U) -- A type family over the tope.
  (Aisdiscrete : (t : ψ) -> is-discrete (A t))
  (f g : (t : ψ) -> A t) -- A pair of elements of the extension type
  : Eq (f = g)(hom ((t : ψ) -> A t) f g)
  :=
    triple-comp-equiv
      ( f = g)
      ( (t : ψ) -> f t = g t)
      ( (t : ψ) -> hom (A t) (f t) (g t))
      ( hom ((t : ψ) -> A t) f g)
      ( ExtExtEq extext I ψ (\t -> BOT) A (\ u -> recBOT) f g)
      ( fibered-Eq-extension-Eq
        extext
        I
        ψ
        ( \ t -> f t = g t)
        ( \ t -> hom (A t)(f t)(g t))
        ( \ t -> (arr-eq (A t) (f t) (g t), (Aisdiscrete t (f t)(g t)))))
      ( fubini
        I
        2
        ψ
        ( \ t -> BOT)
        Δ¹
        ∂Δ¹
        ( \ t s -> A t)
        ( \ (t, s) -> recOR (s === 0_2 |-> f t, s === 1_2 |-> g t)))

#def Eq-discrete-extension-map
  (extext : ExtExt) -- This proof uses extension extensionality.
  (I : CUBE) -- A cube.
  (ψ : (t : I) -> TOPE) -- A tope.
  (A : ψ -> U) -- A type family over the tope.
  (Aisdiscrete : (t : ψ) -> is-discrete (A t))
  (f g : (t : ψ) -> A t) -- A pair of elements of the extension type
  (h : f = g)
  : arr-eq ((t : ψ) -> A t) f g h =
    (first (Eq-discrete-extension extext I ψ A Aisdiscrete f g)) h
  :=
    idJ(
      (t : ψ) -> A t,
      f,
      \ g' h' ->
        arr-eq ((t : ψ) -> A t) f g' h' =
        (first (Eq-discrete-extension extext I ψ A Aisdiscrete f g')) h',
      refl,
      g,
      h)

-- [RS17, Proposition 7.2, for extension types]
#def is-discrete-extension-family
  (extext : ExtExt) -- This proof uses extension extensionality.
  (I : CUBE) -- A cube.
  (ψ : (t : I) -> TOPE) -- A tope.
  (A : ψ -> U) -- A type family over the tope.
  (Aisdiscrete : (t : ψ) -> is-discrete (A t))
  : is-discrete ((t : ψ) -> A t)
  := \f g ->
    isEquiv-homotopic-isEquiv
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
    (extext : ExtExt) -- This proof uses extension extensionality.
    (A : U)
    (Aisdiscrete : is-discrete A)
    : is-discrete (arr A)
    := is-discrete-extension-family extext 2 Δ¹ (\t -> A)(\t -> Aisdiscrete)
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
  : isEquiv (f =_{Δ¹ -> A} g)(hom (arr A) f g)(arr-eq (arr A) f g)
  := (is-discrete-arr-is-discrete extext A Aisdiscrete) f g

#def equiv-arr-eq-discrete uses (x y z w)
  : Eq (f =_{Δ¹ -> A} g)(hom (arr A) f g)
  := (arr-eq (arr A) f g,
          (is-discrete-arr-is-discrete extext A Aisdiscrete) f g)

#def equiv-square-hom-arr
  : Eq (hom (arr A) f g)
      (∑(h : hom A x z),
        (∑(k : hom A y w),
          (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                    [((t === 0_2) /\  Δ¹ s) |-> f s,
										((t === 1_2) /\  Δ¹ s) |-> g s,
										(Δ¹ t /\  (s === 0_2)) |-> h t,
										(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
  :=
    ( \ α -> (\t -> α t 0_2, (\ t -> α t 1_2, \(t, s) -> α t s)),
      ( ( \ σ -> \t -> \s -> (second (second σ)) (t, s),
        \ α -> refl ),
        ( \ σ -> \t -> \s -> (second (second σ)) (t, s),
        \ σ -> refl )))

-- The equivalence underlying Eq-arr.
#def fibered-arr-free-arr
  : (arr A) -> (∑ (x : A), (∑ (y : A), hom A x y))
  := \ k -> (k 0_2, (k 1_2, k))

#def id-equiv-Eq-arr uses (w x y z)
  : isEquiv
      ( f =_{Δ¹ -> A} g)
      ( fibered-arr-free-arr f = fibered-arr-free-arr g)
      ( ap (arr A) (∑ (x : A), (∑ (y : A), hom A x y)) f g fibered-arr-free-arr)
  :=
    isEquiv-ap-isEquiv
      ( arr A)
      ( ∑ (x : A), (∑ (y : A), hom A x y))
      fibered-arr-free-arr
      ( second (Eq-arr A))
      f
      g

#def id-Eq-Eq-arr uses (w x y z)
  : Eq (f =_{Δ¹ -> A} g) (fibered-arr-free-arr f = fibered-arr-free-arr g)
  :=
    Eq-ap-isEquiv
      ( arr A)
      (
      ∑ (x : A), (∑ (y : A), hom A x y)) fibered-arr-free-arr
      (second (Eq-arr A))
      f
      g

#def equiv-sigma-over-prod-arr-eq
  : Eq
      (fibered-arr-free-arr f = fibered-arr-free-arr g)
      (∑(p : x = z),
        (∑(q : y = w),
          (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
  := Eq-Sigma-over-Prod-Eq
      A
      A
      ( \ x y -> hom A x y)
      ( fibered-arr-free-arr f)
      ( fibered-arr-free-arr g)

#def equiv-square-sigma-over-prod uses (extext Aisdiscrete)
  : Eq
      (∑(p : x = z),
        (∑(q : y = w),
          (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
      (∑(h : hom A x z),
        (∑(k : hom A y w),
          (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                    [((t === 0_2) /\  Δ¹ s) |-> f s,
										((t === 1_2) /\  Δ¹ s) |-> g s,
										(Δ¹ t /\  (s === 0_2)) |-> h t,
										(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
  :=
    LeftCancel_Eq
      ( f =_{Δ¹ -> A} g)
      ( ∑(p : x = z),
        (∑(q : y = w),
            (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
      ( ∑(h : hom A x z),
        (∑(k : hom A y w),
          (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                    [((t === 0_2) /\  Δ¹ s) |-> f s,
										((t === 1_2) /\  Δ¹ s) |-> g s,
										(Δ¹ t /\  (s === 0_2)) |-> h t,
										(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
      ( comp-equiv
        ( f =_{Δ¹ -> A} g)
        ( fibered-arr-free-arr f = fibered-arr-free-arr g)
        ( ∑(p : x = z),
          (∑(q : y = w),
            (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
        id-Eq-Eq-arr
        equiv-sigma-over-prod-arr-eq)
      ( comp-equiv
        ( f =_{Δ¹ -> A} g)
        ( hom (arr A) f g)
        ( ∑(h : hom A x z),
          (∑(k : hom A y w),
            (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                [((t === 0_2) /\  Δ¹ s) |-> f s,
								((t === 1_2) /\  Δ¹ s) |-> g s,
								(Δ¹ t /\  (s === 0_2)) |-> h t,
								(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
        equiv-arr-eq-discrete
        equiv-square-hom-arr)

#end discrete-arr-equivalences

-- closing the section so I can use path induction
#def fibered-map-square-Sigma-over-Prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y z w : A)
  (f : hom A x y)
  (p : x = z)
  (q : y = w)
  : (g : hom A z w) ->
    (prod-transport A A (\a b -> hom A a b) x z y w p q f = g) ->
    (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
        [((t === 0_2) /\  Δ¹ s) |-> f s,
				((t === 1_2) /\  Δ¹ s) |-> g s,
				(Δ¹ t /\  (s === 0_2)) |-> (arr-eq A x z p) t,
				(Δ¹ t /\  (s === 1_2)) |-> (arr-eq A y w q) t ]>)
  :=
    idJ(
      A,
      x,
      \ z' p' ->
        (g : hom A z' w) ->
        (prod-transport A A (\ a b -> hom A a b) x z' y w p' q f = g) ->
        (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
            [((t === 0_2) /\  Δ¹ s) |-> f s,
						((t === 1_2) /\  Δ¹ s) |-> g s,
						(Δ¹ t /\  (s === 0_2)) |-> (arr-eq A x z' p') t,
						(Δ¹ t /\  (s === 1_2)) |-> (arr-eq A y w q) t ]>),
        idJ(
          A,
          y,
          \ w' q' ->
            (g : hom A x w') ->
            (prod-transport A A (\a b -> hom A a b) x x y w' refl q' f = g) ->
            (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                  [((t === 0_2) /\  Δ¹ s) |-> f s,
									((t === 1_2) /\  Δ¹ s) |-> g s,
									(Δ¹ t /\  (s === 0_2)) |-> x,
									(Δ¹ t /\  (s === 1_2)) |-> (arr-eq A y w' q') t ]>),
          \ g τ ->
            idJ(
              hom A x y,
              f,
              \ g' τ' -> (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                            [((t === 0_2) /\  Δ¹ s) |-> f s,
								            ((t === 1_2) /\  Δ¹ s) |-> g' s,
					            			(Δ¹ t /\  (s === 0_2)) |-> x,
					            			(Δ¹ t /\  (s === 1_2)) |-> y ]>),
              \ (t , s) -> f s,
              g,
              τ),
          w,
          q),
      z,
      p)

#def square-Sigma-over-Prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y z w : A)
  (f : hom A x y)
  (g : hom A z w)
  ((p, (q, τ)) : (∑(p : x = z), (∑(q : y = w),
                  (prod-transport A A (\a b -> hom A a b) x z y w p q f = g))))
  : (∑(h : hom A x z),
      (∑(k : hom A y w),
        (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
            [((t === 0_2) /\  Δ¹ s) |-> f s,
						((t === 1_2) /\  Δ¹ s) |-> g s,
						(Δ¹ t /\  (s === 0_2)) |-> h t,
						(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
  :=
    (arr-eq A x z p,
      ( arr-eq A y w q,
        fibered-map-square-Sigma-over-Prod
          extext
          A
          Aisdiscrete
          x
          y
          z
          w
          f
          p
          q
          g
          τ))

#def refl-refl-map-equiv-square-sigma-over-prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y : A)
  (f g : hom A x y)
  (τ : prod-transport A A (\a b -> hom A a b) x x y y refl refl f = g)
  : (first (equiv-square-sigma-over-prod extext A Aisdiscrete x y x y f g))
          (refl, (refl, τ)) =
    (square-Sigma-over-Prod extext A Aisdiscrete x y x y f g) (refl, (refl, τ))
  :=
    idJ(
      hom A x y,
      f,
      \ g' τ' ->
        (first (equiv-square-sigma-over-prod extext A Aisdiscrete x y x y f g'))
          (refl, (refl, τ')) =
        (square-Sigma-over-Prod extext A Aisdiscrete x y x y f g')
          (refl, (refl, τ')),
      refl,
      g,
      τ)

#def map-equiv-square-sigma-over-prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y z w : A)
  (f : hom A x y)
  (p : x = z)
  (q : y = w)
  : (g : hom A z w) ->
    (τ : prod-transport A A (\a b -> hom A a b) x z y w p q f = g) ->
    (first (equiv-square-sigma-over-prod extext A Aisdiscrete x y z w f g))
          (p, (q, τ)) =
    (square-Sigma-over-Prod extext A Aisdiscrete x y z w f g) (p, (q, τ))
  :=
    idJ(
      A,
      y,
      \ w' q' ->
        (g : hom A z w') ->
        (τ : prod-transport A A (\a b -> hom A a b) x z y w' p q' f = g) ->
        (first (equiv-square-sigma-over-prod extext A Aisdiscrete x y z w' f g))
          (p, (q', τ)) =
        (square-Sigma-over-Prod extext A Aisdiscrete x y z w' f g) (p, (q', τ)),
      idJ(
        A,
        x,
        \ z' p' ->
          (g : hom A z' y) ->
          (τ : prod-transport A A (\a b -> hom A a b) x z' y y p' refl f = g) ->
          (first (equiv-square-sigma-over-prod extext A Aisdiscrete x y z' y f g))
            (p', (refl, τ)) =
          (square-Sigma-over-Prod extext A Aisdiscrete x y z' y f g)
            (p', (refl, τ)),
        \ g τ ->
          refl-refl-map-equiv-square-sigma-over-prod
            extext
            A
            Aisdiscrete
            x
            y
            f
            g
            τ,
        z,
        p),
      w,
      q)

#def is-equiv-square-sigma-over-prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y z w : A)
  (f : hom A x y)
  (g : hom A z w)
  : isEquiv
      (∑(p : x = z),
        (∑(q : y = w),
            (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
      (∑(h : hom A x z),
        (∑(k : hom A y w),
          (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                    [((t === 0_2) /\  Δ¹ s) |-> f s,
										((t === 1_2) /\  Δ¹ s) |-> g s,
										(Δ¹ t /\  (s === 0_2)) |-> h t,
										(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
      (square-Sigma-over-Prod extext A Aisdiscrete x y z w f g)
  :=
    isEquiv-rev-homotopic-isEquiv
      ( ∑(p : x = z),
        (∑(q : y = w),
            (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)))
      ( ∑(h : hom A x z),
        (∑(k : hom A y w),
          (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                    [((t === 0_2) /\  Δ¹ s) |-> f s,
										((t === 1_2) /\  Δ¹ s) |-> g s,
										(Δ¹ t /\  (s === 0_2)) |-> h t,
										(Δ¹ t /\  (s === 1_2)) |-> k t ]>)))
      ( first (equiv-square-sigma-over-prod extext A Aisdiscrete x y z w f g))
      ( square-Sigma-over-Prod extext A Aisdiscrete x y z w f g)
      ( \ (p, (q, τ)) -> map-equiv-square-sigma-over-prod
                          extext A Aisdiscrete x y z w f p q g τ)
      ( second (equiv-square-sigma-over-prod extext A Aisdiscrete x y z w f g))

#def is-equiv-fibered-map-square-sigma-over-prod
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y z w : A)
  (f : hom A x y)
  (g : hom A z w)
  (p : x = z)
  (q : y = w)
  : isEquiv
    (prod-transport A A (\a b -> hom A a b) x z y w p q f = g)
    (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
        [((t === 0_2) /\  Δ¹ s) |-> f s,
				((t === 1_2) /\  Δ¹ s) |-> g s,
				(Δ¹ t /\  (s === 0_2)) |-> (arr-eq A x z p) t,
				(Δ¹ t /\  (s === 1_2)) |-> (arr-eq A y w q) t ]>)
    (fibered-map-square-Sigma-over-Prod extext A Aisdiscrete x y z w f p q g)
  :=
    fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
      ( x = z)
      ( hom A x z)
      ( y = w)
      ( hom A y w)
      ( \ p' q' -> (prod-transport A A (\a b -> hom A a b) x z y w p' q' f = g))
      ( \ h' k' -> (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                      [((t === 0_2) /\  Δ¹ s) |-> f s,
										  ((t === 1_2) /\  Δ¹ s) |-> g s,
										  (Δ¹ t /\  (s === 0_2)) |-> h' t,
										  (Δ¹ t /\  (s === 1_2)) |-> k' t ]>))
      ( arr-eq A x z)
      ( arr-eq A y w)
      ( \ p' q' -> (fibered-map-square-Sigma-over-Prod
                      extext A Aisdiscrete x y z w f p' q' g))
      ( is-equiv-square-sigma-over-prod extext A Aisdiscrete x y z w f g)
      ( Aisdiscrete x z)
      ( Aisdiscrete y w)
      p
      q

#def is-equiv-fibered-map-square-sigma-over-prod-refl-refl
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y : A)
  (f : hom A x y)
  (g : hom A x y)
  : isEquiv
    (f = g)
    (<{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
            [((t === 0_2) /\  Δ¹ s) |-> f s,
						((t === 1_2) /\  Δ¹ s) |-> g s,
						(Δ¹ t /\  (s === 0_2)) |-> x,
          	(Δ¹ t /\  (s === 1_2)) |-> y ]>)
    (fibered-map-square-Sigma-over-Prod
      extext A Aisdiscrete x y x y f refl refl g)
  :=
    is-equiv-fibered-map-square-sigma-over-prod
      extext A Aisdiscrete x y x y f g refl refl

#def is-equiv-sum-fibered-map-square-sigma-over-prod-refl-refl
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y : A)
  (f : hom A x y)
  : isEquiv
      ( ∑ (g : hom A x y), f = g)
      ( ∑ (g : hom A x y), <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
      ( family-of-maps-total-map
        ( hom A x y)
        ( \ g -> f = g)
        ( \ g -> <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
        ( \ g ->
            (fibered-map-square-Sigma-over-Prod
              extext A Aisdiscrete x y x y f refl refl g)))
  :=
    family-of-equiv-total-equiv
      ( hom A x y)
      ( \ g -> f = g)
      ( \ g -> <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                          [((t === 0_2) /\  Δ¹ s) |-> f s,
								          ((t === 1_2) /\  Δ¹ s) |-> g s,
								          (Δ¹ t /\  (s === 0_2)) |-> x,
								          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
      ( \ g ->
          (fibered-map-square-Sigma-over-Prod
            extext A Aisdiscrete x y x y f refl refl g))
      ( \ g -> is-equiv-fibered-map-square-sigma-over-prod-refl-refl
                  extext
                  A
                  Aisdiscrete
                  x
                  y
                  f
                  g)

#def equiv-sum-fibered-map-square-sigma-over-prod-refl-refl
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y : A)
  (f : hom A x y)
  : Eq
      ( ∑ (g : hom A x y), f = g)
      ( ∑ (g : hom A x y), <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
  :=
    ( ( family-of-maps-total-map
        ( hom A x y)
        ( \ g -> f = g)
        ( \ g -> <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
        ( \ g ->
            (fibered-map-square-Sigma-over-Prod
              extext A Aisdiscrete x y x y f refl refl g))),
    is-equiv-sum-fibered-map-square-sigma-over-prod-refl-refl
      extext A Aisdiscrete x y f)

#def is-contr-horn-refl-refl-extension-type
  (extext : ExtExt)
  (A : U)
  (Aisdiscrete : is-discrete A)
  (x y : A)
  (f : hom A x y)
  : isContr ( ∑ (g : hom A x y), <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
  := isEquiv-fromContr-isContr
      ( ∑ (g : hom A x y), f = g)
      ( ∑ (g : hom A x y), <{(t, s) : 2 * 2 | Δ¹×Δ¹ (t, s)} -> A
                             [((t === 0_2) /\  Δ¹ s) |-> f s,
										          ((t === 1_2) /\  Δ¹ s) |-> g s,
										          (Δ¹ t /\  (s === 0_2)) |-> x,
										          (Δ¹ t /\  (s === 1_2)) |-> y ]>)
      ( equiv-sum-fibered-map-square-sigma-over-prod-refl-refl
          extext A Aisdiscrete x y f)
      ( based-paths-contractible (hom A x y) f)
```
