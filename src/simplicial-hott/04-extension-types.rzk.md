# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/4-equivalences.rzk` — contains the definitions of `Eq` and `comp-equiv`
- the file `hott/4-equivalences.rzk` relies in turn on the previous files in
  `hott/`

## Commutation of arguments and currying

```rzk title="RS17, Theorem 4.1"
#def flip-ext-fun
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( X : U)
  ( Y : ψ -> X -> U)
  ( f : (t : ϕ) -> (x : X) -> Y t x)
  : Equiv
      ( (t : ψ) -> ((x : X) -> Y t x) [ϕ t |-> f t])
      ( (x : X) -> (t : ψ) -> Y t x [ϕ t |-> f t x])
  :=
    ( \ g x t -> g t x ,
      ( ( \ h t x -> (h x) t ,
          \ g -> refl) ,
        ( \ h t x -> (h x) t ,
          \ h -> refl)))

#def flip-ext-fun-inv
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( X : U)
  ( Y : ψ -> X -> U)
  ( f : (t : ϕ) -> (x : X) -> Y t x)
  : Equiv
    ( (x : X) -> (t : ψ) -> Y t x [ ϕ t |-> f t x])
    ( (t : ψ) -> ((x : X) -> Y t x) [ ϕ t |-> f t ])
  :=
    ( \ h t x -> (h x) t , -- the one-way map
      ( ( \ g x t -> g t x , -- the retraction
          \ h -> refl) , -- the retracting homotopy
        ( \ g x t -> g t x , -- the section
          \ g -> refl)))
```

```rzk title="RS17, Theorem 4.2"
#def curry-uncurry
  ( I J : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( ζ : J -> TOPE)
  ( χ : ζ -> TOPE)
  ( X : ψ -> ζ -> U)
  ( f : { (t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s )
  : Equiv
    ( (t : ψ) -> ((s : ζ) -> X t s [ χ s |-> f (t , s) ])
      [ ϕ t |-> \ s -> f (t , s)])
    ( { (t , s) : I * J | ψ t /\ ζ s} -> X t s
      [(ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)])
  :=
    ( \ g (t , s) -> (g t) s , -- the one way map
      ( ( \ h t s -> h (t , s) , -- its retraction
          \ g -> refl) , -- the retracting homotopy
        ( \ h t s -> h (t , s) , -- its section
          \ h -> refl)))  -- the section homotopy

#def uncurry-opcurry
  ( I J : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( ζ : J -> TOPE)
  ( χ : ζ -> TOPE)
  ( X : ψ -> ζ -> U)
  ( f : { (t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s )
  : Equiv
    ( { (t , s) : I * J | ψ t /\ ζ s} -> X t s
      [ (ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)])
    ( (s : ζ) -> ((t : ψ) -> X t s [ ϕ t |-> f (t , s) ])
      [ χ s |-> \ t -> f (t , s) ])
  :=
    ( \ h s t -> h (t , s) ,
      ( ( \ g (t , s) -> (g s) t ,
          \ h -> refl) ,
        ( \ g (t , s) -> (g s) t ,
          \ g -> refl)))

#def fubini
  ( I J : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( ζ : J -> TOPE)
  ( χ : ζ -> TOPE)
  ( X : ψ -> ζ -> U)
  ( f : { (t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s )
  : Equiv
    ( {t : I | ψ t} -> ({ s : J | ζ s} -> X t s [ χ s |-> f (t , s) ])
        [ ϕ t |-> \ s -> f (t , s) ])
    ( {s : J | ζ s} -> ({ t : I | ψ t} -> X t s [ ϕ t |-> f (t , s) ])
        [ χ s |-> \ t -> f (t , s) ])
  :=
    comp-equiv
      ( {t : I | ψ t} -> ({ s : J | ζ s} -> X t s [ χ s |-> f (t , s) ])
        [ ϕ t |-> \ s -> f (t , s) ])
      ( { (t , s) : I * J | ψ t /\ ζ s} -> X t s
        [(ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)])
      ( {s : J | ζ s} -> ({ t : I | ψ t} -> X t s [ ϕ t |-> f (t , s) ])
        [ χ s |-> \ t -> f (t , s) ])
      ( curry-uncurry I J ψ ϕ ζ χ X f)
      ( uncurry-opcurry I J ψ ϕ ζ χ X f)
```

## Extending into Σ-types (the non-axiom of choice)

```rzk title="RS17, Theorem 4.3"
#def axiom-choice
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( X : ψ -> U)
  ( Y : (t : ψ) -> (x : X t) -> U)
  ( a : (t : ϕ) -> X t)
  ( b : (t : ϕ) -> Y t (a t))
  : Equiv
    ( {t : I | ψ t} -> (Σ (x : X t) , Y t x) [ ϕ t |-> (a t , b t) ])
    ( Σ ( f : ({t : I | ψ t} -> X t [ϕ t |-> a t ])) ,
        ( {t : I | ψ t} -> Y t (f t) [ ϕ t |-> b t ]))
    :=
      ( \ g -> (\ t -> (first (g t)) , \ t -> second (g t)) ,
        ( ( \ (f, h) t -> (f t , h t) ,
            \ _ -> refl) ,
          ( \ (f, h) t -> (f t , h t) ,
            \ _ -> refl)))
```

## Composites and unions of cofibrations

```rzk title="RS17, Theorem 4.4"
-- Reformulated via tope disjunction instead of inclusion.
-- See https://github.com/rzk-lang/rzk/issues/8
#def cofibration-composition'
  ( I : CUBE)
  ( χ ψ ϕ : I -> TOPE)
  ( X : χ -> U)
  ( a : {t : I | χ t /\ ψ t /\ ϕ t} -> X t )
  : Equiv
      ( (t : χ) -> X t [ χ t /\ ψ t /\ ϕ t |-> a t ])
      ( Σ ( f : {t : I | χ t /\ ψ t} -> X t [ χ t /\ ψ t /\ ϕ t |-> a t ]) ,
          ( (t : χ) -> X t [ χ t /\ ψ t |-> f t ]))
  :=
    ( \ h -> (\ t -> h t , \ t -> h t) ,
      ( ( \ fg t -> (second fg) t , \ h -> refl) ,
        ( \ fg t -> (second fg) t , \ h -> refl)))
```

```rzk title="RS17, Theorem 4.4"
-- original form
#def cofibration-composition
  ( I : CUBE)
  ( χ : I -> TOPE)
  ( ψ : χ -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( X : χ -> U)
  ( a : (t : ϕ) -> X t)
  : Equiv
    ( (t : χ) -> X t [ ϕ t |-> a t ])
    ( Σ ( f : (t : ψ) -> X t [ ϕ t |-> a t ]) ,
        ( (t : χ) -> X t [ ψ t |-> f t ]))
  :=
    ( \ h -> (\ t -> h t , \ t -> h t) ,
      ( ( \ fg t -> (second fg) t , \ h -> refl) ,
        ( ( \ fg t -> (second fg) t , \ h -> refl))))
```

```rzk title="RS17, Theorem 4.5"
#def cofibration-union
  ( I : CUBE)
  ( ϕ ψ : I -> TOPE)
  ( X : {t : I | ϕ t \/ ψ t} -> U )
  ( a : (t : ψ) -> X t)
  : Equiv
      ( {t : I | ϕ t \/ ψ t} -> X t [ ψ t |-> a t ])
      ( (t : ϕ) -> X t [ ϕ t /\ ψ t |-> a t ])
  :=
    (\ h -> \ t -> h t ,
      ( ( \ g -> \ t -> recOR (ϕ t |-> g t , ψ t |-> a t) , \ h -> refl) ,
        ( \ g -> \ t -> recOR (ϕ t |-> g t , ψ t |-> a t) , \ h -> refl)))
```

## Relative function extensionality

There are various equivalent forms of the relative function extensionality
axiom. Here we state the one that will be most useful and derive an application.

```rzk
#def ext-htpy-eq
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( A : ψ -> U)
  ( a : (t : ϕ) -> A t)
  ( f g : (t : ψ) -> A t [ ϕ t |-> a t ])
  ( p : f = g)
  : (t : ψ) -> (f t = g t) [ ϕ t |-> refl ]
  := idJ
    ( ( (t : ψ) -> A t [ ϕ t |-> a t ]) ,
      ( f) ,
      ( \ g' p' -> (t : ψ) -> (f t = g' t) [ ϕ t |-> refl ]) ,
      ( \ t -> refl) ,
      ( g) ,
      ( p))
```

The type that encodes the extension extensionality axiom. As suggested by
footnote 8, we assert this as an "extension extensionality" axiom

```rzk title="RS17, Proposition 4.8(ii)"

#def ExtExt
  : U
  :=
    ( I : CUBE) ->
    ( ψ : I -> TOPE) ->
    ( ϕ : ψ -> TOPE) ->
    ( A : ψ -> U) ->
    ( a : (t : ϕ) -> A t) ->
    ( f : (t : ψ) -> A t [ ϕ t |-> a t ]) ->
    ( g : (t : ψ) -> A t [ ϕ t |-> a t ]) ->
    is-equiv
      ( f = g)
      ( (t : ψ) -> (f t = g t) [ ϕ t |-> refl ])
      ( ext-htpy-eq I ψ ϕ A a f g)

-- The equivalence provided by extension extensionality.
#def equiv-ExtExt
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( A : ψ -> U)
  ( a : (t : ϕ) -> A t)
  ( f g : (t : ψ) -> A t [ ϕ t |-> a t ])
  : Equiv (f = g) ((t : ψ) -> (f t = g t) [ ϕ t |-> refl ])
  := (ext-htpy-eq I ψ ϕ A a f g , extext I ψ ϕ A a f g)
```

In particular, extension extensionality implies that homotopies give rise to
identifications. This definition defines `eq-ext-htpy` to be the retraction to
`ext-htpy-eq`.

```rzk
#def eq-ext-htpy
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( ϕ : ψ -> TOPE)
  ( A : ψ -> U)
  ( a : (t : ϕ) -> A t)
  ( f g : (t : ψ) -> A t [ ϕ t |-> a t ])
  : ((t : ψ) -> (f t = g t) [ ϕ t |-> refl ]) -> (f = g)
  := first (first (extext I ψ ϕ A a f g))
```

By extension extensionality, fiberwise equivalences of extension types define
equivalences of extension types.

```rzk
-- A fiberwise equivalence defines an equivalence of extension types, for
-- simplicity extending from BOT
#def equiv-extension-equiv-fibered
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I -> TOPE)
  ( A B : ψ -> U)
  ( fibequiv : (t : ψ) -> (Equiv (A t) (B t)) )
  : Equiv ((t : ψ) -> A t ) ((t : ψ) -> B t )
  :=
    ( ( \ a t -> (first (fibequiv t)) (a t)) ,
      ( ( ( \ b t -> (first (first (second (fibequiv t)))) (b t)) ,
          ( \ a ->
            eq-ext-htpy
              ( extext)
              ( I)
              ( ψ)
              ( \ t -> BOT)
              ( A)
              ( \ u -> recBOT)
              ( \ t ->
                first (first (second (fibequiv t))) (first (fibequiv t) (a t)))
              ( a)
              ( \ t -> second (first (second (fibequiv t))) (a t)))) ,
        ( ( \ b t -> first (second (second (fibequiv t))) (b t)) ,
          ( \ b ->
            eq-ext-htpy
              ( extext)
              ( I)
              ( ψ)
              ( \ t -> BOT)
              ( B)
              ( \ u -> recBOT)
              ( \ t ->
                first (fibequiv t) (first (second (second (fibequiv t))) (b t)))
              ( b)
              ( \ t -> second (second (second (fibequiv t))) (b t))))))
```
