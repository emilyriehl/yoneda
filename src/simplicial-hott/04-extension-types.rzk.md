# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/4-equivalences.rzk` — contains the definitions of `#!rzk Equiv` and
  `#!rzk comp-equiv`
- the file `hott/4-equivalences.rzk` relies in turn on the previous files in
  `hott/`

## Commutation of arguments and currying

```rzk title="RS17, Theorem 4.1"
#def flip-ext-fun
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
      ( ( t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
      ( ( x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
  :=
    ( \ g x t → g t x
    , ( ( \ h t x → (h x) t
        , \ g → refl)
      , ( \ h t x → (h x) t
        , \ h → refl)))

#def flip-ext-fun-inv
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
    ( ( x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
    ( ( t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
  :=
    ( \ h t x → (h x) t
    , ( ( \ g x t → g t x
        , \ h → refl)
      , ( \ g x t → g t x
        , \ g → refl)))
```

```rzk title="RS17, Theorem 4.2"
#def curry-uncurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( t : ψ)
    → ( ( s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
  :=
    ( \ g ( t , s) → (g t) s
    , ( ( \ h t s → h (t , s)
        , \ g → refl)
      , ( \ h t s → h (t , s)
        , \ h → refl)))

#def uncurry-opcurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
    ( ( s : ζ)
    → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
  :=
    ( \ h s t → h (t , s)
    , ( ( \ g ( t , s) → (g s) t
        , \ h → refl)
      , ( \ g ( t , s) → (g s) t
        , \ g → refl)))

#def fubini
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( t : ψ)
    → ( ( s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
    ( ( s : ζ)
    → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
  :=
    equiv-comp
      ( ( t : ψ)
      → ( ( s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
      ( ( ( t , s) : I × J | ψ t ∧ ζ s)
      → X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
      ( ( s : ζ)
      → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
      ( curry-uncurry I J ψ ϕ ζ χ X f)
      ( uncurry-opcurry I J ψ ϕ ζ χ X f)
```

## Extending into Σ-types (the non-axiom of choice)

```rzk title="RS17, Theorem 4.3"
#def axiom-choice
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : ψ → U)
  ( Y : (t : ψ) → (x : X t) → U)
  ( a : ( t : ϕ) → X t)
  ( b : (t : ϕ) → Y t (a t))
  : Equiv
    ( ( t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t]))
      , ( ( t : ψ) → Y t (f t) [ϕ t ↦ b t]))
  :=
      ( \ g → ( \ t → (first (g t)) , \ t → second (g t))
      , ( ( \ ( f , h) t → (f t , h t)
          , \ _ → refl)
        , ( \ ( f , h) t → (f t , h t)
          , \ _ → refl)))
```

```rzk
#def inv-axiom-choice
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : ψ → U)
  ( Y : (t : ψ) → (x : X t) → U)
  ( a : ( t : ϕ) → X t)
  ( b : (t : ϕ) → Y t (a t))
  : Equiv
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t]))
      , ( ( t : ψ) → Y t (f t) [ϕ t ↦ b t]))
    ( ( t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
  :=
      ( \ ( f , h) → (\ t → (f t , h t))
      , ( ( \ g → ( \ t → (first (g t)) , \ t → second (g t))
          , \ _ → refl)
        , ( \ g → ( \ t → (first (g t)) , \ t → second (g t))
          , \ _ → refl)
        )
      )
```

## Composites and unions of cofibrations

The original form.

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition
  ( I : CUBE)
  ( χ : I → TOPE)
  ( ψ : χ → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : χ → U)
  ( a : ( t : ϕ) → X t)
  : Equiv
    ( ( t : χ) → X t [ϕ t ↦ a t])
    ( Σ ( f : (t : ψ) → X t [ϕ t ↦ a t])
      , ( ( t : χ) → X t [ψ t ↦ f t]))
  :=
    ( \ h → (\ t → h t , \ t → h t)
    , ( ( \ ( _f , g) t → g t , \ h → refl)
      , ( ( \ ( _f , g) t → g t , \ h → refl))))
```

A reformulated version via tope disjunction instead of inclusion (see
<https://github.com/rzk-lang/rzk/issues/8>).

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition'
  ( I : CUBE)
  ( χ ψ ϕ : I → TOPE)
  ( X : χ → U)
  ( a : ( t : I | χ t ∧ ψ t ∧ ϕ t) → X t)
  : Equiv
      ( ( t : χ) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t])
      ( Σ ( f : (t : I | χ t ∧ ψ t) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t])
        , ( ( t : χ) → X t [χ t ∧ ψ t ↦ f t]))
  :=
    ( \ h → (\ t → h t , \ t → h t)
    , ( ( \ ( _f , g) t → g t , \ h → refl)
      , ( \ ( _f , g) t → g t , \ h → refl)))
```

```rzk title="RS17, Theorem 4.5"
#def cofibration-union
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( X : (t : I | ϕ t ∨ ψ t) → U)
  ( a : ( t : ψ) → X t)
  : Equiv
      ( ( t : I | ϕ t ∨ ψ t) → X t [ψ t ↦ a t])
      ( ( t : ϕ) → X t [ϕ t ∧ ψ t ↦ a t])
  :=
    ( \ h t → h t
    , ( ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl)
      , ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl)))
```

## Relative function extensionality

There are various equivalent forms of the relative function extensionality
axiom. Here we state the one that will be most useful and derive an application.

```rzk
#def ext-htpy-eq
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : ( t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  ( p : f = g)
  : ( t : ψ) → (f t = g t) [ϕ t ↦ refl]
  :=
    ind-path
      ( ( t : ψ) → A t [ϕ t ↦ a t])
      ( f)
      ( \ g' p' → (t : ψ) → (f t = g' t) [ϕ t ↦ refl])
      ( \ t → refl)
      ( g)
      ( p)
```

The type that encodes the extension extensionality axiom. As suggested by
footnote 8, we assert this as an "extension extensionality" axiom

```rzk title="RS17, Proposition 4.8(ii)"

#def ExtExt
  : U
  :=
    ( I : CUBE)
  → ( ψ : I → TOPE)
  → ( ϕ : ψ → TOPE)
  → ( A : ψ → U)
  → ( a : ( t : ϕ) → A t)
  → ( f : (t : ψ) → A t [ϕ t ↦ a t])
  → ( g : ( t : ψ) → A t [ϕ t ↦ a t])
  → is-equiv
      ( f = g)
      ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl])
      ( ext-htpy-eq I ψ ϕ A a f g)

#assume extext : ExtExt
```

```rzk title="The equivalence provided by extension extensionality"
#def equiv-ExtExt uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : ( t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  : Equiv (f = g) ((t : ψ) → (f t = g t) [ϕ t ↦ refl])
  := ( ext-htpy-eq I ψ ϕ A a f g , extext I ψ ϕ A a f g)
```

In particular, extension extensionality implies that homotopies give rise to
identifications. This definition defines `#!rzk eq-ext-htpy` to be the
retraction to `#!rzk ext-htpy-eq`.

```rzk
#def eq-ext-htpy uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : ( t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  : ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl]) → (f = g)
  := first (first (extext I ψ ϕ A a f g))
```

By extension extensionality, fiberwise equivalences of extension types define
equivalences of extension types. For simplicity, we extend from `#!rzk BOT`.

```rzk
#def equiv-extension-equiv-family uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A B : ψ → U)
  ( famequiv : (t : ψ) → (Equiv (A t) (B t)))
  : Equiv ((t : ψ) → A t) ((t : ψ) → B t)
  :=
    ( ( \ a t → (first (famequiv t)) (a t))
    , ( ( ( \ b t → (first (first (second (famequiv t)))) (b t))
        , ( \ a →
            eq-ext-htpy
              ( I)
              ( ψ)
              ( \ t → BOT)
              ( A)
              ( \ u → recBOT)
              ( \ t →
                first (first (second (famequiv t))) (first (famequiv t) (a t)))
              ( a)
              ( \ t → second (first (second (famequiv t))) (a t))))
      , ( ( \ b t → first (second (second (famequiv t))) (b t))
        , ( \ b →
            eq-ext-htpy
              ( I)
              ( ψ)
              ( \ t → BOT)
              ( B)
              ( \ u → recBOT)
              ( \ t →
                first (famequiv t) (first (second (second (famequiv t))) (b t)))
              ( b)
              ( \ t → second (second (second (famequiv t))) (b t))))))
```
