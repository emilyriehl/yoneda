# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/4-equivalences.rzk` — contains the definitions of `Eq` and `comp-equiv`
- the file `hott/4-equivalences.rzk` relies in turn on the previous files in
  `hott/`

## Commutation of arguments and currying

```rzk
-- [RS17, Theorem 4.1]
#def flip-ext-fun
   (I : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (X : U)
   (Y : ψ -> X -> U)
   (f : (t : ϕ) -> (x : X) -> Y t x)
   : Equiv (<{t : I | ψ t} -> ((x : X) -> Y t x) [ ϕ t |-> f t ]>)
       ((x : X) -> <{t : I | ψ t} -> Y t x [ ϕ t |-> f t x]>)
   := (\ g x t -> g t x , -- the one-way map
            ((\ h t x -> (h x) t , -- the retraction
            \ g -> refl) , -- the retracting homotopy
            (\ h t x -> (h x) t , -- the section
            \ h -> refl))) -- the section homotopy

#def flip-ext-fun-inv
   (I : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (X : U)
   (Y : ψ -> X -> U)
   (f : (t : ϕ) -> (x : X) -> Y t x)
   : Equiv ((x : X) -> <{t : I | ψ t} -> Y t x [ ϕ t |-> f t x]>)
      (<{t : I | ψ t} -> ((x : X) -> Y t x) [ ϕ t |-> f t ]>)
   := (\ h t x -> (h x) t , -- the one-way map
            ((\ g x t -> g t x , -- the retraction
            \ h -> refl) , -- the retracting homotopy
            (\ g x t -> g t x , -- the section
            \ g -> refl)))

-- [RS17, Theorem 4.2]
#def curry-uncurry
   (I J : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (ζ : J -> TOPE)
   (χ : ζ -> TOPE)
   (X : ψ -> ζ -> U)
   (f : <{(t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s >)
   : Equiv (<{t : I | ψ t} -> <{ s : J | ζ s} -> X t s [ χ s |-> f (t , s) ]> [ ϕ t |-> \{s : J | ζ s} -> f (t , s) ]>)
      (<{(t , s) : I * J | ψ t /\ ζ s} -> X t s [(ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)]>)
   := (\ g (t , s) -> (g t) s , -- the one way map
         ((\ h t s -> h (t , s) -- its retraction
            ,\ g -> refl) , -- the retracting homotopy
         (\ h t s -> h (t , s) -- its section
            ,\ h -> refl)))  -- the section homotopy

#def uncurry-opcurry
   (I J : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (ζ : J -> TOPE)
   (χ : ζ -> TOPE)
   (X : ψ -> ζ -> U)
   (f : <{(t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s >)
   : Equiv (<{(t , s) : I * J | ψ t /\ ζ s} -> X t s [(ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)]>)
      (<{s : J | ζ s} -> <{ t : I | ψ t} -> X t s [ ϕ t |-> f (t , s) ]> [ χ s |-> \{t : I | ψ t} -> f (t , s) ]>)
   := (\ h s t -> h (t , s) , -- the one way map
      ((\ g (t , s) -> (g s) t -- its retraction
            ,\ h -> refl) , -- the retracting homotopy
      (\ g (t , s) -> (g s) t -- its section
            ,\ g -> refl))) -- the section homotopy

#def fubini
   (I J : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (ζ : J -> TOPE)
   (χ : ζ -> TOPE)
   (X : ψ -> ζ -> U)
   (f : <{(t , s) : I * J | (ϕ t /\ ζ s) \/ (ψ t /\ χ s)} -> X t s >)
   : Equiv (<{t : I | ψ t} -> <{ s : J | ζ s} -> X t s [ χ s |-> f (t , s) ]> [ ϕ t |-> \{s : J | ζ s} -> f (t , s) ]>)
      (<{s : J | ζ s} -> <{ t : I | ψ t} -> X t s [ ϕ t |-> f (t , s) ]> [ χ s |-> \{t : I | ψ t} -> f (t , s) ]>)
   := comp-equiv
         (<{t : I | ψ t} -> <{ s : J | ζ s} -> X t s [ χ s |-> f (t , s) ]> [ ϕ t |-> \{s : J | ζ s} -> f (t , s) ]>)
         (<{(t , s) : I * J | ψ t /\ ζ s} -> X t s [(ϕ t /\ ζ s) \/ (ψ t /\ χ s) |-> f (t , s)]>)
         (<{s : J | ζ s} -> <{ t : I | ψ t} -> X t s [ ϕ t |-> f (t , s) ]> [ χ s |-> \{t : I | ψ t} -> f (t , s) ]>)
         (curry-uncurry I J ψ ϕ ζ χ X f)
         (uncurry-opcurry I J ψ ϕ ζ χ X f)
```

## Extending into Σ-types (the non-axiom of choice)

```rzk
-- [RS17, Theorem 4.3]
#def axiom-choice
   (I : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (X : ψ -> U)
   (Y : (t : ψ) -> (x : X t) -> U)
   (a : (t : ϕ) -> X t)
   (b : (t : ϕ) -> Y t (a t))
   : Equiv (<{t : I | ψ t} -> (Σ (x : X t) , Y t x) [ ϕ t |-> (a t , b t) ]>)
     (Σ (f : (<{t : I | ψ t} -> X t [ϕ t |-> a t ]>)) , (<{t : I | ψ t} -> Y t (f t) [ ϕ t |-> b t ]>))
     := (\ g -> (\ t -> (first (g t)) , \ t -> second (g t)) , -- the one way map
            ((\ h t -> ((first h) t , (second h) t) -- its retraction
            , \ g -> refl) , -- the retracting homotopy
            (\ h t -> ((first h) t , (second h) t) -- its section
            , \ h -> refl))) -- the section homotopy
```

## Composites and unions of cofibrations

```rzk
-- [RS17, Theorem 4.4]
-- Reformulated via tope disjunction instead of inclusion.
-- See https://github.com/fizruk/rzk/issues/8
#def cofibration-composition'
   (I : CUBE)
   (χ ψ ϕ : I -> TOPE)
   (X : χ -> U)
   (a : <{t : I | χ t /\ ψ t /\ ϕ t} -> X t >)
   : Equiv <{t : I | χ t} -> X t [ χ t /\ ψ t /\ ϕ t |-> a t ]>
       (Σ (f : <{t : I | χ t /\ ψ t} -> X t [ χ t /\ ψ t /\ ϕ t |-> a t ]>) ,
          <{t : I | χ t} -> X t [ χ t /\ ψ t |-> f t ]>)
  := (\ h -> (\ t -> h t ,
             \ t -> h t) ,
      ((\ fg t -> (second fg) t , \ h -> refl) ,
      ((\ fg t -> (second fg) t , \ h -> refl))))

-- [RS17, Theorem 4.4]
-- original form
#def cofibration-composition
   (I : CUBE)
   (χ : I -> TOPE)
   (ψ : χ -> TOPE)
   (ϕ : ψ -> TOPE)
   (X : χ -> U)
   (a : (t : ϕ) -> X t)
   : Equiv <{t : I | χ t} -> X t [ ϕ t |-> a t ]>
      (Σ (f : <{t : I | ψ t} -> X t [ ϕ t |-> a t ]>) ,
          <{t : I | χ t} -> X t [ ψ t |-> f t ]>)
   := (\ h -> (\ t -> h t ,
             \ t -> h t) ,
      ((\ fg t -> (second fg) t , \ h -> refl) ,
      ((\ fg t -> (second fg) t , \ h -> refl))))

-- [RS17, Theorem 4.5]
#def cofibration_union
   (I : CUBE)
   (ϕ ψ : I -> TOPE)
   (X : <{t : I | ϕ t \/ ψ t} -> U >)
   (a : (t : ψ) -> X t)
   : Equiv <{t : I | ϕ t \/ ψ t} -> X t [ ψ t |-> a t ]>
       <{t : I | ϕ t} -> X t [ ϕ t /\ ψ t |-> a t ]>
  := (\ h -> \ t -> h t ,
      ((\ g -> \ t -> recOR (ϕ t |-> g t , ψ t |-> a t) , \ h -> refl) ,
       (\ g -> \ t -> recOR (ϕ t |-> g t , ψ t |-> a t) , \ h -> refl)))
```

## Relative function extensionality

There are various equivalent forms of the relative function extensionality
axiom. Here we state the one that will be most useful and derive an application.

```rzk
#def ext-htpy-eq
      (I : CUBE)
      (ψ : I -> TOPE)
      (ϕ : ψ -> TOPE)
      (A : ψ -> U)
      (a : (t : ϕ) -> A t)
      (f g : <{t : I | ψ t} -> A t [ ϕ t |-> a t ]>)
      (p : f = g)
      : <{t : I | ψ t} -> (f t = g t) [ ϕ t |-> refl ]>
      := idJ (<{t : I | ψ t} -> A t [ ϕ t |-> a t ]> , f ,
               \ g' p' -> <{t : I | ψ t} -> (f t = g' t) [ ϕ t |-> refl ]> ,
               \ t -> refl ,
               g ,
               p)

-- [RS17, Proposition 4.8(ii)]
-- as suggested by footnote 8, we assert this as an "extension extensionality" axiom
-- The type that encodes the extension extensionality axiom.
#def ExtExt : U
   := (I : CUBE) ->
      (ψ : I -> TOPE) ->
      (ϕ : ψ -> TOPE) ->
      (A : ψ -> U) ->
      (a : (t : ϕ) -> A t) ->
      (f : <{t : I | ψ t} -> A t [ ϕ t |-> a t ]>) ->
      (g : <{t : I | ψ t} -> A t [ ϕ t |-> a t ]>) ->
      is-equiv (f = g) (<{t : I | ψ t} -> (f t = g t) [ ϕ t |-> refl ]>)
         (ext-htpy-eq I ψ ϕ A a f g)

-- The equivalence provided by extension extensionality.
#def ExtExtEquiv
   (extext : ExtExt)
   (I : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (A : ψ -> U)
   (a : (t : ϕ) -> A t)
   (f g : <{t : I | ψ t} -> A t [ ϕ t |-> a t ]>)
   : Equiv (f = g) (<{t : I | ψ t} -> (f t = g t) [ ϕ t |-> refl ]>)
   := (ext-htpy-eq I ψ ϕ A a f g , extext I ψ ϕ A a f g)

-- In particular, extension extensionality implies that homotopies give rise to identifications. This definition defines eq-ext-htpy to be the retraction to ext-htpy-eq.
#def eq-ext-htpy
   (extext : ExtExt)
   (I : CUBE)
   (ψ : I -> TOPE)
   (ϕ : ψ -> TOPE)
   (A : ψ -> U)
   (a : (t : ϕ) -> A t)
   (f g : <{t : I | ψ t} -> A t [ ϕ t |-> a t ]>)
   : (<{t : I | ψ t} -> (f t = g t) [ ϕ t |-> refl ]>) -> (f = g)
   := first (first (extext I ψ ϕ A a f g))
```

By extension extensionality, fiberwise equivalences of extension types define
equivalences of extension types.

```rzk
-- A fiberwise equivalence defines an equivalence of extension types, for simplicity extending from BOT
#def fibered-Eq-extension-Equiv
   (extext : ExtExt)
   (I : CUBE)
   (ψ : I -> TOPE)
   (A B : ψ -> U)
   (fibequiv : (t : ψ) -> (Equiv (A t) (B t)) )
   : Equiv (<{t : I | ψ t } -> A t >) (<{t : I | ψ t } -> B t >)
   := ((\ a t -> (first (fibequiv t)) (a t)) ,
         (((\ b t -> (first (first (second (fibequiv t)))) (b t)) ,
            \ a -> eq-ext-htpy
                     extext
                     I
                     ψ
                     (\ t -> BOT)
                     A
                     (\ u -> recBOT)
                     (\ t -> (first (first (second (fibequiv t)))) ((first (fibequiv t)) (a t)))
                     a
                     (\ t -> (second (first (second (fibequiv t)))) (a t))) ,
         ((\ b t -> (first (second (second (fibequiv t)))) (b t)) ,
            (\ b -> eq-ext-htpy
                     extext
                     I
                     ψ
                     (\ t -> BOT)
                     B
                     (\ u -> recBOT)
                     (\ t -> (first (fibequiv t)) ((first (second (second (fibequiv t)))) (b t)))
                     b
                     (\ t -> (second (second (second (fibequiv t)))) (b t))))))
```
