# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```
## Prerequisites

- `hott/4-equivalences.rzk` — contains the definitions of `Eq` and `compose_Eq`
- the file `hott/4-equivalences.rzk` relies in turn on the previous files in `hott/`

## Commutation of arguments and currying

```rzk
-- [RS17, Theorem 4.1]
#def flip-ext-fun 
   (I : CUBE)
   (psi : I -> TOPE)
   (phi : psi -> TOPE)
   (X : U)
   (Y : psi -> X -> U)
   (f : (t : phi) -> (x : X) -> Y t x)
   : Eq (<{t : I | psi t} -> ((x : X) -> Y t x) [ phi t |-> f t ]>)
       ((x : X) -> <{t : I | psi t} -> Y t x [ phi t |-> f t x]>)
   := (\g x t -> g t x, -- the one-way map
            ((\h t x -> (h x) t, -- the retraction
            \g -> refl), -- the retracting homotopy
            (\h t x -> (h x) t, -- the section
            \h -> refl))) -- the section homotopy

#def flip-ext-fun-inv 
   (I : CUBE)
   (psi : I -> TOPE)
   (phi : psi -> TOPE)
   (X : U)
   (Y : psi -> X -> U)
   (f : (t : phi) -> (x : X) -> Y t x)
   : Eq ((x : X) -> <{t : I | psi t} -> Y t x [ phi t |-> f t x]>)
      (<{t : I | psi t} -> ((x : X) -> Y t x) [ phi t |-> f t ]>)
   := (\h t x -> (h x) t, -- the one-way map
            ((\g x t -> g t x, -- the retraction
            \h -> refl), -- the retracting homotopy
            (\g x t -> g t x, -- the section
            \g -> refl)))

-- [RS17, Theorem 4.2]
#def curry-uncurry
   (I J : CUBE)
   (psi : I -> TOPE)
   (phi : psi -> TOPE)
   (zeta : J -> TOPE)
   (chi : zeta -> TOPE)
   (X : psi -> zeta -> U)
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >)
   : Eq (<{t : I | psi t} -> <{ s : J | zeta s} -> X t s [ chi s |-> f (t, s) ]> [ phi t |-> \{s : J | zeta s} -> f (t, s) ]>)
      (<{(t, s) : I * J | psi t /\ zeta s} -> X t s [(phi t /\ zeta s) \/ (psi t /\ chi s) |-> f (t , s)]>)
   := (\g (t, s) -> (g t) s, -- the one way map
         ((\h t s -> h (t , s) -- its retraction
            ,\g -> refl), -- the retracting homotopy 
         (\h t s -> h (t , s) -- its section
            ,\h -> refl)))  -- the section homotopy

#def uncurry-opcurry 
   (I J : CUBE)
   (psi : I -> TOPE)
   (phi : psi -> TOPE)
   (zeta : J -> TOPE)
   (chi : zeta -> TOPE)
   (X : psi -> zeta -> U)
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >)
   : Eq (<{(t, s) : I * J | psi t /\ zeta s} -> X t s [(phi t /\ zeta s) \/ (psi t /\ chi s) |-> f (t , s)]>) 
      (<{s : J | zeta s} -> <{ t : I | psi t} -> X t s [ phi t |-> f (t, s) ]> [ chi s |-> \{t : I | psi t} -> f (t, s) ]>)
   := (\h s t -> h (t , s) , -- the one way map
      ((\g (t, s) -> (g s) t -- its retraction
            ,\h -> refl), -- the retracting homotopy 
      (\g (t, s) -> (g s) t -- its section
            ,\g -> refl))) -- the section homotopy

#def fubini 
   (I J : CUBE)
   (psi : I -> TOPE)
   (phi : psi -> TOPE)
   (zeta : J -> TOPE)
   (chi : zeta -> TOPE)
   (X : psi -> zeta -> U)
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >)
   : Eq (<{t : I | psi t} -> <{ s : J | zeta s} -> X t s [ chi s |-> f (t, s) ]> [ phi t |-> \{s : J | zeta s} -> f (t, s) ]>)
      (<{s : J | zeta s} -> <{ t : I | psi t} -> X t s [ phi t |-> f (t, s) ]> [ chi s |-> \{t : I | psi t} -> f (t, s) ]>)
   := compose_Eq
         (<{t : I | psi t} -> <{ s : J | zeta s} -> X t s [ chi s |-> f (t, s) ]> [ phi t |-> \{s : J | zeta s} -> f (t, s) ]>)
         (<{(t, s) : I * J | psi t /\ zeta s} -> X t s [(phi t /\ zeta s) \/ (psi t /\ chi s) |-> f (t , s)]>)
         (<{s : J | zeta s} -> <{ t : I | psi t} -> X t s [ phi t |-> f (t, s) ]> [ chi s |-> \{t : I | psi t} -> f (t, s) ]>)
         (curry-uncurry I J psi phi zeta chi X f)
         (uncurry-opcurry I J psi phi zeta chi X f)
```

## Extending into ∑-types (the non-axiom of choice)

```rzk
-- [RS17, Theorem 4.3]
#def axiom-choice 
   (I : CUBE)
   (psi : I -> TOPE) 
   (phi : psi -> TOPE)
   (X : psi -> U) 
   (Y : (t : psi) -> (x : X t) -> U)
   (a : (t : phi) -> X t)
   (b : (t : phi) -> Y t (a t))
   : Eq (<{t : I | psi t} -> (∑ (x : X t), Y t x) [ phi t |-> (a t , b t) ]>) 
     (∑ (f : (<{t : I | psi t} -> X t [phi t |-> a t ]>)), (<{t : I | psi t} -> Y t (f t) [ phi t |-> b t ]>)) 
     := (\g -> (\t -> (first (g t)), \t -> second (g t))  , -- the one way map
            ((\h t -> ((first h) t, (second h) t) -- its retraction
            , \g -> refl), -- the retracting homotopy
            (\h t -> ((first h) t, (second h) t) -- its section
            , \h -> refl))) -- the section homotopy
```

## Composites and unions of cofibrations

```rzk
-- [RS17, Theorem 4.4]
-- Reformulated via tope disjunction instead of inclusion.
-- See https://github.com/fizruk/rzk/issues/8
#def cofibration_composition'
   (I : CUBE)
   (chi psi phi : I -> TOPE)
   (X : chi -> U)
   (a : <{t : I | chi t /\ psi t /\ phi t} -> X t >)
   : Eq <{t : I | chi t} -> X t [ chi t /\ psi t /\ phi t |-> a t ]>
       (∑ (f : <{t : I | chi t /\ psi t} -> X t [ chi t /\ psi t /\ phi t |-> a t ]>),
          <{t : I | chi t} -> X t [ chi t /\ psi t |-> f t ]>)
  := (\h -> (\t -> h t,
             \t -> h t),
      ((\fg t -> (second fg) t, \h -> refl),
      ((\fg t -> (second fg) t, \h -> refl))))

-- [RS17, Theorem 4.4]      
-- original form
#def cofibration-composition
   (I : CUBE)
   (chi : I -> TOPE) 
   (psi : chi -> TOPE)
   (phi : psi -> TOPE)
   (X : chi -> U)
   (a : (t : phi) -> X t)
   : Eq <{t : I | chi t} -> X t [ phi t |-> a t ]>
      (∑ (f : <{t : I | psi t} -> X t [ phi t |-> a t ]>),
          <{t : I | chi t} -> X t [ psi t |-> f t ]>)
   := (\h -> (\t -> h t,
             \t -> h t),
      ((\fg t -> (second fg) t, \h -> refl),
      ((\fg t -> (second fg) t, \h -> refl))))

-- [RS17, Theorem 4.5]
#def cofibration_union
   (I : CUBE)
   (phi psi : I -> TOPE)
   (X : <{t : I | phi t \/ psi t} -> U >)
   (a : (t : psi) -> X t)
   : Eq <{t : I | phi t \/ psi t} -> X t [ psi t |-> a t ]>
       <{t : I | phi t} -> X t [ phi t /\ psi t |-> a t ]>
  := (\h -> \t -> h t,
      ((\g -> \t -> recOR(phi t |-> g t, psi t |-> a t), \h -> refl),
       (\g -> \t -> recOR(phi t |-> g t, psi t |-> a t), \h -> refl)))
```

## Relative function extensionality

There are various equivalent forms of the relative function extensionality axiom. 
Here we state the one that will be most useful and derive an application.

```rzk
-- [RS17, Proposition 4.8(ii)]
-- as suggested by footnote 8, we assert this as an "extension extensionality" axiom
#def ExtExt : U
   := (I : CUBE) ->
      (psi : I -> TOPE) ->
      (phi : psi -> TOPE) ->
      (A : psi -> U) ->
      (a : (t : phi) -> A t) ->
      (f : <{t : I | psi t} -> A t [ phi t |-> a t ]>) ->
      (g : <{t : I | psi t} -> A t [ phi t |-> a t ]>) ->
      (_ : <{t : I | psi t} -> (f t = g t) [ phi t |-> refl ]>) ->
      (f = g)

-- A fiberwise equivalence defines an equivalence of extension types, for simplicity extending from BOT
#def fibered-equiv-extension-equiv 
   (extext : ExtExt)
   (I : CUBE)
   (psi : I -> TOPE)
   (A B : psi -> U)
   (fibequiv : (t : psi) -> (Eq (A t) (B t)) )
   : Eq (<{t : I | psi t } -> A t >) (<{t : I | psi t } -> B t >)
   := ((\a t -> (first (fibequiv t)) (a t)),
         (((\b t -> (first (first (second (fibequiv t)))) (b t)),
            \a -> extext
                     I
                     psi
                     (\t -> BOT)
                     A
                     (\u -> recBOT)
                     (\t -> (first (first (second (fibequiv t)))) ((first (fibequiv t)) (a t))) 
                     a 
                     (\t -> (second (first (second (fibequiv t)))) (a t))), 
         ((\b t -> (first (second (second (fibequiv t)))) (b t)),
            (\b -> extext 
                     I
                     psi
                     (\t -> BOT)
                     B 
                     (\u -> recBOT)
                     (\t -> (first (fibequiv t)) ((first (second (second (fibequiv t)))) (b t))) 
                     b 
                     (\t -> (second (second (second (fibequiv t)))) (b t))))))              
```        
