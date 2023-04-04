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
   : (I : CUBE) ->
      (psi : (t : I) -> TOPE) ->
      (phi : {(t : I) | psi t} -> TOPE) ->
      (X : U) ->
      (Y : <{t : I | psi t } -> (x : X) -> U >) ->
      (f : <{t : I | phi t } -> (x : X) -> Y t x >) ->
      Eq (<{t : I | psi t} -> (x : X) -> Y t x [ phi t |-> f t ]>)
       ((x : X) -> <{t : I | psi t} -> Y t x [ phi t |-> f t x]>)
   := \I -> \psi -> \phi -> \X -> \Y -> \f -> 
         (\g -> \x -> \{t : I | psi t} -> g t x, -- the one-way map; needs the context for t to typecheck
            ((\h -> \{t : I | psi t} -> \x -> (h x) t, -- the retraction
            \g -> refl_{g}), -- the retracting homotopy
            (\h -> \{t : I | psi t} -> \x -> (h x) t, -- the section
            \h -> refl_{h})))

#def flip-ext-fun-inv 
   : (I : CUBE) ->
      (psi : (t : I) -> TOPE) ->
      (phi : {(t : I) | psi t} -> TOPE) ->
      (X : U) ->
      (Y : <{t : I | psi t } -> (x : X) -> U >) ->
      (f : <{t : I | phi t } -> (x : X) -> Y t x >) ->
      Eq ((x : X) -> <{t : I | psi t} -> Y t x [ phi t |-> f t x]>)
      (<{t : I | psi t} -> (x : X) -> Y t x [ phi t |-> f t ]>)
   := \I -> \psi -> \phi -> \X -> \Y -> \f -> 
         (\h -> \{t : I | psi t} -> \x -> (h x) t, -- the one-way map
            ((\g -> \x -> \{t : I | psi t} -> g t x, -- the retraction
            \h -> refl_{h}), -- the retracting homotopy
            (\g -> \x -> \{t : I | psi t} -> g t x, -- the section
            \g -> refl_{g})))

-- [RS17, Theorem 4.2]
#def curry-uncurry :
   (I : CUBE) ->
   (J : CUBE) ->
   (psi : (t : I) -> TOPE) -> 
   (phi : {(t : I) | psi t} -> TOPE) ->
   (zeta : (s : J) -> TOPE) ->
   (chi : {(s : J) | zeta s} -> TOPE) ->   
   (X : <{t : I | psi t} -> <{s : J | zeta s} -> U > >) ->
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >) ->
   Eq (<{t : I | psi t} -> <{ s : J | zeta s} -> X t s [ chi s |-> f (t, s) ]> [ phi t |-> \{s : J | zeta s} -> f (t, s) ]>)
      (<{(t, s) : I * J | psi t /\ zeta s} -> X t s [(phi t /\ zeta s) \/ (psi t /\ chi s) |-> f (t , s)]>)
   := \I -> \J -> \psi -> \phi -> \zeta -> \chi -> \X -> \f -> 
      (\g -> \{(t, s) : I * J | psi t /\ zeta s} -> (g t) s, -- the one way map
         ((\h -> \{t : I | psi t} -> \{ s : J | zeta s} -> h (t , s) -- its retraction
            ,\g -> refl_{g} ), -- the retracting homotopy 
         (\h -> \{t : I | psi t} -> \{ s : J | zeta s} -> h (t , s) -- its section
            ,\h -> refl_{h})))  -- the section homotopy

#def uncurry-opcurry :
   (I : CUBE) ->
   (J : CUBE) ->
   (psi : (t : I) -> TOPE) -> 
   (phi : {(t : I) | psi t} -> TOPE) ->
   (zeta : (s : J) -> TOPE) ->
   (chi : {(s : J) | zeta s} -> TOPE) ->   
   (X : <{t : I | psi t} -> <{s : J | zeta s} -> U > >) ->
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >) ->
   Eq (<{(t, s) : I * J | psi t /\ zeta s} -> X t s [(phi t /\ zeta s) \/ (psi t /\ chi s) |-> f (t , s)]>) 
      (<{s : J | zeta s} -> <{ t : I | psi t} -> X t s [ phi t |-> f (t, s) ]> [ chi s |-> \{t : I | psi t} -> f (t, s) ]>)
   := \I -> \J -> \psi -> \phi -> \zeta -> \chi -> \X -> \f -> 
      (\h -> \{s : J | zeta s} -> \{t : I | psi t} -> h (t , s) , -- the one way map
      ((\g -> \{(t, s) : I * J | psi t /\ zeta s} -> (g s) t -- its retraction
            ,\h -> refl_{h} ), -- the retracting homotopy 
      (\g -> \{(t, s) : I * J | psi t /\ zeta s} -> (g s) t -- its section
            ,\g -> refl_{g}))) -- the section homotopy

#def fubini : 
   (I : CUBE) ->
   (J : CUBE) ->
   (psi : (t : I) -> TOPE) -> 
   (phi : {(t : I) | psi t} -> TOPE) ->
   (zeta : (s : J) -> TOPE) ->
   (chi : {(s : J) | zeta s} -> TOPE) ->   
   (X : <{t : I | psi t} -> <{s : J | zeta s} -> U > >) ->
   (f : <{(t, s) : I * J | (phi t /\ zeta s) \/ (psi t /\ chi s)} -> X t s >) ->
   Eq (<{t : I | psi t} -> <{ s : J | zeta s} -> X t s [ chi s |-> f (t, s) ]> [ phi t |-> \{s : J | zeta s} -> f (t, s) ]>)
      (<{s : J | zeta s} -> <{ t : I | psi t} -> X t s [ phi t |-> f (t, s) ]> [ chi s |-> \{t : I | psi t} -> f (t, s) ]>)
   := \I -> \J -> \psi -> \phi -> \zeta -> \chi -> \X -> \f 
      -> compose_Eq
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
   : (I : CUBE) ->
     (psi : (t : I) -> TOPE) ->
     (phi : {(t : I) | psi t} -> TOPE) ->
     (X : <{t : I | psi t} -> U >) ->
     (Y : <{t : I | psi t} -> (x : X t) -> U >) ->
     (a : <{t : I | phi t} -> X t >) ->
     (b : <{t : I | phi t} -> Y t (a t) >) ->
     Eq (<{t : I | psi t} -> (∑ (x : X t), Y t x) [ phi t |-> (a t , b t) ]>) 
     (∑ (f : (<{t : I | psi t} -> X t [phi t |-> a t ]>)), (<{t : I | psi t} -> Y t (f t) [ phi t |-> b t ]>)) 
     := \I -> \psi -> \phi -> \X -> \Y -> \a -> \b -> 
         (\g -> (\{t : I | psi t} -> (first (g t)), \{t : I | psi t} -> second (g t))  , -- the one way map
            ((\h -> \{t : I | psi t} -> ((first h) t, (second h) t) -- its retraction
            , \g -> refl_{g}), -- the retracting homotopy
            (\h -> \{t : I | psi t} -> ((first h) t, (second h) t) -- its section
            , \h -> refl_{h}))) -- the section homotopy
```

## Composites and unions of cofibrations

```rzk
-- [RS17, Theorem 4.4]
-- Reformulated via tope disjunction instead of inclusion.
-- See https://github.com/fizruk/rzk/issues/8
#def cofibration_composition'
  : (I : CUBE) ->
    (chi : (t : I) -> TOPE) ->
    (psi : (t : I) -> TOPE) ->
    (phi : (t : I) -> TOPE) ->
    (X : <{t : I | chi t} -> U >) ->
    (a : <{t : I | chi t /\ psi t /\ phi t} -> X t >) ->
    Eq <{t : I | chi t} -> X t [ chi t /\ psi t /\ phi t |-> a t ]>
       (∑ (f : <{t : I | chi t /\ psi t} -> X t [ chi t /\ psi t /\ phi t |-> a t ]>),
          <{t : I | chi t} -> X t [ chi t /\ psi t |-> f t ]>)
  := \I -> \chi -> \psi -> \phi ->
     \X -> \a ->
     (\h -> (\{t : I | chi t /\ psi t} -> h t,
             \{t : I | chi t} -> h t),
      ((\fg -> \{t : I | chi t} -> (second fg) t, \h -> refl_{h}),
      ((\fg -> \{t : I | chi t} -> (second fg) t, \h -> refl_{h}))))

-- [RS17, Theorem 4.5]
#def cofibration_union
  : (I : CUBE) ->
    (phi : (t : I) -> TOPE) ->
    (psi : (t : I) -> TOPE) ->
    (X : <{t : I | phi t \/ psi t} -> U >) ->
    (a : <{t : I | psi t} -> X t >) ->
    Eq <{t : I | phi t \/ psi t} -> X t [ psi t |-> a t ]>
       <{t : I | phi t} -> X t [ phi t /\ psi t |-> a t ]>
  := \I -> \phi -> \psi ->
     \X -> \a ->
     (\h -> \{t : I | phi t} -> h t,
      ((\g -> \{t : I | phi t \/ psi t} -> recOR(phi t, psi t, g t, a t), \h -> refl_{h}),
       (\g -> \{t : I | phi t \/ psi t} -> recOR(phi t, psi t, g t, a t), \h -> refl_{h})))
```

## Relative function extensionality

A more complete treatment still needs to be done.

```rzk
-- [RS17, Proposition 4.8(ii)]
-- as suggested by footnote 8, we assert this as an "extension extensionality" axiom
#def ExtExt : U
   := (I : CUBE) ->
      (psi : (t : I) -> TOPE) ->
      (phi : {(t : I) | psi t} -> TOPE) ->
      (A : <{t : I | psi t } -> U >) ->
      (a : <{t : I | phi t } -> A t >) ->
      (f : <{t : I | psi t} -> A t [ phi t |-> a t ]>) ->
      (g : <{t : I | psi t} -> A t [ phi t |-> a t ]>) ->
      (_ : <{t : I | psi t} -> (f t =_{A t} g t) [ phi t |-> refl_{a t} ]>) ->
      (f =_{<{t : I | psi t} -> A t [ phi t |-> a t ]>} g)


-- A fibered equivalence defines functions between extension types, for simplicity extending from BOT
#def fibered-function-function :
   (I : CUBE) ->
   (psi : (t : I) -> TOPE) ->
   (A : <{t : I | psi t } -> U >) ->
   (B : <{t : I | psi t } -> U >) ->
   (_ : <{t : I | psi t } -> ((_ : (A t)) -> (B t)) >) ->
   (a : <{t : I | psi t } -> A t >) -> (<{t : I | psi t } -> B t >)
    := \I -> \psi -> \A -> \B -> \fibfun -> \a -> 
        \{t : I | psi t } -> (fibfun t) (a t)

#def fibered-equiv-function :
   (I : CUBE) ->
   (psi : (t : I) -> TOPE) ->
   (A : <{t : I | psi t } -> U >) ->
   (B : <{t : I | psi t } -> U >) ->
   (_ : <{t : I | psi t } -> (Eq (A t) (B t)) >) ->
   (a : <{t : I | psi t } -> A t >) -> (<{t : I | psi t } -> B t >)
    := \I -> \psi -> \A -> \B -> \fibequiv -> \a -> 
        \{t : I | psi t } -> ((first (fibequiv t)) (a t))       
```        

-- A fibered equivalence defines functions between extension types, for simplicity extending from BOT
#def fibered-equiv-function-iff :
   (I : CUBE) ->
   (psi : (t : I) -> TOPE) ->
   (A : <{t : I | psi t } -> U >) ->
   (B : <{t : I | psi t } -> U >) ->
   (_ : <{t : I | psi t } -> (Eq (A t) (B t)) >) ->
   iff (<{t : I | psi t } -> A t >) (<{t : I | psi t } -> B t >)
    := \I -> \psi -> \A -> \B -> \fibequiv -> 
        ((\a -> \{t : I | psi t } -> (first (fibequiv t)) (a t)) ,
        (\b -> \{t : I | psi t } -> (first (first (second fibequiv t))) (b t)))

```

-- A fibered equivalence defines functions between dependent function types
#def fibered-equiv-function-iff :
    (X : U) -> (A : (_ : X) -> U) -> (B : (_ : X) -> U) -> (_ : (x : X) -> Eq (A x) (B x)) ->
    iff ((x : X) -> A x) ((x : X) -> B x)
    := \X -> \A -> \B -> \fibequiv -> 
        ((\a -> \x -> (first (fibequiv x)) (a x)) ,
        (\b -> \x -> (first (first (second fibequiv x))) (b x)))

-- A fiberwise equivalence defines an equivalence of dependent function types
#def fibered-equiv-function-equiv :
    (_ : FunExt) -> (X : U) -> (A : (_ : X) -> U) -> (B : (_ : X) -> U) -> (_ : (x : X) -> Eq (A x) (B x)) ->
    Eq ((x : X) -> A x) ((x : X) -> B x)
    := \funext -> \X -> \A -> \B -> \fibequiv -> 
        ((\a -> \x -> (first (fibequiv x)) (a x)),
            (((\b -> \x -> (first (first (second (fibequiv x)))) (b x)),
                \a -> funext X A (\x -> (first (first (second fibequiv x))) ((first (fibequiv x)) (a x))) a (\x -> (second (first (second (fibequiv x)))) (a x))), 
           ((\b -> \x -> (first (second (second fibequiv x))) (b x)),
            (\b -> funext X B (\x -> (first (fibequiv x)) ((first (second (second fibequiv x))) (b x))) b (\x -> (second (second (second fibequiv x))) (b x))))))