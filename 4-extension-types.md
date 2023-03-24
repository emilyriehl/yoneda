# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Commutation of arguments and currying

To be done.

## Extending into ∑-types (the non-axiom of choice)

To be done.

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

To be done.