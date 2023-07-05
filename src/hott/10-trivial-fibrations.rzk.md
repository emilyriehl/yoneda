# 10. Trivial Fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

In what follows we show that the projection from the total space of a sigma type
is an equivalence if and only if its fibers are contractible.

```rzk
#def total-space-projection
  (A : U)
  (B : A -> U)
  : (Σ (x : A) , B x) -> A
  := \ z -> first z
```

## Contractible fibers

The following type asserts that the fibers of a type family are contractible.

```rzk
#def contractible-fibers
  (A : U)
  (B : A -> U)
  : U
  := ((x : A) -> is-contr (B x))

#section contractible-fibers-data

#variable A : U
#variable B : A -> U
#variable ABcontrfib : contractible-fibers A B

-- The center of contraction in a contractible fibers
#def contractible-fibers-section
  : (x : A) -> B x
  := \ x -> contraction-center (B x) (ABcontrfib x)

-- The section of the total space projection built from the contraction centers
#def contractible-fibers-actual-section uses (ABcontrfib)
  : (a : A) -> Σ (x : A) , B x
  := \ a -> (a , contractible-fibers-section a)

#def contractible-fibers-section-htpy uses (ABcontrfib)
  : homotopy A A
    ( composition A (Σ (x : A) , B x) A
      ( total-space-projection A B) (contractible-fibers-actual-section))
    ( identity A)
  := \ x -> refl

#def contractible-fibers-section-is-section uses (ABcontrfib)
  : has-section (Σ (x : A) , B x) A (total-space-projection A B)
  := ( contractible-fibers-actual-section , contractible-fibers-section-htpy)

-- This can be used to define the retraction homotopy for the total space projection, called "first" here
#def contractible-fibers-retraction-htpy
  : (z : Σ (x : A) , B x) ->
      (contractible-fibers-actual-section) (first z) = z
  := \ z ->
      sigma-path-fibered-path A B
        ( first z)
        ( (contractible-fibers-section) (first z))
        ( second z)
        ( contracting-htpy (B (first z)) (ABcontrfib (first z)) (second z))

#def contractible-fibers-retraction uses (ABcontrfib)
  : has-retraction (Σ (x : A) , B x) A (total-space-projection A B)
  := (contractible-fibers-actual-section , contractible-fibers-retraction-htpy)

-- The first half of our main result:
#def is-equiv-projection-contractible-fibers uses (ABcontrfib)
  : is-equiv (Σ (x : A) , B x) A (total-space-projection A B)
  := (contractible-fibers-retraction , contractible-fibers-section-is-section)

#def equiv-projection-contractible-fibers uses (ABcontrfib)
  : Equiv (Σ (x : A) , B x) A
  := (total-space-projection A B , is-equiv-projection-contractible-fibers)

#end contractible-fibers-data
```

## Projection equivalences

```rzk
-- From a projection equivalence, it's not hard to inhabit fibers
#def inhabited-fibers-is-equiv-projection
  (A : U)
  (B : A -> U)
  (ABprojequiv : is-equiv (Σ (x : A) , B x) A (total-space-projection A B))
  (a : A)
  : B a
  :=
    transport A B (first ((first (second ABprojequiv)) a)) a
      ( (second (second ABprojequiv)) a)
      ( second ((first (second ABprojequiv)) a))

-- This is great but we need more coherence to show that the inhabited fibers
-- are contractible; the following proof fails
-- #def is-equiv-projection-implies-contractible-fibers
--    (A : U)
--    (B : A -> U)
--    (ABprojequiv : is-equiv (Σ (x : A) , B x) A (total-space-projection A B))
--    : contractible-fibers A B
--    :=
--      \ x -> (second ((first (first ABprojequiv)) x) ,
--      \ u -> second-path-Σ A B ((first (first ABprojequiv)) x) (x , u)
--             ( (second (first ABprojequiv)) (x , u)) )

#section projection-hae-data
#variable A : U
#variable B : A -> U
#variable ABprojHAE :
  is-half-adjoint-equiv (Σ (x : A) , B x) A (total-space-projection A B)
#variable w : (Σ (x : A) , B x)

-- We start over from a stronger hypothesis of a half adjoint equivalence
#def projection-hae-inverse
  (a : A)
  : Σ (x : A) , B x
  := (first (first ABprojHAE)) a

#def projection-hae-base-htpy uses (B)
  (a : A)
  : (first (projection-hae-inverse a)) = a
  := (second (second (first ABprojHAE))) a

#def projection-hae-section uses (ABprojHAE)
  (a : A)
  : B a
  := transport A B (first (projection-hae-inverse a)) a
      ( projection-hae-base-htpy a)
      ( second (projection-hae-inverse a))

#def projection-hae-total-htpy
  : (projection-hae-inverse (first w)) = w
  := (first (second (first ABprojHAE))) w

#def projection-hae-fibered-htpy
  : (transport A B (first ((projection-hae-inverse (first w)))) (first w)
    ( first-path-Σ A B
      ( projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
    ( second (projection-hae-inverse (first w)))) =
    ( second w)
  := second-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy)

#def projection-hae-base-coherence
  : ( projection-hae-base-htpy (first w)) =
    ( first-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
  := (second ABprojHAE) w

#def projection-hae-transport-coherence
  : ( projection-hae-section (first w)) =
    ( transport A B (first ((projection-hae-inverse (first w)))) (first w)
      ( first-path-Σ A B
        ( projection-hae-inverse (first w)) w
        ( projection-hae-total-htpy))
      ( second (projection-hae-inverse (first w))))
  :=
    transport2 A B (first (projection-hae-inverse (first w))) (first w)
    ( projection-hae-base-htpy (first w))
    ( first-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
    ( projection-hae-base-coherence)
    ( second (projection-hae-inverse (first w)))

#def projection-hae-fibered-contracting-htpy
  : (projection-hae-section (first w)) =_{B (first w)} (second w)
  :=
    concat (B (first w))
      ( projection-hae-section (first w))
      ( transport A B
        ( first ((projection-hae-inverse (first w))))
        ( first w)
        ( first-path-Σ A B (projection-hae-inverse (first w)) w
          ( projection-hae-total-htpy))
        ( second (projection-hae-inverse (first w))))
      ( second w)
      ( projection-hae-transport-coherence)
      ( projection-hae-fibered-htpy)

#end projection-hae-data

-- Finally we have
#def contractible-fibers-is-half-adjoint-equiv-projection
  (A : U)
  (B : A -> U)
  (ABprojHAE : is-half-adjoint-equiv (Σ (x : A) , B x) A (total-space-projection A B))
  : contractible-fibers A B
  :=
    \ x ->
      ( (projection-hae-section A B ABprojHAE x) ,
        \ u -> (projection-hae-fibered-contracting-htpy A B ABprojHAE (x , u)))

-- The converse to our first result
#def contractible-fibers-is-equiv-projection
  (A : U)
  (B : A -> U)
  (ABprojequiv : is-equiv (Σ (x : A) , B x) A (total-space-projection A B))
  : contractible-fibers A B
  :=
    contractible-fibers-is-half-adjoint-equiv-projection A B
      ( is-half-adjoint-equiv-is-equiv (Σ (x : A) , B x) A
        ( total-space-projection A B) ABprojequiv)

-- The main theorem
#def projection-theorem
  (A : U)
  (B : (a : A) -> U)
  : iff
    ( is-equiv (Σ (x : A) , B x) A (total-space-projection A B))
    ( contractible-fibers A B)
  :=
    ( \ ABprojequiv -> contractible-fibers-is-equiv-projection A B ABprojequiv ,
      \ ABcontrfib -> is-equiv-projection-contractible-fibers A B ABcontrfib)
```
