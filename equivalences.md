#lang rzk-1

-- some path algebra that we need here

-- path reversal
#def rev : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) 
  -> idJ(A, x, \z -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

-- path composition by induction on the second path
#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

-- application of functions to paths
#def ap : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (x : A) -> B) -> (p : x =_{A} y) -> (f x =_{B} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (f x =_{B} f y'), refl_{f x : B}, y, p)

-- transport in a type family along a path in the base
#def transport : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (u : B x) -> B y
  := \A -> \B -> \x -> \y -> \p -> \u -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> B y', u, y, p)

#def transport2 : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (q : x =_{A} y) 
  -> (H : p =_{x =_{A} y} q) -> (u : B x) -> (transport A B x y p u) =_{B y} (transport A B x y q u)
  := \A -> \B -> \x -> \y -> \p -> \q -> \H -> \u -> idJ(x =_{A} y, p, \q' -> \H' -> (transport A B x y p u) =_{B y} (transport A B x y q' u), refl_{transport A B x y p u : B y}, q, H)  

-- homotopies

#def homotopy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> U
    := \A -> \B -> \f -> \g -> (a : A) -> (f a =_{B} g a)
    
#def homotopy-rev : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (_ : homotopy A B f g) -> homotopy A B g f
    := \A -> \B -> \f -> \g -> \H -> \a -> rev B (f a) (g a) (H a)

#def homotopy-composition : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> (h : (_ : A) -> B)
    -> (H : homotopy A B f g) -> (K : homotopy A B g h) -> homotopy A B f h
    := \A -> \B -> \f -> \g -> \h -> \H -> \K -> \a -> concat B (f a) (g a) (h a) (H a) (K a)

-- homotopies of dependent functions
#def dhomotopy : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) -> U  
    := \A -> \B -> \f -> \g -> (a : A) -> (f a =_{B a} g a)

#def dhomotopy-rev : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) 
    -> (_ : dhomotopy A B f g) -> dhomotopy A B g f
    := \A -> \B -> \f -> \g -> \H -> \a -> rev (B a) (f a) (g a) (H a)

-- we define this in the path composition order
#def dhomotopy-composition : (A : U) -> (B : (a : A) -> U) -> (f : (a : A) -> B a) -> (g : (a : A) -> B a) -> (h : (a : A) -> B a)
    -> (H : dhomotopy A B f g) -> (K : dhomotopy A B g h) -> dhomotopy A B f h
    := \A -> \B -> \f -> \g -> \h -> \H -> \K -> \a -> concat (B a) (f a) (g a) (h a) (H a) (K a)

-- for simplicity, we define these for non-dependent functions
-- for some reason this fails with dhomotopy used for non-dependent functions
#def homotopy-postwhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (H : homotopy A B f g) -> (h : (_ : B) -> C) -> homotopy A C (\(x : A) -> h (f x)) (\(x : A) -> h (g x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> ap B C (f a) (g a) h (H a)

#def homotopy-prewhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : B) -> C) -> (g : (_ : B) -> C) 
    -> (H : homotopy B C f g) -> (h : (_ : A) -> B) -> homotopy A C (\(x : A) -> f (h x)) (\(x : A) -> g (h x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> H (h a)

#def isContr : (A : U) -> U
  := \(A : U) -> ∑ (x : A), (y : A) -> x =_{A} y

#def contraction-center : (A : U) -> (_ : isContr A) -> A
  := \(A : U) -> \Aiscontr -> (first Aiscontr)

#def contracting-htpy : (A : U) -> (Aiscontr : isContr A) -> (z : A) -> (contraction-center A Aiscontr) =_{A} z
  := \A -> \Aiscontr -> second Aiscontr

#def prod : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (x : A), B

-- defined to illustrate the syntax for terms in sigma types
#def diagonal : (A : U) -> (_ : A) -> prod A A
  := \A -> \a -> (a , a)

#def hasSection : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \A -> \B -> \f -> ∑ (s : (_ : B) -> A), (b : B) -> (f (s b)) =_{B} b 

#def hasRetraction : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \A -> \B -> \f -> ∑ (r : (_ : B) -> A), (a : A) -> (r (f a)) =_{A} a 

-- incoherent equivalences   
#def hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> ∑ (g : (_ : B) -> A), (prod ((x : A) -> (g (f x)) =_{A} x)) ((y : B) -> (f (g y)) =_{B} y)
 
#def hasInverse-inverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fhasinverse -> first (fhasinverse)

-- equivalences are bi-invertible maps
#def isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> prod (hasRetraction A B f) (hasSection A B f)

#def isEquiv-section : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fisequiv -> (first (second fisequiv))

#def isEquiv-retraction : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fisequiv -> (first (first fisequiv))

#def isEquiv-htpic-inverses : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fisequiv : isEquiv A B f) 
    -> homotopy B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv)
    := \A -> \B -> \f -> \fisequiv -> homotopy-composition B A (isEquiv-section A B f fisequiv) (\x -> (isEquiv-retraction A B f fisequiv) (f ((isEquiv-section A B f fisequiv) x))) (isEquiv-retraction A B f fisequiv) 
    (homotopy-rev B A (\x -> ((isEquiv-retraction A B f fisequiv) (f ((isEquiv-section A B f fisequiv) x)))) (isEquiv-section A B f fisequiv)
    (homotopy-prewhisker B A A(\x -> (isEquiv-retraction A B f fisequiv) (f x)) (\x -> x) (second (first fisequiv)) (isEquiv-section A B f fisequiv)))
    (homotopy-postwhisker B B A (\x -> f ((isEquiv-section A B f fisequiv) x)) (\x -> x) (second (second fisequiv)) (isEquiv-retraction A B f fisequiv))

#def hasInverse-isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> isEquiv A B f
  := \A -> \B -> \f -> \fhasinverse -> ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

#def isEquiv-hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> hasInverse A B f 
    := \A -> \B -> \f -> \fisequiv -> (first (second fisequiv), 
    (homotopy-composition A A (\x -> ((isEquiv-section A B f fisequiv) (f x))) (\x -> ((isEquiv-retraction A B f fisequiv) (f x))) (\x -> x)  (homotopy-prewhisker A B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv) (isEquiv-htpic-inverses A B f fisequiv) f) second (first fisequiv) , second (second  fisequiv)))

#def hasInverse-triple-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : A) -> B
    := \A -> \B -> \f -> \fhasinverse -> \a -> f ((hasInverse-inverse A B f fhasinverse) (f a))

#def hasInverse-retraction-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : A) -> A
    := \A -> \B -> \f -> \fhasinverse -> \a -> (hasInverse-inverse A B f fhasinverse) (f a) 

#def hasInverse-section-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : B) -> B
    := \A -> \B -> \f -> \fhasinverse -> \b -> f ((hasInverse-inverse A B f fhasinverse) b)

#def weird-but-fine : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
    := \A -> \B -> \f 
        -> ∑ (fhasinverse : (hasInverse A B f)), (hasInverse-inverse A B f fhasinverse) =_{(_ : B) -> A} (hasInverse-inverse A B f fhasinverse)

#def weird-but-fails : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
     := \A -> \B -> \f 
        -> ∑ (fhasinverse : (hasInverse A B f)), (hasInverse-inverse A B f fhasinverse) =_{(_ : B) -> A} (first fhasinverse)

-- #def isHalfAdjointEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
--     := \A -> \B -> \f 
--         -> ∑ (fhasinverse : (hasInverse A B f)), ((homotopy-prewhisker A B B (hasInverse-section-composite A B f fhasinverse)
--    (\b -> b) (second (second fhasinverse)) f)
--     =_{homotopy A B (hasInverse-triple-composite A B f fhasinverse) f} 
--     ((homotopy-postwhisker A A B (hasInverse-retraction-composite A B f fhasinverse) (\a -> a) (first (second fhasinverse)) f)))

-- the type of equivalences between types
#def Eq : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (f : (_ : A) -> B), ((isEquiv A) B) f

-- the type of logical equivalences between types
#def iff : (A : U) -> (B : U) -> U
  := \A -> \B -> prod ((_ : A) -> B) ((_ : B) -> A)

#def total-space-projection : (A : U) -> (B : (a : A) -> U) -> (_ : ∑ (x : A), B x) -> A
  := \A -> \B -> \z -> first z

#def contractible-fibers : (A : U) -> (B : (a : A) -> U) -> U
  := \A -> \B -> ((x : A) -> isContr (B x))

#def contractible-fibers-section : (A : U) -> (B : (a : A) -> U) 
    -> (_ : contractible-fibers A B) -> (x : A) -> B x
  := \A -> \B -> \ABcontrfib -> \x -> contraction-center (B x) (ABcontrfib x)

#def contractible-fibers-actual-section : (A : U) -> (B : (a : A) -> U) 
    -> (_ : contractible-fibers A B) -> (x : A) -> ∑ (x : A), B x
  := \A -> \B -> \ABcontrfib -> \x -> (x , contractible-fibers-section A B ABcontrfib x)

#def contractible-fibers-section-htpy : (A : U) -> (B : (a : A) -> U)
        -> (ABcontrfib : contractible-fibers A B) -> (x : A) -> ((total-space-projection A B) ((contractible-fibers-actual-section A B ABcontrfib) (x))) =_{A} x
    := \A -> \B -> \ABcontrfib -> \x -> refl_{x : A}

#def contractible-fibers-section-is-section : (A : U) -> (B : (a : A) -> U)
        -> (_ : contractible-fibers A B) -> hasSection (∑ (x : A), B x) A (total-space-projection A B)
    := \A -> \B -> \ABcontrfib -> (contractible-fibers-actual-section A B ABcontrfib , contractible-fibers-section-htpy A B  ABcontrfib)

-- judgmental eta rules
#def check : (A : U) -> (B : (a : A) -> U) -> (z : ∑ (x : A), B x) -> (z =_{∑ (x : A), B x} (first z, second z))
    := \A -> \B -> \z -> refl_{z : ∑ (x : A), B x}

#def fibered-path-to-sigma-path : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (u : B x) -> (v : B x) -> (p : u =_{B x} v) 
    -> (x , u) =_{∑ (a : A), B a} (x , v)
    := \A -> \B -> \x -> \u -> \v -> \p -> idJ(B x, u, \v' -> \p' -> (x , u) =_{∑ (a : A), B a} (x , v'), refl_{(x , u) : ∑ (a : A), B a}, v, p)

#def contractible-fibers-retraction-htpy : (A : U) -> (B : (a : A) -> U)
        -> (ABcontrfib : contractible-fibers A B) -> (z : ∑ (x : A), B x) -> ((contractible-fibers-actual-section A B ABcontrfib) (first z)) =_{∑ (x : A), B x} z
     := \A -> \B -> \ABcontrfib -> \z -> fibered-path-to-sigma-path A B (first z) ((contractible-fibers-section A B ABcontrfib) (first z)) (second z) (contracting-htpy (B (first z)) (ABcontrfib (first z)) (second z))

#def contractible-fibers-retraction : (A : U) -> (B : (a : A) -> U)
        -> (_ : contractible-fibers A B) -> hasRetraction (∑ (x : A), B x) A (total-space-projection A B)
    := \A -> \B -> \ABcontrfib -> (contractible-fibers-actual-section A B ABcontrfib , contractible-fibers-retraction-htpy A B  ABcontrfib)

#def contractible-fibers-implies-projection-equiv : (A : U) -> (B : (a : A) -> U) 
    -> (_ : contractible-fibers A B) -> isEquiv (∑ (x : A), B x) A (total-space-projection A B)
  := \A -> \B -> \ABcontrfib -> (contractible-fibers-retraction A B ABcontrfib , contractible-fibers-section-is-section A B ABcontrfib)

#def total-path-to-base-path : (A : U) -> (B : (a : A) -> U) -> (z : ∑ (a : A), B a) -> (w : ∑ (a : A), B a) 
    -> (p : z =_{∑ (a : A), B a} w) -> ((first z) =_{A} first w)
    := \A -> \B -> \z -> \w -> \p -> ap (∑ (a : A), B a) A z w (total-space-projection A B) p 

#def total-path-to-fibered-path : (A : U) -> (B : (a : A) -> U) -> (z : ∑ (a : A), B a) -> (w : ∑ (a : A), B a) 
    -> (p : z =_{∑ (a : A), B a} w) -> (transport A B (first z) (first w) (total-path-to-base-path A B z w p) (second z)) =_{B (first w)} (second w)
    := \A -> \B -> \z -> \w -> \p -> idJ((∑ (a : A), B a), z, \w' -> \p' -> (transport A B (first z) (first w') (total-path-to-base-path A B z w' p') (second z)) =_{B (first w')} (second w'), refl_{second z : B (first z)}, w, p)

#def projection-equiv-implies-inhabited-fibers : (A : U) -> (B : (a : A) -> U) 
    -> (_ : isEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> (x : A) -> B x
    := \A -> \B -> \ABprojequiv -> \x -> transport A B (first ((first (second ABprojequiv)) x)) x ((second (second ABprojequiv)) x) (second ((first (second ABprojequiv)) x))
    
-- #def projection-equiv-implies-contractible-fibers : (A : U) -> (B : (a : A) -> U) 
--    -> (_ : isEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> contractible-fibers A B
--    := \A -> \B -> \ABprojequiv -> \x -> (second ((first (first ABprojequiv)) x) , 
--    \(u : B x) -> total-path-to-fibered-path A B ((first (first ABprojequiv)) x) (x, u) ((second (first ABprojequiv)) (x, u)) )