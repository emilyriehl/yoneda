#lang rzk-1

-- some path algebra that we need here

-- path reversal
#def rev : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) 
  -> idJ(A, x, \z -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

-- path composition by induction on the second path
#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

-- an alternative construction of path composition by induction on the first path
#def altconcat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (q' : y' =_{A} z) -> (x =_{A} z), \(q' : x =_{A} z) -> q', y, p)

-- the coherence we don't have definitionally
#def refl-concat : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (concat A x x y (refl_{x : A}) p) =_{x =_{A} y} p
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (concat A x x y' (refl_{x : A}) p') =_{x =_{A} y'} p', refl_{refl_{x : A} : x =_{A} x}, y, p)

#def concat-altconcat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z)
    -> (concat A x y z p q) =_{x =_{A} z} altconcat A x y z p q
    := \A -> \x -> \y -> \z -> \p -> idJ(A, x, \y' -> \p' -> (q' : y' =_{A} z) -> (concat A x y' z p' q') =_{x =_{A} z} altconcat A x y' z p' q', \q' -> refl-concat A x z q', y, p)

#def altconcat-concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z)
    -> (altconcat A x y z p q) =_{x =_{A} z} concat A x y z p q
    := \A -> \x -> \y -> \z -> \p -> \q 
    -> rev (x =_{A} z) (concat A x y z p q) (altconcat A x y z p q) (concat-altconcat A x y z p q)

#def concat-right-cancel : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : x =_{A} y) -> (r : y =_{A} z)
    -> (H : (concat A x y z p r) =_{x =_{A} z} (concat A x y z q r)) -> (p =_{x =_{A} y} q)
    := \A -> \x -> \y -> \z -> \p -> \q -> \r -> idJ(A, y, \z' -> \r' -> (H : (concat A x y z' p r') =_{x =_{A} z'} (concat A x y z' q r')) -> (p =_{x =_{A} y} q), \H -> H, z, r)    

-- prewhiskering paths of paths
#def concat-homotopy : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (z : A) -> (q : y =_{A} z) -> (r : y =_{A} z)
    -> (H : q =_{y =_{A} z} r) -> (concat A x y z p q) =_{x =_{A} z} (concat A x y z p r)
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (z : A) -> (q : y' =_{A} z) -> (r : y' =_{A} z) -> (H : q =_{y' =_{A} z} r) -> (concat A x y' z p' q) =_{x =_{A} z} (concat A x y' z p' r), \z -> \q -> \r -> \H -> concat (x =_{A} z) (concat A x x z refl_{x : A} q) r (concat A x x z refl_{x : A} r) (concat (x =_{A} z) (concat A x x z refl_{x : A} q) q r (refl-concat A x z q) H) (rev (x =_{A} z) (concat A x x z refl_{x : A} r) r (refl-concat A x z r)), y, p)

-- postwhiskering paths of paths
#def homotopy-concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : x =_{A} y) -> (H : p =_{x =_{A} y} q) 
    -> (r : y =_{A} z) -> (concat A x y z p r) =_{x =_{A} z} (concat A x y z q r)
    := \A -> \x -> \y -> \z -> \p -> \q -> \H -> \r -> idJ(A, y, \z' -> \r' -> (concat A x y z' p r') =_{x =_{A} z'} (concat A x y z' q r'), H, z, r)

#def alt-triangle-rotation : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} z) -> (q : x =_{A} y) -> (r : y =_{A} z)
  -> (H : p =_{x =_{A} z} altconcat A x y z q r) -> (altconcat A y x z (rev A x y q) p) =_{y =_{A} z} r
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, x, \y' -> \q' -> (r' : y' =_{A} z) -> (H' : p =_{x =_{A} z} altconcat A x y' z q' r') -> (altconcat A y' x z (rev A x y' q') p) =_{y' =_{A} z} r', \r' -> \H' -> H', y, q)

#def half-alt-triangle-rotation : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} z) -> (q : x =_{A} y) -> (r : y =_{A} z)
  -> (H : p =_{x =_{A} z} altconcat A x y z q r) -> (concat A y x z (rev A x y q) p) =_{y =_{A} z} r
  := \A -> \x -> \y -> \z -> \p -> \q -> \r -> \H -> concat (y =_{A} z)  (concat A y x z (rev A x y q) p)  (altconcat A y x z (rev A x y q) p) r
  (concat-altconcat A y x z (rev A x y q) p)
  (alt-triangle-rotation A x y z p q r H)

#def triangle-rotation : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} z) -> (q : x =_{A} y) -> (r : y =_{A} z)
   -> (H : p =_{x =_{A} z} concat A x y z q r) -> (concat A y x z (rev A x y q) p) =_{y =_{A} z} r
    := \A -> \x -> \y -> \z -> \p -> \q -> \r -> \H -> 
    half-alt-triangle-rotation A x y z p q r (concat (x =_{A} z) p (concat A x y z q r) (altconcat A x y z q r) H (concat-altconcat A x y z q r))

-- application of functions to paths
#def ap : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (x : A) -> B) -> (p : x =_{A} y) -> (f x =_{B} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (f x =_{B} f y'), refl_{f x : B}, y, p)

#def ap-id : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (ap A A x y (\z -> z) p) =_{x =_{A} y} p
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (ap A A x y' (\z -> z) p') =_{x =_{A} y'} p', refl_{refl_{x : A} : x =_{A} x}, y, p)

#def ap-htpy : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (_ : A) -> B) -> (p : x =_{A} y) -> (q : x =_{A} y) 
    -> (H : p =_{x =_{A} y} q) -> (ap A B x y f p) =_{f x =_{B} f y} (ap A B x y f q)
    := \A -> \B -> \x -> \y -> \f -> \p -> \q -> \H -> idJ(x =_{A} y, p, \q' -> \H' -> (ap A B x y f p) =_{f x =_{B} f y} (ap A B x y f q'), refl_{ap A B x y f p : f x =_{B} f y}, q, H)

#def ap-comp : (A : U) -> (B : U) -> (C : U) -> (x : A) -> (y : A) -> (f : (_ : A) -> B) -> (g : (_ : B) -> C) 
    -> (p : x =_{A} y) -> (ap A C x y (\z -> g (f z)) p) =_{g (f x) =_{C} g (f y)} (ap B C (f x) (f y) g (ap A B x y f p))
    := \A -> \B -> \C -> \x -> \y -> \f -> \g -> \p -> idJ(A, x, \y' -> \p' -> (ap A C x y' (\z -> g (f z)) p') =_{g (f x) =_{C} g (f y')} (ap B C (f x) (f y') g (ap A B x y' f p')), refl_{refl_{(g (f x)) : C} : g (f x) =_{C} g (f x)}, y, p)

#def rev-ap-comp : (A : U) -> (B : U) -> (C : U) -> (x : A) -> (y : A) -> (f : (_ : A) -> B) -> (g : (_ : B) -> C) 
    -> (p : x =_{A} y) -> (ap B C (f x) (f y) g (ap A B x y f p)) =_{g (f x) =_{C} g (f y)} (ap A C x y (\z -> g (f z)) p) 
    := \A -> \B -> \C -> \x -> \y -> \f -> \g -> \p -> rev (g (f x) =_{C} g (f y)) (ap A C x y (\z -> g (f z)) p) (ap B C (f x) (f y) g (ap A B x y f p)) (ap-comp A B C x y f g p)
    
-- transport in a type family along a path in the base
#def transport : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (u : B x) -> B y
  := \A -> \B -> \x -> \y -> \p -> \u -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> B y', u, y, p)

-- for later use, some higher transport
#def transport2 : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (q : x =_{A} y) 
  -> (H : p =_{x =_{A} y} q) -> (u : B x) -> (transport A B x y p u) =_{B y} (transport A B x y q u)
  := \A -> \B -> \x -> \y -> \p -> \q -> \H -> \u -> idJ(x =_{A} y, p, \q' -> \H' -> (transport A B x y p u) =_{B y} (transport A B x y q' u), refl_{transport A B x y p u : B y}, q, H)  

-- application of dependent functions to paths
#def apd : (A : U) -> (B : (a : A) -> U) -> (x : A) -> (y : A) -> (f : (z : A) -> B z) -> (p : x =_{A} y) 
  -> ((transport A B x y p (f x)) =_{B y} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(p' : x =_{A} y') 
  -> ((transport A B x y' p' (f x)) =_{B y'} f y'), refl_{f x : B x}, y, p)

-- homotopies

#def homotopy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> U
    := \A -> \B -> \f -> \g -> (a : A) -> (f a =_{B} g a)
    
#def homotopy-rev : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (_ : homotopy A B f g) -> homotopy A B g f
    := \A -> \B -> \f -> \g -> \H -> \a -> rev B (f a) (g a) (H a)

#def homotopy-composition : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> (h : (_ : A) -> B)
    -> (H : homotopy A B f g) -> (K : homotopy A B g h) -> homotopy A B f h
    := \A -> \B -> \f -> \g -> \h -> \H -> \K -> \a -> concat B (f a) (g a) (h a) (H a) (K a)

#def homotopy-postwhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (H : homotopy A B f g) -> (h : (_ : B) -> C) -> homotopy A C (\(x : A) -> h (f x)) (\(x : A) -> h (g x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> ap B C (f a) (g a) h (H a)

#def homotopy-prewhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : B) -> C) -> (g : (_ : B) -> C) 
    -> (H : homotopy B C f g) -> (h : (_ : A) -> B) -> homotopy A C (\(x : A) -> f (h x)) (\(x : A) -> g (h x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> H (h a)

#def nat-htpy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> (H : (a : A) -> ((f a) =_{B} (g a))) 
    -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (concat B (f x) (f y) (g y) (ap A B x y f p) (H y)) =_{(f x) =_{B} (g y)} 
    (concat B (f x) (g x) (g y) (H x) (ap A B x y g p))
    := \A -> \B -> \f -> \g -> \H -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (concat B (f x) (f y') (g y') (ap A B x y' f p') (H y')) =_{(f x) =_{B} (g y')} (concat B (f x) (g x) (g y') (H x) (ap A B x y' g p')), refl-concat B (f x) (g x) (H x), y, p)

#def a-cylinder-homotopy-coherence : (A : U) -> (f : (_ : A) -> A) -> (H : (x : A) -> ((f x) =_{A} x)) -> (a : A) 
    -> (concat A (f (f a)) (f a) a (ap A A (f a) a f (H a)) (H a)) =_{(f (f a)) =_{A} a} (concat A (f (f a)) (f a) (a) (H (f a)) (ap A A (f a) a (\x -> x) (H a)))
    := \A -> \f -> \H -> \a -> nat-htpy A A f (\x -> x) H (f a) a (H a)

#def another-cylinder-homotopy-coherence : (A : U) -> (f : (_ : A) -> A) -> (H : (x : A) -> ((f x) =_{A} x)) -> (a : A) 
    -> (concat A (f (f a)) (f a) a (ap A A (f a) a f (H a)) (H a)) =_{(f (f a)) =_{A} a} 
    (concat A (f (f a)) (f a) (a) (H (f a)) (H a))
    := \A -> \f -> \H -> \a -> concat ((f (f a)) =_{A} a) (concat A (f (f a)) (f a) a (ap A A (f a) a f (H a)) (H a)) 
    (concat A (f (f a)) (f a) (a) (H (f a)) (ap A A (f a) a (\x -> x) (H a)))
     (concat A (f (f a)) (f a) (a) (H (f a)) (H a))
     (a-cylinder-homotopy-coherence A f H a)
     (concat-homotopy A (f (f a)) (f a) (H (f a)) a (ap A A (f a) a (\x -> x) (H a)) (H a) (ap-id A (f a) a (H a)))

#def cylinder-homotopy-coherence : (A : U) -> (f : (_ : A) -> A) -> (H : (x : A) -> ((f x) =_{A} x)) -> (a : A) 
    -> (ap A A (f a) a  f (H a)) =_{f (f a) =_{A} f a} (H (f a)) 
    := \A -> \f -> \H -> \a -> concat-right-cancel A (f (f a)) (f a) a (ap A A (f a) a  f (H a)) (H (f a)) (H a) 
    (another-cylinder-homotopy-coherence A f H a)

#def rev-cylinder-homotopy-coherence : (A : U) -> (f : (_ : A) -> A) -> (H : (x : A) -> ((f x) =_{A} x)) -> (a : A) 
    -> (H (f a)) =_{f (f a) =_{A} f a} (ap A A (f a) a  f (H a))  
    := \A -> \f -> \H -> \a -> rev (f (f a) =_{A} f a) (ap A A (f a) a  f (H a)) (H (f a)) (concat-right-cancel A (f (f a)) (f a) a (ap A A (f a) a  f (H a)) (H (f a)) (H a) 
    (another-cylinder-homotopy-coherence A f H a))

-- contractible types
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

-- the following type of more coherent equivalences is not a proposition
#def hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
  := \(A : U) -> \(B : U) -> \(f : (_ : A) -> B) -> ∑ (g : (_ : B) -> A), (prod ((x : A) -> (g (f x)) =_{A} x)) ((y : B) -> (f (g y)) =_{B} y)
 
#def hasInverse-inverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : B) -> A
    := \A -> \B -> \f -> \fhasinverse -> first (fhasinverse)

-- invertible maps are equivalences
#def hasInverse-isEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> isEquiv A B f
  := \A -> \B -> \f -> \fhasinverse -> ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

-- equivalences are invertible
#def isEquiv-hasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : isEquiv A B f) -> hasInverse A B f 
    := \A -> \B -> \f -> \fisequiv -> (first (second fisequiv), 
    (homotopy-composition A A (\x -> ((isEquiv-section A B f fisequiv) (f x))) (\x -> ((isEquiv-retraction A B f fisequiv) (f x))) (\x -> x)  (homotopy-prewhisker A B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv) (isEquiv-htpic-inverses A B f fisequiv) f) second (first fisequiv) , second (second  fisequiv)))

#def hasInverse-retraction-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : A) -> A
    := \A -> \B -> \f -> \fhasinverse -> \a -> (hasInverse-inverse A B f fhasinverse (f a)) 

#def hasInverse-section-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : B) -> B
    := \A -> \B -> \f -> \fhasinverse -> \b -> f (hasInverse-inverse A B f fhasinverse b)

-- this composite is parallel to f
#def hasInverse-triple-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : A) -> B
    := \A -> \B -> \f -> \fhasinverse -> \a -> f ((hasInverse-inverse A B f fhasinverse) (f a))

-- this composite is also parallel to f
#def hasInverse-quintuple-composite : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (_ : hasInverse A B f) -> (_ : A) -> B
    := \A -> \B -> \f -> \fhasinverse -> \a -> f ((hasInverse-inverse A B f fhasinverse) (f ((hasInverse-inverse A B f fhasinverse) (f a))))

-- we'll require a more coherent notion of equivalence
#def isHalfAdjointEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
     := \A -> \B -> \f 
         -> ∑ (fhasinverse : (hasInverse A B f)), (a : A) -> 
         (((second (second fhasinverse))) (f a))
     =_{(hasInverse-triple-composite A B f fhasinverse a) =_{B} (f a)} 
     (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (((first (second fhasinverse))) a))

-- I prefer this definition, but homotopies are still not always recognized as functions
#def ALTisHalfAdjointEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> U
     := \A -> \B -> \f 
         -> ∑ (fhasinverse : (hasInverse A B f)), ((homotopy-prewhisker A B B (hasInverse-section-composite A B f fhasinverse)
    (\b -> b) (second (second fhasinverse)) f)
     =_{homotopy A B (hasInverse-triple-composite A B f fhasinverse) f} 
     ((homotopy-postwhisker A A B (hasInverse-retraction-composite A B f fhasinverse) (\a -> a) (first (second fhasinverse)) f)))

-- to promote an invertible map to a half adjoint equivalence we keep one homotopy and discard the other
#def hasInverse-kept-htpy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) 
    -> homotopy A A (hasInverse-retraction-composite A B f fhasinverse) (\a -> a)
    := \A -> \B -> \f -> \fhasinverse -> (first (second fhasinverse))

#def hasInverse-discarded-htpy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) 
    -> homotopy B B (hasInverse-section-composite A B f fhasinverse) (\b -> b)
    := \A -> \B -> \f -> \fhasinverse -> (second (second fhasinverse))    

#def hasInverse-discarded-naturality-square : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) -> 
    concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)) 
    (hasInverse-discarded-htpy A B f fhasinverse (f a)) =_{(hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (f a)} 
   concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := \A -> \B -> \f -> \fhasinverse -> \a -> nat-htpy A B (hasInverse-triple-composite A B f fhasinverse) f (\x -> hasInverse-discarded-htpy A B f fhasinverse (f x)) (hasInverse-retraction-composite A B f fhasinverse a) (a) (hasInverse-kept-htpy A B f fhasinverse a)

#def hasInverse-rev-cylinder-homotopy-coherence : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) 
    -> (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) =_{(hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) =_{A} (hasInverse-retraction-composite A B f fhasinverse a)}
    ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)
    := \A -> \B -> \f -> \fhasinverse -> \a -> rev-cylinder-homotopy-coherence A 
    (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse) a

#def hasInverse-ap-rev-cylinder-homotopy-coherence : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) 
    -> ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    =_{(hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (hasInverse-triple-composite A B f fhasinverse a)}
    ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f 
    (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
    := \A -> \B -> \f -> \fhasinverse -> \a -> ap-htpy A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f 
    (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
    (hasInverse-rev-cylinder-homotopy-coherence A B f fhasinverse a)

-- written out to debug the following code but not needed anymore
#def hasInverse-ap-comp-coherence : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) 
    ->  ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f 
    (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
    =_{(hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (hasInverse-triple-composite A B f fhasinverse a)}
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
    (hasInverse-kept-htpy A B f fhasinverse a)) 
    := \A -> \B -> \f -> \fhasinverse -> \a -> (rev-ap-comp A A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) f (hasInverse-kept-htpy A B f fhasinverse a))

#def hasInverse-cylinder-coherence : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) 
    -> ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    =_{(hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (hasInverse-triple-composite A B f fhasinverse a)}
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
   (hasInverse-kept-htpy A B f fhasinverse a)) 
    := \A -> \B -> \f -> \fhasinverse -> \a -> 
    concat ((hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (hasInverse-triple-composite A B f fhasinverse a)) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
    (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f 
    (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)))
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
    (hasInverse-kept-htpy A B f fhasinverse a)) 
    (hasInverse-ap-rev-cylinder-homotopy-coherence A B f fhasinverse a)
    (rev-ap-comp A A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) f (hasInverse-kept-htpy A B f fhasinverse a))
    
#def hasInverse-replaced-naturality-square : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f)
    -> (a : A) -> 
    concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) (hasInverse-retraction-composite A B f fhasinverse a) f 
    (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))) 
    (hasInverse-discarded-htpy A B f fhasinverse (f a)) =_{(hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (f a)} 
   concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := \A -> \B -> \f -> \fhasinverse -> \a -> 
    concat ((hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (f a)) 
    (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) (hasInverse-retraction-composite A B f fhasinverse a) f 
    (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))) 
    (hasInverse-discarded-htpy A B f fhasinverse (f a)))
    (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)) 
    (hasInverse-discarded-htpy A B f fhasinverse (f a)))
    (concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
    (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a)))
    (homotopy-concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
    (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
   (hasInverse-kept-htpy A B f fhasinverse a))
    (hasInverse-cylinder-coherence A B f fhasinverse a)
    (hasInverse-discarded-htpy A B f fhasinverse (f a)))
    (hasInverse-discarded-naturality-square A B f fhasinverse a)

-- this will replace the discarded homotopy
#def hasInverse-corrected-htpy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) 
    -> homotopy B B (hasInverse-section-composite A B f fhasinverse) (\b -> b)
    := \A -> \B -> \f -> \fhasinverse -> \b ->  concat B 
    ((hasInverse-section-composite A B f fhasinverse) b) 
    ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b)) 
    b
    (rev B ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))  ((hasInverse-section-composite A B f fhasinverse) b)  
    (hasInverse-discarded-htpy A B f fhasinverse ((hasInverse-section-composite A B f fhasinverse) b)))  
    (concat B  
    ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
    ((hasInverse-section-composite A B f fhasinverse) b) 
    b
    (ap A B ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse b)) (hasInverse-inverse A B f fhasinverse b) f ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse b)))
    ((hasInverse-discarded-htpy A B f fhasinverse b)))

-- this is the half adjoint coherence
#def hasInverse-coherence : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) -> (a : A)
    -> (hasInverse-corrected-htpy A B f fhasinverse (f a)) =_{(hasInverse-triple-composite A B f fhasinverse a) =_{B} (f a)}
    (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := \A -> \B -> \f -> \fhasinverse -> \a 
    -> triangle-rotation B 
    (hasInverse-quintuple-composite A B f fhasinverse a) 
    (hasInverse-triple-composite A B f fhasinverse a) 
    (f a) 
     (concat B  
    ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) (f a)))
    ((hasInverse-section-composite A B f fhasinverse) (f a)) 
    (f a)
    (ap A B ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse (f a))) (hasInverse-inverse A B f fhasinverse (f a)) f ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse (f a))))
    ((hasInverse-discarded-htpy A B f fhasinverse (f a))))
     (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a)) (hasInverse-replaced-naturality-square A B f fhasinverse a)

-- to promote an invertible map to a half adjoint equivalence we change the data of the invertible map
#def hasInverse-correctedhasInverse : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) 
    -> hasInverse A B f
    := \A -> \B -> \f -> \fhasinverse 
    -> (hasInverse-inverse A B f fhasinverse, (hasInverse-kept-htpy A B f fhasinverse, hasInverse-corrected-htpy A B f fhasinverse))

-- I had to change from the ALT version to the new version of isHalfAdjointEquiv to get this to compile
#def hasInverse-isHalfAdjointEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fhasinverse : hasInverse A B f) 
    -> isHalfAdjointEquiv A B f
    := \A -> \B -> \f -> \fhasinverse -> (hasInverse-correctedhasInverse A B f fhasinverse, hasInverse-coherence A B f fhasinverse)

-- equivalences -> coherent equivalences
#def isEquiv-isHalfAdjointEquiv : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (fisequiv : isEquiv A B f)
    -> isHalfAdjointEquiv A B f
    := \A -> \B -> \f -> \fisequiv -> hasInverse-isHalfAdjointEquiv A B f (isEquiv-hasInverse A B f fisequiv)

-- the type of equivalences between types
#def Eq : (A : U) -> (B : U) -> U
  := \(A : U) -> \(B : U) -> ∑ (f : (_ : A) -> B), ((isEquiv A) B) f

-- the type of logical equivalences between types
#def iff : (A : U) -> (B : U) -> U
  := \A -> \B -> prod ((_ : A) -> B) ((_ : B) -> A)

-- In what follows we apply the above to show that the projection from the total space of a sigma type is an equivalence if and only if its fibers are contractible
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

-- thankfully we have judgmental eta rules
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

-- The first half of our main result
#def contractible-fibers-projection-equiv : (A : U) -> (B : (a : A) -> U) 
    -> (_ : contractible-fibers A B) -> isEquiv (∑ (x : A), B x) A (total-space-projection A B)
  := \A -> \B -> \ABcontrfib -> (contractible-fibers-retraction A B ABcontrfib , contractible-fibers-section-is-section A B ABcontrfib)

#def total-path-to-base-path : (A : U) -> (B : (a : A) -> U) -> (z : ∑ (a : A), B a) -> (w : ∑ (a : A), B a) 
    -> (p : z =_{∑ (a : A), B a} w) -> ((first z) =_{A} first w)
    := \A -> \B -> \z -> \w -> \p -> ap (∑ (a : A), B a) A z w (total-space-projection A B) p 

#def total-path-to-fibered-path : (A : U) -> (B : (a : A) -> U) -> (z : ∑ (a : A), B a) -> (w : ∑ (a : A), B a) 
    -> (p : z =_{∑ (a : A), B a} w) -> (transport A B (first z) (first w) (total-path-to-base-path A B z w p) (second z)) =_{B (first w)} (second w)
    := \A -> \B -> \z -> \w -> \p -> idJ((∑ (a : A), B a), z, \w' -> \p' -> (transport A B (first z) (first w') (total-path-to-base-path A B z w' p') (second z)) =_{B (first w')} (second w'), refl_{second z : B (first z)}, w, p)

-- From a projection equivalence, it's not hard to inhabit fibers
#def projection-equiv-implies-inhabited-fibers : (A : U) -> (B : (a : A) -> U) 
    -> (_ : isEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> (x : A) -> B x
    := \A -> \B -> \ABprojequiv -> \x -> transport A B (first ((first (second ABprojequiv)) x)) x ((second (second ABprojequiv)) x) (second ((first (second ABprojequiv)) x))

-- this is great but I'll need more coherence to show that the inhabited fibers are contractible; the following proof fails
-- #def projection-equiv-implies-contractible-fibers : (A : U) -> (B : (a : A) -> U) 
--    -> (_ : isEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> contractible-fibers A B
--    := \A -> \B -> \ABprojequiv -> \x -> (second ((first (first ABprojequiv)) x) , 
--    \(u : B x) -> total-path-to-fibered-path A B ((first (first ABprojequiv)) x) (x, u) ((second (first ABprojequiv)) (x, u)) )

-- we start over from a strong hypothesis of a half adjoint equivalence
#def projection-coherent-equiv-inverse : (A : U) -> (B : (x : A) -> U)
    -> (_ : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> (a : A) -> ∑ (x : A), B x
    := \A -> \B -> \ABprojcequiv -> \a -> (first (first ABprojcequiv)) a

#def projection-coherent-equiv-base-htpy : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (a : A) -> (first (projection-coherent-equiv-inverse A B ABprojcequiv a)) =_{A} a
    := \A -> \B -> \ABprojcequiv -> \a -> (second (second (first ABprojcequiv))) a

#def projection-coherent-equiv-section : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (a : A) -> B a
    := \A -> \B -> \ABprojcequiv -> \a -> transport A B (first (projection-coherent-equiv-inverse A B ABprojcequiv a)) a 
    (projection-coherent-equiv-base-htpy A B ABprojcequiv a) (second (projection-coherent-equiv-inverse A B ABprojcequiv a))

#def projection-coherent-equiv-total-htpy : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (z : (∑ (x : A), B x)) -> (projection-coherent-equiv-inverse A B ABprojcequiv (first z)) =_{∑ (x : A), B x} z
    := \A -> \B -> \ABprojcequiv -> \z -> (first (second (first ABprojcequiv))) z

#def projection-coherent-equiv-fibered-htpy : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (w : (∑ (x : A), B x)) 
    -> (transport A B (first ((projection-coherent-equiv-inverse A B ABprojcequiv (first w)))) (first w) 
    (total-path-to-base-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w (projection-coherent-equiv-total-htpy A B ABprojcequiv w)) 
    (second (projection-coherent-equiv-inverse A B ABprojcequiv (first w)))) =_{B (first w)} (second w)
    := \A -> \B -> \ABprojcequiv -> \w 
    -> total-path-to-fibered-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w  (projection-coherent-equiv-total-htpy A B ABprojcequiv w)

#def projection-coherent-equiv-base-coherence : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (w : (∑ (x : A), B x)) -> (projection-coherent-equiv-base-htpy A B ABprojcequiv (first w)) =_{(first (projection-coherent-equiv-inverse A B ABprojcequiv (first w))) =_{A} (first w)} (total-path-to-base-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w (projection-coherent-equiv-total-htpy A B ABprojcequiv w)) 
    := \A -> \B -> \ABprojcequiv -> \w -> (second ABprojcequiv) w

#def projection-coherent-equiv-transport-coherence : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (w : (∑ (x : A), B x)) -> (projection-coherent-equiv-section A B ABprojcequiv (first w))
    =_{B (first w)}
    (transport A B (first ((projection-coherent-equiv-inverse A B ABprojcequiv (first w)))) (first w) 
    (total-path-to-base-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w (projection-coherent-equiv-total-htpy A B ABprojcequiv w)) 
    (second (projection-coherent-equiv-inverse A B ABprojcequiv (first w))))
    := \A -> \B -> \ABprojcequiv -> \w -> transport2 A B (first (projection-coherent-equiv-inverse A B ABprojcequiv (first w))) (first w) 
    (projection-coherent-equiv-base-htpy A B ABprojcequiv (first w)) 
    (total-path-to-base-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w (projection-coherent-equiv-total-htpy A B ABprojcequiv w))
    (projection-coherent-equiv-base-coherence A B ABprojcequiv w)
    (second (projection-coherent-equiv-inverse A B ABprojcequiv (first w)))

#def projection-coherent-equiv-fibered-contracting-htpy : (A : U) -> (B : (x : A) -> U)
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B)) 
    -> (w : (∑ (x : A), B x)) 
    -> (projection-coherent-equiv-section A B ABprojcequiv (first w)) =_{B (first w)} (second w)
    := \A -> \B -> \ABprojcequiv -> \w 
    -> concat (B (first w)) (projection-coherent-equiv-section A B ABprojcequiv (first w))
    (transport A B (first ((projection-coherent-equiv-inverse A B ABprojcequiv (first w)))) (first w) 
    (total-path-to-base-path A B (projection-coherent-equiv-inverse A B ABprojcequiv (first w)) w (projection-coherent-equiv-total-htpy A B ABprojcequiv w)) 
    (second (projection-coherent-equiv-inverse A B ABprojcequiv (first w))))
    (second w)
    (projection-coherent-equiv-transport-coherence A B ABprojcequiv w)
    (projection-coherent-equiv-fibered-htpy A B ABprojcequiv w)

-- finally we have
#def projection-coherent-equiv-contractible-fibers : (A : U) -> (B : (a : A) -> U) 
    -> (ABprojcequiv : isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B))-> contractible-fibers A B
    := \A -> \B -> \ABprojcequiv -> \x -> ((projection-coherent-equiv-section A B ABprojcequiv x), 
    \(u : B x) -> (projection-coherent-equiv-fibered-contracting-htpy A B ABprojcequiv (x, u)))
    
-- the converse to our first result    
#def projection-equiv-contractible-fibers : (A : U) -> (B : (a : A) -> U) 
    -> (ABprojequiv : isEquiv (∑ (x : A), B x) A (total-space-projection A B)) -> contractible-fibers A B
    := \A -> \B -> \ABprojequiv -> projection-coherent-equiv-contractible-fibers A B (isEquiv-isHalfAdjointEquiv (∑ (x : A), B x) A (total-space-projection A B) ABprojequiv)
    
-- the main theorem    
#def projection-theorem : (A : U) -> (B : (a : A) -> U) 
    -> iff (isEquiv (∑ (x : A), B x) A (total-space-projection A B)) (contractible-fibers A B)
    := \A -> \B 
    -> (\ABprojequiv -> projection-equiv-contractible-fibers A B ABprojequiv, \ABcontrfib -> contractible-fibers-projection-equiv A B ABcontrfib)
    

