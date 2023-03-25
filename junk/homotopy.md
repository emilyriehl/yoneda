#lang rzk-1

-- some path algebra that we need here

-- path reversal
#def rev : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> y =_{A} x
  := \(A : U) -> \(x : A) -> \(y : A) -> \(p : x =_{A} y) 
  -> idJ(A, x, \z -> \(_ : x =_{A} z) -> z =_{A} x, refl_{x : A}, y, p)

-- path composition by induction on the second path
#def concat : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : y =_{A} z) -> (x =_{A} z)
  := \A -> \x -> \y -> \z -> \p -> \q -> idJ(A, y, \(w : A) -> \(_ : y =_{A} w) -> (x =_{A} w), p, z, q)

-- the coherence we don't have definitionally
#def refl-concat : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (concat A x x y (refl_{x : A}) p) =_{x =_{A} y} p
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (concat A x x y' (refl_{x : A}) p') =_{x =_{A} y'} p', refl_{refl_{x : A} : x =_{A} x}, y, p)

#def concat-right-cancel : (A : U) -> (x : A) -> (y : A) -> (z : A) -> (p : x =_{A} y) -> (q : x =_{A} y) -> (r : y =_{A} z)
    -> (H : (concat A x y z p r) =_{x =_{A} z} (concat A x y z q r)) -> (p =_{x =_{A} y} q)
    := \A -> \x -> \y -> \z -> \p -> \q -> \r -> idJ(A, y, \z' -> \r' -> (H : (concat A x y z' p r') =_{x =_{A} z'} (concat A x y z' q r')) -> (p =_{x =_{A} y} q), \H -> H, z, r)    

#def concat-homotopy : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (z : A) -> (q : y =_{A} z) -> (r : y =_{A} z)
    -> (H : q =_{y =_{A} z} r) -> (concat A x y z p q) =_{x =_{A} z} (concat A x y z p r)
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (z : A) -> (q : y' =_{A} z) -> (r : y' =_{A} z) -> (H : q =_{y' =_{A} z} r) -> (concat A x y' z p' q) =_{x =_{A} z} (concat A x y' z p' r), \z -> \q -> \r -> \H -> concat (x =_{A} z) (concat A x x z refl_{x : A} q) r (concat A x x z refl_{x : A} r) (concat (x =_{A} z) (concat A x x z refl_{x : A} q) q r (refl-concat A x z q) H) (rev (x =_{A} z) (concat A x x z refl_{x : A} r) r (refl-concat A x z r)), y, p)

-- application of functions to paths
#def ap : (A : U) -> (B : U) -> (x : A) -> (y : A) -> (f : (x : A) -> B) -> (p : x =_{A} y) -> (f x =_{B} f y)
  := \A -> \B -> \x -> \y -> \f -> \p -> idJ(A, x, \(y' : A) -> \(_ : x =_{A} y') -> (f x =_{B} f y'), refl_{f x : B}, y, p)

#def ap-id : (A : U) -> (x : A) -> (y : A) -> (p : x =_{A} y) -> (ap A A x y (\z -> z) p) =_{x =_{A} y} p
    := \A -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' -> (ap A A x y' (\z -> z) p') =_{x =_{A} y'} p', refl_{refl_{x : A} : x =_{A} x}, y, p)

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

-- for simplicity, we only define these for non-dependent functions
#def homotopy-postwhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) 
    -> (H : homotopy A B f g) -> (h : (_ : B) -> C) -> homotopy A C (\(x : A) -> h (f x)) (\(x : A) -> h (g x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> ap B C (f a) (g a) h (H a)

#def homotopy-prewhisker : (A : U) -> (B : U) -> (C : U) -> (f : (_ : B) -> C) -> (g : (_ : B) -> C) 
    -> (H : homotopy B C f g) -> (h : (_ : A) -> B) -> homotopy A C (\(x : A) -> f (h x)) (\(x : A) -> g (h x))
    := \A -> \B -> \C -> \f -> \g -> \H -> \h -> \a -> H (h a)

#def nat-htpy : (A : U) -> (B : U) -> (f : (_ : A) -> B) -> (g : (_ : A) -> B) -> (H : homotopy A B f g)
  -> (x : A) -> (y : A)
    -> (p : x =_{A} y) -> (concat B (f x) (f y) (g y) (ap A B x y f p) (H y)) =_{(f x) =_{B} (g y)} 
    (concat B (f x) (g x) (g y) (H x) (ap A B x y g p))
    := \A -> \B -> \f -> \g -> \H -> \x -> \y -> \p -> idJ(A, x, \y' -> \p' 
     -> (concat B (f x) (f y') (g y') (ap A B x y' f p') (H y')) =_{(f x) =_{B} (g y')} (concat B (f x) (g x) (g y') (H x) 
    (ap A B x y' g p')), refl-concat B (f x) (g x) (H x), y, p)

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

