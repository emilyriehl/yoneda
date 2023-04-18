#lang rzk-1

#def hasSection 
    (A B : U)
    (f : A -> B) 
    : U
    := ∑ (s : B -> A), homotopy B B (composition B A B f s)(identity B)
  
#def hasRetraction    (A B : U)
    (f : A -> B) 
    : U
    := ∑ (r : B -> A), homotopy A A (composition A B A r f)(identity A)
  
-- equivalences are bi-invertible maps
#def isEquiv     
    (A B : U)
    (f : A -> B) 
    : U  
    := prod (hasRetraction A B f) (hasSection A B f)

#def isEquiv-section
    (A B : U)
    (f : A -> B) 
    (fisequiv : isEquiv A B f)
    : B -> A
    := (first (second fisequiv))

#def isEquiv-retraction     
    (A B : U)
    (f : A -> B) 
    (fisequiv : isEquiv A B f)
    : B -> A
    := (first (first fisequiv))

-- the homotopy between the section and retraction of an equivalence
#def isEquiv-htpic-inverses 
    (A B : U)
    (f : A -> B) 
    (fisequiv : isEquiv A B f)
    : homotopy B A (isEquiv-section A B f fisequiv) (isEquiv-retraction A B f fisequiv)
    := homotopy-composition B A 
            (isEquiv-section A B f fisequiv) 
            (triple-composition B A B A (isEquiv-retraction A B f fisequiv) f ((isEquiv-section A B f fisequiv))) 
            (isEquiv-retraction A B f fisequiv) 
            (homotopy-rev B A 
                (triple-composition B A B A (isEquiv-retraction A B f fisequiv) f ((isEquiv-section A B f fisequiv)))     (isEquiv-section A B f fisequiv)
                (homotopy-prewhisker B A A
                    (composition A B A (isEquiv-retraction A B f fisequiv) f) 
                    (identity A) 
                    (second (first fisequiv)) 
                    (isEquiv-section A B f fisequiv)))
            (homotopy-postwhisker B B A 
                (composition B A B f (isEquiv-section A B f fisequiv)) 
                (identity B) 
                (second (second fisequiv)) 
                (isEquiv-retraction A B f fisequiv))

-- the following type of more coherent equivalences is not a proposition
#def hasInverse 
    (A B : U)
    (f : A -> B) 
    : U
    := ∑ (g : B -> A),    -- A two-sided inverse
        (prod 
            (homotopy A A (composition A B A g f)(identity A))    -- The retracting homotopy
            (homotopy B B (composition B A B f g)(identity B)))   -- The section homotopy
 
#def hasInverse-inverse 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : B -> A
    := first (fhasinverse)

-- invertible maps are equivalences
#def hasInverse-isEquiv
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : isEquiv A B f
  := ((first fhasinverse, first (second fhasinverse)), (first fhasinverse, second (second fhasinverse)))

-- equivalences are invertible
#def isEquiv-hasInverse 
    (A B : U)
    (f : A -> B) 
    (fisequiv : isEquiv A B f)
    : hasInverse A B f 
    := (isEquiv-section A B f fisequiv, 
            (homotopy-composition A A 
                (composition A B A (isEquiv-section A B f fisequiv) f) 
                (composition A B A (isEquiv-retraction A B f fisequiv) f) 
                (identity A)  
                    (homotopy-prewhisker A B A 
                        (isEquiv-section A B f fisequiv) 
                        (isEquiv-retraction A B f fisequiv) 
                        (isEquiv-htpic-inverses A B f fisequiv) 
                        f) 
                    (second (first fisequiv)) ,
            second (second  fisequiv)))

-- Some iterated composites associated to a pair of invertible maps.
#def hasInverse-retraction-composite 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : A -> A
    := composition A B A (hasInverse-inverse A B f fhasinverse) f 

#def hasInverse-section-composite 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : B -> B
    := composition B A B f (hasInverse-inverse A B f fhasinverse)

-- This composite is parallel to f; we won't need the dual notion.
#def hasInverse-triple-composite 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : A -> B
    := triple-composition A B A B f (hasInverse-inverse A B f fhasinverse) f

-- This composite is also parallel to f; again we won't need the dual notion.
#def hasInverse-quintuple-composite
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : A -> B
    := \a -> f ((hasInverse-inverse A B f fhasinverse) (f ((hasInverse-inverse A B f fhasinverse) (f a))))

-- We'll require a more coherent notion of equivalence
#def isHalfAdjointEquiv 
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (hasInverse A B f)), 
            (a : A) -> (((second (second fhasinverse))) (f a)) =
                        (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (((first (second fhasinverse))) a))

-- By function extensionality, the previous definition coincides with the following one:
#def ALTisHalfAdjointEquiv
    (A B : U)
    (f : A -> B)
    : U
    := ∑ (fhasinverse : (hasInverse A B f)), 
            ((homotopy-prewhisker A B B 
                (hasInverse-section-composite A B f fhasinverse) (identity B) (second (second fhasinverse)) f)
            = ((homotopy-postwhisker A A B 
                (hasInverse-retraction-composite A B f fhasinverse) (identity A) (first (second fhasinverse)) f)))

-- To promote an invertible map to a half adjoint equivalence we keep one homotopy and discard the other
#def hasInverse-kept-htpy 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : homotopy A A (hasInverse-retraction-composite A B f fhasinverse) (identity A)
    := (first (second fhasinverse))

#def hasInverse-discarded-htpy 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : homotopy B B (hasInverse-section-composite A B f fhasinverse) (identity B)
    := (second (second fhasinverse))    

-- the required coherence will be built by transforming an instance of this naturality square
#def hasInverse-discarded-naturality-square 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse)(hasInverse-kept-htpy A B f fhasinverse a)) 
            (hasInverse-discarded-htpy A B f fhasinverse (f a)) 
                =
            concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := nat-htpy A B (hasInverse-triple-composite A B f fhasinverse) f 
            (\x -> hasInverse-discarded-htpy A B f fhasinverse (f x)) 
            (hasInverse-retraction-composite A B f fhasinverse a) (a) (hasInverse-kept-htpy A B f fhasinverse a)

-- building a path that will be whiskered into the naturality square above
#def hasInverse-cylinder-homotopy-coherence 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
            = ap A A (hasInverse-retraction-composite A B f fhasinverse a) a 
                (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)
    := cylinder-homotopy-coherence A (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse) a

#def hasInverse-ap-cylinder-homotopy-coherence 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
            (hasInverse-retraction-composite A B f fhasinverse a) 
            f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
        = ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
                 (hasInverse-retraction-composite A B f fhasinverse a) f 
                 (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a))
    := ap-htpy A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
            (hasInverse-retraction-composite A B f fhasinverse a) f 
            (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
                (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a 
                    (hasInverse-retraction-composite A B f fhasinverse) 
                    (hasInverse-kept-htpy A B f fhasinverse a))
            (hasInverse-cylinder-homotopy-coherence A B f fhasinverse a)

#def hasInverse-cylinder-coherence 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : ap A B 
            (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
            (hasInverse-retraction-composite A B f fhasinverse a) 
                f 
                (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
            =
        (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a 
            (hasInverse-triple-composite A B f fhasinverse) 
            (hasInverse-kept-htpy A B f fhasinverse a)) 
    := concat ((hasInverse-quintuple-composite A B f fhasinverse a) = (hasInverse-triple-composite A B f fhasinverse a)) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
                (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
                (hasInverse-retraction-composite A B f fhasinverse a) f 
                (ap A A (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-retraction-composite A B f fhasinverse) (hasInverse-kept-htpy A B f fhasinverse a)))
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
                (hasInverse-kept-htpy A B f fhasinverse a)) 
            (hasInverse-ap-cylinder-homotopy-coherence A B f fhasinverse a)
            (rev-ap-comp A A B (hasInverse-retraction-composite A B f fhasinverse a) a 
                (hasInverse-retraction-composite A B f fhasinverse) 
                f 
                (hasInverse-kept-htpy A B f fhasinverse a))

-- this morally gives the half adjoint inverse coherence; it just requires rotation    
#def hasInverse-replaced-naturality-square 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))
                (hasInverse-retraction-composite A B f fhasinverse a) f 
                (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a))) 
            (hasInverse-discarded-htpy A B f fhasinverse (f a)) 
                =
        concat B (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a) 
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := concat ((hasInverse-quintuple-composite A B f fhasinverse a) =_{B} (f a)) 
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
            (homotopy-concat B 
                (hasInverse-quintuple-composite A B f fhasinverse a) (hasInverse-triple-composite A B f fhasinverse a) (f a)
                (ap A B (hasInverse-retraction-composite A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)) 
                    (hasInverse-retraction-composite A B f fhasinverse a) f (hasInverse-kept-htpy A B f fhasinverse (hasInverse-retraction-composite A B f fhasinverse a)))
                (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a (hasInverse-triple-composite A B f fhasinverse) 
                    (hasInverse-kept-htpy A B f fhasinverse a))
                (hasInverse-cylinder-coherence A B f fhasinverse a)
                (hasInverse-discarded-htpy A B f fhasinverse (f a)))
            (hasInverse-discarded-naturality-square A B f fhasinverse a)

-- This will replace the discarded homotopy
#def hasInverse-corrected-htpy 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : homotopy B B (hasInverse-section-composite A B f fhasinverse) (\b -> b)
    := \b -> concat B 
                ((hasInverse-section-composite A B f fhasinverse) b) 
                ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b)) 
                b
                (rev B ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
                ((hasInverse-section-composite A B f fhasinverse) b)  
                (hasInverse-discarded-htpy A B f fhasinverse ((hasInverse-section-composite A B f fhasinverse) b)))  
                (concat B  
                    ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) b))
                    ((hasInverse-section-composite A B f fhasinverse) b) 
                    b
                    (ap A B ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse b))
                        (hasInverse-inverse A B f fhasinverse b) f 
                        ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse b)))
                    ((hasInverse-discarded-htpy A B f fhasinverse b)))

-- this is the half adjoint coherence
#def hasInverse-coherence 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    (a : A) 
    : (hasInverse-corrected-htpy A B f fhasinverse (f a)) 
                = (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a))
    := triangle-rotation B 
            (hasInverse-quintuple-composite A B f fhasinverse a)(hasInverse-triple-composite A B f fhasinverse a) (f a) 
            (concat B  
                ((hasInverse-section-composite A B f fhasinverse) ((hasInverse-section-composite A B f fhasinverse) (f a)))
                ((hasInverse-section-composite A B f fhasinverse) (f a)) 
                (f a)
            (ap A B 
                ((hasInverse-retraction-composite A B f fhasinverse) (hasInverse-inverse A B f fhasinverse (f a)))
                (hasInverse-inverse A B f fhasinverse (f a)) 
                f ((first (second fhasinverse)) (hasInverse-inverse A B f fhasinverse (f a))))
            ((hasInverse-discarded-htpy A B f fhasinverse (f a))))
            (hasInverse-discarded-htpy A B f fhasinverse (hasInverse-triple-composite A B f fhasinverse a)) 
            (ap A B (hasInverse-retraction-composite A B f fhasinverse a) a f (hasInverse-kept-htpy A B f fhasinverse a)) (hasInverse-replaced-naturality-square A B f fhasinverse a)

-- to promote an invertible map to a half adjoint equivalence we change the data of the invertible map by replacing the discarded homotopy with the corrected one.
#def hasInverse-correctedhasInverse 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : hasInverse A B f
    := (hasInverse-inverse A B f fhasinverse, (hasInverse-kept-htpy A B f fhasinverse, hasInverse-corrected-htpy A B f fhasinverse))

-- Invertible maps are half adjoint equivalences!
#def hasInverse-isHalfAdjointEquiv 
    (A B : U)
    (f : A -> B) 
    (fhasinverse : hasInverse A B f)
    : isHalfAdjointEquiv A B f
    := (hasInverse-correctedhasInverse A B f fhasinverse, hasInverse-coherence A B f fhasinverse)

-- Equivalences are half adjoint equivalences!
#def isEquiv-isHalfAdjointEquiv 
    (A B : U)
    (f : A -> B) 
    (fisequiv : isEquiv A B f)
    : isHalfAdjointEquiv A B f
    := hasInverse-isHalfAdjointEquiv A B f (isEquiv-hasInverse A B f fisequiv)

-- The type of equivalences between types uses the propositional notion isEquiv rather than the incoherent hasInverse.
#def Eq (A B : U) : U
  :=  ∑ (f : A -> B), ((isEquiv A) B) f

-- The data of an equivalence is not symmetric so we promote an equivalence to an invertible map to prove symmetry
#def sym_Eq 
    (A B : U)
    (e : Eq A B)
    : Eq B A
    := (first (isEquiv-hasInverse A B (first e) (second e)) , 
            (( first e , 
                second (second (isEquiv-hasInverse A B (first e) (second e))) ) , 
            ( first e , 
                first (second (isEquiv-hasInverse A B (first e) (second e))) ) ))

-- Composition of equivalences in diagrammatic order.
#def compose_Eq
    (A B C : U)
    (A=B : Eq A B)
    (B=C : Eq B C)
    : Eq A C
    := (\a -> (first B=C) ((first A=B) a), -- the composite equivalence 
             ((\c -> (first (first (second A=B))) ((first (first (second (B=C)))) c),
            (\a -> 
                concat A
                ((first (first (second A=B))) ((first (first (second B=C))) ((first B=C) ((first A=B) a))))
                ((first (first (second A=B))) ((first A=B) a))
                a
                (ap B A
                    ((first (first (second B=C))) ((first B=C) ((first A=B) a))) -- should be inferred
                    ((first A=B) a) -- should be inferred
                    (first (first (second A=B)))
                    ((second (first (second B=C))) ((first A=B) a)))
                ((second (first (second A=B))) a))),
                    (\c -> (first (second (second A=B))) ((first (second (second (B=C)))) c),
            (\c ->
                concat C
                ((first B=C) ((first A=B) ((first (second (second A=B))) ((first (second (second B=C))) c))))
                ((first B=C) ((first (second (second B=C))) c))
                c
                (ap B C
                    ((first A=B) ((first (second (second A=B))) ((first (second (second B=C))) c))) -- should be inferred
                    ((first (second (second B=C))) c) -- should be inferred
                    (first B=C)
                    ((second (second (second A=B))) ((first (second (second B=C))) c)))
                ((second (second (second B=C))) c)))))

-- now we compose the functions that are equivalences
#def compose_isEquiv
    (A B C : U) 
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (g : B -> C)
    (gisequiv : isEquiv B C g) 
    : isEquiv A C (composition A B C g f)
    := ((composition C B A (isEquiv-retraction A B f fisequiv) (isEquiv-retraction B C g gisequiv), 
        \a -> 
            concat A
            ((isEquiv-retraction A B f fisequiv) ((isEquiv-retraction B C g gisequiv) (g (f a))))
            ((isEquiv-retraction A B f fisequiv) (f a))
            a
            (ap B A
                ((isEquiv-retraction B C g gisequiv) (g (f a))) -- should be inferred
                (f a) -- should be inferred
                (isEquiv-retraction A B f fisequiv)
                ((second (first gisequiv)) (f a)))
            ((second (first fisequiv)) a)),
        (composition C B A (isEquiv-section A B f fisequiv) (isEquiv-section B C g gisequiv),
        \c ->
            concat C
            (g (f ((first (second fisequiv)) ((first (second gisequiv)) c))))
            (g ((first (second gisequiv)) c))
            c
            (ap B C
                (f ((first (second fisequiv)) ((first (second gisequiv)) c))) -- should be inferred
                ((first (second gisequiv)) c) -- should be inferred
                g
               ((second (second fisequiv)) ((first (second gisequiv)) c)))
            ((second (second gisequiv)) c)))  

-- a composition of three equivalences
#def triple_compose_Eq
    (A B C D : U) 
    (A=B : Eq A B) 
    (B=C : Eq B C) 
    (C=D : Eq C D) 
    : Eq A D
    := compose_Eq A B D (A=B) (compose_Eq B C D B=C C=D)  

#def triple_compose_isEquiv
    (A B C D : U) 
    (f : A -> B)
    (fisequiv : isEquiv A B f)
    (g : B -> C)
    (gisequiv : isEquiv B C g) 
    (h : C -> D)
    (hisequiv : isEquiv C D h)
    : isEquiv A D (triple-composition A B C D h g f)    
    := compose_isEquiv A B D f fisequiv (composition B C D h g) (compose_isEquiv B C D g gisequiv h hisequiv)

-- the next result requires function extensionality
#def FunExt : U
    := (X : U) -> (A : X -> U) -> (f : (x : X) -> A x) -> (g : (x : X) -> A x) ->
        (px : (x : X) -> f x = g x) -> f = g

-- A fiberwise equivalence defines an equivalence of dependent function types
#def fibered-equiv-function-equiv
    (funext : FunExt)
    (X : U)
    (A B : X -> U)
    (fibequiv : (x : X) -> Eq (A x) (B x))
    : Eq ((x : X) -> A x) ((x : X) -> B x)
    := ((\a -> \x -> (first (fibequiv x)) (a x)),
            (((\b -> \x -> (first (first (second (fibequiv x)))) (b x)),
                \a -> funext X A (\x -> (first (first (second (fibequiv x)))) ((first (fibequiv x)) (a x))) a (\x -> (second (first (second (fibequiv x)))) (a x))), 
           ((\b -> \x -> (first (second (second (fibequiv x)))) (b x)),
            (\b -> funext X B (\x -> (first (fibequiv x)) ((first (second (second (fibequiv x)))) (b x))) b (\x -> (second (second (second (fibequiv x)))) (b x))))))

-- Setting up identity types of sigma types

-- Sigma-induction
#def ind-Sigma
        (A : U)
        (B : A -> U)
        (C : (∑(a : A), B a) -> U)
        (s : ∑(a : A), B a)
        (f : (a : A) -> (b : B a) -> C (a, b))
        : C s
        := (f (first s)) (second s)

-- [Rijke 22, Definition 9.3.1]
#def Eq-Sigma
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    : U
    := ∑(p : (first s) = (first t)), (transport A B (first s) (first t) p (second s)) = (second t)

-- [Rijke 22, used in Lemma 9.3.2]
#def refl-in-Sigma
    (A : U)
    (B : A -> U)
    (x : A)
    (y : B x)
    : ∑(p : (x = x)), ((transport A B x x refl_{x} y) = y)
    := (refl_{x}, refl_{y})

-- [Rijke 22, Lemma 9.3.2]
-- Eq-sigma is reflexive
#def reflexive-Eq-Sigma
       (A : U)
       (B : A -> U)
       (s : ∑(a : A), B a)
       : (Eq-Sigma A B s s)
       := (ind-Sigma 
      A
      B
     (\k -> (Eq-Sigma A B k k))
      s
     (\u v -> (refl_{u}, refl_{v}))
      )

-- [Rijke 22, Definition 9.3.3]
#def pair-eq
    (A : U)
    (B : A -> U)
    (s t : ∑(a : A), B a)
    (p : s = t)
    : (Eq-Sigma A B s t)
    := idJ(∑(a : A), B a, s, \t' p' -> (Eq-Sigma A B s t'), (reflexive-Eq-Sigma A B s), t, p)

-- [Rijke 22, Theorem 9.3.3, Characterization of identity types of sigma types]
-- #def eq-pair
--     (A : U)
--     (B : A -> U)
--     (s t : ∑(a : A), B a)
--     TODO 
-- #def eq-sigma
--     (A : U)
--     (B : A -> U)
--     (s t : ∑(a : A), B a)
--     (p : (s = t))
--     : (Eq-Sigma A B s t)
--     := TODO

-- -- Split off homotopy in a sigma type
-- #def sigma-htopy-split
--     (A : U)
--     (B : A -> U)
--     (k m : (∑(a : A), B a))
--     (p : (k = m))
--     : (∑(q : (first k) = (first m)), 
--          )

