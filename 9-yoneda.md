# The Yoneda lemma

These formalisations correspond to Section 5 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

-- [RS17, Section 9]
-- Definition of evid and the Yoneda map as its claimed inverse
-- Auxiliary definition of the type of "generalized elements" of C at a:A
```rzk
#def
    genElts
        (A : U)
        (C : A -> U)
        (a : A)
        : U
        := ( (x : A) -> hom A a x -> C x)
```

```rzk
#def
    evid : (A : U) -> (C : A -> U) -> (a : A)
        -> (genElts A C a)  -> C a
    := \A -> \C -> \a -> \f -> (f a (id-arr A a))

#def
    yon
        (A : U)
        (C : A -> U)
        (CisCov : isCovFam A C)
        (a : A)
        : (C a) ->  (genElts A C a) 
        := \u -> \x -> \f -> covTrans A C CisCov a x f u
-- #def
--     yon.evid-is-id
--         (A : U)
--         (AisSegal : isSegal A)
--         (C : A -> U)
--         (CisCov : isCovFam C)
--         (a : A)
--         :  (genElts A C a) 
--         -> (homotopy (genElts A C a)
--                      (genElts A C a) 
--                      (id-arr genElts A C a)
--                      (comp (genElts A C a) (C a) (evid A C a) (yon A C CisCov a))
--                     )
--         := TODO

```