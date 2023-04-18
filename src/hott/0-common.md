# 0. Common

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Products of types
```rzk
#def prod (A B : U) : U
  := ∑ (x : A), B

-- defined to illustrate the syntax for terms in sigma types
#def diagonal (A : U) (a : A) : prod A A
  := (a , a)
```

## The type of logical equivalences between types
```rzk
#def iff (A B : U) : U
  := prod (A -> B) (B -> A)
```

## Basic function definitions
```rzk
#def composition 
  (A B C : U)     -- Three types.
  (g : B -> C)    -- The second function.
  (f : A -> B)    -- The first function.
  : A -> C        -- The composite function.
  := \z -> g (f z)

#def triple-composition 
  (A B C D : U)
  (h : C -> D) 
  (g : B -> C) 
  (f : A -> B)
  : A -> D  
  := \z -> h (g (f z))

#def identity (A : U) (a : A) : A
  := a  

#def constant 
  (X A : U)       -- The source and target types.
  (a : A)         -- The constant output value.
  : X -> A
  := \x -> a
```
## Substitution
```rzk
-- Reindexing a type family along a function into the base type.  
#def reindex 
  (A B : U) 
  (f : B -> A) 
  (C : A -> U) 
  : (B -> U)
  := \b -> C (f b)
```