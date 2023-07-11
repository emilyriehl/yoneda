# 3. Simplicial Type Theory

These formalisations correspond in part to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Simplices and their subshapes

### Simplices

```rzk
-- the 1-simplex
#def Δ¹ : 2 -> TOPE
  := \ t -> TOP

-- the 2-simplex
#def Δ² : (2 * 2) -> TOPE
  := \ (t , s) -> s <= t

-- the 3-simplex
#def Δ³ : (2 * 2 * 2) -> TOPE
  := \ ((t1 , t2) , t3) -> t3 <= t2 /\ t2 <= t1
```

### Boundaries of simplices

```rzk
-- the boundary of a 1-simplex
#def ∂Δ¹ : Δ¹ -> TOPE
  := \ t -> (t === 0_2 \/ t === 1_2)

-- the boundary of a 2-simplex
#def ∂Δ² : Δ² -> TOPE
  :=
    \ (t, s) ->
    ( s === 0_2 \/ t === 1_2 \/ s === t)
```

### The inner horn

```rzk
#def Λ : (2 * 2) -> TOPE
  := \ (t , s) -> (s === 0_2 \/ t === 1_2)
```

### Products

The product of topes defines the product of shapes.

```rzk
#def shapeprod
  (I J : CUBE)
  (ψ : I -> TOPE)
  (χ : J -> TOPE)
  : (I * J) -> TOPE
  := \ (t , s) -> ψ t /\ χ s

-- the square as a product
#def Δ¹×Δ¹ : (2 * 2) -> TOPE
  := shapeprod 2 2 Δ¹ Δ¹

-- the total boundary of the square
#def ∂□ : (2 * 2) -> TOPE
  := \ (t ,s) -> ((∂Δ¹ t) /\ (Δ¹ s)) \/ ((Δ¹ t) /\ (∂Δ¹ s))

-- the vertical boundary of the square
#def ∂Δ¹×Δ¹ : (2 * 2) -> TOPE
  := shapeprod 2 2 ∂Δ¹ Δ¹

-- the horizontal boundary of the square
#def Δ¹×∂Δ¹ : (2 * 2) -> TOPE
  := shapeprod 2 2 Δ¹ ∂Δ¹

-- the prism from a 2-simplex in an arrow type
#def Δ²×Δ¹ : (2 * 2 * 2) -> TOPE
  := shapeprod (2 * 2) 2 Δ² Δ¹
```

### Intersections

The intersection of shapes is defined by conjunction on topes:

```rzk
#def shapeIntersection
  (I : CUBE) (ψ χ : I -> TOPE) : I -> TOPE
  := \ t -> ψ t /\ χ t
```

### Unions

The union of shapes is defined by disjunction on topes:

```rzk
#def shapeUnion
  (I : CUBE) (ψ χ : I -> TOPE) : I -> TOPE
  := \ t -> ψ t \/ χ t
```
