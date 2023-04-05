# 3. Simplicial Type Theory

These formalisations correspond to Section 3 of RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Simplicies and their subshapes

Simplicies:

```rzk
-- 1-simplex
#def Δ¹ : (t : 2) -> TOPE
  := \(t : 2) -> TOP

-- 2-simplex
#def Δ² : (t : 2 * 2) -> TOPE
  := \(t, s) -> s <= t

-- 3-simplex
#def Δ³ : (t : 2 * 2 * 2) -> TOPE
  := \((t1, t2), t3) -> t3 <= t2 /\ t2 <= t1
```

Boundaries of simplices:

```rzk
-- boundary of a 1-simplex
#def ∂Δ¹ : (t : 2) -> TOPE
  := \(t : 2) -> (t === 0_2 \/ t === 1_2)

-- boundary of a 2-simplex
#def ∂Δ² : {(ts : 2 * 2) | Δ² ts} -> TOPE
  := \{ts : 2 * 2 | Δ² ts} -> ((second ts) === 0_2 \/ (first ts) === 1_2 \/ (second ts) === (first ts))
```

Horns:

```rzk
-- the (2,1)-horn
#def Λ : (t : 2 * 2) -> TOPE
  := \(t, s) -> (s === 0_2 \/ t === 1_2)
```

More to be done.

## Joins of simplices

To be done.