# 1. Paths

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Path induction

We define path induction in terms of the built-in J rule, so that we can apply
it like any other function.

```rzk
#define ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) → (a = x) → U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
```

## Some basic path algebra

```rzk
#section path-algebra

#variable A : U
#variables x y z : A
```

### Path reversal

```rzk
#def rev
  ( p : x = y)
  : y = x
  :=
  ind-path A x
    ( \ y' p' → y' = x)
    ( refl)
    ( y)
    ( p)
```

### Path concatenation

We take path concatenation defined by induction on the second path variable as
our main definition.

```rzk
#def concat
  ( p : x = y)
  ( q : y = z)
  : x = z
  :=
  ind-path A y
    ( \ z' q' → (x = z'))
    ( p)
    ( z)
    ( q)
```

We also introduce a version defined by induction on the first path variable, for
situations where it is easier to induct on the first path.

```rzk
#def concat'
  ( p : x = y)
  : ( y = z)
  → ( x = z)
  :=
  ind-path A x
    ( \ y' p' → (y' = z) → (x = z))
    ( \ q' → q')
    ( y)
    ( p)

#end path-algebra
```

## Some basic coherences in path algebra

```rzk
#section basic-path-coherence

#variable A : U
#variables w x y z : A

#def rev-rev
  ( p : x = y)
  : rev A y x (rev A x y p) = p
  :=
  ind-path A x
    ( \ y' p' → (rev A y' x (rev A x y' p')) = p')
    ( refl)
    ( y)
    ( p)
```

### Left unit law for path concatenation

The left unit law for path concatenation does not hold definitionally due to our
choice of definition.

```rzk
#def left-unit-concat
  ( p : x = y)
  : concat A x x y refl p = p
  :=
  ind-path A x
    ( \ y' p' → (concat A x x y' refl p') = p')
    ( refl)
    ( y)
    ( p)
```

### Associativity of path concatenation

```rzk
#def associative-concat
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : concat A w y z (concat A w x y p q) r
  = concat A w x z p (concat A x y z q r)
  :=
    ind-path A y
      ( \ z' r' →
        concat A w y z' (concat A w x y p q) r'
      = concat A w x z' p (concat A x y z' q r'))
      ( refl)
      ( z)
      ( r)

#def rev-associative-concat
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : concat A w x z p (concat A x y z q r)
  = concat A w y z (concat A w x y p q) r
  :=
    ind-path A y
      ( \ z' r' →
          concat A w x z' p (concat A x y z' q r')
        = concat A w y z' (concat A w x y p q) r')
      ( refl)
      ( z)
      ( r)

#def right-inverse-concat
  ( p : x = y)
  : concat A x y x p (rev A x y p) = refl
  :=
    ind-path A x
      ( \ y' p' → concat A x y' x p' (rev A x y' p') = refl)
      ( refl)
      ( y)
      ( p)

#def left-inverse-concat
  ( p : x = y)
  : concat A y x y (rev A x y p) p = refl
  :=
    ind-path A x
      ( \ y' p' → concat A y' x y' (rev A x y' p') p' = refl)
      ( refl)
      ( y)
      ( p)
```

### Concatenation of two paths with common codomain

Concatenation of two paths with common codomain; defined using `#!rzk concat`
and `#!rzk rev`.

```rzk
#def zig-zag-concat
  ( p : x = y)
  ( q : z = y)
  : x = z
  := concat A x y z p (rev A z y q)
```

### Concatenation of two paths with common domain

Concatenation of two paths with common domain; defined using `#!rzk concat` and
`#!rzk rev`.

```rzk
#def zag-zig-concat
  ( p : y = x)
  ( q : y = z)
  : x = z
  := concat A x y z (rev A y x p) q

#def right-cancel-concat
  ( p q : x = y)
  ( r : y = z)
  : ( concat A x y z p r = concat A x y z q r)
  → ( p = q)
  :=
    ind-path A y
      ( \ z' r' →
          ( concat A x y z' p r' = concat A x y z' q r')
        → ( p = q))
      ( \ H → H)
      ( z)
      ( r)

#end basic-path-coherence
```

## Some derived coherences in path algebra

The statements or proofs of the following path algebra coherences reference one
of the path algebra coherences defined above.

```rzk
#section derived-path-coherence
#variable A : U
#variables x y z : A

#def rev-concat
  ( p : x = y)
  ( q : y = z)
  : rev A x z (concat A x y z p q)
  = concat A z y x (rev A y z q) (rev A x y p)
  :=
    ind-path A y
      ( \ z' q' →
          rev A x z' (concat A x y z' p q')
        = concat A z' y x (rev A y z' q') (rev A x y p))
      ( rev
          ( y = x)
          ( concat A y y x refl (rev A x y p))
          ( rev A x y p)
          ( left-unit-concat A y x (rev A x y p)))
      ( z)
      ( q)
```

### Postwhiskering paths of paths

```rzk
#def concat-eq-left
  ( p q : x = y)
  ( H : p = q)
  ( r : y = z)
  : concat A x y z p r
  = concat A x y z q r
  :=
    ind-path A y
      ( \ z' r' → (concat A x y z' p r') = (concat A x y z' q r'))
      ( H)
      ( z)
      ( r)
```

### Prewhiskering paths of paths

Prewhiskering paths of paths is much harder.

```rzk
#def concat-eq-right
  ( p : x = y)
  : ( q : y = z)
  → ( r : y = z)
  → ( H : q = r)
  → concat A x y z p q
  = concat A x y z p r
  :=
    ind-path A x
      ( \ y' p' →
        ( q : y' = z)
      → ( r : y' = z)
      → ( H : q = r)
      → ( concat A x y' z p' q) = (concat A x y' z p' r))
      ( \ q r H →
        concat
          ( x = z)
          ( concat A x x z refl q)
          ( r)
          ( concat A x x z refl r)
          ( concat (x = z) (concat A x x z refl q) q r (left-unit-concat A x z q) H)
          ( rev (x = z) (concat A x x z refl r) r (left-unit-concat A x z r)))
      ( y)
      ( p)
```

### Identifying the two definitions of path concatenation

```rzk
#def concat-concat'
  ( p : x = y)
  : ( q : y = z)
  → concat A x y z p q
  = concat' A x y z p q
  :=
    ind-path A x
      ( \ y' p' →
          ( q' : y' =_{A} z)
        → ( concat A x y' z p' q') =_{x =_{A} z} concat' A x y' z p' q')
      ( \ q' → left-unit-concat A x z q')
      ( y)
      ( p)

#def concat'-concat
  ( p : x = y)
  ( q : y = z)
  : concat' A x y z p q
  = concat A x y z p q
  :=
    rev
      ( x = z)
      ( concat A x y z p q)
      ( concat' A x y z p q)
      ( concat-concat' p q)
```

This is easier to prove for `#!rzk concat'` than for `#!rzk concat`.

```rzk
#def alt-triangle-rotation
  ( p : x = z)
  ( q : x = y)
  : ( r : y = z)
  → ( H : p = concat' A x y z q r)
  → concat' A y x z (rev A x y q) p = r
  :=
    ind-path A x
      ( \ y' q' →
        ( r' : y' =_{A} z)
      → ( H' : p = concat' A x y' z q' r')
      → ( concat' A y' x z (rev A x y' q') p) = r')
      ( \ r' H' → H')
      ( y)
      ( q)
```

The following needs to be outside the previous section because of the usage of
`#!rzk concat-concat' A y x`.

```rzk
#end derived-path-coherence

#def triangle-rotation
  ( A : U)
  ( x y z : A)
  ( p : x = z)
  ( q : x = y)
  ( r : y = z)
  ( H : p = concat A x y z q r)
  : concat A y x z (rev A x y q) p = r
  :=
    concat
      ( y = z)
      ( concat A y x z (rev A x y q) p)
      ( concat' A y x z (rev A x y q) p)
      ( r)
      ( concat-concat' A y x z (rev A x y q) p)
      ( alt-triangle-rotation
        ( A) (x) (y) (z) (p) (q) (r)
        ( concat
          ( x = z)
          ( p)
          ( concat A x y z q r)
          ( concat' A x y z q r)
          ( H)
          ( concat-concat' A x y z q r)))
```

## Application of functions to paths

```rzk
#def ap
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( f x = f y)
  := ind-path (A) (x) (\ y' p' → (f x = f y')) (refl) (y) (p)

#def ap-rev
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( ap A B y x f (rev A x y p)) = (rev B (f x) (f y) (ap A B x y f p))
  :=
    ind-path A x
      ( \ y' p' →
        ap A B y' x f (rev A x y' p') = rev B (f x) (f y') (ap A B x y' f p'))
      ( refl)
      ( y)
      ( p)

#def ap-concat
  ( A B : U)
  ( x y z : A)
  ( f : A → B)
  ( p : x = y)
  ( q : y = z)
  : ( ap A B x z f (concat A x y z p q))
  = ( concat B (f x) (f y) (f z) (ap A B x y f p) (ap A B y z f q))
  :=
    ind-path A y
      ( \ z' q' →
        ( ap A B x z' f (concat A x y z' p q'))
      = ( concat B (f x) (f y) (f z') (ap A B x y f p) (ap A B y z' f q')))
      ( refl)
      ( z)
      ( q)

#def rev-ap-rev
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( rev B (f y) (f x) (ap A B y x f (rev A x y p))) = (ap A B x y f p)
  :=
    ind-path A x
      ( \ y' p' →
        ( rev B (f y') (f x) (ap A B y' x f (rev A x y' p')))
      = ( ap A B x y' f p'))
      ( refl)
      ( y)
      ( p)
```

The following is for a specific use.

```rzk
#def concat-ap-rev-ap-id
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( concat
      ( B) (f y) (f x) (f y)
      ( ap A B y x f (rev A x y p))
      ( ap A B x y f p))
  = ( refl)
  :=
    ind-path A x
      ( \ y' p' →
        ( concat
          ( B) (f y') (f x) (f y')
          ( ap A B y' x f (rev A x y' p')) (ap A B x y' f p'))
      = ( refl))
      ( refl)
      ( y)
      ( p)

#def ap-id
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : ( ap A A x y (identity A) p) = p
  := ind-path (A) (x) (\ y' p' → (ap A A x y' (\ z → z) p') = p') (refl) (y) (p)
```

Application of a function to homotopic paths yields homotopic paths.

```rzk
#def ap-eq
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p q : x = y)
  ( H : p = q)
  : ap A B x y f p
  = ap A B x y f q
  :=
    ind-path
      ( x = y)
      ( p)
      ( \ q' H' → (ap A B x y f p) = (ap A B x y f q'))
      ( refl)
      ( q)
      ( H)

#def ap-comp
  ( A B C : U)
  ( x y : A)
  ( f : A → B)
  ( g : B → C)
  ( p : x = y)
  : ( ap A C x y (comp A B C g f) p)
  = ( ap B C (f x) (f y) g (ap A B x y f p))
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( ap A C x y' (\ z → g (f z)) p')
      = ( ap B C (f x) (f y') g (ap A B x y' f p')))
      ( refl)
      ( y)
      ( p)

#def rev-ap-comp
  ( A B C : U)
  ( x y : A)
  ( f : A → B)
  ( g : B → C)
  ( p : x = y)
  : ( ap B C (f x) (f y) g (ap A B x y f p))
  = ( ap A C x y (comp A B C g f) p)
  :=
    rev
      ( g ( f x) = g (f y))
      ( ap A C x y (\ z → g (f z)) p)
      ( ap B C (f x) (f y) g (ap A B x y f p))
      ( ap-comp A B C x y f g p)
```

## Transport

```rzk
#section transport

#variable A : U
#variable B : A → U
```

### Transport in a type family along a path in the base

```rzk
#def transport
  ( x y : A)
  ( p : x = y)
  ( u : B x)
  : B y
  := ind-path (A) (x) (\ y' p' → B y') (u) (y) (p)
```

### The lift of a base path to a path from a term in the total space to its transport

```rzk
#def transport-lift
  ( x y : A)
  ( p : x = y)
  ( u : B x)
  : ( x , u) =_{Σ (z : A) , B z} (y , transport x y p u)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → (x , u) =_{Σ (z : A) , B z} (y' , transport x y' p' u))
      ( refl)
      ( y)
      ( p)
```

### Transport along concatenated paths

```rzk
#def transport-concat
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  ( u : B x)
  : ( transport x z (concat A x y z p q) u)
  = ( transport y z q (transport x y p u))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
        ( transport x z' (concat A x y z' p q') u)
      = ( transport y z' q' (transport x y p u)))
      ( refl)
      ( z)
      ( q)

#def transport-concat-rev
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  ( u : B x)
  : ( transport y z q (transport x y p u))
  = ( transport x z (concat A x y z p q) u)
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
        ( transport y z' q' (transport x y p u))
      = ( transport x z' (concat A x y z' p q') u))
      ( refl)
      ( z)
      ( q)
```

### Transport along homotopic paths

```rzk
#def transport2
  ( x y : A)
  ( p q : x = y)
  ( H : p = q)
  ( u : B x)
  : ( transport x y p u) = (transport x y q u)
  :=
    ind-path
      ( x = y)
      ( p)
      ( \ q' H' → (transport x y p u) = (transport x y q' u))
      ( refl)
      ( q)
      ( H)
```

### Transport along a loop

```rzk
#def transport-loop
  ( a : A)
  ( b : B a)
  : ( a = a) → B a
  := \ p → (transport a a p b)
```

```rzk
#end transport
```

## Dependent application

```rzk
#def apd
  ( A : U)
  ( B : A → U)
  ( x y : A)
  ( f : (z : A) → B z)
  ( p : x = y)
  : ( transport A B x y p (f x)) = f y
  :=
    ind-path
      ( A)
      ( x)
      ( ( \ y' p' → (transport A B x y' p' (f x)) = f y'))
      ( refl)
      ( y)
      ( p)
```

## Higher-order concatenation

For convenience, we record lemmas for higher-order concatenation here.

```rzk
#section higher-concatenation
#variable A : U

#def triple-concat
  ( a0 a1 a2 a3 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  : a0 = a3
  := concat A a0 a1 a3 p1 (concat A a1 a2 a3 p2 p3)

#def quadruple-concat
  ( a0 a1 a2 a3 a4 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  : a0 = a4
  := triple-concat a0 a1 a2 a4 p1 p2 (concat A a2 a3 a4 p3 p4)

#def quintuple-concat
  ( a0 a1 a2 a3 a4 a5 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  ( p5 : a4 = a5)
  : a0 = a5
  := quadruple-concat a0 a1 a2 a3 a5 p1 p2 p3 (concat A a3 a4 a5 p4 p5)

#def alternating-quintuple-concat
  ( a0 : A)
  ( a1 : A) (p1 : a0 = a1)
  ( a2 : A) (p2 : a1 = a2)
  ( a3 : A) (p3 : a2 = a3)
  ( a4 : A) (p4 : a3 = a4)
  ( a5 : A) (p5 : a4 = a5)
  : a0 = a5
  := quadruple-concat a0 a1 a2 a3 a5 p1 p2 p3 (concat A a3 a4 a5 p4 p5)

#def 12ary-concat
  ( a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  ( p5 : a4 = a5)
  ( p6 : a5 = a6)
  ( p7 : a6 = a7)
  ( p8 : a7 = a8)
  ( p9 : a8 = a9)
  ( p10 : a9 = a10)
  ( p11 : a10 = a11)
  ( p12 : a11 = a12)
  : a0 = a12
  :=
    quintuple-concat
      a0 a1 a2 a3 a4 a12
      p1 p2 p3 p4
      ( quintuple-concat
        a4 a5 a6 a7 a8 a12
        p5 p6 p7 p8
        ( quadruple-concat
          a8 a9 a10 a11 a12
          p9 p10 p11 p12))
```

The following is the same as above but with alternating arguments.

```rzk
#def alternating-12ary-concat
  ( a0 : A)
  ( a1 : A) (p1 : a0 = a1)
  ( a2 : A) (p2 : a1 = a2)
  ( a3 : A) (p3 : a2 = a3)
  ( a4 : A) (p4 : a3 = a4)
  ( a5 : A) (p5 : a4 = a5)
  ( a6 : A) (p6 : a5 = a6)
  ( a7 : A) (p7 : a6 = a7)
  ( a8 : A) (p8 : a7 = a8)
  ( a9 : A) (p9 : a8 = a9)
  ( a10 : A) (p10 : a9 = a10)
  ( a11 : A) (p11 : a10 = a11)
  ( a12 : A) (p12 : a11 = a12)
  : a0 = a12
  :=
    12ary-concat
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
      p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12

#end higher-concatenation
```

## Higher-order coherences

```rzk
#def rev-refl-id-triple-concat
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : triple-concat A y x x y (rev A x y p) refl p = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → triple-concat A y' x x y' (rev A x y' p') refl p' = refl)
      ( refl)
      ( y)
      ( p)

#def ap-rev-refl-id-triple-concat
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( ap A B y y f (triple-concat A y x x y (rev A x y p) refl p)) = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( ap A B y' y' f (triple-concat A y' x x y' (rev A x y' p') refl p'))
      = ( refl))
      ( refl)
      ( y)
      ( p)

#def ap-triple-concat
  ( A B : U)
  ( w x y z : A)
  ( f : A → B)
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : ( ap A B w z f (triple-concat A w x y z p q r))
  = ( triple-concat
      ( B)
      ( f w)
      ( f x)
      ( f y)
      ( f z)
      ( ap A B w x f p)
      ( ap A B x y f q)
      ( ap A B y z f r))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' →
        ( ap A B w z' f (triple-concat A w x y z' p q r'))
      = ( triple-concat
          ( B)
          ( f w) (f x) (f y) (f z')
          ( ap A B w x f p)
          ( ap A B x y f q)
          ( ap A B y z' f r')))
      ( ap-concat A B w x y f p q)
      ( z)
      ( r)

#def triple-concat-eq-first
  ( A : U)
  ( w x y z : A)
  ( p q : w = x)
  ( r : x = y)
  ( s : y = z)
  ( H : p = q)
  : ( triple-concat A w x y z p r s) = (triple-concat A w x y z q r s)
  := concat-eq-left A w x z p q H (concat A x y z r s)

#def triple-concat-eq-second
  ( A : U)
  ( w x y z : A)
  ( p : w = x)
  ( q r : x = y)
  ( s : y = z)
  ( H : q = r)
  : ( triple-concat A w x y z p q s) = (triple-concat A w x y z p r s)
  :=
    ind-path
      ( x = y)
      ( q)
      ( \ r' H' →
        triple-concat A w x y z p q s = triple-concat A w x y z p r' s)
      ( refl)
      ( r)
      ( H)
```
