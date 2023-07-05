# 5. Sigma types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Paths involving products

```rzk
#section paths-in-products

#variables A B : U

#def path-product
  ( a a' : A)
  ( b b' : B)
  ( e_A : a = a')
  ( e_B : b = b')
  : (a , b) =_{prod A B} (a' , b')
  := transport A (\ x -> (a , b) =_{prod A B} (x , b')) a a' e_A
      ( transport B (\ y -> (a , b) =_{prod A B} (a , y)) b b' e_B refl)

#def first-path-product
  ( x y : prod A B)
  ( e : x =_{prod A B} y)
  : first x = first y
  := ap (prod A B) A x y (\ z -> first z) e

#def second-path-product
  ( x y : prod A B)
  ( e : x =_{prod A B} y)
  : second x = second y
  := ap (prod A B) B x y (\ z -> second z) e

#end paths-in-products
```

## Identity types of sigma types

```rzk
#section paths-in-sigma

#variable A : U
#variable B : A -> U

#def first-path-Σ
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : first s = first t
  := ap (Σ (a : A) , B a) A s t (\ z -> first z) e

#def second-path-Σ
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : ( transport A B (first s) (first t) (first-path-Σ s t e) (second s)) =
    ( second t)
  :=
    idJ
    ( ( Σ (a : A) , B a) ,
      ( s) ,
      ( \ t' e' ->
        ( transport A B
          ( first s) (first t') (first-path-Σ s t' e') (second s)) =
        ( second t')) ,
      ( refl) ,
      ( t) ,
      ( e))

-- [Rijke 22, Definition 9.3.1]
#def Eq-Σ
  ( s t : Σ (a : A) , B a)
  : U
  :=
    Σ ( p : (first s) = (first t)) ,
      ( transport A B (first s) (first t) p (second s)) = (second t)

-- [Rijke 22, Definition 9.3.3]
#def pair-eq
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : Eq-Σ s t
  := (first-path-Σ s t e , second-path-Σ s t e)

-- A path in a fiber defines a path in the total space
#def sigma-path-fibered-path
  ( x : A)
  ( u v : B x)
  ( p : u = v)
  : (x , u) =_{Σ (a : A) , B a} (x , v)
  := idJ (B x , u , \ v' p' -> (x , u) = (x , v') , refl , v , p)

-- Essentially eq-pair but with explicit arguments.
#def path-of-pairs-pair-of-paths
  ( x y : A)
  ( p : x = y)
  : ( u : B x) ->
    ( v : B y) ->
    ( (transport A B x y p u) = v) ->
    ( x , u) =_{Σ (z : A) , B z} (y , v)
  :=
    idJ
    ( ( A) ,
      ( x) ,
      ( \ y' p' -> (u' : B x) -> (v' : B y') ->
        ((transport A B x y' p' u') = v') ->
        (x , u') =_{Σ (z : A) , B z} (y' , v')) ,
      ( \ u' v' q' -> (sigma-path-fibered-path x u' v' q')) ,
      ( y) ,
      ( p))

-- The inverse to `pair-eq`.
#def eq-pair
  ( s t : Σ (a : A) , B a)
  ( e : Eq-Σ s t)
  : (s = t)
  :=
    path-of-pairs-pair-of-paths
      ( first s) (first t) (first e) (second s) (second t) (second e)

#def eq-pair-pair-eq
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : (eq-pair s t (pair-eq s t e)) = e
  :=
    idJ
    ( Σ (a : A) ,
      B a ,
      s ,
      \ t' e' -> (eq-pair s t' (pair-eq s t' e')) = e' ,
      refl ,
      t ,
      e)

-- Here we've decomposed e : Eq-Σ s t as (e0, e1) and decomposed s and t
-- similarly for induction purposes
#def pair-eq-eq-pair-split
  ( s0 : A)
  ( s1 : B s0)
  ( t0 : A)
  ( e0 : s0 = t0)
  : ( t1 : B t0) ->
    ( e1 : (transport A B s0 t0 e0 s1) = t1) ->
    ( ( pair-eq (s0 , s1) (t0 , t1) (eq-pair (s0 , s1) (t0 , t1) (e0 , e1)))
      =_{Eq-Σ (s0 , s1) (t0 , t1)}
      ( e0 , e1))
  :=
    idJ
    ( A ,
      s0 ,
      ( \ t0' e0' ->
        (t1 : B t0') -> (e1 : (transport A B s0 t0' e0' s1) = t1) ->
        ( ( pair-eq (s0 , s1) (t0' , t1) (eq-pair (s0 , s1) (t0' , t1) (e0' , e1)))
          =_{Eq-Σ (s0 , s1) (t0' , t1)}
          ( e0' , e1))) ,
      ( \ t1 e1 ->
        idJ
        ( B s0 ,
          s1 ,
          \ t1' e1' ->
            ( pair-eq (s0 , s1) (s0 , t1')
              ( eq-pair (s0 , s1) (s0 , t1') (refl , e1')))
              =_{Eq-Σ (s0 , s1) (s0 , t1')} (refl , e1') ,
          refl ,
          t1 ,
          e1)) ,
      t0 ,
      e0)

#def pair-eq-eq-pair
  ( s t : Σ (a : A) , B a)
  ( e : Eq-Σ s t)
  : ( pair-eq s t (eq-pair s t e)) =_{Eq-Σ s t} e
  :=
    pair-eq-eq-pair-split
    ( first s) (second s) (first t) (first e) (second t) (second e)

#def Eq-Σ-equiv
  ( s t : Σ (a : A) , B a)
  : Equiv (s = t) (Eq-Σ s t)
  :=
    ( pair-eq s t ,
      ( ( eq-pair s t , eq-pair-pair-eq s t) ,
        ( eq-pair s t , pair-eq-eq-pair s t)))

#end paths-in-sigma
```

## Identity types of sigma types over a product

```rzk
#section paths-in-sigma-over-prod

#variables A B : U
#variable C : A -> B -> U

#def prod-transport
  ( a a' : A)
  ( b b' : B)
  ( p : a = a')
  ( q : b = b')
  ( c : C a b)
  : C a' b'
  :=
    idJ
    ( B ,
      b ,
      \ b'' q' -> C a' b'' ,
      idJ (A , a , \ a'' p' -> C a'' b , c , a' , p) ,
      b' ,
      q)

#def Eq-Σ-over-prod
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  : U
  :=
    Σ ( p : (first s) = (first t)) ,
      ( Σ ( q : (first (second s)) = (first (second t))) ,
          ( prod-transport
            ( first s) (first t)
            ( first (second s)) (first (second t)) p q (second (second s)) =
            ( second (second t))))

-- ! This is the lazy definition with bad computational properties.
#def triple-eq
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : s = t)
  : Eq-Σ-over-prod s t
  :=
    idJ
    ( Σ (a : A) , (Σ (b : B) , C a b) ,
      s ,
      \ t' e' -> (Eq-Σ-over-prod s t') ,
      ( refl , (refl , refl)) ,
      t ,
      e)

-- The inverse with explicit arguments.
-- It's surprising this typechecks since we defined prod-transport by a dual
-- path induction over both p and q , rather than by saying that when p is refl
-- this is ordinary transport
#def path-of-triples-to-triple-of-paths
  ( a a' : A)
  ( u u' : B)
  ( c : C a u)
  ( p : a = a')
  : ( q : u = u') ->
    ( c' : C a' u') ->
    ( r : prod-transport a a' u u' p q c = c') ->
    ( (a, (u, c)) =_{(Σ (x : A), (Σ (y : B) , C x y))} (a', (u', c')))
  :=
    idJ
    ( ( A) ,
      ( a) ,
      ( \ a'' p' ->
        (q : u = u') ->
        (c' : C a'' u') ->
        (r : prod-transport a a'' u u' p' q c = c') ->
        ( (a, (u, c)) =_{(Σ (x : A) , (Σ (y : B), C x y))} (a'', (u', c')))) ,
      ( \ q c' r ->
        ( sigma-path-fibered-path A (\x -> (Σ (v : B) , C x v)) a
          ( u, c) ( u', c')
          ( path-of-pairs-pair-of-paths B (\y -> C a y) u u' q c c' r))) ,
      ( a') ,
      ( p))

#def eq-triple
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : Eq-Σ-over-prod s t)
  : (s = t)
  :=
    path-of-triples-to-triple-of-paths
    ( first s) (first t)
    ( first (second s)) (first (second t))
    ( second (second s)) (first e)
    ( first (second e)) (second (second t))
    ( second (second e))

#def eq-triple-triple-eq
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : s = t)
  : (eq-triple s t (triple-eq s t e)) = e
  :=
    idJ
    ( ( Σ (a : A) , (Σ (b : B) , C a b)) ,
      ( s) ,
      ( \ t' e' -> (eq-triple s t' (triple-eq s t' e')) = e') ,
      ( refl) ,
      ( t) ,
      ( e))

-- Here we've decomposed s t e for induction purposes
#def triple-eq-eq-triple-split
  ( a a' : A)
  ( b b' : B)
  ( c : C a b)
  ( p : a = a')
  : ( q : b = b') ->
    ( c' : C a' b') ->
    ( r : prod-transport a a' b b' p q c = c') ->
    ( triple-eq
      ( a , (b , c)) (a' , (b' , c'))
      ( eq-triple (a , (b , c)) (a' , (b' , c')) (p , (q , r)))) =
    ( p , (q , r))
  :=
    idJ
    ( ( A) ,
      ( a) ,
      ( \ a'' p' ->
        ( q : b = b') ->
        ( c' : C a'' b') ->
        ( r : prod-transport a a'' b b' p' q c = c') ->
        ( triple-eq
          ( a , (b , c)) (a'' , (b' , c'))
          ( eq-triple (a , (b , c)) (a'' , (b' , c')) (p' , (q , r)))) =
        ( p' , (q , r))) ,
      \ q ->
        idJ
        ( ( B) ,
          ( b) ,
          ( \ b'' q' ->
            ( c' : C a b'') ->
            ( r : prod-transport a a b b'' refl q' c = c') ->
            ( triple-eq
              ( a , (b , c)) (a , (b'' , c'))
              ( eq-triple (a , (b , c)) (a , (b'' , c')) (refl , (q' , r)))) =
              ( refl , (q' , r))) ,
          ( \ c' r ->
            idJ
            ( ( C a b) ,
              ( c) ,
              ( \ c'' r' ->
                triple-eq
                  ( a , (b , c)) (a , (b , c''))
                  ( eq-triple
                    ( a , (b , c)) (a , (b , c''))
                    ( refl , (refl , r'))) =
                  ( refl , (refl , r'))) ,
              ( refl) ,
              ( c') ,
              ( r))) ,
          ( b') ,
          ( q)) ,
      ( a') ,
      ( p))

#def triple-eq-eq-triple
  ( s t : Σ (a : A) , (Σ (b : B) , C a b))
  ( e : Eq-Σ-over-prod s t)
  : (triple-eq s t (eq-triple s t e)) = e
  :=
    triple-eq-eq-triple-split
      ( first s) (first t)
      ( first (second s)) (first (second t))
      ( second (second s)) (first e)
      ( first (second e)) (second (second t))
      ( second (second e))

#def equiv-Eq-Σ-over-prod
  (s t : Σ (a : A) , (Σ (b : B) , C a b))
  : Equiv (s = t) (Eq-Σ-over-prod s t)
  :=
    ( triple-eq s t ,
      ( ( eq-triple s t , eq-triple-triple-eq s t) ,
        ( eq-triple s t , triple-eq-eq-triple s t)))

#end paths-in-sigma-over-prod
```

## Symmetry of products

```rzk
#def sym-prod
  (A B : U)
  : Equiv (prod A B) (prod B A)
  :=
    ( \ (a , b) -> (b , a) ,
      ( ( \ (b , a) -> (a , b) ,\ p -> refl) ,
        ( \ (b , a) -> (a , b) ,\ p -> refl)))
```

## Fubini

Given a family over a pair of independent types , the order of summation is
unimportant.

```rzk
#def fubini-Σ
  (A B : U)
  (C : A -> B -> U)
  : Equiv (Σ (x : A) , Σ (y : B) , C x y) (Σ (y : B) , Σ (x : A) , C x y)
  :=
    ( \ t -> (first (second t) , (first t , second (second t))) ,
      ( ( \ t -> (first (second t) , (first t , second (second t))) ,
          \ t -> refl) ,
        ( \ t -> (first (second t) , (first t , second (second t))) ,
          \ t -> refl)))
```

Products distribute inside a sigma type:

```rzk
#def distributive-prod-Σ
  (A B : U)
  (C : B -> U)
  : Equiv (prod A (Σ (b : B) , C b)) (Σ (b : B) , prod A (C b))
  :=
    ( \ (a , (b , c)) -> (b , (a , c)) ,
      ( ( \ (b , (a , c)) -> (a , (b , c)) , \ z -> refl) ,
        ( \ (b , (a , c)) -> (a , (b , c)) , \ z -> refl)))
```

## Associativity

```rzk
#def associative-Σ
  (A : U)
  (B : A -> U)
  (C : (a : A) -> B a -> U)
  : Equiv
      ( Σ (a : A) , Σ (b : B a) , C a b)
      ( Σ (ab : Σ (a : A) , B a) , C (first ab) (second ab))
  :=
    ( \ (a , (b , c)) -> ((a , b) , c) ,
      ( ( \ ((a , b) , c) -> (a , (b , c)) , \ _ -> refl) ,
        ( \ ((a , b) , c) -> (a , (b , c)) , \ _ -> refl)))
```
