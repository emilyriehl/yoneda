# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk

#section isomorphisms

#def arrow-has-retraction
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    (g : hom A y x)
    : U
    := (Segal-comp A AisSegal x y x f g) =_{hom A x x} (id-arr A x)

#def arrow-Retraction
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (g : hom A y x) , (arrow-has-retraction A AisSegal x y f g)

#def arrow-has-section
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    (h : hom A y x)
    : U
    := (Segal-comp A AisSegal y x y h f) =_{hom A y y} (id-arr A y)

#def arrow-Section
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (h : hom A y x) , (arrow-has-section A AisSegal x y f h)

#def arrow-is-iso
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := prod (arrow-Retraction A AisSegal x y f) (arrow-Section A AisSegal x y f)

#def Iso
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    : U
    := Σ (f : hom A x y) , arrow-is-iso A AisSegal x y f

#def arrow-has-inverse
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (g : hom A y x) , prod (arrow-has-retraction A AisSegal x y f g) (arrow-has-section A AisSegal x y f g)

#def arrow-inverse-to-iso
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-has-inverse A AisSegal x y f) -> (arrow-is-iso A AisSegal x y f)
    := (\ (g , (p , q)) -> ((g , p) , (g , q)))

#def arrow-iso-to-inverse
    (extext : ExtExt) -- This proof uses extension extensionality.
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-is-iso A AisSegal x y f) -> (arrow-has-inverse A AisSegal x y f)
    := (\ ((g , p) , (h , q))
        -> (g , (p ,
            (concat
            (hom A y y)
            (Segal-comp A AisSegal y x y g f)
            (Segal-comp A AisSegal y x y h f)
            (id-arr A y)
            (Segal-homotopy-postwhisker A AisSegal y x y g h f
                (alternating-quintuple-concat (hom A y x)
                g (Segal-comp A AisSegal y y x (id-arr A y) g) -- a0 = g and a1 = g o id_y
                (rev (hom A y x) (Segal-comp A AisSegal y y x (id-arr A y) g) g (Segal-id-comp A AisSegal y x g)) -- p1 = identity law

                (Segal-comp A AisSegal y y x (Segal-comp A AisSegal y x y h f) g) -- a2 = g o (f o h)
                (Segal-homotopy-postwhisker A AisSegal y y x                      -- p2 = postwhiskering
        (id-arr A y)
        (Segal-comp A AisSegal y x y h f)
        g
        (rev (hom A y y) (Segal-comp A AisSegal y x y h f) (id-arr A y) q)
                )

                (Segal-comp A AisSegal y x x h (Segal-comp A AisSegal x y x f g)) -- a3 = (g o f) o h
                (Segal-associativity extext A AisSegal y x y x h f g)             -- p3 = associativity

                (Segal-comp A AisSegal y x x h (id-arr A x)) -- a4 = id_x o h
                (Segal-homotopy-prewhisker A AisSegal y x x h -- p4 = prewhiskering
                (Segal-comp A AisSegal x y x f g)
                (id-arr A x)
                p)
                h -- a5 = h
                (Segal-comp-id A AisSegal y x h) -- p5 = connect through identity law
                )
                )
            q
            )
        )
    )
 )

#def arrow-inverse-iff-iso
    (extext : ExtExt) -- This proof uses extension extensionality.
    (A : U)
    (AisSegal : is-segal A)
    (x y : A)
    (f : hom A x y)
    : iff (arrow-has-inverse A AisSegal x y f) (arrow-is-iso A AisSegal x y f)
    := (arrow-inverse-to-iso A AisSegal x y f , arrow-iso-to-inverse extext A AisSegal x y f)

#def if-iso-then-postcomp-has-retraction
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  : (z : A) -> has-retraction (hom A z x) (hom A z y) (Segal-postcomp A AisSegal x y f z)
  :=
    \ z ->
    ( (Segal-postcomp A AisSegal y x g z) ,
        \ k ->
      (triple-concat
        (hom A z x) -- k is an arrow z -> x
        (Segal-comp A AisSegal z y x (Segal-comp A AisSegal z x y k f) g) -- g(fk)
        (Segal-comp A AisSegal z x x k (Segal-comp A AisSegal x y x f g)) -- (gf)k
        (Segal-comp A AisSegal z x x k (id-arr A x)) -- id_x k
        k --k
      (Segal-associativity extext A AisSegal z x y x k f g) -- g(fk) = (gf)k
      (Segal-homotopy-prewhisker A AisSegal z x x k (Segal-comp A AisSegal x y x f g) (id-arr A x) gg)  -- (gf)k = id_x k from (gf) = id_x
      (Segal-comp-id A AisSegal z x k) -- id_x k = k
       )
  )

#def if-iso-then-postcomp-has-section
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : (z : A) -> has-section (hom A z x) (hom A z y) (Segal-postcomp A AisSegal x y f z)
  :=
    \ z ->
    ( (Segal-postcomp A AisSegal y x h z) ,
        \ k ->
      (triple-concat
        (hom A z y) -- k is an arrow z to y
        (Segal-comp A AisSegal z x y (Segal-comp A AisSegal z y x k h) f) -- f(hk)
        (Segal-comp A AisSegal z y y k (Segal-comp A AisSegal y x y h f)) -- (fh)k
        (Segal-comp A AisSegal z y y k (id-arr A y)) -- id_y k
        k --k
      (Segal-associativity extext A AisSegal z y x y k h f) -- f(hk) = (fh)k
      (Segal-homotopy-prewhisker A AisSegal z y y k (Segal-comp A AisSegal y x y h f) (id-arr A y) hh)  -- (fh)k = id_y k from (fh) = id_y
      (Segal-comp-id A AisSegal z y k) -- id_y k = k
       )
  )

#def if-iso-then-postcomp-is-equiv
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : (z : A) -> is-equiv (hom A z x) (hom A z y) (Segal-postcomp A AisSegal x y f z)
  :=
    \ z ->
    ( (if-iso-then-postcomp-has-retraction extext A AisSegal x y f g gg z) ,
      (if-iso-then-postcomp-has-section extext A AisSegal x y f h hh z))

#def if-iso-then-precomp-has-retraction
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : (z : A) -> has-retraction (hom A y z) (hom A x z) (Segal-precomp A AisSegal x y f z)
  :=
    \ z ->
    ( (Segal-precomp A AisSegal y x h z) ,
        \ k ->
      (triple-concat
        (hom A y z) -- k is an arrow y -> z
        (Segal-comp A AisSegal y x z h (Segal-comp A AisSegal x y z f k)) -- (kf)h
        (Segal-comp A AisSegal y y z (Segal-comp A AisSegal y x y h f) k) -- k(fh)
        (Segal-comp A AisSegal y y z (id-arr A y) k) -- k id_y
        k --k
      (rev (hom A y z)
          (Segal-comp A AisSegal y y z (Segal-comp A AisSegal y x y h f) k)
          (Segal-comp A AisSegal y x z h (Segal-comp A AisSegal x y z f k))
          (Segal-associativity extext A AisSegal y x y z h f k)
      ) -- (kf)h = k(fh)

      (Segal-homotopy-postwhisker A AisSegal y y z (Segal-comp A AisSegal y x y h f) (id-arr A y) k hh)  -- k(fh) = k id_y from (fh) = id_y
      (Segal-id-comp A AisSegal y z k) -- k id_y = k
       )
  )

#def if-iso-then-precomp-has-section
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  : (z : A) -> has-section (hom A y z) (hom A x z) (Segal-precomp A AisSegal x y f z)
  :=
    \ z ->
    ( (Segal-precomp A AisSegal y x g z) ,
        \ k ->
      (triple-concat
        (hom A x z) -- k is an arrow x -> z
        (Segal-comp A AisSegal x y z f (Segal-comp A AisSegal y x z g k)) -- (kg)f
        (Segal-comp A AisSegal x x z (Segal-comp A AisSegal x y x f g) k) -- k(gf)
        (Segal-comp A AisSegal x x z (id-arr A x) k) -- k id_x
        k --k
      (rev (hom A x z)
          (Segal-comp A AisSegal x x z (Segal-comp A AisSegal x y x f g) k)
          (Segal-comp A AisSegal x y z f (Segal-comp A AisSegal y x z g k))
          (Segal-associativity extext A AisSegal x y x z f g k)
      ) -- (kg)f = k(gf)
      (Segal-homotopy-postwhisker A AisSegal x x z (Segal-comp A AisSegal x y x f g) (id-arr A x) k gg)  -- k(gf) = k id_x from (gf) = id_x
      (Segal-id-comp A AisSegal x z k) -- k id_x = k
       )
  )

#def if-iso-then-precomp-is-equiv
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : (z : A) -> is-equiv (hom A y z) (hom A x z) (Segal-precomp A AisSegal x y f z)
  :=
    \ z ->
    ( (if-iso-then-precomp-has-retraction extext A AisSegal x y f h hh z) ,
    (if-iso-then-precomp-has-section extext A AisSegal x y f g gg z))

#def iso-inhabited-implies-hasRetr-contr
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : is-contr (arrow-Retraction A AisSegal x y f)
  := (is-contr-map-is-equiv (hom A y x) (hom A x x) (Segal-precomp A AisSegal x y f x)
                          (if-iso-then-precomp-is-equiv extext A AisSegal x y f g gg h hh x))
      (id-arr A x)

#def iso-inhabited-implies-hasSec-contr
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : is-contr (arrow-Section A AisSegal x y f)
  := (is-contr-map-is-equiv (hom A y x) (hom A y y) (Segal-postcomp A AisSegal x y f y)
                          (if-iso-then-postcomp-is-equiv extext A AisSegal x y f g gg h hh y))
      (id-arr A y)

#def iso-inhabited-implies-iso-contr
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A AisSegal x y f h)
  : is-contr (arrow-is-iso A AisSegal x y f)
  := (is-contr-product (arrow-Retraction A AisSegal x y f) (arrow-Section A AisSegal x y f)
      (iso-inhabited-implies-hasRetr-contr extext A AisSegal x y f g gg h hh)
      (iso-inhabited-implies-hasSec-contr extext A AisSegal x y f g gg h hh)
    )

#def iso-is-prop
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  (f : hom A x y)
   : (is-prop (arrow-is-iso A AisSegal x y f))
  := (is-prop-is-contr-is-inhabited (arrow-is-iso A AisSegal x y f)
      (\ is-isof -> (iso-inhabited-implies-iso-contr extext A AisSegal x y f (first (first is-isof)) (second (first is-isof))
        (first (second is-isof)) (second (second is-isof))))
    )

#def id-iso
  (A : U)
  (AisSegal : is-segal A)
  : (x : A) -> Iso A AisSegal x x
  :=
    \ x ->
    (
    (id-arr A x) ,
    (
    (
      (id-arr A x) ,
      (Segal-id-comp A AisSegal x x (id-arr A x))
    ) ,
    (
      (id-arr A x) ,
      (Segal-id-comp A AisSegal x x (id-arr A x))
    )
      )
  )

#def idtoiso
  (A : U)
  (AisSegal : is-segal A)
  (x y : A)
  : (x = y) -> Iso A AisSegal x y
  := \ p -> idJ (A , x , \ y' p' -> Iso A AisSegal x y' , (id-iso A AisSegal x) , y , p)

#def is-rezk
  (A : U)
  : U
  := Σ (AisSegal : is-segal A) , (x : A) -> (y : A) -> is-equiv (x = y) (Iso A AisSegal x y) (idtoiso A AisSegal x y)



#end isomorphisms
```

#def cocomma (B : U) (b : B) : U := (Σ (x : B) , (hom B b x))

#def comma (B : U) (b : B) : U := (Σ (x : B) , (hom B x b))

#def hom-cocomma (B : U) (b : B) : U := axiom-choice 2 Δ¹ ∂Δ¹ (\ t ->

#def axiom-choice (I : CUBE) (ψ : I -> TOPE) (ϕ : ψ -> TOPE) (X : ψ -> U) (Y :
(t : ψ) -> (x : X t) -> U) (a : (t : ϕ) -> X t) (b : (t : ϕ) -> Y t (a t)) : Eq
({t : I | ψ t} -> (Σ (x : X t) , Y t x) [ ϕ t |-> (a t , b t) ]) (Σ (f : ({t : I
| ψ t} -> X t [ϕ t |-> a t ])) , ({t : I | ψ t} -> Y t (f t) [ ϕ t |-> b t ]))
