# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on extension extensionality:

```rzk
#assume extext : ExtExt
```

```rzk
#section isomorphisms

#def arrow-has-retraction
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    (g : hom A y x)
    : U
    := (Segal-comp A is-segal-A x y x f g) =_{hom A x x} (id-arr A x)

#def arrow-Retraction
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (g : hom A y x) , (arrow-has-retraction A is-segal-A x y f g)

#def arrow-has-section
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    (h : hom A y x)
    : U
    := (Segal-comp A is-segal-A y x y h f) =_{hom A y y} (id-arr A y)

#def arrow-Section
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (h : hom A y x) , (arrow-has-section A is-segal-A x y f h)

#def arrow-is-iso
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := product (arrow-Retraction A is-segal-A x y f) (arrow-Section A is-segal-A x y f)

#def Iso
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    : U
    := Σ (f : hom A x y) , arrow-is-iso A is-segal-A x y f

#def arrow-has-inverse
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : U
    := Σ (g : hom A y x) , product (arrow-has-retraction A is-segal-A x y f g) (arrow-has-section A is-segal-A x y f g)

#def arrow-inverse-to-iso
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-has-inverse A is-segal-A x y f) → (arrow-is-iso A is-segal-A x y f)
    := (\ (g , (p , q)) → ((g , p) , (g , q)))

#def arrow-iso-to-inverse uses (extext)
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-is-iso A is-segal-A x y f) → (arrow-has-inverse A is-segal-A x y f)
    := (\ ((g , p) , (h , q))
        → (g , (p ,
            (concat
            (hom A y y)
            (Segal-comp A is-segal-A y x y g f)
            (Segal-comp A is-segal-A y x y h f)
            (id-arr A y)
            (Segal-homotopy-postwhisker A is-segal-A y x y g h f
                (alternating-quintuple-concat (hom A y x)
                g (Segal-comp A is-segal-A y y x (id-arr A y) g) -- a0 = g and a1 = g o id_y
                (rev (hom A y x) (Segal-comp A is-segal-A y y x (id-arr A y) g) g (Segal-id-comp A is-segal-A y x g)) -- p1 = identity law

                (Segal-comp A is-segal-A y y x (Segal-comp A is-segal-A y x y h f) g) -- a2 = g o (f o h)
                (Segal-homotopy-postwhisker A is-segal-A y y x                      -- p2 = postwhiskering
        (id-arr A y)
        (Segal-comp A is-segal-A y x y h f)
        g
        (rev (hom A y y) (Segal-comp A is-segal-A y x y h f) (id-arr A y) q)
                )

                (Segal-comp A is-segal-A y x x h (Segal-comp A is-segal-A x y x f g)) -- a3 = (g o f) o h
                (Segal-associativity extext A is-segal-A y x y x h f g)             -- p3 = associativity

                (Segal-comp A is-segal-A y x x h (id-arr A x)) -- a4 = id_x o h
                (Segal-homotopy-prewhisker A is-segal-A y x x h -- p4 = prewhiskering
                (Segal-comp A is-segal-A x y x f g)
                (id-arr A x)
                p)
                h -- a5 = h
                (Segal-comp-id A is-segal-A y x h) -- p5 = connect through identity law
                )
                )
            q
            )
        )
    )
 )

#def arrow-inverse-iff-iso uses (extext)
    (A : U)
    (is-segal-A : is-segal A)
    (x y : A)
    (f : hom A x y)
    : iff (arrow-has-inverse A is-segal-A x y f) (arrow-is-iso A is-segal-A x y f)
    := (arrow-inverse-to-iso A is-segal-A x y f , arrow-iso-to-inverse A is-segal-A x y f)

#def if-iso-then-postcomp-has-retraction uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  : (z : A) → has-retraction (hom A z x) (hom A z y) (Segal-postcomp A is-segal-A x y f z)
  :=
    \ z →
    ( (Segal-postcomp A is-segal-A y x g z) ,
        \ k →
      (triple-concat
        (hom A z x) -- k is an arrow z → x
        (Segal-comp A is-segal-A z y x (Segal-comp A is-segal-A z x y k f) g) -- g(fk)
        (Segal-comp A is-segal-A z x x k (Segal-comp A is-segal-A x y x f g)) -- (gf)k
        (Segal-comp A is-segal-A z x x k (id-arr A x)) -- id_x k
        k --k
      (Segal-associativity extext A is-segal-A z x y x k f g) -- g(fk) = (gf)k
      (Segal-homotopy-prewhisker A is-segal-A z x x k (Segal-comp A is-segal-A x y x f g) (id-arr A x) gg)  -- (gf)k = id_x k from (gf) = id_x
      (Segal-comp-id A is-segal-A z x k) -- id_x k = k
      )
  )

#def if-iso-then-postcomp-has-section uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : (z : A) → has-section (hom A z x) (hom A z y) (Segal-postcomp A is-segal-A x y f z)
  :=
    \ z →
    ( (Segal-postcomp A is-segal-A y x h z) ,
        \ k →
      (triple-concat
        (hom A z y) -- k is an arrow z to y
        (Segal-comp A is-segal-A z x y (Segal-comp A is-segal-A z y x k h) f) -- f(hk)
        (Segal-comp A is-segal-A z y y k (Segal-comp A is-segal-A y x y h f)) -- (fh)k
        (Segal-comp A is-segal-A z y y k (id-arr A y)) -- id_y k
        k --k
      (Segal-associativity extext A is-segal-A z y x y k h f) -- f(hk) = (fh)k
      (Segal-homotopy-prewhisker A is-segal-A z y y k (Segal-comp A is-segal-A y x y h f) (id-arr A y) hh)  -- (fh)k = id_y k from (fh) = id_y
      (Segal-comp-id A is-segal-A z y k) -- id_y k = k
      )
  )

#def if-iso-then-postcomp-is-equiv uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : (z : A) → is-equiv (hom A z x) (hom A z y) (Segal-postcomp A is-segal-A x y f z)
  :=
    \ z →
    ( (if-iso-then-postcomp-has-retraction A is-segal-A x y f g gg z) ,
      (if-iso-then-postcomp-has-section A is-segal-A x y f h hh z))

#def if-iso-then-precomp-has-retraction uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : (z : A) → has-retraction (hom A y z) (hom A x z) (Segal-precomp A is-segal-A x y f z)
  :=
    \ z →
    ( (Segal-precomp A is-segal-A y x h z) ,
        \ k →
      (triple-concat
        (hom A y z) -- k is an arrow y → z
        (Segal-comp A is-segal-A y x z h (Segal-comp A is-segal-A x y z f k)) -- (kf)h
        (Segal-comp A is-segal-A y y z (Segal-comp A is-segal-A y x y h f) k) -- k(fh)
        (Segal-comp A is-segal-A y y z (id-arr A y) k) -- k id_y
        k --k
      (rev (hom A y z)
          (Segal-comp A is-segal-A y y z (Segal-comp A is-segal-A y x y h f) k)
          (Segal-comp A is-segal-A y x z h (Segal-comp A is-segal-A x y z f k))
          (Segal-associativity extext A is-segal-A y x y z h f k)
      ) -- (kf)h = k(fh)

      (Segal-homotopy-postwhisker A is-segal-A y y z (Segal-comp A is-segal-A y x y h f) (id-arr A y) k hh)  -- k(fh) = k id_y from (fh) = id_y
      (Segal-id-comp A is-segal-A y z k) -- k id_y = k
      )
  )

#def if-iso-then-precomp-has-section uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  : (z : A) → has-section (hom A y z) (hom A x z) (Segal-precomp A is-segal-A x y f z)
  :=
    \ z →
    ( (Segal-precomp A is-segal-A y x g z) ,
        \ k →
      (triple-concat
        (hom A x z) -- k is an arrow x → z
        (Segal-comp A is-segal-A x y z f (Segal-comp A is-segal-A y x z g k)) -- (kg)f
        (Segal-comp A is-segal-A x x z (Segal-comp A is-segal-A x y x f g) k) -- k(gf)
        (Segal-comp A is-segal-A x x z (id-arr A x) k) -- k id_x
        k --k
      (rev (hom A x z)
          (Segal-comp A is-segal-A x x z (Segal-comp A is-segal-A x y x f g) k)
          (Segal-comp A is-segal-A x y z f (Segal-comp A is-segal-A y x z g k))
          (Segal-associativity extext A is-segal-A x y x z f g k)
      ) -- (kg)f = k(gf)
      (Segal-homotopy-postwhisker A is-segal-A x x z (Segal-comp A is-segal-A x y x f g) (id-arr A x) k gg)  -- k(gf) = k id_x from (gf) = id_x
      (Segal-id-comp A is-segal-A x z k) -- k id_x = k
      )
  )

#def if-iso-then-precomp-is-equiv uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : (z : A) → is-equiv (hom A y z) (hom A x z) (Segal-precomp A is-segal-A x y f z)
  :=
    \ z →
    ( (if-iso-then-precomp-has-retraction A is-segal-A x y f h hh z) ,
    (if-iso-then-precomp-has-section A is-segal-A x y f g gg z))

#def iso-inhabited-implies-hasRetr-contr uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : is-contr (arrow-Retraction A is-segal-A x y f)
  := (is-contr-map-is-equiv (hom A y x) (hom A x x) (Segal-precomp A is-segal-A x y f x)
                          (if-iso-then-precomp-is-equiv A is-segal-A x y f g gg h hh x))
      (id-arr A x)

#def iso-inhabited-implies-hasSec-contr uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : is-contr (arrow-Section A is-segal-A x y f)
  := (is-contr-map-is-equiv (hom A y x) (hom A y y) (Segal-postcomp A is-segal-A x y f y)
                          (if-iso-then-postcomp-is-equiv A is-segal-A x y f g gg h hh y))
      (id-arr A y)

#def iso-inhabited-implies-iso-contr uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : is-contr (arrow-is-iso A is-segal-A x y f)
  := (is-contr-product (arrow-Retraction A is-segal-A x y f) (arrow-Section A is-segal-A x y f)
      (iso-inhabited-implies-hasRetr-contr A is-segal-A x y f g gg h hh)
      (iso-inhabited-implies-hasSec-contr A is-segal-A x y f g gg h hh)
    )

#def iso-is-prop uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
   : (is-prop (arrow-is-iso A is-segal-A x y f))
  := (is-prop-is-contr-is-inhabited (arrow-is-iso A is-segal-A x y f)
      (\ is-isof → (iso-inhabited-implies-iso-contr A is-segal-A x y f (first (first is-isof)) (second (first is-isof))
        (first (second is-isof)) (second (second is-isof))))
    )

#def id-iso
  (A : U)
  (is-segal-A : is-segal A)
  : (x : A) → Iso A is-segal-A x x
  :=
    \ x →
    (
    (id-arr A x) ,
    (
    (
      (id-arr A x) ,
      (Segal-id-comp A is-segal-A x x (id-arr A x))
    ) ,
    (
      (id-arr A x) ,
      (Segal-id-comp A is-segal-A x x (id-arr A x))
    )
      )
  )

#def idtoiso
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  : (x = y) → Iso A is-segal-A x y
  := \ p → ind-path (A) (x) (\ y' p' → Iso A is-segal-A x y') ((id-iso A is-segal-A x)) (y) (p)

#def is-rezk
  (A : U)
  : U
  := Σ (is-segal-A : is-segal A) , (x : A) → (y : A) → is-equiv (x = y) (Iso A is-segal-A x y) (idtoiso A is-segal-A x y)
#end isomorphisms
```

In a Segal type, initial objects are isomorphic.

```rzk
#def initial-iso
  (A : U)
  (is-segal-A : is-segal A)
  (a b : A)
  (ainitial : is-initial A a)
  (binitial : is-initial A b)
  : Iso A is-segal-A a b
  :=
    ( first (ainitial b) ,
      ( ( first (binitial a) ,
          contractible-connecting-htpy
            ( hom A a a)
            ( ainitial a)
            ( Segal-comp A is-segal-A a b a
              ( first (ainitial b))
              ( first (binitial a)))
            ( id-arr A a)) ,
        ( first (binitial a) ,
          contractible-connecting-htpy
            ( hom A b b)
            ( binitial b)
            ( Segal-comp A is-segal-A b a b
              ( first (binitial a))
              ( first (ainitial b)))
            ( id-arr A b))))
```

In a Segal type, final objects are isomorphic.

```rzk
#def final-iso
  (A : U)
  (is-segal-A : is-segal A)
  (a b : A)
  (afinal : is-final A a)
  (bfinal : is-final A b)
  (iso : Iso A is-segal-A a b)
  : Iso A is-segal-A a b
  :=
    ( first (bfinal a) ,
      ( ( first (afinal b) ,
          contractible-connecting-htpy
            ( hom A a a)
            ( afinal a)
            ( Segal-comp A is-segal-A a b a
              ( first (bfinal a))
              ( first (afinal b)))
            ( id-arr A a)) ,
        ( first (afinal b) ,
          contractible-connecting-htpy
            ( hom A b b)
            ( bfinal b)
            ( Segal-comp A is-segal-A b a b
              ( first (afinal b))
              ( first (bfinal a)))
            ( id-arr A b))))
```
