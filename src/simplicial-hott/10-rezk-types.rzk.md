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
    := (comp-Segal A is-segal-A x y x f g) =_{hom A x x} (id-arr A x)

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
    := (comp-Segal A is-segal-A y x y h f) =_{hom A y y} (id-arr A y)

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
            (comp-Segal A is-segal-A y x y g f)
            (comp-Segal A is-segal-A y x y h f)
            (id-arr A y)
            (postwhisker-homotopy-Segal A is-segal-A y x y g h f
                (alternating-quintuple-concat (hom A y x)
                g (comp-Segal A is-segal-A y y x (id-arr A y) g) -- a0 = g and a1 = g o id_y
                (rev (hom A y x) (comp-Segal A is-segal-A y y x (id-arr A y) g) g (id-comp-Segal A is-segal-A y x g)) -- p1 = identity law

                (comp-Segal A is-segal-A y y x (comp-Segal A is-segal-A y x y h f) g) -- a2 = g o (f o h)
                (postwhisker-homotopy-Segal A is-segal-A y y x                      -- p2 = postwhiskering
        (id-arr A y)
        (comp-Segal A is-segal-A y x y h f)
        g
        (rev (hom A y y) (comp-Segal A is-segal-A y x y h f) (id-arr A y) q)
                )

                (comp-Segal A is-segal-A y x x h (comp-Segal A is-segal-A x y x f g)) -- a3 = (g o f) o h
                (associativity-Segal extext A is-segal-A y x y x h f g)             -- p3 = associativity

                (comp-Segal A is-segal-A y x x h (id-arr A x)) -- a4 = id_x o h
                (prewhisker-homotopy-Segal A is-segal-A y x x h -- p4 = prewhiskering
                (comp-Segal A is-segal-A x y x f g)
                (id-arr A x)
                p)
                h -- a5 = h
                (comp-id-Segal A is-segal-A y x h) -- p5 = connect through identity law
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
  : (z : A) → has-retraction (hom A z x) (hom A z y) (postcomp-Segal A is-segal-A x y f z)
  :=
    \ z →
    ( (postcomp-Segal A is-segal-A y x g z) ,
        \ k →
      (triple-concat
        (hom A z x) -- k is an arrow z → x
        (comp-Segal A is-segal-A z y x (comp-Segal A is-segal-A z x y k f) g) -- g(fk)
        (comp-Segal A is-segal-A z x x k (comp-Segal A is-segal-A x y x f g)) -- (gf)k
        (comp-Segal A is-segal-A z x x k (id-arr A x)) -- id_x k
        k --k
      (associativity-Segal extext A is-segal-A z x y x k f g) -- g(fk) = (gf)k
      (prewhisker-homotopy-Segal A is-segal-A z x x k (comp-Segal A is-segal-A x y x f g) (id-arr A x) gg)  -- (gf)k = id_x k from (gf) = id_x
      (comp-id-Segal A is-segal-A z x k) -- id_x k = k
      )
  )

#def if-iso-then-postcomp-has-section uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (h : hom A y x)
  (hh : arrow-has-section A is-segal-A x y f h)
  : (z : A) → has-section (hom A z x) (hom A z y) (postcomp-Segal A is-segal-A x y f z)
  :=
    \ z →
    ( (postcomp-Segal A is-segal-A y x h z) ,
        \ k →
      (triple-concat
        (hom A z y) -- k is an arrow z to y
        (comp-Segal A is-segal-A z x y (comp-Segal A is-segal-A z y x k h) f) -- f(hk)
        (comp-Segal A is-segal-A z y y k (comp-Segal A is-segal-A y x y h f)) -- (fh)k
        (comp-Segal A is-segal-A z y y k (id-arr A y)) -- id_y k
        k --k
      (associativity-Segal extext A is-segal-A z y x y k h f) -- f(hk) = (fh)k
      (prewhisker-homotopy-Segal A is-segal-A z y y k (comp-Segal A is-segal-A y x y h f) (id-arr A y) hh)  -- (fh)k = id_y k from (fh) = id_y
      (comp-id-Segal A is-segal-A z y k) -- id_y k = k
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
  : (z : A) → is-equiv (hom A z x) (hom A z y) (postcomp-Segal A is-segal-A x y f z)
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
  : (z : A) → has-retraction (hom A y z) (hom A x z) (precomp-Segal A is-segal-A x y f z)
  :=
    \ z →
    ( (precomp-Segal A is-segal-A y x h z) ,
        \ k →
      (triple-concat
        (hom A y z) -- k is an arrow y → z
        (comp-Segal A is-segal-A y x z h (comp-Segal A is-segal-A x y z f k)) -- (kf)h
        (comp-Segal A is-segal-A y y z (comp-Segal A is-segal-A y x y h f) k) -- k(fh)
        (comp-Segal A is-segal-A y y z (id-arr A y) k) -- k id_y
        k --k
      (rev (hom A y z)
          (comp-Segal A is-segal-A y y z (comp-Segal A is-segal-A y x y h f) k)
          (comp-Segal A is-segal-A y x z h (comp-Segal A is-segal-A x y z f k))
          (associativity-Segal extext A is-segal-A y x y z h f k)
      ) -- (kf)h = k(fh)

      (postwhisker-homotopy-Segal A is-segal-A y y z (comp-Segal A is-segal-A y x y h f) (id-arr A y) k hh)  -- k(fh) = k id_y from (fh) = id_y
      (id-comp-Segal A is-segal-A y z k) -- k id_y = k
      )
  )

#def if-iso-then-precomp-has-section uses (extext)
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-has-retraction A is-segal-A x y f g)
  : (z : A) → has-section (hom A y z) (hom A x z) (precomp-Segal A is-segal-A x y f z)
  :=
    \ z →
    ( (precomp-Segal A is-segal-A y x g z) ,
        \ k →
      (triple-concat
        (hom A x z) -- k is an arrow x → z
        (comp-Segal A is-segal-A x y z f (comp-Segal A is-segal-A y x z g k)) -- (kg)f
        (comp-Segal A is-segal-A x x z (comp-Segal A is-segal-A x y x f g) k) -- k(gf)
        (comp-Segal A is-segal-A x x z (id-arr A x) k) -- k id_x
        k --k
      (rev (hom A x z)
          (comp-Segal A is-segal-A x x z (comp-Segal A is-segal-A x y x f g) k)
          (comp-Segal A is-segal-A x y z f (comp-Segal A is-segal-A y x z g k))
          (associativity-Segal extext A is-segal-A x y x z f g k)
      ) -- (kg)f = k(gf)
      (postwhisker-homotopy-Segal A is-segal-A x x z (comp-Segal A is-segal-A x y x f g) (id-arr A x) k gg)  -- k(gf) = k id_x from (gf) = id_x
      (id-comp-Segal A is-segal-A x z k) -- k id_x = k
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
  : (z : A) → is-equiv (hom A y z) (hom A x z) (precomp-Segal A is-segal-A x y f z)
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
  := (is-contr-map-is-equiv (hom A y x) (hom A x x) (precomp-Segal A is-segal-A x y f x)
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
  := (is-contr-map-is-equiv (hom A y x) (hom A y y) (postcomp-Segal A is-segal-A x y f y)
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
      (id-comp-Segal A is-segal-A x x (id-arr A x))
    ) ,
    (
      (id-arr A x) ,
      (id-comp-Segal A is-segal-A x x (id-arr A x))
    )
      )
  )

#def idtoiso
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  : (x = y) → Iso A is-segal-A x y
  := \ p → idJ (A , x , \ y' p' → Iso A is-segal-A x y' , (id-iso A is-segal-A x) , y , p)

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
            ( comp-Segal A is-segal-A a b a
              ( first (ainitial b))
              ( first (binitial a)))
            ( id-arr A a)) ,
        ( first (binitial a) ,
          contractible-connecting-htpy
            ( hom A b b)
            ( binitial b)
            ( comp-Segal A is-segal-A b a b
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
            ( comp-Segal A is-segal-A a b a
              ( first (bfinal a))
              ( first (afinal b)))
            ( id-arr A a)) ,
        ( first (afinal b) ,
          contractible-connecting-htpy
            ( hom A b b)
            ( bfinal b)
            ( comp-Segal A is-segal-A b a b
              ( first (afinal b))
              ( first (bfinal a)))
            ( id-arr A b))))
```
