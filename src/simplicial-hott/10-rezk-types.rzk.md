# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk

#section isomorphisms

#def arrow-hasRetraction
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    (g : hom A y x)
    : U
    := (Segal-comp A AisSegal x y x f g) =_{hom A x x} (id-arr A x)

#def arrow-Retraction
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (g : hom A y x), (arrow-hasRetraction A AisSegal x y f g)

#def arrow-hasSection
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    (h : hom A y x)
    : U
    := (Segal-comp A AisSegal y x y h f) =_{hom A y y} (id-arr A y)

#def arrow-Section
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (h : hom A y x), (arrow-hasSection A AisSegal x y f h)

#def arrow-isIso
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := prod (arrow-Retraction A AisSegal x y f) (arrow-Section A AisSegal x y f)

#def Iso
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    : U
    := ∑ (f : hom A x y), arrow-isIso A AisSegal x y f

#def arrow-hasInverse
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : U
    := ∑ (g : hom A y x), prod (arrow-hasRetraction A AisSegal x y f g) (arrow-hasSection A AisSegal x y f g)

#def arrow-inverse-to-iso
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-hasInverse A AisSegal x y f) -> (arrow-isIso A AisSegal x y f)
    := (\(g, (p, q)) -> ((g, p), (g, q)))

#def arrow-iso-to-inverse
    (extext : ExtExt) -- This proof uses extension extensionality.
    (A : U)
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : (arrow-isIso A AisSegal x y f) -> (arrow-hasInverse A AisSegal x y f)
    := (\((g, p), (h, q))
        -> (g, (p,
            (concat
            (hom A y y)
            (Segal-comp A AisSegal y x y g f)
            (Segal-comp A AisSegal y x y h f)
            (id-arr A y)
            (Segal-homotopy-postwhisker A AisSegal y x y g h f
                (quintuple-concat-alternating (hom A y x)
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
    (AisSegal : isSegal A)
    (x y : A)
    (f : hom A x y)
    : iff (arrow-hasInverse A AisSegal x y f) (arrow-isIso A AisSegal x y f)
    := (arrow-inverse-to-iso A AisSegal x y f, arrow-iso-to-inverse extext A AisSegal x y f)

#def if-iso-then-postcomp-is-fam-of-equiv
  (extext : ExtExt) -- This proof uses extension extensionality.
  (A : U)
  (AisSegal : isSegal A)
  (x y : A)
  (f : hom A x y)
  (g : hom A y x)
  (gg : arrow-hasRetraction A AisSegal x y f g)
  (h : hom A y x)
  (hh : arrow-hasSection A AisSegal x y f h)
  : (z : A) -> hasRetraction (hom A z x) (hom A z y) (Segal-postcomp A AisSegal x y f z)
  := \z -> (
        (Segal-postcomp A AisSegal y x g z),
        \k ->
      (triple-concat
        (hom A z x)
        (Segal-comp A AisSegal z y x (Segal-comp A AisSegal z x y k f) g) -- g(fk)
        (Segal-comp A AisSegal z x x k (Segal-comp A AisSegal x y x f g)) -- (gf)k
        (Segal-comp A AisSegal z x x k (id-arr A x)) -- id_x k
        k --k
      (Segal-associativity extext A AisSegal z x y x k f g) -- g(fk) = (gf)k
      (Segal-homotopy-prewhisker A AisSegal z x x k (Segal-comp A AisSegal x y x f g) (id-arr A x) gg)  -- (gf)k = id_x k from (gf) = id_x
      (Segal-comp-id A AisSegal z x k) -- id_x k = k
       )
  )
#end isomorphisms
```
