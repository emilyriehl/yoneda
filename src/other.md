# Other Yoneda formalizations

Below is an incomplete list of Yoneda lemma formalizations in different systems:

| Library                                                  | System       | Foundations                 | Yoneda                                                                |
| -------------------------------------------------------- | ------------ | --------------------------- | --------------------------------------------------------------------- |
| [agda-categories]                                        | Agda         | Traditional, proof relevant | [1-categories][agda-categories-yoneda][^1]                            |
| [agda-unimath]                                           | Agda         | HoTT/UF                     | [1-categories][agda-unimath-yoneda]                                   |
| [UniMath]                                                | Coq          | HoTT/UF                     | [1-categories][Unimath-yoneda], [bicategories][UniMath-yoneda-bi][^2] |
| [1lab]                                                   | Cubical Agda | HoTT/UF (cubical)           | [1-categories][1lab-yoneda]                                           |
| [mathlib][lean-mathlib]                                  | Lean 4       | Traditional                 | [1-categories][lean-mathlib-yoneda]                                   |
| [:simple-github: sinhp/CovariantYonedaLean3][sina-lean3] | Lean 3       | Traditional                 | [1-categories][sina-lean3-yoneda]                                     |
| [:simple-github: sinhp/CovariantYonedaLean4][sina-lean4] | Lean 4       | Traditional                 | [1-categories][sina-lean4-yoneda]                                     |
| [Archive of Formal Proofs][AFP]                          | Isabelle/HOL | Traditional                 | 1-categories[^3] [^4] [^5]                                            |
| This project                                             | Rzk          | HoTT/UF (simplicial)        | [∞-categories](simplicial-hott/09-yoneda.rzk.md)                      |

[agda-categories]: https://agda.github.io/agda-categories/
[agda-categories-yoneda]:
  https://agda.github.io/agda-categories/Categories.Yoneda.html
[agda-unimath]: https://unimath.github.io/agda-unimath/
[agda-unimath-yoneda]:
  https://unimath.github.io/agda-unimath/category-theory.yoneda-lemma-precategories.html
[UniMath]: https://github.com/UniMath/UniMath
[UniMath-yoneda]:
  https://github.com/UniMath/UniMath/blob/7d7fb997dbe84b0d0107adc963281c6efb97ff60/UniMath/CategoryTheory/yoneda.v#L325-L328
[UniMath-yoneda-bi]:
  https://unimath.github.io/doc/UniMath/c26d11b//UniMath.Bicategories.Core.YonedaLemma.html#bicategorical_yoneda_lemma
[1lab]: https://1lab.dev
[1lab-yoneda]: https://1lab.dev/Cat.Functor.Hom.html#the-yoneda-embedding
[sina-lean3]: https://github.com/sinhp/CovariantYonedaLean3
[sina-lean3-yoneda]:
  https://github.com/sinhp/CovariantYonedaLean3/blob/f2479dfd306a0f1af2be578750c6b27d11a52555/src/CovariantYoneda.lean#L561-L586
[sina-lean4]: https://github.com/sinhp/CovariantYonedaLean4
[sina-lean4-yoneda]:
  https://github.com/sinhp/CovariantYonedaLean4/blob/1c8005c6702dd24d251b31ecdd0e388782236ad5/CovYoneda/src/yoneda.lean#L86-L94
[AFP]: https://www.isa-afp.org
[lean-mathlib]: https://github.com/leanprover-community/mathlib
[lean-mathlib-yoneda]:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Yoneda.html#CategoryTheory.yoneda

[^1]:
    The [agda-categories] library internalizes a version of Hom-equality to each
    category, resulting in a flavour of bicategory theory.

[^2]:
    B. Ahrens, D. Frumin, M. Maggesi, N. Veltri, and N. van der Weide.
    _Bicategories in univalent foundations_. Mathematical Structures in Computer
    Science, vol. 31, no. 10, pp. 1232–1269, 2021.
    <https://arxiv.org/abs/1903.01152>

[^3]: <https://www.isa-afp.org/sessions/category/#Yoneda>
[^4]: <https://www.isa-afp.org/sessions/category2/#Yoneda>
[^5]: <https://www.isa-afp.org/sessions/category3/#Yoneda>
