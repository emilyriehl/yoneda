# Yoneda for ∞-categories

[![Check with latest Rzk](https://github.com/emilyriehl/yoneda/actions/workflows/rzk.yml/badge.svg)](https://github.com/emilyriehl/yoneda/actions/workflows/rzk.yml)
[![MkDocs to GitHub Pages](https://github.com/emilyriehl/yoneda/actions/workflows/mkdocs.yml/badge.svg)](https://github.com/emilyriehl/yoneda/actions/workflows/mkdocs.yml)

This is a formalization library for simplicial Homotopy Type Theory (sHoTT) with
the aim of proving the Yoneda lemma for ∞-categories following the paper
"[A type theory for synthetic ∞-categories](https://higher-structures.math.cas.cz/api/files/issues/Vol1Iss1/RiehlShulman)"
[1]. This formalization project could be regarded as a companion to the article
"[Could ∞-category theory be taught to undergraduates?](https://www.ams.org/journals/notices/202305/noti2692/noti2692.html)"
[2].

The formalizations are implemented using [`rzk`](https://github.com/fizruk/rzk),
an experimental proof assistant for a variant of type theory with shapes
developed by [Nikolai Kudasov](https://fizruk.github.io/). Formalizations were
contributed by [Fredrik Bakke](https://github.com/fredrik-bakke),
[Nikolai Kudasov](https://fizruk.github.io/),
[Emily Riehl](https://emilyriehl.github.io/), and
[Jonathan Weinberger](https://sites.google.com/view/jonathanweinberger). The
formalizations can be viewed as markdown files rendered at
[emilyriehl.github.io/yoneda/](https://emilyriehl.github.io/yoneda/) using
syntax highlighting supplied by Nikolai.

Another aim of this project is to compare the proof of the Yoneda lemma for
∞-categories in simplicial HoTT with proofs of the Yoneda lemma for 1-categories
in other proof assistants. To that end
[Sina Hazratpour](https://sinhp.github.io/) has contributed a formalization in
[`Lean3`](https://leanprover-community.github.io/) extracted from materials he
prepared to teach
[Introduction to Proofs](https://sinhp.github.io/teaching/2022-introduction-to-proofs-with-Lean)
at Johns Hopkins, which can be found
[here](https://github.com/emilyriehl/yoneda/blob/master/lean/yoneda.lean).

We also contributed a proof of the
[Yoneda lemma for precategories](https://unimath.github.io/agda-unimath/category-theory.yoneda-lemma-precategories.html)
to the [Agda-Unimath](https://unimath.github.io/agda-unimath/) library. Here we
prove the Yoneda lemma for pre-∞-categories, since the univalence/completeness
condition is not required for this result. By analogy, precategories are the
non-univalent 1-categories in HoTT.

## Checking the Formalisations Locally

Install [`rzk`](https://github.com/fizruk/rzk) proof assistant. Then run the
following command from the root of this repository:

```sh
stack exec rzk typecheck src/hott/* src/simplicial-hott/*
```

# References

1. Emily Riehl & Michael Shulman. A type theory for synthetic ∞-categories.
   Higher Structures 1(1), 147-224. 2017. https://arxiv.org/abs/1705.07442

2. Emily Riehl. Could ∞-category theory be taught to undergraduates? Notices of
   the AMS. May 2023.
   https://www.ams.org/journals/notices/202305/noti2692/noti2692.html
