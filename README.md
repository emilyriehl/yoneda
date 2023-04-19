# Yoneda for ∞-categories 

This is a formalization library for simplicial Homotopy Type Theory (sHoTT) with the aim of proving the Yoneda lemma for ∞-categories following the paper "[A type theory for synthetic ∞-categories](https://higher-structures.math.cas.cz/api/files/issues/Vol1Iss1/RiehlShulman)" [1]. This formalization project could be regarded as a companion to the article "[Could ∞-category theory be taught to undergraduates?](https://www.ams.org/journals/notices/202305/noti2692/noti2692.html)" [2].

The formalizations are implemented using [`rzk`](https://github.com/fizruk/rzk), an experimental proof assistant for a variant of type theory with shapes developed by [Nikolai Kudasov](https://fizruk.github.io/). Formalizations were contributed by [Nikolai Kudasov](https://fizruk.github.io/), [Emily Riehl](https://emilyriehl.github.io/), and [Jonathan Weinberger](https://sites.google.com/view/jonathanweinberger).

In the future we hope to compare the proof of the Yoneda lemma for ∞-categories in simplicial HoTT with proofs of the Yoneda lemma for 1-categories in other proof assistants. This comparative formalization project is joint with [Sina Hazratpour](https://sinhp.github.io/).

## Checking the Formalisations Locally

Install [`rzk`](https://github.com/fizruk/rzk) proof assistant. Then run the following command from the root of this repository:

```sh
rzk typecheck hott/* simplicial-hott/*
```

# References

1. Emily Riehl & Michael Shulman. A type theory for synthetic ∞-categories. Higher Structures 1(1), 147-224. 2017. https://arxiv.org/abs/1705.07442

2. Emily Riehl. Could ∞-category theory be taught to undergraduates? Notices of the AMS. May 2023. https://www.ams.org/journals/notices/202305/noti2692/noti2692.html
