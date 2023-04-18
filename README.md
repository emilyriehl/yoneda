# Yoneda for ∞-categories 

This is a formalization library for simplicial Homotopy Type Theory (sHoTT) with the aim of proving the Yoneda lemma for ∞-categories following the paper "A type theory for synthetic ∞-categories" [1].

The formalizations are implemented using [`rzk`](https://github.com/fizruk/rzk), an experimental proof assistant for a variant of type theory with shapes developed by [Nikolai Kudasov](https://fizruk.github.io/). Formalizations were contributed by Nikolai Kudasov, [Emily Riehl](https://emilyriehl.github.io/), and [Jonathan Weinberger](https://sites.google.com/view/jonathanweinberger).

In the future we hope to compare the proof of the Yoneda lemma for ∞-categories in simplicial HoTT with proofs of the Yoneda lemma for 1-categories in other proof assistants. This comparative formalization project is joint with [Sina Hazratpour](https://sinhp.github.io/).

## Checking the Formalisations Locally

Install [`rzk`](https://github.com/fizruk/rzk) proof assistant. Then run the following command from the root of this repository:

```sh
rzk typecheck hott/* simplicial-hott/*
```

# References

1. Emily Riehl, & Michael Shulman. (2017). A type theory for synthetic ∞-categories. https://arxiv.org/abs/1705.07442
