# Yoneda for ∞-categories

This is a formalization library for simplicial Homotopy Type Theory (HoTT) with
the aim of proving the Yoneda lemma for ∞-categories following the paper
"[A type theory for synthetic ∞-categories](https://higher-structures.math.cas.cz/api/files/issues/Vol1Iss1/RiehlShulman)"
[1]. This formalization project follows the philosophy layed out in
"[Could ∞-category theory be taught to undergraduates?](https://www.ams.org/journals/notices/202305/noti2692/noti2692.html)"
[2].

The formalizations are implemented using
[`rzk`](https://github.com/rzk-lang/rzk), an experimental proof assistant for a
variant of type theory with shapes.

## Checking the Formalisations Locally

Install the
[`rzk`](https://rzk-lang.github.io/rzk/latest/getting-started/install/) proof
assistant. Then run the following command from the root of the project:

```sh
rzk typecheck src/hott/* src/simplicial-hott/*
```

## References

1. Emily Riehl & Michael Shulman. A type theory for synthetic ∞-categories.
   Higher Structures 1(1), 147-224. 2017. <https://arxiv.org/abs/1705.07442>

2. Emily Riehl. Could ∞-category theory be taught to undergraduates? Notices of
   the AMS. May 2023.
   <https://www.ams.org/journals/notices/202305/noti2692/noti2692.html>
