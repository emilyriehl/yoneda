# Style guide and design principles

This guide provides a set of design principles and guidelines for the `yoneda`
project. Our style and design principles borrows heavily from
[`agda-unimath`](https://github.com/UniMath/agda-unimath).

## The structure of code

We enforce strict formatting rules. This formatting allows the type of the
defined term to be easily readable, and aids in understanding the structure of
the definition.

The general format of a definition is as follows:

```rzk
#def concat
  ( p : x = y)
  ( q : y = z)
  : (x = z)
  := idJ (A , y , \ z' q' -> (x = z') , p , z , q)
```

- We start with the name, and place every assumption on a new line.

- The conclusion of the definition is placed on its own line, which starts with
  a colon (`:`).

- Then, on the next line, the walrus separator (`:=`) is placed, and after it
  follows the actual construction of the definition. If the construction does
  not fit on a single line, we immediately insert a new line after the walrus
  separator and indent the code an extra level (2 spaces).

(Currently just taken from agda-unimath and adapted to Rzk) In Rzk, every
construction is structured like a tree, where each operation can be seen as a
branching point. We use indentation levels and parentheses to highlight this
structure, which makes the code feel more organized and understandable. For
example, when a definition part extends beyond a line, we introduce line breaks
at the earliest branching point, clearly displaying the tree structure of the
definition. This allows the reader to follow the branches of the tree, and to
visually grasp the scope of each operation and argument. Consider the following
example about Segal types:

```rzk
#def is-segal-is-local-horn-inclusion
  ( A : U)
  ( is-local-horn-inclusion-A : is-local-horn-inclusion A)
  : isSegal A
  :=
    \ x y z f g ->
    projection-equiv-contractible-fibers
      ( < {t : 2 * 2 | Λ t} -> A >)
      ( \ k ->
        Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
          ( hom2 A
            ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
            ( \ t -> k (t , 0_2))
            ( \ t -> k (1_2 , t))
            ( h)))
      ( second
        ( comp-equiv
          ( Σ ( k : < {t : 2 * 2 | Λ t} -> A >) ,
            Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
              ( hom2 A
                ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                ( \ t -> k (t , 0_2))
                ( \ t -> k (1_2 , t))
                ( h)))
          ( < {t : 2 * 2 | Δ² t} -> A >)
          ( < {t : 2 * 2 | Λ t} -> A >)
          ( inv-equiv
            ( < {t : 2 * 2 | Δ² t} -> A >)
            ( Σ ( k : < {t : 2 * 2 | Λ t} -> A >) ,
              Σ ( h : hom A (k (0_2 , 0_2)) (k (1_2 , 1_2))) ,
                ( hom2 A
                  ( k (0_2 , 0_2)) (k (1_2 , 0_2)) (k (1_2 , 1_2))
                  ( \t -> k (t , 0_2))
                  ( \t -> k (1_2 , t))
                  ( h)))
            ( equiv-horn-restriction A))
          ( horn-restriction A , is-local-horn-inclusion-A)))
      ( horn A x y z f g)
```

The root here is the function `projection-equiv-contractible-fibers`. It takes
four arguments, each starting on a fresh line and is indented an extra level
from the root. The first argument fits neatly on one line, but the second one is
too large. In these cases, we add a line break right after the `->`-symbol
following the lambda-abstraction, which is the earliest branching point in this
case. The next node is again `Σ`, with two arguments. The first one fits on a
line, but the second does not, so we add a line break between them. This process
is continued until the definition is complete.

Note also that we use parentheses to mark the branches. The extra space after
the opening parentheses marking a branch is there to visually emphasize the tree
structure of the definition, and synergizes with our convention to have
two-space indentation level increases.

## Naming conventions

- As a main strategy, we strive to keep a tight connection between names of
  constructions and their types. Take for instance [...].
  > - Add example
  > - prepending assumptions and then conclusion
  > - See agda-unimath's description
  > - > We start with the initial assumption, then, working our way to the
  >   > conclusion, prepending every central assumption to the name, and finally
  >   > the conclusion. So for instance the name `iso-is-initial-is-segal`
  >   > should read like we get an iso of something which is initial given that
  >   > something is Segal. The true reading should then be obvious.
  >
  > > The naming conventions are aimed at improving the readability of the code,
  > > not to ensure the shortest possible names, nor to minimize the amount of
  > > typing by the implementers of the library.
- We mainly use lower case names with words separated by hyphens.
- Capitalized names are reserved for subuniverses and similar collections. When
  a construction is made internally to such a collection, we _append_ its name.
  For instance, the subuniverse of Segal types is called `Segal`, and its
  internal hom, called `function-type-Segal,` has the following signature:

  ```rzk
  #def function-type-Segal
    ( A B : Segal)
    : Segal
  ```

- Use meaningful names that accurately represent the concepts applied. For
  example, if a concept is known best by a special name, that name should
  probably be used.

- For technical lemmas or definitions, where the chance they will be reused is
  very low, the specific names do not matter as much. In these cases, one may
  resort to a simplified naming scheme, like enumeration. Please note, however,
  that if you find yourself appealing to this convention frequently, that is a
  sign that your code should be refactored.

## Use of Comments

> We do not explicitly ban code comments, but our other conventions should
> heavily limit their need.
>
> - [ ] Literate file format for prose
> - [ ] Descriptive definition names shouldn't need additional explanation
> - [ ] Strictly organized code to ease reading and understanding
> - [ ] Essential information should be carried by code, not only comments
>
> Still, code annotations may find their uses.
>
> Where to place literature references?

- Create and use named projections instead of using the `first` and `second`
  projections. In many cases, their meaning is not immediately obvious, and so
  one could be tempted to annotate the code with their meaning using comments.

  For instance, instead of writing `first (second is-invertible-f)`, we define a
  named projection `is-section-is-invertible`. This may then be used as
  `is-section-is-invertible A B f is-invertible-f` in other places. This way,
  the code becomes self-documenting, and much easier to read.

  However, we recognize that in `rzk`, since we do not have the luxury of
  implicit arguments, this may sometimes cause unnecessarily verbose code. In
  such cases, you may revert to using `first` and `second`.

## Adapting and Evolving the Style Guide

This style guide should evolve as Rzk develops and grows. If new features, like
implicit arguments, `let`-expressions, or `where`-blocks are added to the
language, or if there is made changes to the syntax of the language, their use
should be incorporated into this style guide.

At all times, the goal is to have code that is easy to read and navigate, even
for those who are not the authors. We should also ensure that we maintain a
consistent style across the entire repository.
