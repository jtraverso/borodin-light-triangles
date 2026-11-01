# Borodin's light triangles in planar graphs of minimum degree five in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of Borodin's theorem on light triangles (O. V. Borodin, *Math.
Notes* 46 (1989) 835–837, [doi:10.1007/BF01139613](https://doi.org/10.1007/BF01139613)). The
*weight* of a triangle is the sum of the degrees of its vertices.

| Lean (namespace `BorodinTheorem`) | Statement |
|---|---|
| `light_face` | Every plane map of a finite simple graph of minimum degree at least five has a face of length three of weight at most `17`. |
| `light_triangle` | A finite simple planar graph of minimum degree at least five has a triangle of weight at most `17`. |

The bound is sharp (the dodecahedron with a vertex added in each face); the example is not
formalized.

## Planarity

As in the registered entry
[Kuratowski's theorem](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000018&version=1):
a *plane map* is a rotation system of the darts of `G` of Euler defect `0`; its faces are the
cycles of `rot * dartSymm`. The definitions, from `numClasses` to `IsPlanar`, are copied verbatim
from that entry's `Challenge.lean`. A face of length three through a dart `d` is expressed by
`(rot * dartSymm) ^ 3` fixing `d`.

## The proof

Discharging on the rotation system (`Borodin/Discharging.lean`), with the rules of the proof
sketch in Cranston–West, *An introduction to the discharging method via graph coloring*
([arXiv:1306.4434](https://arxiv.org/abs/1306.4434), Theorem 3.4), starting from the dart-level
Euler formula of [`jtraverso/kotzig-light-edges`](https://github.com/jtraverso/kotzig-light-edges)
(total charge `-12 K < 0`):

- every face of length at least four gives `1/2` to each of its corners;
- every `7`-vertex gives `1/3` to each `5`-neighbour;
- every vertex of degree at least eight gives `1/4` through each incident triangular face to its
  `5`-vertices, split equally.

No edge-maximal counterexample is used: faces of length at least four pay for themselves
(`2ℓ - 6 ≥ ℓ/2`), and a `7`-vertex with `s` `5`-neighbours has at least `2s - 7` corners between
two consecutive `5`-neighbours, none on a triangle (weight `17`). A `5`-vertex receives at least
`1` in each of the `32768` configurations of corner types and neighbour degrees (capped at eight);
this finite check is `Borodin.local_check`, proved by `decide` (`Borodin/Local.lean`).

## Files

- [`BorodinChallenge.lean`](BorodinChallenge.lean): the definitions and the two statements; it
  imports only Mathlib.
- [`BorodinSolution.lean`](BorodinSolution.lean): the same definitions, the conversion of plane
  maps to the Kuratowski library (field by field) and the two theorems.
- `Borodin/Local.lean`, `Borodin/Discharging.lean`, `Borodin/Main.lean`.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Dependencies

- [`jtraverso/kotzig-light-edges`](https://github.com/jtraverso/kotzig-light-edges) @ `0e9f2a2`,
  pinned (Kotzig's theorem; Palomar submission pending), and through it
  [`jtraverso/kuratowski`](https://github.com/jtraverso/kuratowski) @ `696ec89`
  (PALOMAR-2026-10-15-000018).

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the two
theorems; the elaborated statements and definitions of `BorodinChallenge.lean` and
`BorodinSolution.lean` are identical (`pp.all`).

The Lean development is AI-written under the author's direction (see `formalization.yaml`).
