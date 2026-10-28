# The Corrádi–Hajnal theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

K. Corrádi and A. Hajnal, *On the maximal number of independent circuits in a graph*, Acta Math.
Acad. Sci. Hungar. 14 (1963) 423–439,
[doi:10.1007/BF01895727](https://doi.org/10.1007/BF01895727): **every graph on at least `3k`
vertices with minimum degree at least `2k` contains `k` vertex-disjoint cycles.** Mathlib has
cycles and minimum degree but not this theorem.

| Lean (namespace `CorradiHajnalTheorem`) | Statement |
|---|---|
| `corradi_hajnal` | `3k ≤ n`, `2k ≤ δ(G)` ⟹ `k` closed walks that are cycles, with pairwise disjoint supports. |
| `corradi_hajnal_sets` | The same with the disjoint cycles of the registered Erdős–Pósa entry: `k` pairwise disjoint vertex sets, each inducing a non-acyclic subgraph. |
| `three_mul_le_card_of_hasDisjointCycles` | `k` disjoint cycles need at least `3k` vertices. |
| `not_hasDisjointCycles_top` | For `k ≥ 2`, `K_{3k−1}` has `δ = 3k − 2 ≥ 2k` and no `k` disjoint cycles: the order condition is needed. |
| `not_hasDisjointCycles_completeBipartite` | For `m ≥ 2k`, `K_{2k−1, m}` has at least `3k` vertices, `δ = 2k − 1`, and no `k` disjoint cycles: the degree condition is needed. |

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the statements; it imports only
  Mathlib. `CyclePacking.HasDisjointCycles` is copied verbatim from
  [PALOMAR-2026-10-20-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-20-000003&version=1)
  (jtraverso/erdos-posa-cycles).
- [`Solution.lean`](Solution.lean) and [`CorradiHajnal/`](CorradiHajnal): the proofs.
- [`comparator.json`](comparator.json), [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md),
  [`formalization.yaml`](formalization.yaml).

## How the proof goes

The library works with *cyclic* vertex sets (some nonempty `U ⊆ S` spans at least `|U|` edges),
which contain cycles (`CycleOfCyc.lean`, by peeling off vertices of degree at most one and a
longest-path argument).

1. **Induction on non-edges** (`Theorem.lean`). A complete graph on at least `3k` vertices has `k`
   disjoint triangles. Otherwise add a missing edge `xy`; the larger graph has `k` disjoint cyclic
   sets, and at most one of them uses the new edge, so `G` has `k − 1` of them.
2. **Optimal families** (`Family.lean`, `Optimal.lean`). Among families of `k − 1` disjoint cyclic
   sets leaving at least three vertices uncovered, take one minimizing the covered vertices and
   then maximizing the edges among the uncovered ones; if `G` has no `k` disjoint cyclic sets,
   exchange arguments (`Witness.lean`) constrain how the uncovered vertices see the members.
3. **Two cases.** At least four uncovered vertices (`Low.lean`, `LongRest.lean`): counting edges
   to the family finds a triangle member receiving many edges, which gives an exchange. Exactly
   three (`ShortRest.lean`): the rest is a path `a − u − b`, and a weighted count over a triangle
   member, checked by a finite case analysis (`Finite.lean`), gives a contradiction.

The sharpness examples are in `Sharpness.lean`, the sanity checks on `K₃`, `K₅`, `K₆` in
`Sanity.lean`, and the bridge to the Erdős–Pósa definition in `SetForm.lean`.

## Provenance and checks

The theorems were chosen by the author. The proofs were produced by Harmonic's Aristotle from the
formal statements and a proof route, audited, and migrated to Lean `v4.35.0-rc3` and the module
system with Claude (Claude Code). Lean `v4.35.0-rc3`, Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`: `lake build`; no `sorry`; `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`; the elaborated statements and definitions of the
Challenge and the Solution are identical (`pp.all`).
