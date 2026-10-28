/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import CorradiHajnal.SetForm
public import CorradiHajnal.Sharpness

/-!
# Proofs of the statements in `Challenge.lean`

The definitions are copied verbatim from `Challenge.lean`. The theorems are those of the library
`CorradiHajnal` (`CorradiHajnal/Theorem.lean`, `CorradiHajnal/SetForm.lean`,
`CorradiHajnal/Sharpness.lean`), whose definition of disjoint cycles is literally the same.
-/

@[expose] public section

open SimpleGraph

namespace CyclePacking

universe u

/-- `G` contains `k` vertex-disjoint cycles: there are `k` pairwise disjoint vertex sets each
inducing a subgraph that is not acyclic. -/
def HasDisjointCycles {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Fin k → Set V, Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    ∀ i, ¬ (G.induce (S i)).IsAcyclic

end CyclePacking

namespace CorradiHajnalTheorem

/-- `k` pairwise vertex-disjoint cycles of `G`: closed walks that are cycles (in Mathlib's sense,
`SimpleGraph.Walk.IsCycle`), no two of which share a vertex. -/
def HasDisjointCycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (base : Fin k → V) (c : (i : Fin k) → G.Walk (base i) (base i)),
    (∀ i, (c i).IsCycle) ∧
      ∀ i j, i ≠ j → ∀ v, v ∈ (c i).support → v ∉ (c j).support

/-- **The Corrádi–Hajnal theorem.** A graph on at least `3k` vertices with minimum degree at least
`2k` contains `k` vertex-disjoint cycles. -/
theorem corradi_hajnal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hn : 3 * k ≤ Fintype.card V) (hδ : 2 * k ≤ G.minDegree) :
    HasDisjointCycles G k :=
  CorradiHajnal.corradi_hajnal G k hn hδ

/-- **The Corrádi–Hajnal theorem**, with the disjoint cycles of the Erdős–Pósa entry. -/
theorem corradi_hajnal_sets {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hn : 3 * k ≤ Fintype.card V) (hδ : 2 * k ≤ G.minDegree) :
    CyclePacking.HasDisjointCycles G k :=
  CorradiHajnal.corradi_hajnal_sets G k hn hδ

/-- A graph with `k` disjoint cycles has at least `3k` vertices. -/
theorem three_mul_le_card_of_hasDisjointCycles {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (h : HasDisjointCycles G k) : 3 * k ≤ Fintype.card V :=
  CorradiHajnal.three_mul_le_card_of_hasDisjointCycles h

/-- **Sharpness of the order condition.** For `k ≥ 2`, the complete graph on `3k - 1` vertices
has minimum degree `3k - 2 ≥ 2k` but no `k` disjoint cycles. -/
theorem not_hasDisjointCycles_top (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Fin (3 * k - 1)) = 3 * k - 1 ∧
      (⊤ : SimpleGraph (Fin (3 * k - 1))).minDegree = 3 * k - 2 ∧
      2 * k ≤ (⊤ : SimpleGraph (Fin (3 * k - 1))).minDegree ∧
      ¬ HasDisjointCycles (⊤ : SimpleGraph (Fin (3 * k - 1))) k :=
  CorradiHajnal.not_hasDisjointCycles_top k hk

/-- **Sharpness of the degree condition.** For `k ≥ 1` and `m ≥ 2k`, the complete bipartite
graph `K_{2k-1, m}` has at least `3k` vertices and minimum degree exactly `2k - 1`, but no `k`
disjoint cycles. -/
theorem not_hasDisjointCycles_completeBipartite (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) :
    3 * k ≤ Fintype.card (Fin (2 * k - 1) ⊕ Fin m) ∧
      (completeBipartiteGraph (Fin (2 * k - 1)) (Fin m)).minDegree = 2 * k - 1 ∧
      ¬ HasDisjointCycles (completeBipartiteGraph (Fin (2 * k - 1)) (Fin m)) k :=
  CorradiHajnal.not_hasDisjointCycles_completeBipartite k m hk hm

end CorradiHajnalTheorem
