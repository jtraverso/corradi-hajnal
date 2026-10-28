/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Theorem

/-!
# Disjoint cycles as vertex sets

The registered formalization of the Erdős–Pósa theorem for cycles
(`jtraverso/erdos-posa-cycles`) says that `G` has `k` disjoint cycles when there are `k`
pairwise disjoint vertex sets each inducing a subgraph that is not acyclic. Vertex-disjoint
closed walks that are cycles give such sets: their supports.

* `exists_disjoint_not_isAcyclic_of_hasDisjointCycles` — the bridge;
* `corradi_hajnal_sets` — the Corrádi–Hajnal theorem in that form.
-/

@[expose] public section

namespace CorradiHajnal

open SimpleGraph

/-- `k` vertex-disjoint cycles give `k` pairwise disjoint vertex sets, none inducing an acyclic
graph. -/
theorem exists_disjoint_not_isAcyclic_of_hasDisjointCycles {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (h : HasDisjointCycles G k) :
    ∃ S : Fin k → Set V, Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i, ¬ (G.induce (S i)).IsAcyclic := by
  obtain ⟨base, c, hc, hd⟩ := h
  refine ⟨fun i => {v | v ∈ (c i).support}, fun i j hij => ?_, fun i hac => ?_⟩
  · exact Set.disjoint_left.2 fun v hv hv' => hd i j hij v hv hv'
  · have hw : ∀ x ∈ (c i).support, x ∈ {v | v ∈ (c i).support} := fun x hx => hx
    have h1 : (((c i).induce {v | v ∈ (c i).support} hw).map
        (Embedding.induce {v | v ∈ (c i).support}).toHom).IsCycle := by
      rw [Walk.map_induce]
      exact hc i
    exact hac _ (Walk.IsCycle.of_map h1)

/-- **The Corrádi–Hajnal theorem**, with disjoint cycles as vertex sets inducing non-acyclic
graphs. -/
theorem corradi_hajnal_sets {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hn : 3 * k ≤ Fintype.card V) (hδ : 2 * k ≤ G.minDegree) :
    ∃ S : Fin k → Set V, Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ i, ¬ (G.induce (S i)).IsAcyclic :=
  exists_disjoint_not_isAcyclic_of_hasDisjointCycles (corradi_hajnal G k hn hδ)

end CorradiHajnal
