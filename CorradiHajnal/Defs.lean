/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Vertex-disjoint cycles: definitions

A family of `k` cycles of a simple graph, given as closed walks that are cycles, is vertex-disjoint
if no vertex lies on two of them.
-/

@[expose] public section

namespace CorradiHajnal

/-- `k` pairwise vertex-disjoint cycles of `G`: closed walks that are cycles (in Mathlib's sense,
`SimpleGraph.Walk.IsCycle`), no two of which share a vertex. -/
def HasDisjointCycles {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (base : Fin k → V) (c : (i : Fin k) → G.Walk (base i) (base i)),
    (∀ i, (c i).IsCycle) ∧
      ∀ i j, i ≠ j → ∀ v, v ∈ (c i).support → v ∉ (c j).support

end CorradiHajnal
