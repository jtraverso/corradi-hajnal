/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Theorem

/-!
# Sharpness of the Corrádi–Hajnal theorem

Both hypotheses of `corradi_hajnal` are needed:

* **Degree condition.** The complete bipartite graph `K_{2k-1, m}` with `m ≥ 2k` has at least
  `3k` vertices and minimum degree `2k - 1`, but every cycle uses at least two vertices of the
  small side, so it has no `k` disjoint cycles (`not_hasDisjointCycles_completeBipartite`).
* **Order condition.** The complete graph on `3k - 1` vertices has minimum degree
  `3k - 2 ≥ 2k` for `k ≥ 2`, but cycles have at least three vertices, so it has no `k`
  disjoint cycles (`not_hasDisjointCycles_top`).
-/

@[expose] public section

namespace CorradiHajnal

open Finset SimpleGraph

/-- `k` pairwise disjoint finsets with at least `c` elements each need `c * k` elements. -/
lemma mul_le_card_of_disjoint {α : Type*} [Fintype α] {k c : ℕ}
    (S : Fin k → Finset α) (hd : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hc : ∀ i, c ≤ #(S i)) :
    c * k ≤ Fintype.card α := by
  classical
  exact calc c * k = ∑ _i : Fin k, c := by simp [mul_comm]
    _ ≤ ∑ i, #(S i) := sum_le_sum fun i _ => hc i
    _ = #(univ.biUnion S) := (card_biUnion fun i _ j _ hij => hd i j hij).symm
    _ ≤ Fintype.card α := card_le_univ _

/-- A cycle has at least three vertices. -/
lemma three_le_card_support {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    {c : G.Walk v v} (hc : c.IsCycle) : 3 ≤ #c.support.toFinset := by
  have h1 := hc.three_le_length
  have h2 := c.length_support
  have h3 := List.toFinset_card_of_nodup hc.support_nodup
  have h4 : c.support.tail.toFinset ⊆ c.support.toFinset := fun x hx =>
    List.mem_toFinset.2 (List.mem_of_mem_tail (List.mem_toFinset.1 hx))
  have := card_le_card h4
  rw [h3, List.length_tail, h2] at this
  omega

/-- A graph with `k` disjoint cycles has at least `3k` vertices. -/
theorem three_mul_le_card_of_hasDisjointCycles {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k : ℕ} (h : HasDisjointCycles G k) : 3 * k ≤ Fintype.card V := by
  classical
  obtain ⟨base, c, hc, hd⟩ := h
  exact mul_le_card_of_disjoint (fun i => (c i).support.toFinset)
    (fun i j hij => disjoint_left.2 fun v hv hv' =>
      hd i j hij v (List.mem_toFinset.1 hv) (List.mem_toFinset.1 hv'))
    fun i => three_le_card_support (hc i)

/-- **Sharpness of the order condition.** For `k ≥ 2`, the complete graph on `3k - 1` vertices
has minimum degree `3k - 2 ≥ 2k` but no `k` disjoint cycles. -/
theorem not_hasDisjointCycles_top (k : ℕ) (hk : 2 ≤ k) :
    Fintype.card (Fin (3 * k - 1)) = 3 * k - 1 ∧
      (⊤ : SimpleGraph (Fin (3 * k - 1))).minDegree = 3 * k - 2 ∧
      2 * k ≤ (⊤ : SimpleGraph (Fin (3 * k - 1))).minDegree ∧
      ¬ HasDisjointCycles (⊤ : SimpleGraph (Fin (3 * k - 1))) k := by
  have hmin : (⊤ : SimpleGraph (Fin (3 * k - 1))).minDegree = 3 * k - 2 := by
    rw [minDegree_top, Fintype.card_fin]
    omega
  refine ⟨Fintype.card_fin _, hmin, by omega, fun h => ?_⟩
  have := three_mul_le_card_of_hasDisjointCycles h
  rw [Fintype.card_fin] at this
  omega

/-- In a cycle every vertex has two distinct neighbours on the cycle. -/
lemma exists_two_adj_of_isCycle {V : Type*} {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) {u : V} (hu : u ∈ c.support) :
    ∃ x y, x ≠ y ∧ x ∈ c.support ∧ y ∈ c.support ∧ G.Adj u x ∧ G.Adj u y := by
  obtain ⟨x, y, hxy, he⟩ := Set.ncard_eq_two.1 (hc.ncard_neighborSet_toSubgraph_eq_two hu)
  have hx : x ∈ c.toSubgraph.neighborSet u := he ▸ Set.mem_insert x {y}
  have hy : y ∈ c.toSubgraph.neighborSet u := he ▸ Set.mem_insert_of_mem x rfl
  exact ⟨x, y, hxy, Walk.mem_support_of_adj_toSubgraph hx.symm,
    Walk.mem_support_of_adj_toSubgraph hy.symm, hx.adj_sub, hy.adj_sub⟩

/-- A cycle of a complete bipartite graph has two vertices on the left side. -/
lemma exists_two_left_of_isCycle {α β : Type*} {v : α ⊕ β}
    {c : (completeBipartiteGraph α β).Walk v v} (hc : c.IsCycle) :
    ∃ a b : α, a ≠ b ∧ Sum.inl a ∈ c.support ∧ Sum.inl b ∈ c.support := by
  obtain ⟨w, hw⟩ : ∃ w : β, Sum.inr w ∈ c.support := by
    cases v with
    | inr w => exact ⟨w, c.start_mem_support⟩
    | inl a =>
      obtain ⟨x, -, -, hx, -, hax, -⟩ := exists_two_adj_of_isCycle hc c.start_mem_support
      cases x with
      | inl _ => simp [completeBipartiteGraph] at hax
      | inr w => exact ⟨w, hx⟩
  obtain ⟨x, y, hxy, hx, hy, hwx, hwy⟩ := exists_two_adj_of_isCycle hc hw
  cases x with
  | inr _ => simp [completeBipartiteGraph] at hwx
  | inl a =>
    cases y with
    | inr _ => simp [completeBipartiteGraph] at hwy
    | inl b => exact ⟨a, b, fun h => hxy (h ▸ rfl), hx, hy⟩

instance {α β : Type*} : DecidableRel (completeBipartiteGraph α β).Adj := fun v w =>
  inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

lemma degree_completeBipartite_inl {α β : Type*} [Fintype α] [Fintype β] (a : α) :
    (completeBipartiteGraph α β).degree (Sum.inl a) = Fintype.card β := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have : (univ.filter ((completeBipartiteGraph α β).Adj (Sum.inl a))) =
      (univ : Finset β).map Function.Embedding.inr := by
    ext x
    cases x <;> simp [completeBipartiteGraph]
  rw [this, card_map, card_univ]

lemma degree_completeBipartite_inr {α β : Type*} [Fintype α] [Fintype β] (b : β) :
    (completeBipartiteGraph α β).degree (Sum.inr b) = Fintype.card α := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  have : (univ.filter ((completeBipartiteGraph α β).Adj (Sum.inr b))) =
      (univ : Finset α).map Function.Embedding.inl := by
    ext x
    cases x <;> simp [completeBipartiteGraph]
  rw [this, card_map, card_univ]

/-- **Sharpness of the degree condition.** For `k ≥ 1` and `m ≥ 2k`, the complete bipartite
graph `K_{2k-1, m}` has at least `3k` vertices and minimum degree exactly `2k - 1`, but no `k`
disjoint cycles. -/
theorem not_hasDisjointCycles_completeBipartite (k m : ℕ) (hk : 1 ≤ k) (hm : 2 * k ≤ m) :
    3 * k ≤ Fintype.card (Fin (2 * k - 1) ⊕ Fin m) ∧
      (completeBipartiteGraph (Fin (2 * k - 1)) (Fin m)).minDegree = 2 * k - 1 ∧
      ¬ HasDisjointCycles (completeBipartiteGraph (Fin (2 * k - 1)) (Fin m)) k := by
  refine ⟨by simp; omega, le_antisymm ?_ ?_, fun h => ?_⟩
  · refine ((completeBipartiteGraph _ _).minDegree_le_degree (Sum.inr ⟨0, by omega⟩)).trans ?_
    rw [degree_completeBipartite_inr, Fintype.card_fin]
  · have : Nonempty (Fin (2 * k - 1) ⊕ Fin m) := ⟨Sum.inr ⟨0, by omega⟩⟩
    refine le_minDegree_of_forall_le_degree _ _ fun v => ?_
    cases v with
    | inl a => rw [degree_completeBipartite_inl, Fintype.card_fin]; omega
    | inr b => rw [degree_completeBipartite_inr, Fintype.card_fin]
  · obtain ⟨base, c, hc, hd⟩ := h
    have := mul_le_card_of_disjoint
      (fun i => (univ : Finset (Fin (2 * k - 1))).filter fun a => Sum.inl a ∈ (c i).support)
      (fun i j hij => disjoint_left.2 fun a ha ha' =>
        hd i j hij _ (mem_filter.1 ha).2 (mem_filter.1 ha').2)
      (c := 2) fun i => by
        obtain ⟨a, b, hab, ha, hb⟩ := exists_two_left_of_isCycle (hc i)
        calc 2 = #({a, b} : Finset (Fin (2 * k - 1))) := (card_pair hab).symm
          _ ≤ _ := card_le_card fun x hx => by
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> simpa
    rw [Fintype.card_fin] at this
    omega

/-- A concrete instance: `K_{3,4}` has `7 ≥ 6` vertices and minimum degree `3 = 2 · 2 - 1`, but
no two disjoint cycles. -/
example : 3 * 2 ≤ Fintype.card (Fin 3 ⊕ Fin 4) ∧
    (completeBipartiteGraph (Fin 3) (Fin 4)).minDegree = 3 ∧
    ¬ HasDisjointCycles (completeBipartiteGraph (Fin 3) (Fin 4)) 2 :=
  not_hasDisjointCycles_completeBipartite 2 4 (by norm_num) (by norm_num)

end CorradiHajnal
