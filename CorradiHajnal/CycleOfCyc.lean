/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Counting

/-!
# Cyclic vertex sets contain cycles

If `Cyc G S`, then `G` has a cycle (in the sense of `SimpleGraph.Walk.IsCycle`) all of whose
vertices lie in `S`. The proof peels off vertices of degree at most one and then uses a
longest-path argument in the graph induced on a set of minimum degree two.
-/

@[expose] public section

namespace CorradiHajnal

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The subgraph of `G` keeping only the edges inside `W`. -/
def restrictTo (G : SimpleGraph V) (W : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ W ∧ b ∈ W
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma restrictTo_adj {W : Finset V} {a b : V} :
    (restrictTo G W).Adj a b ↔ G.Adj a b ∧ a ∈ W ∧ b ∈ W := Iff.rfl

lemma restrictTo_le (W : Finset V) : restrictTo G W ≤ G := fun _ _ h => (restrictTo_adj.1 h).1

lemma mem_or_eq_of_mem_support {W : Finset V} :
    ∀ {u v : V} (p : (restrictTo G W).Walk u v), ∀ x ∈ p.support, x ∈ W ∨ x = v
  | _, _, .nil, x, hx => by rw [Walk.support_nil, List.mem_singleton] at hx; exact Or.inr hx
  | _, _, .cons h p, x, hx => by
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl (restrictTo_adj.1 h).2.1
    · exact mem_or_eq_of_mem_support p x hx

/-- In a nonempty set where every vertex has two neighbours, the restricted graph has a cycle. -/
lemma not_isAcyclic_restrictTo [Finite V] [DecidableRel G.Adj] {W : Finset V}
    (hne : W.Nonempty)
    (h2 : ∀ w ∈ W, 2 ≤ nb G W w) : ¬ (restrictTo G W).IsAcyclic := by
  intro hac
  classical
  have := Fintype.ofFinite V
  set H := restrictTo G W
  let P : ℕ → Prop := fun n => ∃ a ∈ W, ∃ b, ∃ p : H.Walk a b, p.IsPath ∧ p.length = n
  obtain ⟨a0, ha0⟩ := hne
  have hP0 : P 0 := ⟨a0, ha0, a0, .nil, Walk.IsPath.nil, rfl⟩
  have hPle : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨a, -, b, p, hp, rfl⟩
    exact hp.length_lt.le
  set N := Nat.findGreatest P (Fintype.card V)
  have hPN : P N := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  obtain ⟨a, haW, b, p, hp, hpN⟩ := hPN
  -- two distinct neighbours of `a` inside `W`
  have ha2 := h2 a haW
  unfold nb at ha2
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (show 1 < #(W.filter (G.Adj a)) by omega)
  rw [mem_filter] at hx hy
  have hHx : H.Adj a x := restrictTo_adj.2 ⟨hx.2, haW, hx.1⟩
  have hHy : H.Adj a y := restrictTo_adj.2 ⟨hy.2, haW, hy.1⟩
  -- every neighbour of `a` lies on `p`, by maximality
  have hmem : ∀ z, H.Adj a z → z ∈ p.support := by
    intro z hz
    by_contra hzp
    have hq : (Walk.cons hz.symm p).IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hp, hzp⟩
    have hPn : P (N + 1) := ⟨z, (restrictTo_adj.1 hz).2.2, b, _, hq, by simp [hpN]⟩
    have hle := hPle _ hPn
    exact absurd (Nat.le_findGreatest hle hPn) (by omega)
  have ex := hac.eq_snd_of_adj_start hp hHx (hmem x hHx)
  have ey := hac.eq_snd_of_adj_start hp hHy (hmem y hHy)
  exact hxy (ex.trans ey.symm)

/-- A cyclic set contains (the vertex set of) a cycle of `G`. -/
theorem Cyc.exists_isCycle [Finite V] [DecidableRel G.Adj] {S : Finset V}
    (h : Cyc G S) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ ∀ x ∈ c.support, x ∈ S := by
  obtain ⟨U, hUS, hUne, hU⟩ := h
  obtain ⟨W, hWU, hWne, hW2⟩ := exists_two_le_nb hUne hU
  have hna := not_isAcyclic_restrictTo hWne hW2
  rw [IsAcyclic] at hna
  push Not at hna
  obtain ⟨v, c, hc⟩ := hna
  refine ⟨v, c.mapLe (restrictTo_le W), hc.mapLe _, ?_⟩
  intro x hx
  rw [Walk.support_mapLe_eq_support] at hx
  apply hUS
  apply hWU
  rcases mem_or_eq_of_mem_support c x hx with hx | rfl
  · exact hx
  · cases c with
    | nil => exact absurd rfl hc.ne_nil
    | cons h _ => exact (restrictTo_adj.1 h).2.1

end CorradiHajnal
