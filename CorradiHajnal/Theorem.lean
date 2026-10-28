/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Defs
public import CorradiHajnal.ShortRest
public import CorradiHajnal.CycleOfCyc

/-!
# The Corrádi–Hajnal theorem

**Theorem** (K. Corrádi and A. Hajnal, 1963). Every graph on `n ≥ 3k` vertices with minimum
degree at least `2k` contains `k` vertex-disjoint cycles.

The proof goes by induction on the number of non-edges. A complete graph on at least `3k`
vertices contains `k` disjoint triangles. Otherwise we add a missing edge `xy`; by induction the
larger graph has `k` disjoint cyclic sets, and at most one of them (containing both `x` and `y`)
fails to be cyclic in `G`. The remaining `k - 1` sets leave at least three vertices uncovered, and
the main lemma `hasK_succ` (proved via an optimal family) yields `k` disjoint cyclic sets in `G`.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Main lemma.** If every vertex has degree at least `2 (m + 1)` and there are `m` disjoint
cyclic sets leaving at least three vertices uncovered, then there are `m + 1` disjoint cyclic
sets. -/
theorem hasK_succ {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v)
    (h : ∃ F : Fin m → Finset V, Valid G F ∧ 3 ≤ #(Rest F)) : HasK G (m + 1) := by
  by_contra hK
  obtain ⟨F, hF⟩ := exists_optimal h
  have := hF.card_rest_le_three hK hδ
  have := hF.card_rest_ne_three hK hδ
  have := hF.three_le_rest
  omega

omit [Fintype V] [DecidableEq V] in
/-- A cyclic set of a larger graph is cyclic in `G` if all its larger-graph edges are edges
of `G`. -/
lemma Cyc.of_le {G G' : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    {S : Finset V} (h : Cyc G' S) (hS : ∀ v ∈ S, ∀ w ∈ S, G'.Adj v w → G.Adj v w) :
    Cyc G S := by
  obtain ⟨U, hU, hne, hc⟩ := h
  refine ⟨U, hU, hne, hc.trans ?_⟩
  unfold E2 nb
  exact sum_le_sum fun v hv => card_le_card fun w hw => by
    rw [mem_filter] at hw ⊢
    exact ⟨hw.1, hS v (hU hv) w (hU hw.1) hw.2⟩

omit [DecidableEq V] in
/-- A complete graph on at least `3k` vertices has `k` disjoint triangles. -/
lemma hasK_of_complete {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hn : 3 * k ≤ Fintype.card V) (hc : ∀ x y, x ≠ y → G.Adj x y) : HasK G k := by
  classical
  let e : Fin (3 * k) ↪ V := (Fin.castLEEmb hn).trans (Fintype.equivFin V).symm.toEmbedding
  have he : ∀ a b : Fin (3 * k), (a : ℕ) ≠ b → e a ≠ e b := fun a b hab h =>
    hab (congrArg Fin.val (e.injective h))
  let f : Fin k → Fin 3 → Fin (3 * k) := fun i r => ⟨3 * i + r, by omega⟩
  refine ⟨fun i => {e (f i 0), e (f i 1), e (f i 2)}, fun i => ?_, fun i j hij => ?_⟩
  · exact cyc_triangle (hc _ _ (he _ _ (by simp [f]))) (hc _ _ (he _ _ (by simp [f])))
      (hc _ _ (he _ _ (by simp [f])))
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rw [disjoint_left]
    simp only [mem_insert, mem_singleton]
    rintro v (rfl | rfl | rfl) <;> rintro (h | h | h) <;> exact he _ _ (by simp [f]; omega) h

/-- Adding the edge `xy` to `G`. -/
def addEdge (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x)
  symm := ⟨fun a b h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    exacts [Or.inl h.symm, Or.inr (Or.inr ⟨h2, h1⟩), Or.inr (Or.inl ⟨h2, h1⟩)]⟩
  loopless := ⟨fun a h => by
    rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    exacts [G.loopless.irrefl a h, hxy (h1.symm.trans h2), hxy (h2.symm.trans h1)]⟩

omit [Fintype V] [DecidableEq V] in
lemma addEdge_adj (G : SimpleGraph V) {x y : V} (hxy : x ≠ y) {a b : V} :
    (addEdge G hxy).Adj a b ↔ G.Adj a b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := Iff.rfl

instance (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V} (hxy : x ≠ y) :
    DecidableRel (addEdge G hxy).Adj := fun _ _ => decidable_of_iff _ (addEdge_adj G hxy).symm

/-- The non-edges of `G`, as ordered pairs. -/
def nonEdges (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  univ.filter fun p => p.1 ≠ p.2 ∧ ¬ G.Adj p.1 p.2

lemma card_nonEdges_addEdge_lt (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    (hxy : x ≠ y) (hn : ¬ G.Adj x y) : #(nonEdges (addEdge G hxy)) < #(nonEdges G) := by
  apply card_lt_card
  refine ⟨fun p hp => ?_, fun h => ?_⟩
  · simp only [nonEdges, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, fun h => hp.2 ((addEdge_adj G hxy).2 (Or.inl h))⟩
  · have : (x, y) ∈ nonEdges G := by simp [nonEdges, hxy, hn]
    have := h this
    simp only [nonEdges, mem_filter, mem_univ, true_and] at this
    exact this.2 ((addEdge_adj G hxy).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-- The theorem in terms of cyclic sets. -/
theorem hasK_of_minDeg (k : ℕ) (hn : 3 * k ≤ Fintype.card V) :
    ∀ (N : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj], #(nonEdges G) = N →
      (∀ v, 2 * k ≤ nb G univ v) → HasK G k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro G _ hN hδ
    by_cases hc : ∀ x y, x ≠ y → G.Adj x y
    · exact hasK_of_complete hn hc
    push Not at hc
    obtain ⟨x, y, hxy, hn'⟩ := hc
    set G' := addEdge G hxy
    have hδ' : ∀ v, 2 * k ≤ nb G' univ v := fun v =>
      (hδ v).trans (card_le_card fun w hw => by
        simp only [mem_filter] at hw ⊢
        exact ⟨hw.1, (addEdge_adj G hxy).2 (Or.inl hw.2)⟩)
    obtain ⟨F, hF⟩ := ih _ (hN ▸ card_nonEdges_addEdge_lt G hxy hn') G' rfl hδ'
    -- sets not containing both `x` and `y` stay cyclic in `G`
    have hcyc : ∀ i, ¬ (x ∈ F i ∧ y ∈ F i) → Cyc G (F i) := fun i hi =>
      (hF.1 i).of_le fun v hv w hw h => by
        rcases (addEdge_adj G hxy).1 h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · exact absurd ⟨hv, hw⟩ hi
        · exact absurd ⟨hw, hv⟩ hi
    by_cases hboth : ∃ i, x ∈ F i ∧ y ∈ F i
    · obtain ⟨i₀, hi₀⟩ := hboth
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by have := i₀.2; omega⟩
      apply hasK_succ hδ
      refine ⟨fun j => F (i₀.succAbove j), ⟨fun j => hcyc _ fun h => ?_, fun j l hjl => ?_⟩, ?_⟩
      · exact hF.not_mem (Fin.succAbove_ne i₀ j).symm hi₀.1 h.1
      · exact hF.disj fun h => hjl (Fin.succAbove_right_injective h)
      · have h3 := (hF.1 i₀).three_le_card
        refine h3.trans (card_le_card fun v hv => mem_rest.2 fun j hj => ?_)
        exact hF.not_mem (Fin.succAbove_ne i₀ j).symm hv hj
    · push Not at hboth
      exact ⟨F, fun i => hcyc i fun h => hboth i h.1 h.2, hF.2⟩

omit [Fintype V] [DecidableEq V] in
/-- Disjoint cyclic sets give disjoint cycles. -/
theorem hasDisjointCycles_of_hasK [Finite V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (h : HasK G k) : HasDisjointCycles G k := by
  obtain ⟨F, hF⟩ := h
  choose base c hc hsupp using fun i => (hF.1 i).exists_isCycle
  exact ⟨base, c, hc, fun i j hij v hv hv' => hF.not_mem hij (hsupp i v hv) (hsupp j v hv')⟩

end

/-- **The Corrádi–Hajnal theorem.** A graph on at least `3k` vertices with minimum degree at least
`2k` contains `k` vertex-disjoint cycles. -/
theorem corradi_hajnal {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hn : 3 * k ≤ Fintype.card V) (hδ : 2 * k ≤ G.minDegree) :
    HasDisjointCycles G k := by
  apply hasDisjointCycles_of_hasK
  refine hasK_of_minDeg k hn _ G rfl fun v => hδ.trans ((G.minDegree_le_degree v).trans ?_)
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  rfl

end CorradiHajnal
