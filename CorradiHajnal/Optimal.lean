/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Family

/-!
# Optimal families and their basic exchange properties

An optimal family of `m` disjoint cyclic sets (leaving at least three vertices uncovered)
minimises the number of covered vertices and, subject to that, maximises the number of edges
spanned by the uncovered vertices. Assuming that `G` has no `m + 1` disjoint cyclic sets, we
derive the basic exchange properties used in the main argument.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {m : ℕ}

variable (G) in
/-- An optimal family: among valid families leaving at least three vertices uncovered, it covers
as few vertices as possible and, subject to this, its rest spans as many edges as possible. -/
def Optimal (F : Fin m → Finset V) : Prop :=
  Valid G F ∧ 3 ≤ #(Rest F) ∧
    ∀ F' : Fin m → Finset V, Valid G F' → 3 ≤ #(Rest F') →
      total F ≤ total F' ∧ (total F' = total F → E2 G (Rest F') ≤ E2 G (Rest F))

lemma exists_optimal (h : ∃ F : Fin m → Finset V, Valid G F ∧ 3 ≤ #(Rest F)) :
    ∃ F : Fin m → Finset V, Optimal G F := by
  classical
  set A := (univ : Finset (Fin m → Finset V)).filter fun F => Valid G F ∧ 3 ≤ #(Rest F)
  have hA : A.Nonempty := by
    obtain ⟨F, hF⟩ := h
    exact ⟨F, by simp [A, hF]⟩
  obtain ⟨F0, hF0, hmin⟩ := exists_min_image A total hA
  set B := A.filter fun F => total F = total F0
  have hB : B.Nonempty := ⟨F0, by simp [B, hF0]⟩
  obtain ⟨F1, hF1, hmax⟩ := exists_max_image B (fun F => E2 G (Rest F)) hB
  simp only [B, A, mem_filter, mem_univ, true_and] at hF1
  refine ⟨F1, hF1.1.1, hF1.1.2, fun F' hF' h3 => ?_⟩
  have hF'A : F' ∈ A := by simp [A, hF', h3]
  refine ⟨hF1.2 ▸ hmin F' hF'A, fun he => hmax F' ?_⟩
  simp [B, A, hF', h3, he, hF1.2]

namespace Optimal

variable {F : Fin m → Finset V} (hF : Optimal G F)
include hF

lemma valid : Valid G F := hF.1

lemma three_le_rest : 3 ≤ #(Rest F) := hF.2.1

/-- No valid family covers fewer vertices. -/
lemma total_le {F' : Fin m → Finset V} (hF' : Valid G F') : total F ≤ total F' := by
  by_contra hlt
  push Not at hlt
  have e1 := card_rest_add_total hF.valid
  have e2 := card_rest_add_total hF'
  have := (hF.2.2 F' hF' (by have := hF.three_le_rest; omega)).1
  omega

lemma E2_le {F' : Fin m → Finset V} (hF' : Valid G F') (he : total F' = total F) :
    E2 G (Rest F') ≤ E2 G (Rest F) := by
  have e1 := card_rest_add_total hF.valid
  have e2 := card_rest_add_total hF'
  exact (hF.2.2 F' hF' (by have := hF.three_le_rest; omega)).2 he

lemma minCyc (i : Fin m) : MinCyc G (F i) := by
  refine ⟨hF.valid.1 i, fun T hT hne hTc => ?_⟩
  have hv := valid_update hF.valid hTc fun j hj => (hF.valid.disj (Ne.symm hj)).mono_left hT
  have h1 := total_update F i T
  have h2 := card_lt_card (ssubset_of_subset_of_ne hT hne)
  have := hF.total_le hv
  omega

lemma three_le_card (i : Fin m) : 3 ≤ #(F i) := (hF.minCyc i).three_le_card

lemma adj_of_card_three {i : Fin m} (h3 : #(F i) = 3) {a b : V} (ha : a ∈ F i) (hb : b ∈ F i)
    (hab : a ≠ b) : G.Adj a b := (hF.minCyc i).adj_of_card_three h3 ha hb hab


lemma not_cyc_rest (hK : ¬ HasK G (m + 1)) : ¬ Cyc G (Rest F) := fun h =>
  hK (hasK_of_extend hF.valid h fun j => (disjoint_rest F j).symm)

/-- A vertex outside the family has at most two neighbours on a member of size at least four. -/
lemma nb_le_two {i : Fin m} (h4 : 4 ≤ #(F i)) {v : V} (hv : v ∈ Rest F) : nb G (F i) v ≤ 2 := by
  by_contra h3
  push Not at h3
  obtain ⟨T, hT, hTc, hTlt⟩ :=
    (hF.minCyc i).exists_smaller h4 (mem_rest.1 hv i) (by omega)
  have hvF := valid_update hF.valid hTc fun j hj => by
    rw [disjoint_left]
    intro x hx hxj
    rcases mem_insert.1 (hT hx) with rfl | hx
    · exact mem_rest.1 hv j hxj
    · exact hF.valid.not_mem (Ne.symm hj) hx hxj
  have h1 := total_update F i T
  have := hF.total_le hvF
  omega

/-- A vertex outside the family has at most three neighbours on any member. -/
lemma nb_le_three (i : Fin m) {v : V} (hv : v ∈ Rest F) : nb G (F i) v ≤ 3 := by
  by_cases h4 : 4 ≤ #(F i)
  · have := hF.nb_le_two h4 hv; omega
  · have := nb_le_card (G := G) (F i) v; omega

/-- **Swap lemma.** If `v ∉ ⋃ F` is adjacent to all three vertices of a triangle `F i`, then
exchanging `v` with any `x ∈ F i` cannot increase the number of edges of the rest. -/
lemma swap {i : Fin m} (h3 : #(F i) = 3) {v : V} (hv : v ∈ Rest F)
    (hadj : ∀ x ∈ F i, G.Adj v x) {x : V} (hx : x ∈ F i) :
    nb G ((Rest F).erase v) x ≤ nb G (Rest F) v := by
  set S := insert v ((F i).erase x) with hS
  have hvi : v ∉ F i := mem_rest.1 hv i
  obtain ⟨a, b, hab, hFe⟩ : ∃ a b, a ≠ b ∧ (F i).erase x = {a, b} := by
    apply card_eq_two.1
    rw [card_erase_of_mem hx, h3]
  have ha : a ∈ F i := mem_of_mem_erase (hFe ▸ mem_insert_self a {b})
  have hb : b ∈ F i := mem_of_mem_erase (hFe ▸ mem_insert_of_mem (mem_singleton_self b))
  have hSc : Cyc G S := by
    rw [hS, hFe]
    exact cyc_triangle (hadj a ha) (hF.adj_of_card_three h3 ha hb hab) (hadj b hb)
  have hSv := valid_update hF.valid hSc fun j hj => by
    rw [disjoint_left]
    intro y hy hyj
    rcases mem_insert.1 hy with rfl | hy
    · exact mem_rest.1 hv j hyj
    · exact hF.valid.not_mem (Ne.symm hj) (mem_of_mem_erase hy) hyj
  have hcard : #S = #(F i) := by
    rw [hS, card_insert_of_notMem (fun h => hvi (mem_of_mem_erase h)), card_erase_of_mem hx]
    omega
  have htot : total (Function.update F i S) = total F := by
    have := total_update F i S; omega
  have hE := hF.E2_le hSv htot
  have hrest : Rest (Function.update F i S) = insert x ((Rest F).erase v) := by
    rw [rest_update hF.valid]
    ext y
    simp only [hS, mem_sdiff, mem_union, mem_insert, mem_erase]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · right; exact ⟨fun e => h2 (Or.inl e), h1⟩
      · left; by_contra hyx; exact h2 (Or.inr ⟨hyx, h1⟩)
    · rintro (rfl | ⟨h1, h2⟩)
      · refine ⟨Or.inr hx, ?_⟩
        rintro (e | ⟨e, -⟩)
        · exact hvi (e ▸ hx)
        · exact e rfl
      · refine ⟨Or.inl h2, ?_⟩
        rintro (e | ⟨-, e⟩)
        · exact h1 e
        · exact not_mem_rest_of_mem e h2
  rw [hrest, E2_insert (fun h => not_mem_rest_of_mem hx (mem_of_mem_erase h))] at hE
  have e := E2_eq_erase_add (G := G) hv
  omega

/-- If a vertex `c` of a triangle `F i` has three neighbours on a long member `F j`, and some
uncovered vertex `w` is adjacent to both other vertices of `F i`, we could shorten the family. -/
lemma nb_le_two_of_long {i j : Fin m} (hij : i ≠ j) (h3 : #(F i) = 3) (h4 : 4 ≤ #(F j))
    {c w : V} (hc : c ∈ F i) (hw : w ∈ Rest F) (hadj : ∀ x ∈ F i, x ≠ c → G.Adj w x) :
    nb G (F j) c ≤ 2 := by
  by_contra h
  push Not at h
  have hcj : c ∉ F j := hF.valid.not_mem hij hc
  obtain ⟨T, hT, hTc, hTlt⟩ := (hF.minCyc j).exists_smaller h4 hcj (by omega)
  set S := insert w ((F i).erase c) with hS
  have hwi : w ∉ F i := mem_rest.1 hw i
  obtain ⟨a, b, hab, hFe⟩ : ∃ a b, a ≠ b ∧ (F i).erase c = {a, b} := by
    apply card_eq_two.1
    rw [card_erase_of_mem hc, h3]
  have ha : a ∈ F i := mem_of_mem_erase (hFe ▸ mem_insert_self a {b})
  have hb : b ∈ F i := mem_of_mem_erase (hFe ▸ mem_insert_of_mem (mem_singleton_self b))
  have hac : a ≠ c := ne_of_mem_erase (hFe ▸ mem_insert_self a {b})
  have hbc : b ≠ c := ne_of_mem_erase (hFe ▸ mem_insert_of_mem (mem_singleton_self b))
  have hSc : Cyc G S := by
    rw [hS, hFe]
    exact cyc_triangle (hadj a ha hac) (hF.adj_of_card_three h3 ha hb hab) (hadj b hb hbc)
  have hST : Disjoint S T := by
    rw [disjoint_left]
    intro y hy hyT
    rcases mem_insert.1 (hT hyT) with rfl | hyj
    · rcases mem_insert.1 hy with e | hy
      · exact hwi (e ▸ hc)
      · exact (ne_of_mem_erase hy) rfl
    · rcases mem_insert.1 hy with rfl | hy
      · exact mem_rest.1 hw j hyj
      · exact hF.valid.not_mem hij (mem_of_mem_erase hy) hyj
  have hv := valid_update₂ hF.valid hij hSc hTc hST
    (fun l hli hlj => by
      rw [disjoint_left]
      intro y hy hyl
      rcases mem_insert.1 hy with rfl | hy
      · exact mem_rest.1 hw l hyl
      · exact hF.valid.not_mem (Ne.symm hli) (mem_of_mem_erase hy) hyl)
    (fun l hli hlj => by
      rw [disjoint_left]
      intro y hy hyl
      rcases mem_insert.1 (hT hy) with rfl | hy
      · exact hF.valid.not_mem (Ne.symm hli) hc hyl
      · exact hF.valid.not_mem (Ne.symm hlj) hy hyl)
  have e1 := total_update (Function.update F j T) i S
  have e2 := total_update F j T
  have hSi : Function.update F j T i = F i := Function.update_of_ne hij _ _
  rw [hSi] at e1
  have hcardS : #S = 3 := by
    rw [hS, card_insert_of_notMem (fun h => hwi (mem_of_mem_erase h)), card_erase_of_mem hc, h3]
  have := hF.total_le hv
  omega

end Optimal

end CorradiHajnal
