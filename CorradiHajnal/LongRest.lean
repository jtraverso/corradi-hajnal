/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Witness

/-!
# The case of at least four uncovered vertices

Let `F` be an optimal family of `m` disjoint cyclic sets in a graph of minimum degree at least
`2 (m + 1)` without `m + 1` disjoint cyclic sets. Counting edges between the uncovered vertices
and the family shows that some member is a triangle receiving many edges from the rest. A careful
analysis of this triangle shows that the rest cannot have at least four vertices and at most two
low vertices.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma exists_adj_ne {S : Finset V} {v : V} (h : 2 ≤ nb G S v) (a : V) :
    ∃ w ∈ S, G.Adj v w ∧ w ≠ a := by
  classical
  have hne : ((S.filter (G.Adj v)).erase a).Nonempty := by
    rw [← card_pos]
    have := pred_card_le_card_erase (s := S.filter (G.Adj v)) (a := a)
    unfold nb at h
    omega
  obtain ⟨w, hw⟩ := hne
  simp only [mem_erase, mem_filter] at hw
  exact ⟨w, hw.2.1, hw.2.2, hw.1⟩

omit [DecidableEq V] in
lemma exists_adj_of_nb_ne_zero {S : Finset V} {v : V} (h : nb G S v ≠ 0) :
    ∃ x ∈ S, G.Adj v x := by
  by_contra h'
  push Not at h'
  exact h (nb_eq_zero_iff.2 h')

omit [DecidableEq V] in
lemma adj_of_nb_eq_two {T : Finset V} (hT : #T = 3) {v z : V} (h2 : nb G T v = 2) (hz : z ∈ T)
    (hvz : ¬ G.Adj v z) : ∀ y ∈ T, y ≠ z → G.Adj v y := by
  classical
  have e := nb_eq_erase_add (G := G) hz v
  rw [ite_eq_right hvz] at e
  have h := nb_eq_card_iff.1 (by rw [card_erase_of_mem hz, hT]; omega :
    nb G (T.erase z) v = #(T.erase z))
  exact fun y hy hyz => h y (mem_erase.2 ⟨hyz, hy⟩)

omit [DecidableEq V] in
lemma exists_not_adj_of_nb_eq_two {T : Finset V} (hT : #T = 3) {v : V} (h2 : nb G T v = 2) :
    ∃ z ∈ T, ¬ G.Adj v z := by
  by_contra h
  push Not at h
  have := nb_eq_card_of_forall h
  omega

variable [Fintype V] {m : ℕ} {F : Fin m → Finset V}

namespace Optimal

variable (hF : Optimal G F)
include hF

/-- Some member receives more than `2 #(Rest F)` edges from the rest. -/
lemma exists_heavy (hK : ¬ HasK G (m + 1)) (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v) :
    ∃ i, 2 * #(Rest F) + 1 ≤ ∑ v ∈ Rest F, nb G (F i) v := by
  by_contra h
  push Not at h
  have hne : (Rest F).Nonempty := by rw [← card_pos]; have := hF.three_le_rest; omega
  have hE := E2_add_two_le_of_not_cyc (hF.not_cyc_rest hK) hne
  have h1 : ∑ _v ∈ Rest F, 2 * (m + 1) ≤
      ∑ v ∈ Rest F, (nb G (Rest F) v + ∑ i, nb G (F i) v) :=
    sum_le_sum fun v _ => (hδ v).trans (nb_univ_eq hF.valid v).le
  rw [sum_add_distrib, sum_comm, sum_const, smul_eq_mul] at h1
  have h2 : ∑ i, ∑ v ∈ Rest F, nb G (F i) v ≤ ∑ _i : Fin m, 2 * #(Rest F) :=
    sum_le_sum fun i _ => by have := h i; omega
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
  unfold E2 at hE
  nlinarith

lemma card_eq_three_of_heavy {i : Fin m} (h : 2 * #(Rest F) + 1 ≤ ∑ v ∈ Rest F, nb G (F i) v) :
    #(F i) = 3 := by
  by_contra h3
  have h4 : 4 ≤ #(F i) := by have := (hF.minCyc i).three_le_card; omega
  have : ∑ v ∈ Rest F, nb G (F i) v ≤ ∑ _v ∈ Rest F, 2 :=
    sum_le_sum fun v hv => hF.nb_le_two h4 hv
  rw [sum_const, smul_eq_mul] at this
  omega

/-- The rest has at most three vertices, provided there are at most two low vertices. -/
lemma card_rest_le_three (hK : ¬ HasK G (m + 1)) (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v) :
    #(Rest F) ≤ 3 := by
  by_contra hr
  push Not at hr
  have hL := hF.card_low_le_two hδ
  have hacyc := hF.not_cyc_rest hK
  obtain ⟨i, hi⟩ := hF.exists_heavy hK hδ
  have hT := hF.card_eq_three_of_heavy hi
  set R3 := (Rest F).filter fun v => nb G (F i) v = 3 with hR3
  set R0 := (Rest F).filter fun v => nb G (F i) v = 0 with hR0
  set R1 := (Rest F).filter fun v => nb G (F i) v = 1 with hR1
  -- counting
  have hcount : #R1 + 2 * #R0 + 1 ≤ #R3 := by
    have key : ∀ v ∈ (Rest F), nb G (F i) v + (if nb G (F i) v = 1 then 1 else 0) +
        2 * (if nb G (F i) v = 0 then 1 else 0) ≤ 2 + (if nb G (F i) v = 3 then 1 else 0) := by
      intro v hv
      have := hF.nb_le_three i hv
      split_ifs <;> omega
    have := sum_le_sum key
    simp only [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul] at this
    simp only [hR3, hR0, hR1, card_filter]
    omega
  -- vertices seeing the whole triangle
  have hR3mem : ∀ {u}, u ∈ R3 → u ∈ (Rest F) ∧ ∀ x ∈ (F i), G.Adj u x := fun {u} hu =>
    ⟨(mem_filter.1 hu).1, hF.adj_of_nb_eq_three (mem_filter.1 hu).1 (mem_filter.1 hu).2⟩
  have hR3nb : ∀ {u}, u ∈ R3 → 2 ≤ nb G (Rest F) u := fun {u} hu => by
    have := hF.sum_le_of_nb_eq_three (mem_filter.1 hu).1 (mem_filter.1 hu).2
    omega
  -- the basic exchange
  have hfan : ∀ {u u' w x}, u ∈ R3 → u' ∈ R3 → w ∈ (Rest F) → u ≠ u' → w ≠ u' → G.Adj u w →
      x ∈ (F i) → G.Adj w x → False := by
    intro u u' w x hu hu' hw huu' hwu' huw hx hwx
    obtain ⟨s, s', hs, hs', hss', hxs, hxs', -⟩ := exists_pair_of_card_three hT hx
    exact hK (hF.hasK_fan hT (hR3mem hu).1 hw (hR3mem hu').1 hx hs hs' hss' hxs hxs' huu' hwu'
      huw ((hR3mem hu).2 x hx) hwx ((hR3mem hu').2 s hs) ((hR3mem hu').2 s' hs'))
  have hR3pos : 1 ≤ #R3 := by omega
  rcases (by omega : 3 ≤ #R3 ∨ #R3 = 2 ∨ #R3 = 1) with h3 | h2 | h1
  · -- at least three vertices see the whole triangle
    have hnbr : ∀ u ∈ R3, ∀ w ∈ (Rest F), G.Adj u w → w ∈ R0 := by
      intro u hu w hw huw
      by_contra hw0
      have hnz : nb G (F i) w ≠ 0 := fun h => hw0 (mem_filter.2 ⟨hw, h⟩)
      obtain ⟨x, hx, hwx⟩ := exists_adj_of_nb_ne_zero hnz
      have hne : ((R3.erase u).erase w).Nonempty := by
        rw [← card_pos]
        have := pred_card_le_card_erase (s := R3.erase u) (a := w)
        have := pred_card_le_card_erase (s := R3) (a := u)
        omega
      obtain ⟨u', hu'⟩ := hne
      simp only [mem_erase] at hu'
      exact hfan hu hu'.2.2 hw (Ne.symm hu'.2.1) (Ne.symm hu'.1) huw hx hwx
    have hnb0 : ∀ u ∈ R3, 2 ≤ nb G R0 u := by
      intro u hu
      refine (hR3nb hu).trans (card_le_card fun w hw => ?_)
      rw [mem_filter] at hw ⊢
      exact ⟨hnbr u hu w hw.1 hw.2, hw.2⟩
    have hdisj : Disjoint R3 R0 := by
      rw [disjoint_left]
      intro v hv hv0
      have := (mem_filter.1 hv).2
      have := (mem_filter.1 hv0).2
      omega
    have hsub : R3 ∪ R0 ⊆ (Rest F) := union_subset (filter_subset _ _) (filter_subset _ _)
    have hne : (R3 ∪ R0).Nonempty := by
      rw [← card_pos, card_union_of_disjoint hdisj]; omega
    have hE := E2_add_two_le_of_not_cyc (fun h => hacyc (h.mono hsub)) hne
    have hA : ∑ v ∈ R3, 2 ≤ ∑ v ∈ R3, nb G (R3 ∪ R0) v :=
      sum_le_sum fun v hv => (hnb0 v hv).trans (nb_mono subset_union_right v)
    have hB : ∑ v ∈ R0, nb G R3 v ≤ ∑ v ∈ R0, nb G (R3 ∪ R0) v :=
      sum_le_sum fun v _ => nb_mono subset_union_left v
    have hC : ∑ v ∈ R3, 2 ≤ ∑ v ∈ R3, nb G R0 v := sum_le_sum hnb0
    rw [sum_nb_comm] at hB
    unfold E2 at hE
    rw [sum_union hdisj, card_union_of_disjoint hdisj] at hE
    rw [sum_const, smul_eq_mul] at hA hC
    omega
  · -- exactly two vertices see the whole triangle
    obtain ⟨u, u', huu', hR3e⟩ := card_eq_two.1 h2
    have hu : u ∈ R3 := by rw [hR3e]; simp
    have hu' : u' ∈ R3 := by rw [hR3e]; simp
    have hR0e : R0 = ∅ := card_eq_zero.1 (by omega)
    obtain ⟨w, hw, huw, hwu'⟩ := exists_adj_ne (hR3nb hu) u'
    have hnz : nb G (F i) w ≠ 0 := fun h => by
      have : w ∈ R0 := mem_filter.2 ⟨hw, h⟩
      rw [hR0e] at this
      simp at this
    obtain ⟨x, hx, hwx⟩ := exists_adj_of_nb_ne_zero hnz
    exact hfan hu hu' hw huu' hwu' huw hx hwx
  · -- exactly one vertex sees the whole triangle
    obtain ⟨u, hR3e⟩ := card_eq_one.1 h1
    have hu : u ∈ R3 := by rw [hR3e]; simp
    have huR := (hR3mem hu).1
    have hR0e : R0 = ∅ := card_eq_zero.1 (by omega)
    have hR1e : R1 = ∅ := card_eq_zero.1 (by omega)
    have htwo : ∀ w ∈ (Rest F), w ≠ u → nb G (F i) w = 2 := by
      intro w hw hwu
      have := hF.nb_le_three i hw
      have h0 : w ∉ R0 := by rw [hR0e]; simp
      have h1' : w ∉ R1 := by rw [hR1e]; simp
      have h3' : w ∉ R3 := by rw [hR3e]; simpa using hwu
      simp only [hR0, hR1, hR3, mem_filter, not_and] at h0 h1' h3'
      have := h0 hw
      have := h1' hw
      have := h3' hw
      omega
    obtain ⟨w₁, hw₁, huw₁, -⟩ := exists_adj_ne (hR3nb hu) u
    have hw₁u : w₁ ≠ u := (G.ne_of_adj huw₁).symm
    obtain ⟨z₁, hz₁, hw₁z₁⟩ := exists_not_adj_of_nb_eq_two hT (htwo w₁ hw₁ hw₁u)
    have hw₁adj := adj_of_nb_eq_two hT (htwo w₁ hw₁ hw₁u) hz₁ hw₁z₁
    -- every other uncovered vertex sees `(F i)` except `z₁`
    have hall : ∀ w ∈ (Rest F), w ≠ u → ∀ y ∈ (F i), y ≠ z₁ → G.Adj w y := by
      intro w hw hwu y hy hyz
      by_contra hwy
      have hwadj := adj_of_nb_eq_two hT (htwo w hw hwu) hy hwy
      have hww₁ : w₁ ≠ w := fun e => hwy (e ▸ hw₁adj y hy hyz)
      obtain ⟨s, s', hs, hs', hss', hys, hys', -⟩ := exists_pair_of_card_three hT hy
      exact hK (hF.hasK_fan hT huR hw₁ hw hy hs hs' hss' hys hys' (Ne.symm hwu) hww₁ huw₁
        ((hR3mem hu).2 y hy) (hw₁adj y hy hyz) (hwadj s hs (Ne.symm hys))
        (hwadj s' hs' (Ne.symm hys')))
    obtain ⟨x, hx, hxz⟩ : ∃ x ∈ (F i), x ≠ z₁ := by
      obtain ⟨s, -, hs, -, -, hzs, -⟩ := exists_pair_of_card_three hT hz₁
      exact ⟨s, hs, Ne.symm hzs⟩
    have hsw := hF.swap hT huR (hR3mem hu).2 hx
    have hxall : nb G ((Rest F).erase u) x = #((Rest F).erase u) :=
      nb_eq_card_of_forall fun w hw =>
        (hall w (mem_of_mem_erase hw) (ne_of_mem_erase hw) x hx hxz).symm
    have hle := nb_le_card_sub_one (G := G) huR
    rw [card_erase_of_mem huR] at hxall
    have huall : ∀ w ∈ (Rest F).erase u, G.Adj u w := by
      apply nb_eq_card_iff.1
      rw [nb_erase_self, card_erase_of_mem huR]
      omega
    have hlow : (Rest F).erase u ⊆ Low G F := by
      intro w hw
      refine mem_filter.2 ⟨mem_of_mem_erase hw, ?_⟩
      by_contra h2
      push Not at h2
      obtain ⟨w', hw', hww', hw'u⟩ := exists_adj_ne (show 2 ≤ nb G (Rest F) w by omega) u
      exact hacyc ((cyc_triangle (huall w hw) hww' (huall w' (mem_erase.2 ⟨hw'u, hw'⟩))).mono
        (triple_subset huR (mem_of_mem_erase hw) hw'))
    have := card_le_card hlow
    rw [card_erase_of_mem huR] at this
    omega

end Optimal

end CorradiHajnal
