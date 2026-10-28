/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.LongRest
public import CorradiHajnal.Finite

/-!
# The case of exactly three uncovered vertices

If the rest of an optimal family has exactly three vertices, it is a path `a - u - b`. Some member
is a triangle `C` seen entirely by `a` (say) and twice by `b`; then `u` has no neighbour on `C`
and a weighted count of the edges from `a, b, u` and a suitable vertex `c ∈ C` to the other
members gives a contradiction.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {m : ℕ} {F : Fin m → Finset V}

namespace Optimal

variable (hF : Optimal G F)
include hF

/-- The weighted count of edges to another triangle of the family. -/
lemma tri_member_bound (hK : ¬ HasK G (m + 1)) {i j : Fin m} (hij : i ≠ j) (hC : #(F i) = 3)
    (hD : #(F j) = 3) {a b u c c₁ c₂ : V} (ha : a ∈ Rest F) (hb : b ∈ Rest F)
    (hu : u ∈ Rest F) (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hc : c ∈ F i)
    (hc₁ : c₁ ∈ F i) (hc₂ : c₂ ∈ F i) (hcc₁ : c ≠ c₁) (hcc₂ : c ≠ c₂) (hc₁₂ : c₁ ≠ c₂)
    (hac : G.Adj a c) (hac₁ : G.Adj a c₁) (hac₂ : G.Adj a c₂) (hbc₁ : G.Adj b c₁)
    (hbc₂ : G.Adj b c₂) (hua : G.Adj u a) (hub : G.Adj u b) :
    nb G (F j) a + nb G (F j) b + 2 * nb G (F j) u + 2 * nb G (F j) c ≤ 12 := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hD'⟩ := card_eq_three.1 hD
  have hx : x ∈ F j := by rw [hD']; simp
  have hy : y ∈ F j := by rw [hD']; simp
  have hz : z ∈ F j := by rw [hD']; simp
  have P1 : ∀ {t s s'}, t ∈ F j → s ∈ F j → s' ∈ F j → s ≠ s' → t ≠ s → t ≠ s' →
      (decide (G.Adj a t) && (decide (G.Adj u t) && (decide (G.Adj b s) &&
        decide (G.Adj b s')))) = false := by
    intro t s s' ht hs hs' hss' hts hts'
    simp only [← Bool.decide_and]
    exact decide_eq_false fun ⟨h₁, h₂, h₃, h₄⟩ => hK (hF.hasK_fan hD hu ha hb ht hs hs' hss'
      hts hts' (Ne.symm hbu) hab hua h₂ h₁ h₃ h₄)
  have P2 : ∀ {t s s'}, t ∈ F j → s ∈ F j → s' ∈ F j → s ≠ s' → t ≠ s → t ≠ s' →
      (decide (G.Adj b t) && (decide (G.Adj u t) && (decide (G.Adj a s) &&
        decide (G.Adj a s')))) = false := by
    intro t s s' ht hs hs' hss' hts hts'
    simp only [← Bool.decide_and]
    exact decide_eq_false fun ⟨h₁, h₂, h₃, h₄⟩ => hK (hF.hasK_fan hD hu hb ha ht hs hs' hss'
      hts hts' (Ne.symm hau) (Ne.symm hab) hub h₂ h₁ h₃ h₄)
  have P3 : ∀ {t s s'}, t ∈ F j → s ∈ F j → s' ∈ F j → s ≠ s' → t ≠ s → t ≠ s' →
      (decide (G.Adj c t) && (decide (G.Adj a t) && (decide (G.Adj u s) &&
        decide (G.Adj u s')))) = false := by
    intro t s s' ht hs hs' hss' hts hts'
    simp only [← Bool.decide_and]
    exact decide_eq_false fun ⟨h₁, h₂, h₃, h₄⟩ => hK (hF.hasK_cross hij hC hD ha hb hu hab hau
      hbu hc hc₁ hc₂ hcc₁ hcc₂ hc₁₂ ht hs hs' hts hts' hss' hac h₁ h₂ hbc₁ hbc₂ h₃ h₄)
  have P4 : ∀ {t s s'}, t ∈ F j → s ∈ F j → s' ∈ F j → s ≠ s' → t ≠ s → t ≠ s' →
      (decide (G.Adj c s) && (decide (G.Adj c s') && (decide (G.Adj u t) &&
        decide (G.Adj b t)))) = false := by
    intro t s s' ht hs hs' hss' hts hts'
    simp only [← Bool.decide_and]
    exact decide_eq_false fun ⟨h₁, h₂, h₃, h₄⟩ => hK (hF.hasK_cross' hij hC hD ha hb hu hab hau
      hc hc₁ hc₂ hcc₁ hcc₂ hc₁₂ ht hs hs' hts hts' hss' h₁ h₂ hac₁ hac₂ hub h₄ h₃)
  have P5 : ∀ {t s s'}, t ∈ F j → s ∈ F j → s' ∈ F j → s ≠ s' → t ≠ s → t ≠ s' →
      (decide (G.Adj c s) && (decide (G.Adj c s') && (decide (G.Adj u t) &&
        decide (G.Adj a t)))) = false := by
    intro t s s' ht hs hs' hss' hts hts'
    simp only [← Bool.decide_and]
    exact decide_eq_false fun ⟨h₁, h₂, h₃, h₄⟩ => hK (hF.hasK_cross' hij hC hD hb ha hu
      (Ne.symm hab) hbu hc hc₁ hc₂ hcc₁ hcc₂ hc₁₂ ht hs hs' hts hts' hss' h₁ h₂ hbc₁ hbc₂ hua h₄ h₃)
  simp only [hD', nb_triple hxy hxz hyz]
  exact tri_bound (P1 hx hy hz hyz hxy hxz) (P1 hy hx hz hxz (Ne.symm hxy) hyz)
    (P1 hz hx hy hxy (Ne.symm hxz) (Ne.symm hyz))
    (P2 hx hy hz hyz hxy hxz) (P2 hy hx hz hxz (Ne.symm hxy) hyz)
    (P2 hz hx hy hxy (Ne.symm hxz) (Ne.symm hyz))
    (P3 hx hy hz hyz hxy hxz) (P3 hy hx hz hxz (Ne.symm hxy) hyz)
    (P3 hz hx hy hxy (Ne.symm hxz) (Ne.symm hyz))
    (P4 hx hy hz hyz hxy hxz) (P4 hy hx hz hxz (Ne.symm hxy) hyz)
    (P4 hz hx hy hxy (Ne.symm hxz) (Ne.symm hyz))
    (P5 hx hy hz hyz hxy hxz) (P5 hy hx hz hxz (Ne.symm hxy) hyz)
    (P5 hz hx hy hxy (Ne.symm hxz) (Ne.symm hyz))

/-- The core of the three-vertex case: the rest is a path `a - u - b` and some triangle `F i` is
seen entirely by `a` and at least twice by `b`. -/
lemma false_of_path (hK : ¬ HasK G (m + 1)) (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v)
    {u a b : V} (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u) (hReq : Rest F = {u, a, b})
    (hua : G.Adj u a) (hub : G.Adj u b) (hnab : ¬ G.Adj a b) {i : Fin m} (hC : #(F i) = 3)
    (hA3 : nb G (F i) a = 3) (hB2 : 2 ≤ nb G (F i) b) : False := by
  have huR : u ∈ Rest F := by rw [hReq]; simp
  have haR : a ∈ Rest F := by rw [hReq]; simp
  have hbR : b ∈ Rest F := by rw [hReq]; simp
  have haC := hF.adj_of_nb_eq_three haR hA3
  have hb3 := hF.nb_le_three i hbR
  -- `u` has no neighbour on `F i`
  have hq : nb G (F i) u = 0 := by
    by_contra hq
    obtain ⟨t, ht, hut⟩ := exists_adj_of_nb_ne_zero hq
    obtain ⟨s, s', hs, hs', hss', hts, hts', -⟩ := exists_pair_of_card_three hC ht
    by_cases hbt : G.Adj b t
    · exact hK (hF.hasK_fan hC huR hbR haR ht hs hs' hss' hts hts' (Ne.symm hau) (Ne.symm hab)
        hub hut hbt (haC s hs) (haC s' hs'))
    · have hb2 : nb G (F i) b = 2 := by
        by_contra h
        exact hbt (hF.adj_of_nb_eq_three hbR (by omega) t ht)
      have hbadj := adj_of_nb_eq_two hC hb2 ht hbt
      exact hK (hF.hasK_fan hC huR haR hbR ht hs hs' hss' hts hts' (Ne.symm hbu) hab hua hut
        (haC t ht) (hbadj s hs (Ne.symm hts)) (hbadj s' hs' (Ne.symm hts')))
  -- a vertex `c ∈ F i` such that `b` sees the other two
  obtain ⟨c, hc, hbc⟩ : ∃ c ∈ F i, ∀ y ∈ F i, y ≠ c → G.Adj b y := by
    by_cases h3 : nb G (F i) b = 3
    · obtain ⟨c, hc⟩ : (F i).Nonempty := by rw [← card_pos]; omega
      exact ⟨c, hc, fun y hy _ => hF.adj_of_nb_eq_three hbR h3 y hy⟩
    · obtain ⟨z, hz, hbz⟩ := exists_not_adj_of_nb_eq_two hC (by omega : nb G (F i) b = 2)
      exact ⟨z, hz, adj_of_nb_eq_two hC (by omega) hz hbz⟩
  have huc : ¬ G.Adj u c := nb_eq_zero_iff.1 hq c hc
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁₂, hcc₁, hcc₂, -⟩ := exists_pair_of_card_three hC hc
  -- degrees inside the rest
  have hdRa : nb G (Rest F) a ≤ 1 := by
    rw [hReq, nb_triple (Ne.symm hau) (Ne.symm hbu) hab]
    have hnba : ¬ G.Adj b a := fun h => hnab h.symm
    simp [hua.symm, hnab]
  have hdRb : nb G (Rest F) b ≤ 1 := by
    rw [hReq, nb_triple (Ne.symm hau) (Ne.symm hbu) hab]
    have hnba : ¬ G.Adj b a := fun h => hnab h.symm
    simp [hub.symm, hnba]
  have hdRu : nb G (Rest F) u ≤ 2 := by
    have := nb_le_card_sub_one (G := G) huR
    have h3 : #(Rest F) = 3 := by
      rw [hReq]; exact card_eq_three.2 ⟨u, a, b, Ne.symm hau, Ne.symm hbu, hab, rfl⟩
    omega
  have hdRc : nb G (Rest F) c ≤ 2 := by
    rw [hReq, nb_triple (Ne.symm hau) (Ne.symm hbu) hab]
    have hcu : ¬ G.Adj c u := fun h => huc h.symm
    simp only [toNat_decide, hcu, ite_false]
    split_ifs <;> simp
  -- lower bounds
  have e := fun v => nb_univ_eq hF.valid v
  have La : 2 * m + 1 ≤ ∑ j, nb G (F j) a := by have := hδ a; have := e a; omega
  have Lb : 2 * m + 1 ≤ ∑ j, nb G (F j) b := by have := hδ b; have := e b; omega
  have Lu : 2 * m ≤ ∑ j, nb G (F j) u := by have := hδ u; have := e u; omega
  have Lc : 2 * m ≤ ∑ j, nb G (F j) c := by have := hδ c; have := e c; omega
  -- upper bounds
  have Ui : nb G (F i) a + nb G (F i) b + 2 * nb G (F i) u + 2 * nb G (F i) c ≤ 10 := by
    have := (hF.minCyc i).nb_eq_two hc
    omega
  have Uj : ∀ j ∈ univ.erase i,
      nb G (F j) a + nb G (F j) b + 2 * nb G (F j) u + 2 * nb G (F j) c ≤ 12 := by
    intro j hj
    have hij : i ≠ j := Ne.symm (ne_of_mem_erase hj)
    by_cases h4 : 4 ≤ #(F j)
    · have := hF.nb_le_two h4 haR
      have := hF.nb_le_two h4 hbR
      have := hF.nb_le_two h4 huR
      have := hF.nb_le_two_of_long hij hC h4 hc haR fun x hx _ => haC x hx
      omega
    · have h3 : #(F j) = 3 := by have := (hF.minCyc j).three_le_card; omega
      exact hF.tri_member_bound hK hij hC h3 haR hbR huR hab hau hbu hc hc₁ hc₂ hcc₁ hcc₂ hc₁₂
        (haC c hc) (haC c₁ hc₁) (haC c₂ hc₂) (hbc c₁ hc₁ (Ne.symm hcc₁))
        (hbc c₂ hc₂ (Ne.symm hcc₂)) hua hub
  have hsum := sum_le_sum Uj
  rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin,
    smul_eq_mul] at hsum
  have htot := sum_erase_add univ
    (fun j => nb G (F j) a + nb G (F j) b + 2 * nb G (F j) u + 2 * nb G (F j) c) (mem_univ i)
  simp only [sum_add_distrib, ← mul_sum] at htot hsum
  have hm : 1 ≤ m := by have := i.2; omega
  have : 12 * (m - 1) + 12 = 12 * m := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

/-- The rest cannot have exactly three vertices. -/
lemma card_rest_ne_three (hK : ¬ HasK G (m + 1)) (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v) :
    #(Rest F) ≠ 3 := by
  intro h3
  have hL := hF.card_low_le_two hδ
  obtain ⟨u, huR, huL⟩ : ∃ u ∈ Rest F, u ∉ Low G F := by
    by_contra h
    push Not at h
    have := card_le_card (show Rest F ⊆ Low G F from h)
    omega
  have hu2 : 2 ≤ nb G (Rest F) u := by
    by_contra h
    exact huL (mem_filter.2 ⟨huR, by omega⟩)
  obtain ⟨a, haR, hua, -⟩ := exists_adj_ne hu2 u
  obtain ⟨b, hbR, hub, hba⟩ := exists_adj_ne hu2 a
  have hau : a ≠ u := (G.ne_of_adj hua).symm
  have hbu : b ≠ u := (G.ne_of_adj hub).symm
  have hReq : Rest F = {u, a, b} := by
    symm
    apply eq_of_subset_of_card_le (triple_subset huR haR hbR)
    rw [h3, card_eq_three.2 ⟨u, a, b, Ne.symm hau, Ne.symm hbu, Ne.symm hba, rfl⟩]
  have hnab : ¬ G.Adj a b := fun h =>
    hF.not_cyc_rest hK (hReq ▸ cyc_triangle hua h hub)
  have e := fun v => nb_univ_eq hF.valid v
  have hdRa : nb G (Rest F) a ≤ 1 := by
    rw [hReq, nb_triple (Ne.symm hau) (Ne.symm hbu) (Ne.symm hba)]
    have hnba : ¬ G.Adj b a := fun h => hnab h.symm
    simp [hua.symm, hnab]
  have hdRb : nb G (Rest F) b ≤ 1 := by
    rw [hReq, nb_triple (Ne.symm hau) (Ne.symm hbu) (Ne.symm hba)]
    have hnba : ¬ G.Adj b a := fun h => hnab h.symm
    simp [hub.symm, hnba]
  have La : 2 * m + 1 ≤ ∑ j, nb G (F j) a := by have := hδ a; have := e a; omega
  have Lb : 2 * m + 1 ≤ ∑ j, nb G (F j) b := by have := hδ b; have := e b; omega
  obtain ⟨i, hi⟩ : ∃ i, 5 ≤ nb G (F i) a + nb G (F i) b := by
    by_contra h
    push Not at h
    have : ∑ j, (nb G (F j) a + nb G (F j) b) ≤ ∑ _j : Fin m, 4 :=
      sum_le_sum fun j _ => by have := h j; omega
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  have ha3 := hF.nb_le_three i haR
  have hb3 := hF.nb_le_three i hbR
  by_cases hA3 : nb G (F i) a = 3
  · exact hF.false_of_path hK hδ (Ne.symm hba) hau hbu hReq hua hub hnab
      (hF.card_eq_three_of_nb_eq_three haR hA3) hA3 (by omega)
  · have hB3 : nb G (F i) b = 3 := by omega
    exact hF.false_of_path hK hδ hba hbu hau (by rw [hReq]; ext; simp; tauto) hub hua
      (fun h => hnab h.symm) (hF.card_eq_three_of_nb_eq_three hbR hB3) hB3 (by omega)

end Optimal

end CorradiHajnal
