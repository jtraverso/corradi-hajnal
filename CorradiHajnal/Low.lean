/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Optimal

/-!
# Low vertices of the rest

For an optimal family `F` in a graph of minimum degree at least `2 (m + 1)`, the set `Low G F` of
uncovered vertices with at most one uncovered neighbour has at most two elements, unless `G`
has `m + 1` disjoint cyclic sets.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {m : ℕ} {F : Fin m → Finset V}

variable (G) in
/-- Uncovered vertices with at most one uncovered neighbour. -/
def Low (F : Fin m → Finset V) : Finset V := (Rest F).filter fun v => nb G (Rest F) v ≤ 1

lemma low_subset : Low G F ⊆ Rest F := filter_subset _ _

namespace Optimal

variable (hF : Optimal G F)
include hF

lemma card_eq_three_of_nb_eq_three {i : Fin m} {v : V} (hv : v ∈ Rest F)
    (h : nb G (F i) v = 3) : #(F i) = 3 := by
  have h1 := nb_le_card (G := G) (F i) v
  by_contra hne
  have := hF.nb_le_two (i := i) (by omega) hv
  omega

lemma adj_of_nb_eq_three {i : Fin m} {v : V} (hv : v ∈ Rest F) (h : nb G (F i) v = 3) :
    ∀ x ∈ F i, G.Adj v x :=
  nb_eq_card_iff.1 (by rw [h, hF.card_eq_three_of_nb_eq_three hv h])

/-- If an uncovered vertex `w` sees a whole triangle `F i`, then the rest sends few edges to it. -/
lemma sum_le_of_nb_eq_three {i : Fin m} {w : V} (hw : w ∈ Rest F) (h3 : nb G (F i) w = 3) :
    ∑ v ∈ Rest F, nb G (F i) v ≤ 3 + 3 * nb G (Rest F) w := by
  have hc := hF.card_eq_three_of_nb_eq_three hw h3
  have hadj := hF.adj_of_nb_eq_three hw h3
  rw [← sum_erase_add _ _ hw, sum_nb_comm, h3]
  have : ∑ x ∈ F i, nb G ((Rest F).erase w) x ≤ ∑ _x ∈ F i, nb G (Rest F) w :=
    sum_le_sum fun x hx => hF.swap hc hw hadj hx
  rw [sum_const, hc, smul_eq_mul] at this
  omega

lemma sum_low_le (i : Fin m) (h3 : 3 ≤ #(Low G F)) :
    ∑ v ∈ Low G F, nb G (F i) v ≤ 2 * #(Low G F) := by
  by_cases h : ∃ w ∈ Low G F, nb G (F i) w = 3
  · obtain ⟨w, hw, h3'⟩ := h
    have hw' := mem_filter.1 hw
    have h1 := hF.sum_le_of_nb_eq_three hw'.1 h3'
    have h2 : ∑ v ∈ Low G F, nb G (F i) v ≤ ∑ v ∈ Rest F, nb G (F i) v :=
      sum_le_sum_of_subset low_subset
    have := hw'.2
    omega
  · push Not at h
    calc ∑ v ∈ Low G F, nb G (F i) v ≤ ∑ _v ∈ Low G F, 2 := sum_le_sum fun v hv => by
          have := hF.nb_le_three i (low_subset hv)
          have := h v hv
          omega
      _ = 2 * #(Low G F) := by rw [sum_const, smul_eq_mul, mul_comm]

/-- There are at most two low vertices. -/
lemma card_low_le_two (hδ : ∀ v, 2 * (m + 1) ≤ nb G univ v) : #(Low G F) ≤ 2 := by
  by_contra h
  push Not at h
  have h1 : ∑ i, ∑ v ∈ Low G F, nb G (F i) v ≤ ∑ _i : Fin m, 2 * #(Low G F) :=
    sum_le_sum fun i _ => hF.sum_low_le i h
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_comm] at h1
  have h2 : ∑ _v ∈ Low G F, (2 * m + 1) ≤ ∑ v ∈ Low G F, ∑ i, nb G (F i) v :=
    sum_le_sum fun v hv => by
      have e := nb_univ_eq hF.valid v
      have := hδ v
      have := (mem_filter.1 hv).2
      omega
  rw [sum_const, smul_eq_mul] at h2
  nlinarith

end Optimal

end CorradiHajnal
