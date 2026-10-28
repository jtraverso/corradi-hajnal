/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Low

/-!
# Exchange witnesses

Configurations of triangles which, inside the union of one or two members of an optimal family and
the uncovered vertices, give one more disjoint cyclic set.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [DecidableEq V]

lemma disjoint_triple {a b c a' b' c' : V} (h1 : a ≠ a') (h2 : a ≠ b') (h3 : a ≠ c')
    (h4 : b ≠ a') (h5 : b ≠ b') (h6 : b ≠ c') (h7 : c ≠ a') (h8 : c ≠ b') (h9 : c ≠ c') :
    Disjoint ({a, b, c} : Finset V) {a', b', c'} := by
  simp [h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm, h9.symm]

lemma triple_subset {a b c : V} {X : Finset V} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) :
    ({a, b, c} : Finset V) ⊆ X := by
  simp [insert_subset_iff, *]

/-- The two other vertices of a triangle. -/
lemma exists_pair_of_card_three {T : Finset V} (h3 : #T = 3) {x : V} (hx : x ∈ T) :
    ∃ s s', s ∈ T ∧ s' ∈ T ∧ s ≠ s' ∧ x ≠ s ∧ x ≠ s' ∧ T = {x, s, s'} := by
  obtain ⟨s, s', hss', he⟩ := card_eq_two.1 (by rw [card_erase_of_mem hx, h3] : #(T.erase x) = 2)
  have hs : s ∈ T.erase x := he ▸ mem_insert_self s {s'}
  have hs' : s' ∈ T.erase x := he ▸ mem_insert_of_mem (mem_singleton_self s')
  refine ⟨s, s', mem_of_mem_erase hs, mem_of_mem_erase hs', hss', (ne_of_mem_erase hs).symm,
    (ne_of_mem_erase hs').symm, ?_⟩
  rw [← insert_erase hx, he]

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ} {F : Fin m → Finset V}


lemma ne_of_rest {i : Fin m} {v t : V} (hv : v ∈ Rest F) (ht : t ∈ F i) : v ≠ t := by
  rintro rfl
  exact not_mem_rest_of_mem ht hv

omit [Fintype V] [DecidableEq V] in
lemma Valid.ne_of_mem (hF : Valid G F) {i j : Fin m} (hij : i ≠ j) {x y : V} (hx : x ∈ F i)
    (hy : y ∈ F j) : x ≠ y := by
  rintro rfl
  exact hF.not_mem hij hx hy

/-- Proves `x ≠ y` from membership of `x` and `y` in the rest or in members of a family. -/
syntax "ne_tac" term:max term:max : tactic

macro_rules
  | `(tactic| ne_tac $hv $hij) => `(tactic| first
      | assumption
      | exact Ne.symm (by assumption)
      | (apply ne_of_rest <;> assumption)
      | (apply Ne.symm; apply ne_of_rest <;> assumption)
      | (apply Valid.ne_of_mem $hv $hij <;> assumption)
      | (apply Valid.ne_of_mem $hv (Ne.symm $hij) <;> assumption))

namespace Optimal

variable (hF : Optimal G F)
include hF

/-- Two disjoint triangles in `F i ∪ Rest F`: `{u, w, x}` and `{u', s, s'}`, where `F i` is a
triangle `{x, s, s'}` and `u, w, u'` are uncovered. -/
lemma hasK_fan {i : Fin m} (hT : #(F i) = 3) {u w u' x s s' : V} (hu : u ∈ Rest F)
    (hw : w ∈ Rest F) (hu' : u' ∈ Rest F) (hx : x ∈ F i) (hs : s ∈ F i) (hs' : s' ∈ F i)
    (hss' : s ≠ s') (hxs : x ≠ s) (hxs' : x ≠ s') (huu' : u ≠ u') (hwu' : w ≠ u')
    (huw : G.Adj u w) (hux : G.Adj u x) (hwx : G.Adj w x) (hu's : G.Adj u' s)
    (hu's' : G.Adj u' s') : HasK G (m + 1) := by
  have hv := hF.valid
  have hii : i ≠ i → False := fun h => h rfl
  have huw' := huw.ne
  refine hasK_of_two hv i (cyc_triangle huw hwx hux)
    (cyc_triangle hu's (hF.adj_of_card_three hT hs hs' hss') hu's') ?_
    (triple_subset (by simp [hu]) (by simp [hw]) (by simp [hx]))
    (triple_subset (by simp [hu']) (by simp [hs]) (by simp [hs']))
  apply disjoint_triple <;>
  first
    | assumption
    | exact Ne.symm (by assumption)
    | (apply ne_of_rest <;> assumption)
    | (apply Ne.symm; apply ne_of_rest <;> assumption)

/-- Three disjoint triangles `{a, c, t}`, `{b, c₁, c₂}`, `{u, s, s'}` in `F i ∪ F j ∪ Rest F`,
where `F i = {c, c₁, c₂}`, `F j = {t, s, s'}` and `a, b, u` are uncovered. -/
lemma hasK_cross {i j : Fin m} (hij : i ≠ j) (hC : #(F i) = 3) (hD : #(F j) = 3)
    {a b u c c₁ c₂ t s s' : V} (ha : a ∈ Rest F) (hb : b ∈ Rest F) (hu : u ∈ Rest F)
    (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hc : c ∈ F i) (hc₁ : c₁ ∈ F i) (hc₂ : c₂ ∈ F i) (hcc₁ : c ≠ c₁) (hcc₂ : c ≠ c₂)
    (hc₁₂ : c₁ ≠ c₂) (ht : t ∈ F j) (hs : s ∈ F j) (hs' : s' ∈ F j) (hts : t ≠ s)
    (hts' : t ≠ s') (hss' : s ≠ s')
    (hac : G.Adj a c) (hct : G.Adj c t) (hat : G.Adj a t) (hbc₁ : G.Adj b c₁)
    (hbc₂ : G.Adj b c₂) (hus : G.Adj u s) (hus' : G.Adj u s') : HasK G (m + 1) := by
  have hv := hF.valid
  refine hasK_of_three hv hij (cyc_triangle hac hct hat)
    (cyc_triangle hbc₁ (hF.adj_of_card_three hC hc₁ hc₂ hc₁₂) hbc₂)
    (cyc_triangle hus (hF.adj_of_card_three hD hs hs' hss') hus') ?_ ?_ ?_
    (triple_subset (by simp [ha]) (by simp [hc]) (by simp [ht]))
    (triple_subset (by simp [hb]) (by simp [hc₁]) (by simp [hc₂]))
    (triple_subset (by simp [hu]) (by simp [hs]) (by simp [hs'])) <;>
  apply disjoint_triple <;> ne_tac hv hij

/-- Three disjoint triangles `{c, s, s'}`, `{a, c₁, c₂}`, `{u, b, t}` in `F i ∪ F j ∪ Rest F`,
where `F i = {c, c₁, c₂}`, `F j = {t, s, s'}` and `a, b, u` are uncovered. -/
lemma hasK_cross' {i j : Fin m} (hij : i ≠ j) (hC : #(F i) = 3) (hD : #(F j) = 3)
    {a b u c c₁ c₂ t s s' : V} (ha : a ∈ Rest F) (hb : b ∈ Rest F) (hu : u ∈ Rest F)
    (hab : a ≠ b) (hau : a ≠ u)
    (hc : c ∈ F i) (hc₁ : c₁ ∈ F i) (hc₂ : c₂ ∈ F i) (hcc₁ : c ≠ c₁) (hcc₂ : c ≠ c₂)
    (hc₁₂ : c₁ ≠ c₂) (ht : t ∈ F j) (hs : s ∈ F j) (hs' : s' ∈ F j) (hts : t ≠ s)
    (hts' : t ≠ s') (hss' : s ≠ s')
    (hcs : G.Adj c s) (hcs' : G.Adj c s') (hac₁ : G.Adj a c₁) (hac₂ : G.Adj a c₂)
    (hub : G.Adj u b) (hbt : G.Adj b t) (hut : G.Adj u t) : HasK G (m + 1) := by
  have hv := hF.valid
  refine hasK_of_three hv hij (cyc_triangle hcs (hF.adj_of_card_three hD hs hs' hss') hcs')
    (cyc_triangle hac₁ (hF.adj_of_card_three hC hc₁ hc₂ hc₁₂) hac₂)
    (cyc_triangle hub hbt hut) ?_ ?_ ?_
    (triple_subset (by simp [hc]) (by simp [hs]) (by simp [hs']))
    (triple_subset (by simp [ha]) (by simp [hc₁]) (by simp [hc₂]))
    (triple_subset (by simp [hu]) (by simp [hb]) (by simp [ht])) <;>
  apply disjoint_triple <;> ne_tac hv hij

end Optimal

end CorradiHajnal
