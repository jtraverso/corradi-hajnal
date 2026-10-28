/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Counting

/-!
# Families of disjoint cyclic sets

A family `F : Fin m → Finset V` is *valid* if its members are cyclic and pairwise disjoint.
`Rest F` is the set of vertices not covered by the family and `total F` the number of covered
vertices. An *optimal* family (among valid families leaving at least three vertices uncovered)
first minimises `total F` and then maximises the number of edges spanned by `Rest F`.

We collect the exchange lemmas used in the proof of the Corrádi–Hajnal theorem.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {m : ℕ}

variable (G) in
/-- A family of pairwise disjoint cyclic sets. -/
def Valid (F : Fin m → Finset V) : Prop :=
  (∀ i, Cyc G (F i)) ∧ ∀ i j, i ≠ j → Disjoint (F i) (F j)

variable (G) in
/-- `G` has `k` pairwise disjoint cyclic sets. -/
def HasK (k : ℕ) : Prop := ∃ F : Fin k → Finset V, Valid G F

/-- The vertices not covered by the family. -/
def Rest (F : Fin m → Finset V) : Finset V := univ.filter fun v => ∀ i, v ∉ F i

/-- The number of covered vertices (counted with multiplicity). -/
def total (F : Fin m → Finset V) : ℕ := ∑ i, #(F i)

lemma mem_rest {F : Fin m → Finset V} {v : V} : v ∈ Rest F ↔ ∀ i, v ∉ F i := by
  simp [Rest]

lemma not_mem_rest_of_mem {F : Fin m → Finset V} {v : V} {i : Fin m} (h : v ∈ F i) :
    v ∉ Rest F := fun h' => mem_rest.1 h' i h

lemma disjoint_rest (F : Fin m → Finset V) (i : Fin m) : Disjoint (F i) (Rest F) :=
  disjoint_left.2 fun _ h => not_mem_rest_of_mem h

omit [Fintype V] [DecidableEq V] in
lemma Valid.disj {F : Fin m → Finset V} (hF : Valid G F) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (F i) (F j) := hF.2 i j hij

omit [Fintype V] [DecidableEq V] in
lemma Valid.not_mem {F : Fin m → Finset V} (hF : Valid G F) {i j : Fin m} (hij : i ≠ j) {v : V}
    (hv : v ∈ F i) : v ∉ F j := disjoint_left.1 (hF.disj hij) hv

lemma univ_eq_rest_union (F : Fin m → Finset V) :
    (univ : Finset V) = Rest F ∪ univ.biUnion F := by
  ext v
  simp only [mem_univ, mem_union, mem_rest, mem_biUnion, true_and, true_iff]
  by_cases h : ∃ i, v ∈ F i
  · exact Or.inr h
  · push Not at h; exact Or.inl h

lemma disjoint_rest_biUnion (F : Fin m → Finset V) : Disjoint (Rest F) (univ.biUnion F) := by
  rw [disjoint_left]
  intro v hv hv'
  obtain ⟨i, -, hi⟩ := mem_biUnion.1 hv'
  exact mem_rest.1 hv i hi

lemma card_rest_add_total {F : Fin m → Finset V} (hF : Valid G F) :
    #(Rest F) + total F = Fintype.card V := by
  rw [← card_univ, univ_eq_rest_union F, card_union_of_disjoint (disjoint_rest_biUnion F),
    card_biUnion]
  · rfl
  · intro i _ j _ hij; exact hF.disj hij

/-- The degree of a vertex splits along the family and the rest. -/
lemma nb_univ_eq {F : Fin m → Finset V} (hF : Valid G F) (v : V) :
    nb G univ v = nb G (Rest F) v + ∑ i, nb G (F i) v := by
  rw [univ_eq_rest_union F, nb_union (disjoint_rest_biUnion F)]
  congr 1
  unfold nb
  rw [filter_biUnion, card_biUnion]
  intro i _ j _ hij
  exact disjoint_filter_filter (hF.disj hij)

/-! ### Modifying families -/

omit [Fintype V] [DecidableEq V] in
lemma total_update (F : Fin m → Finset V) (i : Fin m) (S : Finset V) :
    total (Function.update F i S) + #(F i) = total F + #S := by
  unfold total
  rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ _ (mem_univ i)]
  simp only [Function.update_self]
  rw [sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]]
  ring

omit [Fintype V] [DecidableEq V] in
lemma valid_update {F : Fin m → Finset V} (hF : Valid G F) {i : Fin m} {S : Finset V}
    (hS : Cyc G S) (hd : ∀ j, j ≠ i → Disjoint S (F j)) : Valid G (Function.update F i S) := by
  refine ⟨fun j => ?_, fun j l hjl => ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using hS
    · rw [Function.update_of_ne hj]; exact hF.1 j
  · by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_of_ne (Ne.symm hjl)]
      exact hd l (Ne.symm hjl)
    · by_cases hl : l = i
      · subst hl
        rw [Function.update_self, Function.update_of_ne hj]
        exact (hd j hj).symm
      · rw [Function.update_of_ne hj, Function.update_of_ne hl]
        exact hF.disj hjl

omit [Fintype V] [DecidableEq V] in
lemma update₂_apply (F : Fin m → Finset V) {i j : Fin m} (hij : i ≠ j) (S T : Finset V)
    (l : Fin m) : Function.update (Function.update F j T) i S l =
      if l = i then S else if l = j then T else F l := by
  by_cases hli : l = i
  · subst hli; simp
  · rw [Function.update_of_ne hli, ite_eq_right hli]
    by_cases hlj : l = j
    · subst hlj; simp
    · rw [Function.update_of_ne hlj, ite_eq_right hlj]

omit [Fintype V] [DecidableEq V] in
lemma valid_update₂ {F : Fin m → Finset V} (hF : Valid G F) {i j : Fin m} (hij : i ≠ j)
    {S T : Finset V} (hS : Cyc G S) (hT : Cyc G T) (hST : Disjoint S T)
    (hSd : ∀ l, l ≠ i → l ≠ j → Disjoint S (F l)) (hTd : ∀ l, l ≠ i → l ≠ j → Disjoint T (F l)) :
    Valid G (Function.update (Function.update F j T) i S) := by
  refine ⟨fun l => ?_, fun l l' hll' => ?_⟩
  · rw [update₂_apply F hij]
    split_ifs
    · exact hS
    · exact hT
    · exact hF.1 l
  · rw [update₂_apply F hij, update₂_apply F hij]
    by_cases h1 : l = i
    · subst h1
      rw [ite_eq_left rfl]
      by_cases h3 : l' = l
      · exact absurd h3.symm hll'
      rw [ite_eq_right h3]
      by_cases h4 : l' = j
      · rw [ite_eq_left h4]; exact hST
      · rw [ite_eq_right h4]; exact hSd _ h3 h4
    · rw [ite_eq_right h1]
      by_cases h2 : l = j
      · subst h2
        rw [ite_eq_left rfl]
        by_cases h3 : l' = i
        · rw [ite_eq_left h3]; exact hST.symm
        · rw [ite_eq_right h3]
          by_cases h4 : l' = l
          · exact absurd h4.symm hll'
          rw [ite_eq_right h4]; exact hTd _ h3 h4
      · rw [ite_eq_right h2]
        by_cases h3 : l' = i
        · rw [ite_eq_left h3]; exact (hSd _ h1 h2).symm
        · rw [ite_eq_right h3]
          by_cases h4 : l' = j
          · rw [ite_eq_left h4]; exact (hTd _ h1 h2).symm
          · rw [ite_eq_right h4]; exact hF.disj hll'

lemma rest_update {F : Fin m → Finset V} (hF : Valid G F) (i : Fin m) (S : Finset V) :
    Rest (Function.update F i S) = (Rest F ∪ F i) \ S := by
  ext y
  simp only [mem_rest, mem_sdiff, mem_union]
  constructor
  · intro h
    refine ⟨?_, by simpa using h i⟩
    by_cases hy : y ∈ F i
    · exact Or.inr hy
    · left
      intro j
      by_cases hj : j = i
      · subst hj; exact hy
      · have := h j; rwa [Function.update_of_ne hj] at this
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · rw [Function.update_of_ne hj]
      rcases h1 with h1 | h1
      · exact h1 j
      · exact hF.not_mem (Ne.symm hj) h1

omit [Fintype V] [DecidableEq V] in
/-- Adding one more disjoint cyclic set. -/
lemma hasK_of_extend {F : Fin m → Finset V} (hF : Valid G F) {S : Finset V} (hS : Cyc G S)
    (hd : ∀ j, Disjoint S (F j)) : HasK G (m + 1) := by
  refine ⟨Fin.cons S F, fun l => ?_, fun l l' hll' => ?_⟩
  · cases l using Fin.cases with
    | zero => simpa using hS
    | succ l => simpa using hF.1 l
  · cases l using Fin.cases with
    | zero =>
      cases l' using Fin.cases with
      | zero => exact absurd rfl hll'
      | succ l' => simpa using hd l'
    | succ l =>
      cases l' using Fin.cases with
      | zero => simpa using (hd l).symm
      | succ l' =>
        simp only [Fin.cons_succ]
        exact hF.disj (fun h => hll' (by rw [h]))

lemma disjoint_of_subset_union {F : Fin m → Finset V} (hF : Valid G F) {i j : Fin m}
    (hj : j ≠ i) {A : Finset V} (hA : A ⊆ F i ∪ Rest F) : Disjoint A (F j) := by
  rw [disjoint_left]
  intro v hv hvj
  rcases mem_union.1 (hA hv) with h | h
  · exact hF.not_mem (Ne.symm hj) h hvj
  · exact mem_rest.1 h j hvj

/-- Two disjoint cyclic sets inside `F i ∪ Rest F` give one more cyclic set. -/
lemma hasK_of_two {F : Fin m → Finset V} (hF : Valid G F) (i : Fin m) {A B : Finset V}
    (hA : Cyc G A) (hB : Cyc G B) (hAB : Disjoint A B) (hAs : A ⊆ F i ∪ Rest F)
    (hBs : B ⊆ F i ∪ Rest F) : HasK G (m + 1) := by
  have hF' := valid_update hF hA fun j hj => disjoint_of_subset_union hF hj hAs
  refine hasK_of_extend hF' hB fun j => ?_
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact hAB.symm
  · rw [Function.update_of_ne hj]; exact disjoint_of_subset_union hF hj hBs

lemma disjoint_of_subset_union₂ {F : Fin m → Finset V} (hF : Valid G F) {i j l : Fin m}
    (hli : l ≠ i) (hlj : l ≠ j) {A : Finset V} (hA : A ⊆ F i ∪ F j ∪ Rest F) :
    Disjoint A (F l) := by
  rw [disjoint_left]
  intro v hv hvl
  rcases mem_union.1 (hA hv) with h | h
  · rcases mem_union.1 h with h | h
    · exact hF.not_mem (Ne.symm hli) h hvl
    · exact hF.not_mem (Ne.symm hlj) h hvl
  · exact mem_rest.1 h l hvl

/-- Three disjoint cyclic sets inside `F i ∪ F j ∪ Rest F` give one more cyclic set. -/
lemma hasK_of_three {F : Fin m → Finset V} (hF : Valid G F) {i j : Fin m} (hij : i ≠ j)
    {A B D : Finset V} (hA : Cyc G A) (hB : Cyc G B) (hD : Cyc G D) (hAB : Disjoint A B)
    (hAD : Disjoint A D) (hBD : Disjoint B D) (hAs : A ⊆ F i ∪ F j ∪ Rest F)
    (hBs : B ⊆ F i ∪ F j ∪ Rest F) (hDs : D ⊆ F i ∪ F j ∪ Rest F) : HasK G (m + 1) := by
  have hF' := valid_update₂ hF hij hA hB hAB
    (fun l hli hlj => disjoint_of_subset_union₂ hF hli hlj hAs)
    (fun l hli hlj => disjoint_of_subset_union₂ hF hli hlj hBs)
  refine hasK_of_extend hF' hD fun l => ?_
  rw [update₂_apply F hij]
  split_ifs with h1 h2
  · exact hAD.symm
  · exact hBD.symm
  · exact disjoint_of_subset_union₂ hF h1 h2 hDs

end CorradiHajnal
