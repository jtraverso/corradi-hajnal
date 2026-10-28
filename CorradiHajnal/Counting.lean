/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Counting neighbours inside vertex sets, and cyclic vertex sets

We work with a purely combinatorial notion of "a vertex set containing a cycle":
a finset `S` is *cyclic* (`Cyc G S`) if some nonempty `U ⊆ S` spans at least `#U` edges.
This is equivalent to `G[S]` containing a cycle (see `CorradiHajnal.CycleOfCyc`), but it is
much more convenient for the exchange arguments of the Corrádi–Hajnal proof.

* `nb G S v` : number of neighbours of `v` in `S`;
* `E2 G S`   : twice the number of edges spanned by `S`;
* `Cyc G S`  : `S` contains a cycle;
* `MinCyc G S` : `S` is an inclusion-minimal cyclic set (the vertex set of an induced cycle).
-/

@[expose] public section

namespace CorradiHajnal

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of neighbours of `v` in `S`. -/
def nb (S : Finset V) (v : V) : ℕ := #(S.filter (G.Adj v))

/-- Twice the number of edges of `G` spanned by `S`. -/
def E2 (S : Finset V) : ℕ := ∑ v ∈ S, nb G S v

/-- `S` contains a cycle: some nonempty `U ⊆ S` spans at least `#U` edges. -/
def Cyc (S : Finset V) : Prop := ∃ U ⊆ S, U.Nonempty ∧ 2 * #U ≤ E2 G U

/-- `S` is an inclusion-minimal cyclic set. -/
def MinCyc (S : Finset V) : Prop := Cyc G S ∧ ∀ T ⊆ S, T ≠ S → ¬ Cyc G T

variable {G}

omit [DecidableEq V] in
lemma nb_le_card (S : Finset V) (v : V) : nb G S v ≤ #S := card_filter_le _ _

omit [DecidableEq V] in
lemma nb_mono {S T : Finset V} (h : S ⊆ T) (v : V) : nb G S v ≤ nb G T v :=
  card_le_card (filter_subset_filter _ h)

lemma nb_erase_self (S : Finset V) (v : V) : nb G (S.erase v) v = nb G S v := by
  unfold nb
  congr 1
  ext w
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨⟨fun e => G.irrefl (e ▸ h'), h⟩, h'⟩

omit [DecidableEq V] in
lemma nb_le_card_sub_one {S : Finset V} {v : V} (hv : v ∈ S) : nb G S v ≤ #S - 1 := by
  classical
  rw [← nb_erase_self, ← card_erase_of_mem hv]
  exact nb_le_card _ _

lemma nb_insert_of_not_mem {S : Finset V} {a : V} (ha : a ∉ S) (v : V) :
    nb G (insert a S) v = nb G S v + if G.Adj v a then 1 else 0 := by
  unfold nb
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem]
    simp [mem_filter, ha]
  · simp

lemma nb_eq_erase_add {S : Finset V} {a : V} (ha : a ∈ S) (v : V) :
    nb G S v = nb G (S.erase a) v + if G.Adj v a then 1 else 0 := by
  conv_lhs => rw [← insert_erase ha]
  exact nb_insert_of_not_mem (notMem_erase a S) v

lemma nb_union {S T : Finset V} (h : Disjoint S T) (v : V) :
    nb G (S ∪ T) v = nb G S v + nb G T v := by
  unfold nb
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

omit [DecidableEq V] in
lemma nb_eq_card_of_forall {S : Finset V} {v : V} (h : ∀ w ∈ S, G.Adj v w) : nb G S v = #S := by
  unfold nb
  rw [filter_true_of_mem h]

omit [DecidableEq V] in
lemma nb_eq_zero_iff {S : Finset V} {v : V} : nb G S v = 0 ↔ ∀ w ∈ S, ¬ G.Adj v w := by
  unfold nb
  rw [card_eq_zero, filter_eq_empty_iff]

omit [DecidableEq V] in
lemma nb_eq_card_iff {S : Finset V} {v : V} : nb G S v = #S ↔ ∀ w ∈ S, G.Adj v w := by
  unfold nb
  constructor
  · intro h
    have := (card_filter_eq_iff).1 h
    exact this
  · intro h; rw [filter_true_of_mem h]

omit [DecidableEq V] in
lemma sum_nb_comm (A B : Finset V) : ∑ v ∈ A, nb G B v = ∑ w ∈ B, nb G A w := by
  unfold nb
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => sum_congr rfl fun v _ => ?_
  simp only [G.adj_comm]

lemma E2_insert {S : Finset V} {a : V} (ha : a ∉ S) :
    E2 G (insert a S) = E2 G S + 2 * nb G S a := by
  unfold E2
  rw [sum_insert ha]
  have h1 : nb G (insert a S) a = nb G S a := by
    rw [nb_insert_of_not_mem ha]; simp
  have h2 : ∑ v ∈ S, nb G (insert a S) v = ∑ v ∈ S, nb G S v + nb G S a := by
    simp_rw [nb_insert_of_not_mem ha]
    rw [sum_add_distrib]
    congr 1
    unfold nb
    rw [card_filter]
    refine sum_congr rfl fun v _ => ?_
    simp only [G.adj_comm]
  rw [h1, h2]; ring

lemma E2_eq_erase_add {S : Finset V} {a : V} (ha : a ∈ S) :
    E2 G S = E2 G (S.erase a) + 2 * nb G S a := by
  conv_lhs => rw [← insert_erase ha]
  rw [E2_insert (notMem_erase a S), nb_erase_self]

omit [DecidableEq V] in
lemma even_E2 (S : Finset V) : 2 ∣ E2 G S := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [E2]
  | insert a S ha ih =>
    rw [E2_insert ha]
    exact dvd_add ih (dvd_mul_right _ _)

omit [DecidableEq V] in
lemma E2_le (S : Finset V) : E2 G S ≤ #S * (#S - 1) := by
  unfold E2
  calc ∑ v ∈ S, nb G S v ≤ ∑ _v ∈ S, (#S - 1) :=
        sum_le_sum fun v hv => nb_le_card_sub_one hv
    _ = #S * (#S - 1) := by simp

omit [DecidableEq V] in
lemma E2_mono {S T : Finset V} (h : S ⊆ T) : E2 G S ≤ E2 G T := by
  unfold E2
  calc ∑ v ∈ S, nb G S v ≤ ∑ v ∈ S, nb G T v := sum_le_sum fun v _ => nb_mono h v
    _ ≤ ∑ v ∈ T, nb G T v := sum_le_sum_of_subset h

/-! ### Cyclic sets -/

omit [DecidableEq V] in
lemma Cyc.mono {S T : Finset V} (h : Cyc G S) (hST : S ⊆ T) : Cyc G T := by
  obtain ⟨U, hU, hne, hc⟩ := h
  exact ⟨U, hU.trans hST, hne, hc⟩

omit [DecidableEq V] in
lemma cyc_self {U : Finset V} (hne : U.Nonempty) (h : 2 * #U ≤ E2 G U) : Cyc G U :=
  ⟨U, subset_rfl, hne, h⟩

omit [DecidableEq V] in
lemma Cyc.three_le_card {S : Finset V} (h : Cyc G S) : 3 ≤ #S := by
  obtain ⟨U, hU, hne, hc⟩ := h
  have h1 := E2_le (G := G) U
  have h2 : 0 < #U := hne.card_pos
  have h3 : 3 ≤ #U := by
    by_contra h4
    push Not at h4
    interval_cases hh : #U <;> omega
  exact h3.trans (card_le_card hU)

lemma cyc_triangle {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    Cyc G {a, b, c} := by
  refine cyc_self (by simp) ?_
  have hab' := hab.ne
  have hbc' := hbc.ne
  have hac' := hac.ne
  have hcard : #({a, b, c} : Finset V) = 3 := by
    rw [card_insert_of_notMem (by simp [hab', hac']), card_pair hbc']
  rw [hcard]
  unfold E2
  rw [sum_insert (by simp [hab', hac']), sum_pair hbc']
  have ha : nb G {a, b, c} a = 2 := by
    rw [nb_eq_erase_add (show a ∈ ({a, b, c} : Finset V) by simp)]
    have : ({a, b, c} : Finset V).erase a = {b, c} := by
      rw [erase_insert (by simp [hab', hac'])]
    rw [this, nb_eq_card_of_forall (by simp [hab, hac]), card_pair hbc']
    simp
  have hb : nb G {a, b, c} b = 2 := by
    rw [nb_insert_of_not_mem (by simp [hab', hac']),
      nb_eq_erase_add (show b ∈ ({b, c} : Finset V) by simp)]
    rw [erase_insert (by simp [hbc'])]
    rw [nb_eq_card_of_forall (by simp [hbc])]
    simp [hab.symm]
  have hc : nb G {a, b, c} c = 2 := by
    rw [nb_insert_of_not_mem (by simp [hab', hac']),
      nb_eq_erase_add (show c ∈ ({b, c} : Finset V) by simp)]
    have : ({b, c} : Finset V).erase c = {b} := by
      rw [erase_insert_of_ne hbc', erase_singleton, insert_empty]
    rw [this, nb_eq_card_of_forall (by simp [hbc.symm])]
    simp [hac.symm]
  omega

omit [DecidableEq V] in
/-- An acyclic nonempty set spans fewer than `#S` edges. -/
lemma E2_add_two_le_of_not_cyc {S : Finset V} (h : ¬ Cyc G S) (hne : S.Nonempty) :
    E2 G S + 2 ≤ 2 * #S := by
  have h1 : E2 G S < 2 * #S := by
    by_contra h2
    exact h (cyc_self hne (not_lt.1 h2))
  obtain ⟨c, hc⟩ := even_E2 (G := G) S
  omega

omit [DecidableEq V] in
/-- An acyclic nonempty set has a vertex with at most one neighbour inside. -/
lemma exists_nb_le_one_of_not_cyc {S : Finset V} (h : ¬ Cyc G S) (hne : S.Nonempty) :
    ∃ v ∈ S, nb G S v ≤ 1 := by
  by_contra h2
  push Not at h2
  have h3 := E2_add_two_le_of_not_cyc h hne
  have h4 : 2 * #S ≤ E2 G S := by
    unfold E2
    calc 2 * #S = ∑ _v ∈ S, 2 := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, nb G S v := sum_le_sum fun v hv => h2 v hv
  omega

/-! ### Minimal cyclic sets -/

omit [DecidableEq V] in
lemma exists_minCyc_subset {S : Finset V} (h : Cyc G S) : ∃ T ⊆ S, MinCyc G T := by
  induction hn : #S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hmin : ∀ T ⊆ S, T ≠ S → ¬ Cyc G T
    · exact ⟨S, subset_rfl, h, hmin⟩
    · push Not at hmin
      obtain ⟨T, hTS, hne, hT⟩ := hmin
      have hlt : #T < n := hn ▸ card_lt_card (ssubset_of_subset_of_ne hTS hne)
      obtain ⟨T', hT'T, hT'⟩ := ih _ hlt hT rfl
      exact ⟨T', hT'T.trans hTS, hT'⟩

omit [DecidableEq V] in
lemma MinCyc.two_mul_card_le {S : Finset V} (h : MinCyc G S) : 2 * #S ≤ E2 G S := by
  obtain ⟨⟨U, hU, hne, hc⟩, hmin⟩ := h
  by_cases hUS : U = S
  · exact hUS ▸ hc
  · exact absurd (cyc_self hne hc) (hmin U hU hUS)

omit [DecidableEq V] in
lemma MinCyc.three_le_card {S : Finset V} (h : MinCyc G S) : 3 ≤ #S := h.1.three_le_card

lemma MinCyc.E2_erase_le {S : Finset V} (h : MinCyc G S) {s : V} (hs : s ∈ S) :
    E2 G (S.erase s) + 4 ≤ 2 * #S := by
  have h3 := h.three_le_card
  have hne : (S.erase s).Nonempty := by
    rw [← card_pos, card_erase_of_mem hs]; omega
  have hnc : ¬ Cyc G (S.erase s) := h.2 _ (erase_subset s S) (fun e => by
    have := congrArg (s ∈ ·) e
    simp [hs] at this)
  have := E2_add_two_le_of_not_cyc hnc hne
  rw [card_erase_of_mem hs] at this
  omega

omit [DecidableEq V] in
lemma MinCyc.two_le_nb {S : Finset V} (h : MinCyc G S) {s : V} (hs : s ∈ S) : 2 ≤ nb G S s := by
  classical
  have h1 := h.E2_erase_le hs
  have h2 := h.two_mul_card_le
  have h3 := E2_eq_erase_add (G := G) hs
  omega

omit [DecidableEq V] in
lemma MinCyc.E2_eq {S : Finset V} (h : MinCyc G S) : E2 G S = 2 * #S := by
  classical
  have hne : S.Nonempty := by have := h.three_le_card; rw [← card_pos]; omega
  obtain ⟨s, hs, hmin⟩ := exists_min_image S (nb G S) hne
  have h1 := h.E2_erase_le hs
  have h3 := E2_eq_erase_add (G := G) hs
  have h4 : nb G S s * #S ≤ E2 G S := by
    unfold E2
    calc nb G S s * #S = ∑ _v ∈ S, nb G S s := by simp [mul_comm]
      _ ≤ ∑ v ∈ S, nb G S v := sum_le_sum fun v hv => hmin v hv
  have h5 := h.two_le_nb hs
  have h6 := h.three_le_card
  have h7 := h.two_mul_card_le
  -- (d - 2) (#S - 2) ≤ 0 forces d = 2
  have hd : nb G S s = 2 := by
    by_contra hd
    have hd3 : 3 ≤ nb G S s := by omega
    have : 3 * #S ≤ nb G S s * #S := Nat.mul_le_mul_right _ hd3
    -- E2 S ≤ 2#S - 4 + 2 d and E2 S ≥ d #S
    have key : nb G S s * #S ≤ 2 * #S - 4 + 2 * nb G S s := by omega
    have : (nb G S s - 2) * (#S - 2) ≤ 0 := by
      have e1 : (nb G S s - 2) * (#S - 2) + 2 * #S + 2 * nb G S s
          = nb G S s * #S + 4 := by
        obtain ⟨d, hd'⟩ : ∃ d, nb G S s = d + 2 := ⟨nb G S s - 2, by omega⟩
        obtain ⟨m, hm⟩ : ∃ m, #S = m + 2 := ⟨#S - 2, by omega⟩
        rw [hd', hm]; simp only [Nat.add_sub_cancel]; ring
      omega
    have : 0 < (nb G S s - 2) * (#S - 2) := Nat.mul_pos (by omega) (by omega)
    omega
  omega

omit [DecidableEq V] in
lemma MinCyc.nb_eq_two {S : Finset V} (h : MinCyc G S) {s : V} (hs : s ∈ S) : nb G S s = 2 := by
  have hE := h.E2_eq
  have hsum : ∑ v ∈ S, (nb G S v - 2) = 0 := by
    have : ∑ v ∈ S, (nb G S v - 2) + ∑ _v ∈ S, 2 = ∑ v ∈ S, nb G S v := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun v hv => Nat.sub_add_cancel (h.two_le_nb hv)
    simp only [sum_const, smul_eq_mul] at this
    unfold E2 at hE
    omega
  have := (sum_eq_zero_iff.1 hsum) s hs
  have := h.two_le_nb hs
  omega

omit [DecidableEq V] in
/-- A minimal cyclic set with three vertices is a triangle. -/
lemma MinCyc.adj_of_card_three {S : Finset V} (h : MinCyc G S) (h3 : #S = 3) {a b : V}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : G.Adj a b := by
  classical
  have h2 := h.nb_eq_two ha
  have : nb G S a = #(S.erase a) := by rw [card_erase_of_mem ha, h3, h2]
  rw [← nb_erase_self] at this
  exact (nb_eq_card_iff.1 this) b (mem_erase.2 ⟨hab.symm, hb⟩)

/-- **Shortcut lemma.** If a vertex outside a minimal cyclic set `S` with at least four vertices
has at least three neighbours in `S`, then `S ∪ {v}` contains a strictly smaller cyclic set. -/
lemma MinCyc.exists_smaller {S : Finset V} (h : MinCyc G S) (h4 : 4 ≤ #S) {v : V} (hv : v ∉ S)
    (h3 : 3 ≤ nb G S v) : ∃ T ⊆ insert v S, Cyc G T ∧ #T < #S := by
  -- choose `s` (a non-neighbour of `v` if possible) and a neighbour `p` of `s` in `S`
  have hne : S.Nonempty := by rw [← card_pos]; omega
  obtain ⟨s, hs, hsv⟩ : ∃ s ∈ S, (¬ G.Adj v s) ∨ (∀ w ∈ S, G.Adj v w) := by
    by_cases hall : ∀ w ∈ S, G.Adj v w
    · obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, Or.inr hall⟩
    · push Not at hall
      obtain ⟨s, hs, hns⟩ := hall
      exact ⟨s, hs, Or.inl hns⟩
  have hs2 := h.nb_eq_two hs
  obtain ⟨p, hp⟩ : (S.filter (G.Adj s)).Nonempty := by
    rw [← card_pos]; unfold nb at hs2; omega
  rw [mem_filter] at hp
  obtain ⟨hpS, hsp⟩ := hp
  have hps : p ≠ s := hsp.ne'
  have hpS' : p ∈ S.erase s := mem_erase.2 ⟨hps, hpS⟩
  set W := (S.erase s).erase p with hW
  have hvW : v ∉ W := fun hh => hv (mem_of_mem_erase (mem_of_mem_erase hh))
  refine ⟨insert v W, ?_, cyc_self (by simp) ?_, ?_⟩
  · intro x hx
    rw [mem_insert] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (mem_of_mem_erase (mem_of_mem_erase hx))
  · -- edge count
    have hcardW : #W = #S - 2 := by
      rw [hW, card_erase_of_mem hpS', card_erase_of_mem hs]; omega
    rw [card_insert_of_notMem hvW, E2_insert hvW, hcardW]
    have hE := h.E2_eq
    have e1 := E2_eq_erase_add (G := G) hs
    have e2 := E2_eq_erase_add (G := G) hpS'
    have hp2 := h.nb_eq_two hpS
    have hnbp : nb G (S.erase s) p = 1 := by
      have := nb_eq_erase_add (G := G) hs p
      rw [ite_eq_left hsp.symm] at this
      omega
    have hnbv : 2 ≤ nb G W v := by
      have f1 := nb_eq_erase_add (G := G) hs v
      have f2 := nb_eq_erase_add (G := G) hpS' v
      rw [← hW] at f2
      rcases hsv with hsv | hall
      · rw [ite_eq_right hsv] at f1
        split_ifs at f2 <;> omega
      · have : nb G S v = #S := nb_eq_card_of_forall hall
        split_ifs at f1 f2 <;> omega
    rw [← hW] at e2
    omega
  · rw [card_insert_of_notMem hvW, hW, card_erase_of_mem hpS', card_erase_of_mem hs]
    omega

/-! ### Peeling: from many edges to minimum degree two -/

omit [DecidableEq V] in
lemma exists_two_le_nb {U : Finset V} (hne : U.Nonempty) (h : 2 * #U ≤ E2 G U) :
    ∃ W ⊆ U, W.Nonempty ∧ ∀ w ∈ W, 2 ≤ nb G W w := by
  classical
  induction hn : #U using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    by_cases hall : ∀ w ∈ U, 2 ≤ nb G U w
    · exact ⟨U, subset_rfl, hne, hall⟩
    · push Not at hall
      obtain ⟨w, hw, hlow⟩ := hall
      have e := E2_eq_erase_add (G := G) hw
      have hcard := card_erase_of_mem hw
      have hne' : (U.erase w).Nonempty := by
        rw [← card_pos, hcard]
        by_contra h0
        have h1 : #U = 1 := by have := hne.card_pos; omega
        have := E2_le (G := G) U
        rw [h1] at this h
        omega
      have hlt : #(U.erase w) < n := by rw [hcard]; have := hne.card_pos; omega
      obtain ⟨W, hW, hWne, hW2⟩ := ih _ hlt hne' (by rw [hcard]; omega) rfl
      exact ⟨W, hW.trans (erase_subset _ _), hWne, hW2⟩

end CorradiHajnal
