/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Sharpness

/-!
# Sanity checks for `HasDisjointCycles`

Small cases, checked with explicit cycles:

* every graph has `0` disjoint cycles;
* a triangle has one cycle, but not two disjoint cycles;
* `K₆` has two disjoint cycles (two explicit triangles), while `K₅` does not.
-/

@[expose] public section

namespace CorradiHajnal

open SimpleGraph

/-- The closed walk `a → b → c → a` around a triangle. -/
def triWalk {V : Type*} {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : G.Walk a a :=
  .cons hab (.cons hbc (.cons hca .nil))

lemma triWalk_support {V : Type*} {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) : (triWalk hab hbc hca).support = [a, b, c, a] := rfl

lemma triWalk_isCycle {V : Type*} {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hca : G.Adj c a) : (triWalk hab hbc hca).IsCycle := by
  have h1 := hab.ne
  have h2 := hbc.ne
  have h3 := hca.ne
  rw [triWalk, Walk.cons_isCycle_iff]
  simp [Walk.isPath_def, h1, h2, h3, h1.symm, h3.symm]

/-- Every graph has `0` disjoint cycles. -/
lemma hasDisjointCycles_zero {V : Type*} (G : SimpleGraph V) : HasDisjointCycles G 0 :=
  ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- A triangle has one cycle. -/
lemma triangle_hasDisjointCycles_one : HasDisjointCycles (⊤ : SimpleGraph (Fin 3)) 1 := by
  have h01 : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by decide
  have h12 : (⊤ : SimpleGraph (Fin 3)).Adj 1 2 := by decide
  have h20 : (⊤ : SimpleGraph (Fin 3)).Adj 2 0 := by decide
  exact ⟨fun _ => 0, fun _ => triWalk h01 h12 h20, fun _ => triWalk_isCycle _ _ _,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- A triangle does not have two disjoint cycles. -/
lemma triangle_not_hasDisjointCycles_two : ¬ HasDisjointCycles (⊤ : SimpleGraph (Fin 3)) 2 :=
  fun h => by simpa using three_mul_le_card_of_hasDisjointCycles h

/-- `K₆` has two disjoint cycles: the triangles `0 1 2` and `3 4 5`. -/
lemma K6_hasDisjointCycles_two : HasDisjointCycles (⊤ : SimpleGraph (Fin 6)) 2 := by
  let base : Fin 2 → Fin 6 := ![0, 3]
  have hab : ∀ i, (⊤ : SimpleGraph (Fin 6)).Adj (base i) (base i + 1) := by decide
  have hbc : ∀ i, (⊤ : SimpleGraph (Fin 6)).Adj (base i + 1) (base i + 2) := by decide
  have hca : ∀ i, (⊤ : SimpleGraph (Fin 6)).Adj (base i + 2) (base i) := by decide
  refine ⟨base, fun i => triWalk (hab i) (hbc i) (hca i), fun i => triWalk_isCycle _ _ _, ?_⟩
  simp only [triWalk_support]
  decide

/-- `K₅` does not have two disjoint cycles. -/
lemma K5_not_hasDisjointCycles_two : ¬ HasDisjointCycles (⊤ : SimpleGraph (Fin 5)) 2 :=
  fun h => by simpa using three_mul_le_card_of_hasDisjointCycles h

/-- The main theorem applied to `K₆` with `k = 2` (`6 ≥ 3 · 2` vertices, minimum degree
`5 ≥ 2 · 2`). -/
example : HasDisjointCycles (⊤ : SimpleGraph (Fin 6)) 2 :=
  corradi_hajnal ⊤ 2 (by simp) (by rw [minDegree_top]; simp)

end CorradiHajnal
