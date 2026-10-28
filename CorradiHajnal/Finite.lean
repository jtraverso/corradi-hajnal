/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import CorradiHajnal.Counting

/-!
# A finite check

A Boolean case analysis used in the case of three uncovered vertices: for a triangle `{x₁, x₂, x₃}`
and four vertices `a, b, u, c`, the bits `aₖ, bₖ, uₖ, cₖ` record adjacency to `xₖ`. Unless one of
fifteen forbidden configurations occurs, the weighted number of adjacencies is at most `12`.
-/

@[expose] public section

namespace CorradiHajnal

open Finset

/-- The weighted number of adjacencies is at most `12` unless a forbidden configuration occurs. -/
def triCheck (a₁ a₂ a₃ b₁ b₂ b₃ u₁ u₂ u₃ c₁ c₂ c₃ : Bool) : Bool :=
  (a₁ && (u₁ && (b₂ && b₃))) || (a₂ && (u₂ && (b₁ && b₃))) || (a₃ && (u₃ && (b₁ && b₂))) ||
  (b₁ && (u₁ && (a₂ && a₃))) || (b₂ && (u₂ && (a₁ && a₃))) || (b₃ && (u₃ && (a₁ && a₂))) ||
  (c₁ && (a₁ && (u₂ && u₃))) || (c₂ && (a₂ && (u₁ && u₃))) || (c₃ && (a₃ && (u₁ && u₂))) ||
  (c₂ && (c₃ && (u₁ && b₁))) || (c₁ && (c₃ && (u₂ && b₂))) || (c₁ && (c₂ && (u₃ && b₃))) ||
  (c₂ && (c₃ && (u₁ && a₁))) || (c₁ && (c₃ && (u₂ && a₂))) || (c₁ && (c₂ && (u₃ && a₃))) ||
  decide (a₁.toNat + a₂.toNat + a₃.toNat + (b₁.toNat + b₂.toNat + b₃.toNat) +
    2 * (u₁.toNat + u₂.toNat + u₃.toNat) + 2 * (c₁.toNat + c₂.toNat + c₃.toNat) ≤ 12)

lemma triCheck_eq_true : ∀ a₁ a₂ a₃ b₁ b₂ b₃ u₁ u₂ u₃ c₁ c₂ c₃ : Bool,
    triCheck a₁ a₂ a₃ b₁ b₂ b₃ u₁ u₂ u₃ c₁ c₂ c₃ = true := by
  decide

lemma tri_bound {a₁ a₂ a₃ b₁ b₂ b₃ u₁ u₂ u₃ c₁ c₂ c₃ : Bool}
    (h1 : (a₁ && (u₁ && (b₂ && b₃))) = false) (h2 : (a₂ && (u₂ && (b₁ && b₃))) = false)
    (h3 : (a₃ && (u₃ && (b₁ && b₂))) = false) (h4 : (b₁ && (u₁ && (a₂ && a₃))) = false)
    (h5 : (b₂ && (u₂ && (a₁ && a₃))) = false) (h6 : (b₃ && (u₃ && (a₁ && a₂))) = false)
    (h7 : (c₁ && (a₁ && (u₂ && u₃))) = false) (h8 : (c₂ && (a₂ && (u₁ && u₃))) = false)
    (h9 : (c₃ && (a₃ && (u₁ && u₂))) = false) (h10 : (c₂ && (c₃ && (u₁ && b₁))) = false)
    (h11 : (c₁ && (c₃ && (u₂ && b₂))) = false) (h12 : (c₁ && (c₂ && (u₃ && b₃))) = false)
    (h13 : (c₂ && (c₃ && (u₁ && a₁))) = false) (h14 : (c₁ && (c₃ && (u₂ && a₂))) = false)
    (h15 : (c₁ && (c₂ && (u₃ && a₃))) = false) :
    a₁.toNat + a₂.toNat + a₃.toNat + (b₁.toNat + b₂.toNat + b₃.toNat) +
      2 * (u₁.toNat + u₂.toNat + u₃.toNat) + 2 * (c₁.toNat + c₂.toNat + c₃.toNat) ≤ 12 := by
  have := triCheck_eq_true a₁ a₂ a₃ b₁ b₂ b₃ u₁ u₂ u₃ c₁ c₂ c₃
  simp only [triCheck, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    Bool.false_or, decide_eq_true_eq] at this
  exact this

lemma toNat_decide (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma nb_triple {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (v : V) :
    nb G {x, y, z} v = (decide (G.Adj v x)).toNat + (decide (G.Adj v y)).toNat +
      (decide (G.Adj v z)).toNat := by
  rw [nb_insert_of_not_mem (by simp [hxy, hxz]), nb_insert_of_not_mem (by simp [hyz])]
  simp only [toNat_decide]
  unfold nb
  by_cases h : G.Adj v z <;> simp [filter_singleton, h] <;> omega

end CorradiHajnal
