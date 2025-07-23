-- In Seymour/Seymour/ForMathlib/SetTheory.lean

import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.SymmDiff
import Mathlib.Tactic

import Seymour.Basic

/-!
This provides lemmas about sets (mostly dealing with disjointness) that are missing in Mathlib.
-/

variable {α : Type}

section Other

/- Start of proof attempt -/
lemma round1_set_union_union_eq_rev (X Y Z : Set α) : X ∪ Y ∪ Z = Z ∪ Y ∪ X := by
  ext a
  simp only [Set.mem_union]
  <;> tauto

theorem set_union_union_eq_rev (X Y Z : Set α) : X ∪ Y ∪ Z = Z ∪ Y ∪ X  := by

  exact round1_set_union_union_eq_rev X Y Z
