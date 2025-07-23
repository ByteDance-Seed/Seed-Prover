-- In foundation/Foundation/FirstOrder/Arith/Representation.lean

import Foundation.FirstOrder.Arith.CobhamR0
import Foundation.Vorspiel.Arith
import Mathlib.Computability.Primrec

namespace Part

lemma unit_dom_iff (x : Part Unit) : x.Dom ↔ () ∈ x := by simp [dom_iff_mem, show ∀ x : Unit, x = () by intro x; rfl]

end Part

namespace Mathlib.List.Vector

variable {α : Type*}

/- Start of proof attempt -/
lemma round1_cons_get (a : α) (v : List.Vector α k) : (a ::ᵥ v).get = a :> v.get := by
  funext i
  by_cases h : i.val = 0
  · -- Case 1: i.val = 0
    have h1 : i.val = 0 := h
    have h3 : i = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp [h1]
    rw [h3]
    simp
  · -- Case 2: i.val ≠ 0
    have h2 : 0 < i.val := Nat.pos_of_ne_zero h
    have h4 : ∃ j : ℕ, i.val = j + 1 := by
      refine' ⟨i.val - 1, _⟩
      omega
    rcases h4 with ⟨j, hj⟩
    have h5 : j < k := by
      have h51 : i.val < k + 1 := i.isLt
      omega
    have h6 : j < k := by omega
    have h7 : ∃ (j' : Fin k), j'.val = j := ⟨⟨j, h6⟩, rfl⟩
    rcases h7 with ⟨j', hj'⟩
    have h8 : i.val = j' + 1 := by
      simp [hj, hj']
      <;> omega
    have h9 : i = ⟨j' + 1, by
      have h91 : j' < k := j'.isLt
      omega⟩ := by
      apply Fin.ext
      simp [h8]
      <;> aesop
    rw [h9]
    simp [hj']
    <;> aesop

theorem cons_get (a : α) (v : List.Vector α k) : (a ::ᵥ v).get = a :> v.get  := by

  exact round1_cons_get a v
