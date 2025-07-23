-- In Seymour/Seymour/Matroid/Notions/Loop.lean

import Mathlib.Data.Matroid.Basic
import Seymour.Matroid.Notions.Circuit

variable {α : Type}

/-- Loop is an element of the ground set that is not independent when viewed as a singleton set. -/
def Matroid.Loop (M : Matroid α) (a : α) : Prop :=
  a ∈ M.E ∧ M.Dep {a}

/- Start of proof attempt -/
lemma round1_loop_imp_circuit (M : Matroid α) (a : α) (h : M.Loop a) : M.Circuit {a} := by
  have h1 : a ∈ M.E := h.1
  have h2 : M.Dep {a} := h.2
  have h3 : ∀ (y : Set α), M.Dep y → y ⊆ {a} → {a} ⊆ y := by
    intro y h_dep_y h_y_sub_a
    have h4 : a ∈ y := by
      by_contra h41
      have h5 : y = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro x hx
        have h51 : x ∈ ({a} : Set α) := h_y_sub_a hx
        have h52 : x = a := by simpa using h51
        rw [h52] at hx
        contradiction
      rw [h5] at h_dep_y
      have h6 : M.Indep (∅ : Set α) := M.empty_indep
      have h7 : ¬M.Dep (∅ : Set α) := by
        simp [Matroid.Dep] at *
        <;> tauto
      exact h7 h_dep_y
    have h8 : {a} ⊆ y := by
      intro x hx
      have h9 : x = a := by simpa using hx
      rw [h9]
      exact h4
    exact h8
  exact ⟨h2, h3⟩

lemma round1_circuit_imp_loop (M : Matroid α) (a : α) (h : M.Circuit {a}) : M.Loop a := by
  have h1 : M.Dep {a} := h.1
  have h2 : {a} ⊆ M.E := by
    exact?
  have h3 : a ∈ M.E := by
    have h31 : a ∈ ({a} : Set α) := by simp
    exact h2 h31
  exact ⟨h3, h1⟩

/-- An element is a loop iff its singleton set is a circuit. -/
theorem Matroid.loop_iff_circuit (M : Matroid α) {a : α} :
    M.Loop a ↔ M.Circuit {a}  := by

  constructor
  · exact round1_loop_imp_circuit M a
  · exact round1_circuit_imp_loop M a
