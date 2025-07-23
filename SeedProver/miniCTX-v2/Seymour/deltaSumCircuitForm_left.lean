-- In Seymour/Seymour/Matroid/Operations/SumDelta/CircuitForms.lean

import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.ForMathlib.SetTheory

set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α]

section Basic

/- Start of proof attempt -/
lemma round1_is_union_disjoint_circuits_empty (α : Type) [DecidableEq α] (M : BinaryMatroid α) :
    M.toMatroid.IsUnionDisjointCircuits (∅ : Set α) := by
  exact?

lemma round1_h2 (α : Type) [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) 
    (hCM₁ : M₁.toMatroid.IsUnionDisjointCircuits C) : 
    DeltaSumCircuitsAux M₁ M₂ C C ∅ := by
  constructor
  · -- Proof of C = (C ∪ ∅) \ (C ∩ ∅)
    ext x
    simp
  · -- Proof of M₁.toMatroid.IsUnionDisjointCircuits C ∧ M₂.toMatroid.IsUnionDisjointCircuits ∅
    constructor
    · exact hCM₁
    · exact round1_is_union_disjoint_circuits_empty α M₂

lemma round1_h1 (α : Type) [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α)
    (hCM₁ : M₁.toMatroid.IsUnionDisjointCircuits C) :
    ∃ X₁ X₂, DeltaSumCircuitsAux M₁ M₂ C X₁ X₂ := by
  have h2 : DeltaSumCircuitsAux M₁ M₂ C C ∅ := round1_h2 α M₁ M₂ C hCM₁
  refine ⟨C, ∅, h2⟩

/-- Nonempty union of disjoint circuits of `M₁` satisfies circuit form of `M₁ Δ M₂`  -/
theorem deltaSumCircuitForm_left {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : C.Nonempty) (hCE : C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)) (hCM₁ : M₁.toMatroid.IsUnionDisjointCircuits C) :
    DeltaSumCircuitForm M₁ M₂ C  := by

  have h1 : ∃ X₁ X₂, DeltaSumCircuitsAux M₁ M₂ C X₁ X₂ := round1_h1 α M₁ M₂ C hCM₁
  refine' ⟨hC, hCE, h1⟩
