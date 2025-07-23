-- In Seymour/Seymour/Matroid/Operations/SumDelta/CircuitForms.lean

import Seymour.Matroid.Operations.SumDelta.Basic
import Seymour.ForMathlib.SetTheory

set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α]

section Basic

/-- Nonempty union of disjoint circuits of `M₁` satisfies circuit form of `M₁ Δ M₂`  -/
lemma deltaSumCircuitForm_left {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : C.Nonempty) (hCE : C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)) (hCM₁ : M₁.toMatroid.IsUnionDisjointCircuits C) :
    DeltaSumCircuitForm M₁ M₂ C :=
  ⟨hC, hCE, C, ∅, by simp, hCM₁, M₂.toMatroid.emptyUnionDisjointCircuits⟩

/-- Nonempty union of disjoint circuits of `M₂` satisfies circuit form of `M₁ Δ M₂`  -/
lemma deltaSumCircuitForm_right {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : C.Nonempty) (hCE : C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)) (hCM₂ : M₂.toMatroid.IsUnionDisjointCircuits C) :
    DeltaSumCircuitForm M₁ M₂ C :=
  ⟨hC, hCE, ∅, C, by simp, M₁.toMatroid.emptyUnionDisjointCircuits, hCM₂⟩

end Basic

section CircuitForm1

/-- Form 1 of circuits in `M₁ Δ M₂`: circuits of `M₁` that are disjoint with `M₁.E ∩ M₂.E` -/
def DeltaSumCircuitForm1 (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  M₁.toMatroid.Circuit C ∧ C ⫗ M₁.E ∩ M₂.E

/-- Circuit of form 1 is a circuit in `M₁` -/
lemma DeltaSumCircuitForm1.circuit_M₁ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    M₁.toMatroid.Circuit C :=
  hC.left

/- Start of proof attempt -/
lemma round1_DeltaSumCircuitForm1_disjoint_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⫗ M₁.E ∩ M₂.E := by
  exact hC.right

/-- Circuit of form 1 is disjoint with `M₁.E ∩ M₂.E` -/
theorem DeltaSumCircuitForm1.disjoint_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⫗ M₁.E ∩ M₂.E  := by

  exact round1_DeltaSumCircuitForm1_disjoint_inter hC
