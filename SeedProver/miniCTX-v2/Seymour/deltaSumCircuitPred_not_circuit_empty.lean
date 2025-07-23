-- In Seymour/Seymour/Matroid/Operations/SumDelta/Basic.lean

import Seymour.Matroid.Classes.Binary
import Seymour.Matroid.Constructors.CircuitMatroid
import Seymour.Matroid.Notions.DisjointCircuitFamily

variable {α : Type}

section BasicDefinitions

/-- Circuits in `M₁ Δ M₂` are nonempty subsets of the ground set of form `X₁ Δ X₂`
    where `X₁` and `X₂` are disjoint unions of circuits in `M₁` and `M₂` respectively. -/
def DeltaSumCircuitsAux [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C X₁ X₂ : Set α) : Prop :=
  C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) ∧ M₁.toMatroid.IsUnionDisjointCircuits X₁ ∧ M₂.toMatroid.IsUnionDisjointCircuits X₂

/-- A set satisfies circuit form if for some `X₁` and `X₂` it has the form above. -/
def DeltaSumCircuitForm [DecidableEq α] (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  C.Nonempty ∧ C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) ∧ ∃ X₁ X₂ : Set α, DeltaSumCircuitsAux M₁ M₂ C X₁ X₂

/-- Circuits of Δ-sum are minimal non-empty subsets of `M₁.E Δ M₂.E` of the form `X₁ Δ X₂`
    where `X₁` and `X₂` is a disjoint union of circuits of `M₁` and `M₂` respectively. -/
def DeltaSumCircuitPred [DecidableEq α] (M₁ M₂ : BinaryMatroid α) : CircuitPredicate α :=
  Minimal (DeltaSumCircuitForm M₁ M₂)

end BasicDefinitions

section BasicProperties

/-- A set of circuit form is nonempty. -/
lemma deltaSumCircuitForm.nonempty [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm M₁ M₂ C) :
    C.Nonempty :=
  hC.left

/-- A set of circuit form is a subset of the ground set. -/
lemma DeltaSumCircuitForm.subset_ground [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm M₁ M₂ C) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  hC.right.left

/-- A set of circuit form is the symmetric difference of `X₁` and `X₂` -/
lemma DeltaSumCircuitsAux.eq_symmDiff [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    C = (X₁ ∪ X₂) \ (X₁ ∩ X₂) :=
  hC.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₁` -/
lemma DeltaSumCircuitsAux.udc_left [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    M₁.toMatroid.IsUnionDisjointCircuits X₁ :=
  hC.right.left

/-- A set of circuit form is related to a union of disjoint circuits of `M₂` -/
lemma DeltaSumCircuitsAux.udc_right [DecidableEq α] {M₁ M₂ : BinaryMatroid α} {C X₁ X₂ : Set α}
    (hC : DeltaSumCircuitsAux M₁ M₂ C X₁ X₂) :
    M₂.toMatroid.IsUnionDisjointCircuits X₂ :=
  hC.right.right

end BasicProperties

section CircuitAxioms

/- Start of proof attempt -/
lemma round1_deltaSumCircuitPred_not_circuit_empty [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ¬DeltaSumCircuitPred M₁ M₂ ∅ := by
  intro h
  have h1 : DeltaSumCircuitForm M₁ M₂ ∅ := h.1
  have h2 : (∅ : Set α).Nonempty := h1.1
  simp at h2
  <;> contradiction

/-- In circuit construction of Δ-sum, empty set is not circuit -/
theorem deltaSumCircuitPred_not_circuit_empty [DecidableEq α] (M₁ M₂ : BinaryMatroid α) :
    ¬DeltaSumCircuitPred M₁ M₂ ∅  := by

  exact round1_deltaSumCircuitPred_not_circuit_empty M₁ M₂
