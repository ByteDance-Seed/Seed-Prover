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

/-- Circuit of form 1 is disjoint with `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm1.disjoint_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⫗ M₁.E ∩ M₂.E :=
  hC.right

/-- Circuit of form 1 lies in `M₁.E ∪ M₂.E` -/
lemma DeltaSumCircuitForm1.subset_union {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_left hC.circuit_M₁.subset_ground M₂.E

/-- Circuit of form 1 lies in ground set of `M₁ Δ M₂` -/
lemma DeltaSumCircuitForm1.subset_ground {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of form 1 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma DeltaSumCircuitForm1.subset_M₁_diff_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⊆ M₁.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.circuit_M₁.subset_ground, hC.disjoint_inter⟩

/-- Circuit of form 1 is disjoint with `M₂.E` -/
lemma DeltaSumCircuitForm1.disjoint_M₂ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    C ⫗ M₂.E := by
  have hMM := diff_inter_disjoint_diff_inter M₁.E M₂.E
  have hCM₂ := Set.disjoint_of_subset_left hC.subset_M₁_diff_inter hMM
  have hCM₂ := Set.disjoint_union_right.← ⟨hCM₂, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_right] at hCM₂
  exact hCM₂

/-- Circuit of form 1 satisfies circuit form of `M₁ Δ M₂` -/
lemma DeltaSumCircuitForm1.circuit_form {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) :
    DeltaSumCircuitForm M₁ M₂ C :=
  deltaSumCircuitForm_left hC.circuit_M₁.nonempty hC.subset_ground hC.circuit_M₁.isUnionDisjointCircuits

/-- If `C` satisfies circuit predicate and is a union of disjoint circuits of `M₁`, then `C` is a circuit of `M₁` -/
lemma DeltaSumCircuitPred.udc_M₁ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (C_pred : DeltaSumCircuitPred M₁ M₂ C) (C_udc : M₁.toMatroid.IsUnionDisjointCircuits C) :
    M₁.toMatroid.Circuit C :=
  have ⟨⟨hC, hCE, _⟩, hCmin⟩ := C_pred
  ⟨C_udc.nonempty_dep hC, fun D hD hDC =>
    have ⟨_, D', hD', hDD'⟩ := M₁.toMatroid.dep_iff_has_circuit.→ hD
    (hCmin
        (DeltaSumCircuitForm1.circuit_form ⟨hD', (Set.subset_diff.→ ((hDD'.trans hDC).trans hCE)).right⟩)
        (hDD'.trans hDC)
      ).trans hDD'⟩

end CircuitForm1

section CircuitForm2

/-- Form 2 of circuits in `M₁ Δ M₂`: circuits of `M₂` that are disjoint with `M₁.E ∩ M₂.E` -/
def DeltaSumCircuitForm2 (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  M₂.toMatroid.Circuit C ∧ C ⫗ M₁.E ∩ M₂.E

/-- Circuit of form 2 is a circuit in `M₁` -/
lemma DeltaSumCircuitForm2.circuit_M₂ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    M₂.toMatroid.Circuit C :=
  hC.left

/-- Circuit of form 2 is disjoint with `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm2.disjoint_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⫗ M₁.E ∩ M₂.E :=
  hC.right

/-- Circuit of form 2 lies in `M₁.E ∪ M₂.E` -/
lemma DeltaSumCircuitForm2.subset_union {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_right hC.circuit_M₂.subset_ground M₁.E

/-- Circuit of form 2 lies in ground set of `M₁ Δ M₂` -/
lemma DeltaSumCircuitForm2.subset_ground {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of form 2 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma DeltaSumCircuitForm2.subset_M₂_diff_inter {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⊆ M₂.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.circuit_M₂.subset_ground, hC.disjoint_inter⟩

/-- Circuit of form 2 is disjoint with `M₂.E` -/
lemma DeltaSumCircuitForm2.disjoint_M₁ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⫗ M₁.E := by
  have hMM := diff_inter_disjoint_diff_inter M₁.E M₂.E
  have hCM₂ := Set.disjoint_of_subset_right hC.subset_M₂_diff_inter hMM
  have hCM₂ := Set.disjoint_union_right.← ⟨hCM₂.symm, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_left] at hCM₂
  exact hCM₂

/- Start of proof attempt -/
lemma round1_DeltaSumCircuitForm2_circuit_form {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    DeltaSumCircuitForm M₁ M₂ C := by
  have h1 : C.Nonempty := hC.circuit_M₂.nonempty
  have h2 : C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) := DeltaSumCircuitForm2.subset_ground hC
  have h3 : M₂.toMatroid.IsUnionDisjointCircuits C := hC.circuit_M₂.isUnionDisjointCircuits
  exact deltaSumCircuitForm_right h1 h2 h3

/-- Circuit of form 2 satisfies circuit form of `M₁ Δ M₂` -/
theorem DeltaSumCircuitForm2.circuit_form {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    DeltaSumCircuitForm M₁ M₂ C  := by

  exact round1_DeltaSumCircuitForm2_circuit_form hC
