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

/- Start of proof attempt -/
lemma round1_h1 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (hC : DeltaSumCircuitForm2 M₁ M₂ C):
  C ∩ (M₁.E ∩ M₂.E) = ∅ := by
  simpa [Set.disjoint_iff_inter_eq_empty] using hC.right

lemma round1_h9 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (hC : DeltaSumCircuitForm2 M₁ M₂ C)
  (h1 : C ∩ (M₁.E ∩ M₂.E) = ∅):
  C ∩ M₁.E = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have h3 : x ∈ C := (hx).1
  have h4 : x ∈ M₁.E := (hx).2
  have h5 : C ⊆ M₂.E := hC.left.subset_ground
  have h6 : x ∈ M₂.E := h5 h3
  have h7 : x ∈ M₁.E ∩ M₂.E := ⟨h4, h6⟩
  have h8 : x ∈ C ∩ (M₁.E ∩ M₂.E) := ⟨h3, h7⟩
  rw [h1] at h8
  contradiction

lemma round1_h10 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (h9 : C ∩ M₁.E = ∅):
  C ⫗ M₁.E := by
  simpa [Set.disjoint_iff_inter_eq_empty] using h9

/-- Circuit of form 2 is disjoint with `M₂.E` -/
theorem DeltaSumCircuitForm2.disjoint_M₁ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    C ⫗ M₁.E  := by

  have h1 : C ∩ (M₁.E ∩ M₂.E) = ∅ := by
    exact round1_h1 M₁ M₂ C hC
  have h9 : C ∩ M₁.E = ∅ := by
    exact round1_h9 M₁ M₂ C hC h1
  have h10 : C ⫗ M₁.E := by
    exact round1_h10 M₁ M₂ C h9
  exact h10
