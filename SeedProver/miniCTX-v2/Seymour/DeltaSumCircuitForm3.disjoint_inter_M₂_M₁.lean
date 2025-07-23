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

/-- Circuit of form 2 satisfies circuit form of `M₁ Δ M₂` -/
lemma DeltaSumCircuitForm2.circuit_form {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) :
    DeltaSumCircuitForm M₁ M₂ C :=
  deltaSumCircuitForm_right hC.circuit_M₂.nonempty hC.subset_ground hC.circuit_M₂.isUnionDisjointCircuits

/-- If `C` satisfies circuit predicate and is a union of disjoint circuits of `M₂`, then `C` is a circuit of `M₂` -/
lemma DeltaSumCircuitPred.udc_M₂ {M₁ M₂ : BinaryMatroid α} {C : Set α}
    (hCpred : DeltaSumCircuitPred M₁ M₂ C) (hCudc : M₂.toMatroid.IsUnionDisjointCircuits C) :
    M₂.toMatroid.Circuit C :=
  have ⟨⟨C_nempty, hCE, _⟩, hCmin⟩ := hCpred
  ⟨hCudc.nonempty_dep C_nempty, fun D hD hDC =>
    have ⟨_, D', hD', hDD'⟩ := M₂.toMatroid.dep_iff_has_circuit.→ hD
    (hCmin
        (DeltaSumCircuitForm2.circuit_form ⟨hD', (Set.subset_diff.→ ((hDD'.trans hDC).trans hCE)).right⟩)
        (hDD'.trans hDC)
      ).trans hDD'⟩

end CircuitForm2

section CircuitForm3

/-- Form 3 of circuits in `M₁ Δ M₂`:
    sets `C₁ Δ C₂` where `C₁` and `C₂` are circuits in `M₁` and `M₂`, respectively,
    with `C₁ ∩ (M₁.E ∩ M₂.E)` and `C₂ ∩ (M₁.E ∩ M₂.E)` being the same one-element set.
    Here we use equivalent definition by denoting `p` the single element in `C₁ ∩ C₂` and
    expressing `C₁` and `C₂` via `p`, `C`, and ground sets of `M₁` and `M₂`. -/
def DeltaSumCircuitForm3 (M₁ M₂ : BinaryMatroid α) (C : Set α) (p : α) : Prop :=
  M₁.toMatroid.Circuit ((C ∩ M₁.E) ∪ {p}) ∧
  M₂.toMatroid.Circuit ((C ∩ M₂.E) ∪ {p}) ∧
  C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)

/-- Existential version of form 3 of circuits -/
def IsDeltaSumCircuitForm3 (M₁ M₂ : BinaryMatroid α) (C : Set α) : Prop :=
  ∃ p ∈ M₁.E ∩ M₂.E, DeltaSumCircuitForm3 M₁ M₂ C p

variable {C : Set α} {p : α}

/-- Circuit of form 3 yields a circuit in `M₁` after intersecting it with `M₁.E` and adding `p` -/
def DeltaSumCircuitForm3.to_circuit_M₁ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    M₁.toMatroid.Circuit ((C ∩ M₁.E) ∪ {p}) :=
  hC.left

/-- Circuit of form 3 yields a circuit in `M₂` after intersecting it with `M₁.E` and adding `p` -/
def DeltaSumCircuitForm3.to_circuit_M₂ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    M₂.toMatroid.Circuit ((C ∩ M₂.E) ∪ {p}) :=
  hC.right.left

/-- Circuit of form 3 is subset of ground set of `M₁ Δ M₂` -/
def DeltaSumCircuitForm3.subset_ground {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ⊆ (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E) :=
  hC.right.right

/-- Singleton element in definition of circuit form 3 lies in `M₁.E` -/
lemma DeltaSumCircuitForm3.singleton_subset_M₁ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    {p} ⊆ M₁.E :=
  (Set.union_subset_iff.→ hC.to_circuit_M₁.subset_ground).right

/-- Singleton element in definition of circuit form 3 lies in `M₂.E` -/
lemma DeltaSumCircuitForm3.singleton_subset_M₂ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    {p} ⊆ M₂.E :=
  (Set.union_subset_iff.→ hC.to_circuit_M₂.subset_ground).right

/-- Singleton element in definition of circuit form 3 lies in `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm3.singleton_subset_inter {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    {p} ⊆ M₁.E ∩ M₂.E :=
  Set.subset_inter hC.singleton_subset_M₁ hC.singleton_subset_M₂

/-- Circuit of form 3 lies in `M₁.E ∪ M₂.E` -/
lemma DeltaSumCircuitForm3.subset_union {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ⊆ M₁.E ∪ M₂.E :=
  sub_union_diff_sub_union hC.subset_ground

/-- Circuit of form 3 is disjoint with `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm3.disjoint_inter {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ⫗ M₁.E ∩ M₂.E :=
  Set.disjoint_of_subset_left hC.subset_ground Set.disjoint_sdiff_left

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm3.disjoint_inter_M₁_inter {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₁.E ⫗ M₁.E ∩ M₂.E :=
  hC.disjoint_inter.inter_left M₁.E

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with `M₂.E` -/
lemma DeltaSumCircuitForm3.disjoint_inter_M₁_M₂ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₁.E ⫗ M₂.E := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_assoc, ←Set.disjoint_iff_inter_eq_empty]
  exact hC.disjoint_inter

/-- Circuit of form 3 intersected with `M₁.E` is disjoint with its intersection with `M₂.E` -/
lemma DeltaSumCircuitForm3.disjoint_inter_M₁_inter_M₂ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₁.E ⫗ C ∩ M₂.E :=
  Set.disjoint_of_subset_right Set.inter_subset_right hC.disjoint_inter_M₁_M₂

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma DeltaSumCircuitForm3.disjoint_inter_M₂_inter {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₂.E ⫗ M₁.E ∩ M₂.E :=
  hC.disjoint_inter.inter_left M₂.E

/- Start of proof attempt -/
lemma round1_DeltaSumCircuitForm3_disjoint_inter_M₂_M₁ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₂.E ⫗ M₁.E := by
  have h1 : C ∩ M₂.E ⫗ M₁.E ∩ M₂.E := DeltaSumCircuitForm3.disjoint_inter_M₂_inter hC
  have h11 : (C ∩ M₂.E) ∩ (M₁.E ∩ M₂.E) = ∅ := by simpa [Set.disjoint_iff_inter_eq_empty] using h1
  have h2 : (C ∩ M₂.E) ∩ M₁.E ⊆ (C ∩ M₂.E) ∩ (M₁.E ∩ M₂.E) := by
    intro x hx
    have h21 : x ∈ C ∩ M₂.E := hx.1
    have h22 : x ∈ M₁.E := hx.2
    have h212 : x ∈ M₂.E := h21.2
    have h23 : x ∈ M₁.E ∩ M₂.E := ⟨h22, h212⟩
    exact ⟨h21, h23⟩
  have h3 : (C ∩ M₂.E) ∩ M₁.E = ∅ := by
    have h31 : (C ∩ M₂.E) ∩ M₁.E ⊆ (C ∩ M₂.E) ∩ (M₁.E ∩ M₂.E) := h2
    have h32 : (C ∩ M₂.E) ∩ (M₁.E ∩ M₂.E) = ∅ := h11
    have h33 : (C ∩ M₂.E) ∩ M₁.E ⊆ ∅ := by
      rw [h32] at h31
      exact h31
    have h34 : (C ∩ M₂.E) ∩ M₁.E = ∅ := by simpa using h33
    exact h34
  have h4 : C ∩ M₂.E ⫗ M₁.E := by
    simpa [Set.disjoint_iff_inter_eq_empty] using h3
  exact h4

/-- Circuit of form 3 intersected with `M₂.E` is disjoint with `M₁.E` -/
theorem DeltaSumCircuitForm3.disjoint_inter_M₂_M₁ {M₁ M₂ : BinaryMatroid α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) :
    C ∩ M₂.E ⫗ M₁.E  := by

  exact round1_DeltaSumCircuitForm3_disjoint_inter_M₂_M₁ hC
