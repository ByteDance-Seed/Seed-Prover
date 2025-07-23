-- In Seymour/Seymour/Matroid/Operations/SumDelta/SpecialCase2Sum.lean

import Seymour.Matroid.Operations.Sum2.Basic
import Seymour.Matroid.Operations.SumDelta.CircuitForms

variable {α : Type} [DecidableEq α] {M₁ M₂ : BinaryMatroid α}

section CircuitFormsProperties

/-- Circuit of form 1 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma DeltaSumCircuitForm1.sum2_circuit_pred {C : Set α}
    (hC : DeltaSumCircuitForm1 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    DeltaSumCircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    replace ⟨hC, _⟩ := hC
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    cases hX₂.dep_or_empty with
    | inl X₂_dep =>
      have X₂_eq : X₂ = M₁.E ∩ M₂.E :=
        have symDiff_sub_E₁ := symmDiff_eq_alt X₁ X₂ ▸ hXX ▸ hCC'.trans hC.subset_ground
        have X₂_sub_E₁ := M₁.toMatroid_E ▸ symmDiff_subset_ground_right symDiff_sub_E₁ hX₁.subset_ground
        have X₂_sub_inter := Set.subset_inter X₂_sub_E₁ X₂_dep.subset_ground
        have inter_finite := Set.finite_of_encard_eq_coe assumptions.interSingleton
        have inter_encard_le_X₂_encard := le_of_eq_of_le assumptions.interSingleton
          (Set.one_le_encard_iff_nonempty.← X₂_dep.nonempty)
        inter_finite.eq_of_subset_of_encard_le X₂_sub_inter inter_encard_le_X₂_encard
      have ⟨p, hp⟩ := assumptions.inter_singleton
      have M₂_loop_p : M₂.toMatroid.Loop p := ⟨singleton_inter_in_right hp, hp ▸ X₂_eq ▸ X₂_dep⟩
      exfalso
      exact assumptions.inter_singleton_not_loop_M₂ hp M₂_loop_p
    | inr X₂_empty =>
      rw [X₂_empty, Set.union_empty, Set.inter_empty, Set.diff_empty] at hXX
      rw [hXX] at hCC' C'_nonempty ⊢
      have X₁_dep := hX₁.nonempty_dep C'_nonempty
      exact hC.right X₁_dep hCC'

/-- Circuit of form 2 satisfies circuit predicate of `M₁ Δ M₂` if `M₁.E` and `M₂.E` satisfy the 2-sum assumptions -/
lemma DeltaSumCircuitForm2.sum2_circuit_pred {C : Set α}
    (hC : DeltaSumCircuitForm2 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    DeltaSumCircuitPred M₁ M₂ C := by
  constructor
  · exact hC.circuit_form
  · intro C' hC' hCC'
    replace ⟨hC, _⟩ := hC
    obtain ⟨C'_nonempty, _, X₁, X₂, hXX, hX₁, hX₂⟩ := hC'
    cases hX₁.dep_or_empty with
    | inl X₁_dep =>
      have X₁_eq : X₁ = M₁.E ∩ M₂.E :=
        have symDiff_sub_E₂ := symmDiff_eq_alt X₁ X₂ ▸ hXX ▸ hCC'.trans hC.subset_ground
        have X₁_sub_E₂ := M₂.toMatroid_E ▸ symmDiff_subset_ground_left symDiff_sub_E₂ hX₂.subset_ground
        have hX₁sub_inter := Set.subset_inter X₁_dep.subset_ground X₁_sub_E₂
        have inter_finite := Set.finite_of_encard_eq_coe assumptions.interSingleton
        have inter_encard_le_X₁_encard := le_of_eq_of_le assumptions.interSingleton
          (Set.one_le_encard_iff_nonempty.← X₁_dep.nonempty)
        inter_finite.eq_of_subset_of_encard_le hX₁sub_inter inter_encard_le_X₁_encard
      obtain ⟨p, hp⟩ := assumptions.inter_singleton
      have M₁_loop_p : M₁.toMatroid.Loop p := ⟨singleton_inter_in_left hp, hp ▸ X₁_eq ▸ X₁_dep⟩
      exfalso
      exact assumptions.inter_singleton_not_loop_M₁ hp M₁_loop_p
    | inr X₁_empty =>
      rw [X₁_empty, Set.empty_union, Set.empty_inter, Set.diff_empty] at hXX
      rw [hXX] at hCC' C'_nonempty ⊢
      have X₂_dep := hX₂.nonempty_dep C'_nonempty
      exact hC.right X₂_dep hCC'

/- Start of proof attempt -/
lemma round1_h4 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (p : α)
  (hC : DeltaSumCircuitForm3 M₁ M₂ C p)
  (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid):
  p ∈ M₁.toMatroid.E := by
  have h11 : M₁.toMatroid.Circuit (C ∩ M₁.E ∪ {p}) := hC.left
  have h111 : (C ∩ M₁.E ∪ {p}) ⊆ M₁.toMatroid.E := by
    exact?
  have h114 : {p} ⊆ (C ∩ M₁.E ∪ {p}) := by
    simp
  have h115 : {p} ⊆ M₁.toMatroid.E := by
    exact Set.Subset.trans h114 h111
  have h1 : p ∈ M₁.toMatroid.E := by
    simpa using h115 (by simp)
  exact h1

lemma round1_h5 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (p : α)
  (hC : DeltaSumCircuitForm3 M₁ M₂ C p)
  (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid):
  p ∈ M₂.toMatroid.E := by
  have h21 : M₂.toMatroid.Circuit (C ∩ M₂.E ∪ {p}) := hC.right.1
  have h211 : (C ∩ M₂.E ∪ {p}) ⊆ M₂.toMatroid.E := by
    exact?
  have h214 : {p} ⊆ (C ∩ M₂.E ∪ {p}) := by
    simp
  have h215 : {p} ⊆ M₂.toMatroid.E := by
    exact Set.Subset.trans h214 h211
  have h2 : p ∈ M₂.toMatroid.E := by
    simpa using h215 (by simp)
  exact h2

lemma round1_h7 (M₁ M₂ : BinaryMatroid α)
  (C : Set α)
  (p : α)
  (hC : DeltaSumCircuitForm3 M₁ M₂ C p)
  (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid)
  (h4 : p ∈ M₁.toMatroid.E)
  (h5 : p ∈ M₂.toMatroid.E):
  M₁.toMatroid.E ∩ M₂.toMatroid.E = {p} := by
  obtain ⟨x, hx⟩ := assumptions.inter_singleton
  have h31 : p ∈ M₁.toMatroid.E ∩ M₂.toMatroid.E := ⟨h4, h5⟩
  have h32 : M₁.toMatroid.E ∩ M₂.toMatroid.E = {x} := hx
  have h33 : p ∈ ({x} : Set α) := by rw [← h32]; exact h31
  have h34 : p = x := by simpa using h33
  have h35 : M₁.toMatroid.E ∩ M₂.toMatroid.E = {p} := by
    rw [h32, h34]
    <;> simp
  exact h35

/-- Under 2-sum assumptions, `{p}` in definition of circuits of form 3 is exactly `M₁.E ∩ M₂.E` -/
theorem DeltaSumCircuitForm3.sum2_singleton_eq {C : Set α} {p : α}
    (hC : DeltaSumCircuitForm3 M₁ M₂ C p) (assumptions : TwoSumAssumptions M₁.toMatroid M₂.toMatroid) :
    M₁.E ∩ M₂.E = {p}  := by

  have h4 : p ∈ M₁.toMatroid.E := by
    exact round1_h4 M₁ M₂ C p hC assumptions
  have h5 : p ∈ M₂.toMatroid.E := by
    exact round1_h5 M₁ M₂ C p hC assumptions
  have h7 : M₁.toMatroid.E ∩ M₂.toMatroid.E = {p} := by
    exact round1_h7 M₁ M₂ C p hC assumptions h4 h5
  have h8 : ∀ (y : α), y ∈ M₁.E ∩ M₂.E → y = p := by
    intro y hy
    have hy1 : y ∈ M₁.E := hy.1
    have hy2 : y ∈ M₂.E := hy.2
    have h9 : y ∈ M₁.toMatroid.E := by
      exact?
    have h10 : y ∈ M₂.toMatroid.E := by
      exact?
    have h11 : y ∈ M₁.toMatroid.E ∩ M₂.toMatroid.E := ⟨h9, h10⟩
    have h12 : y ∈ ({p} : Set α) := by
      rw [h7] at h11
      exact h11
    simpa using h12
  have h13 : M₁.E ∩ M₂.E ⊆ {p} := by
    intro y hy
    have h14 : y = p := h8 y hy
    rw [h14]
    <;> simp
  have h15 : p ∈ M₁.E := by
    have h16 : p ∈ M₁.toMatroid.E := h4
    exact?
  have h17 : p ∈ M₂.E := by
    have h18 : p ∈ M₂.toMatroid.E := h5
    exact?
  have h19 : p ∈ M₁.E ∩ M₂.E := ⟨h15, h17⟩
  have h20 : {p} ⊆ M₁.E ∩ M₂.E := by
    intro x hx
    simp at hx
    rw [hx]
    exact h19
  have h21 : M₁.E ∩ M₂.E = {p} := by
    apply Set.Subset.antisymm
    · exact h13
    · exact h20
  exact h21
