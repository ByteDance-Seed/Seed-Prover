-- In Seymour/Seymour/Matroid/Notions/Circuit.lean

import Mathlib.Data.Matroid.Closure
import Seymour.Basic

-- we should use https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Matroid/Circuit.lean instead

variable {α : Type}

/-- Circuit is minimal dependent subset. -/
def Matroid.Circuit (M : Matroid α) (C : Set α) : Prop :=
  Minimal M.Dep C

/-- Every circuit is dependent. -/
lemma Matroid.Circuit.dep (M : Matroid α) {C : Set α} (hC : M.Circuit C) : M.Dep C :=
  hC.left

/-- Every circuit is a subset of the ground set. -/
lemma Matroid.Circuit.subset_ground (M : Matroid α) {C : Set α} (hC : M.Circuit C) : C ⊆ M.E :=
  hC.left.right

/-- Equivalence with explicit definition of circuits. -/
lemma Matroid.circuit_iff_def (M : Matroid α) (C : Set α) :
    M.Circuit C ↔ M.Dep C ∧ ∀ C' : Set α, M.Dep C' → C' ⊆ C → C ⊆ C' :=
  rfl.to_iff

/-- Every strict subset of a circuit is independent. -/
lemma Matroid.Circuit.indep_ssub {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    M.Indep C' := by
  by_contra notIndep_M_C'
  have C'_sub_C : C' ⊆ C := subset_of_ssubset hC'
  have C_sub_E : C ⊆ M.E := hC.subset_ground
  have C'_sub_E : C' ⊆ M.E := hC'.subset.trans C_sub_E
  exact hC'.ne.symm ((hC.right (M.dep_of_not_indep notIndep_M_C' C'_sub_E) C'_sub_C).antisymm C'_sub_C)

/-- Deleting one element from a circuit produces an independent set. -/
lemma Matroid.Circuit.indep_diff_singleton {M : Matroid α} {C : Set α} {a : α} (hC : M.Circuit C) (ha : a ∈ C) :
    M.Indep (C \ {a}) :=
  hC.indep_ssub (Set.diff_singleton_sSubset.← ha)

/-- Empty set is not a circuit. -/
lemma Matroid.Circuit.not_empty {M : Matroid α} (hM : M.Circuit ∅) : False :=
  hM.left.left M.empty_indep

/-- Every circuit is nonempty. -/
lemma Matroid.Circuit.nonempty {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra! C_empty
  rw [C_empty] at hC
  exact hC.not_empty

/-- Independent set is not a circuit. -/
lemma Matroid.Indep.not_circuit {M : Matroid α} {I : Set α} (hI : M.Indep I) : ¬(M.Circuit I) :=
  (·.left.left hI)

/-- No circuit is a subset of another circuit -/
lemma Matroid.Circuit.not_ssubset_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : M.Circuit C') :
    ¬(C ⊂ C') :=
  fun hCC => hCC.right (hC'.right hC.left hCC.subset)

/-- Strict subset of a circuit is not a circuit. -/
lemma Matroid.Circuit.ssubset_not_circuit {M : Matroid α} {C C' : Set α} (hC : M.Circuit C) (hC' : C' ⊂ C) :
    ¬(M.Circuit C') :=
  (·.not_ssubset_circuit hC hC')

/-- A set is dependent iff it is grounded and contains a circuit. -/
lemma Matroid.dep_iff_has_circuit (M : Matroid α) {D : Set α} :
    M.Dep D ↔ D ⊆ M.E ∧ ∃ C : Set α, M.Circuit C ∧ C ⊆ D := by
  constructor
  · intro ⟨hMD, hDE⟩
    refine ⟨hDE, ?_⟩
    -- Source: https://github.com/apnelson1/Matroid/blob/1c75a026d1ea5162210ec53d0204d5900098b31c/Matroid/Circuit.lean#L300
    rw [Matroid.indep_iff_forall_not_mem_closure_diff] at hMD
    push_neg at hMD
    obtain ⟨a, haD, haM⟩ := hMD
    obtain ⟨B, hBDa⟩ := M.exists_basis (D \ {a}) (Set.diff_subset.trans hDE)
    rw [←hBDa.closure_eq_closure] at haM
    obtain ⟨hDaB, hDaE⟩ := hBDa
    -- `B` is the maximal independent subset of `D \ {a}`
    use D
    constructor
    · sorry -- Can we finish the proof the same way Peter Nelson did?
    · rfl
  · intro ⟨hDE, C, hMC, hCD⟩
    obtain ⟨hMC, hCE⟩ := Matroid.dep_iff.→ hMC.dep
    exact ⟨(hMC <| ·.subset hCD), hDE⟩

/-- todo: desc -/
lemma Matroid.Indep.circuit_of_insert_dep {M : Matroid α} {I : Set α} (hI : M.Indep I) {a : α} (hIa : M.Dep (a ᕃ I)) :
    ∃ C : Set α, M.Circuit C ∧ C ⊆ a ᕃ I ∧ a ∈ C := by
  obtain ⟨-, C, hC, hCIa⟩ := M.dep_iff_has_circuit.→ hIa
  exact ⟨C, hC, hCIa, by
    by_contra haC
    exact hC.left.left (hI.subset ((Set.disjoint_singleton_right.← haC).subset_right_of_subset_union hCIa))
  ⟩

/-- If two matroids have the same ground sets and sets of circuits, then they are equal. -/
theorem Matroid.ext_circuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (hC : ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C) :
    M₁ = M₂ := by
  apply Matroid.ext_indep hE
  intro I hI₁
  have hI₂ : I ⊆ M₂.E := hE ▸ hI₁
  simp only [Matroid.indep_iff_not_dep, hI₁, hI₂, Matroid.dep_iff_has_circuit, true_and, and_true, not_iff_not]
  constructor <;> intro ⟨C, hMC, hCI⟩ <;> have hCE := hCI.trans hI₁ <;> refine ⟨C, ?_, hCI⟩
  · rwa [hC _ hCE] at hMC
  · rwa [hC _ hCE]

/- Start of proof attempt -/
lemma round1_forward_direction (M₁ M₂ : Matroid α) :
    M₁ = M₂ → M₁.E = M₂.E ∧ ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C := by
  intro h
  constructor
  · -- Prove `M₁.E = M₂.E`
    rw [h]
  · -- Prove `∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C`
    intro C hC
    rw [h]

lemma round1_backward_direction (M₁ M₂ : Matroid α) :
    (M₁.E = M₂.E ∧ ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C) → M₁ = M₂ := by
  rintro ⟨hE, hC⟩
  exact Matroid.ext_circuit hE hC

/-- Two matroids are equal iff they have the same ground sets and sets of circuits. -/
theorem Matroid.ext_iff_circuit (M₁ M₂ : Matroid α) :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C ⊆ M₁.E, M₁.Circuit C ↔ M₂.Circuit C  := by

  constructor
  · exact round1_forward_direction M₁ M₂
  · exact round1_backward_direction M₁ M₂
