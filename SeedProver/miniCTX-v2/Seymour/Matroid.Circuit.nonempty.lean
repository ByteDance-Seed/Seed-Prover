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

/- Start of proof attempt -/
lemma round1_nonempty {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty := by
  by_contra h
  have h1 : C = ∅ := by
    simp [Set.nonempty_iff_ne_empty] at h
    <;> tauto
  have h2 : M.Circuit ∅ := by
    rw [h1] at hC
    exact hC
  exact Matroid.Circuit.not_empty h2

/-- Every circuit is nonempty. -/
theorem Matroid.Circuit.nonempty {M : Matroid α} {C : Set α} (hC : M.Circuit C) : C.Nonempty  := by

  exact round1_nonempty hC
