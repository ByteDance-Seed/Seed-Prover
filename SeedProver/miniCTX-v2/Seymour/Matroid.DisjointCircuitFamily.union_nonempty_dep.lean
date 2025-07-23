-- In Seymour/Seymour/Matroid/Notions/DisjointCircuitFamily.lean

import Seymour.Matroid.Notions.Circuit

variable {α : Type}

section DisjointCircuitFamily

/-- Family of disjoint circuits of matroid `M`. -/
structure Matroid.DisjointCircuitFamily (M : Matroid α) where
  /-- Indexing set -/
  ι : Set α
  -- question: upgrade from indexing by Set α to indexing by Sort v (see Set.iUnion in Mathlib.Order.SetNotation)?
  -- note: if we know that `C` is a disjoint union of circuits of `M`,
  -- then wlog we can choose `ι` to be set of representatives of those circuits
  /-- Set family indexed by `ι` -/
  F : ι → Set α
  /-- All sets in family are circuits in `M` -/
  AllCircuits : ∀ x : ι, M.Circuit (F x)
  /-- All sets in family are disjoint -/
  AllDisjoint : ∀ x y : ι, x ≠ y → F x ⫗ F y

/-- Shorthand for union of sets in `M.DisjointCircuitFamily`. -/
def Matroid.DisjointCircuitFamily.union {M : Matroid α} (F : M.DisjointCircuitFamily) : Set α :=
  Set.iUnion F.F

/-- Every element in `M.DisjointCircuitFamily` is subset of ground set. -/
lemma Matroid.DisjointCircuitFamily.mem_subset_ground {M : Matroid α} (F : M.DisjointCircuitFamily) (x : F.ι) :
    F.F x ⊆ M.E :=
  (F.AllCircuits x).subset_ground

/-- Union of sets in `M.DisjointCircuitFamily` is subset of ground set. -/
lemma Matroid.DisjointCircuitFamily.union_subset_ground {M : Matroid α} (F : M.DisjointCircuitFamily) :
    F.union ⊆ M.E := by
  simp only [Matroid.DisjointCircuitFamily.union, Set.iUnion_coe_set, Set.iUnion_subset_iff]
  exact fun i hi => mem_subset_ground F ⟨i, hi⟩

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.DisjointCircuitFamily.union_indep_empty {M : Matroid α} (F : M.DisjointCircuitFamily) (hMF : M.Indep F.union):
    F.union = ∅ := by
  by_contra
  obtain ⟨x, -⟩ : ∃ x : F.ι.Elem, (F.F x).Nonempty
  · by_contra!
    simp_all only [Matroid.DisjointCircuitFamily.union, Set.iUnion_coe_set, Set.iUnion_empty, not_true_eq_false]
  exact (F.AllCircuits x).left.not_indep (hMF.subset (Set.subset_iUnion_of_subset x Set.Subset.rfl))

/- Start of proof attempt -/
lemma round1_union_nonempty_dep {M : Matroid α} (F : M.DisjointCircuitFamily) (hF : F.union.Nonempty) :
    M.Dep F.union := by
  by_contra h
  have h4 : F.union ⊆ M.E := Matroid.DisjointCircuitFamily.union_subset_ground F
  have h1 : M.Indep F.union := by
    by_contra h11
    have h5 : F.union ⊆ M.E ∧ ¬ M.Indep F.union := ⟨h4, h11⟩
    have h6 : M.Dep F.union := by tauto
    contradiction
  have h2 : F.union = ∅ := Matroid.DisjointCircuitFamily.union_indep_empty F h1
  rw [h2] at hF
  simp at hF
  <;> contradiction

/-- Nonempty union of disjoint circuits is dependent. -/
theorem Matroid.DisjointCircuitFamily.union_nonempty_dep {M : Matroid α} (F : M.DisjointCircuitFamily) (hF : F.union.Nonempty) :
    M.Dep F.union  := by

  exact round1_union_nonempty_dep F hF
