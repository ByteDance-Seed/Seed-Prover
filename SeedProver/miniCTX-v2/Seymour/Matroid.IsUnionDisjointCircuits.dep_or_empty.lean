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

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.DisjointCircuitFamily.union_nonempty_dep {M : Matroid α} (F : M.DisjointCircuitFamily) (hF : F.union.Nonempty) :
    M.Dep F.union := by
  by_contra contr
  exact Set.not_nonempty_empty (F.union_indep_empty (Matroid.indep_of_not_dep contr F.union_subset_ground) ▸ hF)

/-- Union of disjoint circuits is either dependent or empty. -/
lemma Matroid.DisjointCircuitFamily.dep_or_empty {M : Matroid α} (F : M.DisjointCircuitFamily) :
    M.Dep F.union ∨ F.union = ∅ := by
  if hMF : M.Indep F.union then
    exact Or.inr (F.union_indep_empty hMF)
  else
    exact Or.inl ⟨hMF, F.union_subset_ground⟩

/-- Empty family of disjoint circuits. -/
def Matroid.emptyDisjointCircuitFamily (M : Matroid α) :
    M.DisjointCircuitFamily where
  ι := ∅
  F _ := ∅
  AllCircuits x := x.property.elim
  AllDisjoint x := x.property.elim

/-- Union of sets in empty family is empty. -/
lemma Matroid.emptyDisjointCircuitFamily_union (M : Matroid α) :
    M.emptyDisjointCircuitFamily.union = ∅ :=
  Set.iUnion_empty

/-- Family of one circuit, indexed by one element --- that circuit. -/
def Matroid.Circuit.singleDisjointCircuitFamily {M : Matroid α} {C : Set α} (hC : M.Circuit C) (p : α) :
    M.DisjointCircuitFamily where
  ι := {p}
  F _ := C
  AllCircuits _ := hC
  AllDisjoint x y hxy := ((x.property ▸ y.property ▸ Subtype.coe_ne_coe.← hxy) rfl).elim

/-- Union of sets in family of one circuit is that circuit. -/
lemma Matroid.Circuit.singleDisjointCircuitFamily_union {M : Matroid α} {C : Set α} (hC : M.Circuit C) (p : α) :
    (hC.singleDisjointCircuitFamily p).union = C := by
  simp only [Matroid.Circuit.singleDisjointCircuitFamily, Matroid.DisjointCircuitFamily.union, Set.iUnion_coe_set,
    Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]

end DisjointCircuitFamily

section UnionDisjointCircuits

/-- Set `C` can be represented as disjoint union of circuits of `M`. -/
def Matroid.IsUnionDisjointCircuits (M : Matroid α) (C : Set α) : Prop :=
  ∃ F : M.DisjointCircuitFamily, F.union = C

/-- Empty set is disjoint union of circuits. -/
lemma Matroid.emptyUnionDisjointCircuits (M : Matroid α) :
    M.IsUnionDisjointCircuits ∅ :=
  ⟨M.emptyDisjointCircuitFamily, M.emptyDisjointCircuitFamily_union⟩

/-- If union of disjoint circuits is independent, then it is empty. -/
lemma Matroid.IsUnionDisjointCircuits.indep_empty {M : Matroid α} {X : Set α}
    (hMX : M.IsUnionDisjointCircuits X) (hMX' : M.Indep X) :
    X = ∅ :=
  have ⟨F, hXF⟩ := hMX
  F.union_indep_empty (hXF ▸ hMX') ▸ hXF.symm

/-- Nonempty union of disjoint circuits is dependent. -/
lemma Matroid.IsUnionDisjointCircuits.nonempty_dep {M : Matroid α} {X : Set α}
    (hMX : M.IsUnionDisjointCircuits X) (hX : X.Nonempty) :
    M.Dep X :=
  have ⟨F, hXF⟩ := hMX
  hXF ▸ F.union_nonempty_dep (hXF ▸ hX)

/- Start of proof attempt -/
lemma round1_IsUnionDisjointCircuits_dep_or_empty {M : Matroid α} {X : Set α} (hMX : M.IsUnionDisjointCircuits X) :
    M.Dep X ∨ X = ∅ := by
  rcases hMX with ⟨F, hXF⟩
  have h2 : M.Dep F.union ∨ F.union = ∅ := Matroid.DisjointCircuitFamily.dep_or_empty F
  rw [hXF] at h2
  exact h2

/-- Union of disjoint circuits is either dependent or empty. -/
theorem Matroid.IsUnionDisjointCircuits.dep_or_empty {M : Matroid α} {X : Set α} (hMX : M.IsUnionDisjointCircuits X) :
    M.Dep X ∨ X = ∅  := by

  exact round1_IsUnionDisjointCircuits_dep_or_empty hMX
