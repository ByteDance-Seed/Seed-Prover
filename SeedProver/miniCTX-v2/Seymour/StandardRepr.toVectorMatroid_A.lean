-- In Seymour/Seymour/Matroid/Constructors/VectorMatroid.lean

import Mathlib.Data.Matroid.IndepAxioms
import Mathlib.Data.Matroid.Dual

import Seymour.Basic

section Definition

/-- Vector matroid `M[A]` of matrix `A`. -/
structure VectorMatroid (α R : Type) where
  /-- Row indices. -/
  X : Type
  /-- Column indices. -/
  Y : Type
  /-- Full representation matrix. -/
  A : Matrix X Y R
  /-- The matrix has finite number of columns. -/
  finY : Fintype Y
  /-- How the columns correspond to the elements of the resulting matroid. -/
  emb : Y ↪ α

attribute [instance] VectorMatroid.finY

open scoped Matrix

variable {α R : Type} [DecidableEq α] [Semiring R]

def VectorMatroid.E (M : VectorMatroid α R) : Set α :=
  Set.range M.emb

/-- A set `S` is independent in `M[A]` iff
    `S ⊆ Y` and `S` corresponds to a linearly independent submultiset of columns in `A`. -/
def VectorMatroid.IndepCols (M : VectorMatroid α R) (S : Set α) : Prop :=
  ∃ hS : S ⊆ M.E, LinearIndependent R (fun s : S => (M.A · (M.emb.invOfMemRange (hS.elem s))))

/-- A set `S` is independent in `M[A]` iff
    `S ⊆ Y` and the submatrix that contains only columns of `S` has linearly independent columns. -/
lemma VectorMatroid.indepCols_iff_submatrix (M : VectorMatroid α R) (S : Set α) :
    M.IndepCols S ↔ ∃ hS : S ⊆ M.E, LinearIndependent R (M.A.submatrix id (M.emb.invOfMemRange ∘ hS.elem))ᵀ := by
  rfl

/-- Empty set is independent. -/
theorem VectorMatroid.indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ :=
  ⟨M.E.empty_subset, linearIndependent_empty_type⟩

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem VectorMatroid.indepCols_subset (M : VectorMatroid α R) (I J : Set α) (hMJ : M.IndepCols J) (hIJ : I ⊆ J) :
    M.IndepCols I :=
  have ⟨hJ, hM⟩ := hMJ
  ⟨hIJ.trans hJ, hM.comp hIJ.elem hIJ.elem_injective⟩

/-- A non-maximal linearly independent set of columns can be augmented with another linearly independent column. -/
theorem VectorMatroid.indepCols_aug (M : VectorMatroid α R) (I J : Set α)
    (hMI : M.IndepCols I) (hMI' : ¬Maximal M.IndepCols I) (hMJ : Maximal M.IndepCols J) :
    ∃ x ∈ J \ I, M.IndepCols (x ᕃ I) := by
  by_contra! non_aug
  rw [Maximal] at hMI'
  push_neg at hMI'
  obtain ⟨hI, I_indep⟩ := hMI
  obtain ⟨⟨hJ, J_indep⟩, hJ'⟩ := hMJ

  -- let I' : Set M.E := { x : M.E.Elem | x.val ∈ I }
  -- let J' : Set M.E := { x : M.E.Elem | x.val ∈ J }
  -- let Iᵥ : Set (M.X → R) := M.Aᵀ '' I'
  -- let Jᵥ : Set (M.X → R) := M.Aᵀ '' J'
  -- let Iₛ : Submodule R (M.X → R) := Submodule.span R Iᵥ
  -- let Jₛ : Submodule R (M.X → R) := Submodule.span R Jᵥ

  -- have Jᵥ_ss_Iₛ : Jᵥ ⊆ Iₛ
  -- · intro v ⟨x, hxJ, hxv⟩
  --   by_cases hvI : v ∈ Iᵥ
  --   · aesop
  --   · have x_in_J : ↑x ∈ J := hxJ
  --     have x_ni_I : ↑x ∉ I := by aesop
  --     have x_in_JwoI : ↑x ∈ J \ I := Set.mem_diff_of_mem x_in_J x_ni_I
  --     have hMxI : ¬M.IndepCols (↑x ᕃ I) := non_aug ↑x x_in_JwoI
  --     sorry
  -- have Iᵥ_ss_Jₛ : Iᵥ ⊆ Jₛ
  -- · intro v ⟨x, hxI, hxv⟩
  --   have hMxJ : M.IndepCols (↑x ᕃ J)
  --   · have hxJ : (↑x ᕃ J) ⊆ M.E := Set.insert_subset (hI hxI) hJ
  --     have hvJ : (M.A.submatrix id hxJ.elem)ᵀ '' Set.univ = v ᕃ Jᵥ
  --     · sorry
  --     sorry
  --   have v_in_Jᵥ : v ∈ Jᵥ := by aesop
  --   exact Set.mem_of_mem_of_subset v_in_Jᵥ Submodule.subset_span
  -- have Jₛ_le_Iₛ : Jₛ ≤ Iₛ := Submodule.span_le.← Jᵥ_ss_Iₛ
  -- have Iₛ_le_Jₛ : Iₛ ≤ Jₛ := Submodule.span_le.← Iᵥ_ss_Jₛ
  -- have Iₛ_eq_Jₛ : Iₛ = Jₛ := Submodule.span_eq_span Iᵥ_ss_Jₛ Jᵥ_ss_Iₛ
  -- clear Jᵥ_ss_Iₛ Iᵥ_ss_Jₛ Jₛ_le_Iₛ Iₛ_le_Jₛ
  sorry

/-- Every set of columns contains a maximal independent subset of columns. -/
theorem VectorMatroid.indepCols_maximal (M : VectorMatroid α R) (S : Set α) :
    Matroid.ExistsMaximalSubsetProperty M.IndepCols S := by
  sorry

/-- Vector matroid expressed as `IndepMatroid`. -/
def VectorMatroid.toIndepMatroid (M : VectorMatroid α R) : IndepMatroid α where
  E := M.E
  Indep := M.IndepCols
  indep_empty := M.indepCols_empty
  indep_subset := M.indepCols_subset
  indep_aug := M.indepCols_aug
  indep_maximal S _ := M.indepCols_maximal S
  subset_ground _ := Exists.choose

end Definition

section API

variable {α R : Type} [DecidableEq α] [Semiring R]

/-- Vector matroid converted to `Matroid`. -/
def VectorMatroid.toMatroid (M : VectorMatroid α R) : Matroid α :=
  M.toIndepMatroid.matroid

@[simp]
lemma VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = Set.range M.emb :=
  rfl

@[simp]
lemma VectorMatroid.toMatroid_indep (M : VectorMatroid α R) : M.toMatroid.Indep = M.IndepCols :=
  rfl

end API

section EquivalentTransformations

-- todo: section 2.2/6.3 from Oxley: Different matroid representations
-- the following operations on `A` do not change `M[A]`:
-- 2.2.1 Interchange two rows.  <-- can be generalized for free to reindexing of rows
-- 2.2.2 Multiply a row by non-zero.
-- 2.2.3 Replace a row by the sum of that row and another.
-- 2.2.4 Adjoin or remove a zero row.
-- 2.2.5 Interchange two columns (the labels moving with the columns).  <-- trivial in lean: indices are labeled and unordered
-- 2.2.6 Multiply a column by a non-zero member of F.
-- 2.2.7 Replace each matrix entry by its image under some automorphism of F.

-- todo: if A is non-zero, it can be reduced to [I | B] by a sequence of operations of types 2.2.1-2.2.5

end EquivalentTransformations

section StandardRepr

/-- Standard matrix representation of a vector matroid.
Not in sync with `Matroid.Operations.MatrixSums.Basic/StandardRepresentation` currently! -/
structure StandardRepr (α R : Type) where
  /-- Row indices. -/
  X : Type
  /-- Column indices. -/
  Y : Type
  /-- Standard representation matrix. -/
  B : Matrix X Y R
  /-- The matrix has finite number of rows and columns. -/
  fntp : Fintype (X ⊕ Y) -- TODO two things?
  /-- The computer can distinguish the rows from each other. -/
  deceqX : DecidableEq X
  /-- The computer can distinguish the cols from each other. -/
  deceqY : DecidableEq Y
  /-- How the rows and columns correspond to the elements of the resulting matroid. -/
  emb : X ⊕ Y ↪ α

attribute [instance] StandardRepr.fntp
attribute [instance] StandardRepr.deceqX
attribute [instance] StandardRepr.deceqY

variable {α R : Type} [Ring R]

/-- Vector matroid constructed from standard representation. -/
def StandardRepr.toVectorMatroid (S : StandardRepr α R) : VectorMatroid α R :=
  ⟨S.X, S.X ⊕ S.Y, Matrix.fromCols 1 S.B, S.fntp, S.emb⟩

/-- Ground set of a vector matroid is union of row and column index sets of its standard matrix representation. -/
@[simp]
lemma StandardRepr.toVectorMatroid_E (S : StandardRepr α R) [DecidableEq α] :
    S.toVectorMatroid.toMatroid.E = Set.range S.emb :=
  rfl

/- Start of proof attempt -/
lemma round1_StandardRepr.toVectorMatroid_A (S : StandardRepr α R) :
    S.toVectorMatroid.A = Matrix.fromCols 1 S.B := by
  simp [StandardRepr.toVectorMatroid]
  <;> rfl

/-- Full representation matrix of vector matroid is `[1 | B]`. -/
theorem StandardRepr.toVectorMatroid_A (S : StandardRepr α R) :
    S.toVectorMatroid.A = Matrix.fromCols 1 S.B  := by

  exact round1_StandardRepr.toVectorMatroid_A S
