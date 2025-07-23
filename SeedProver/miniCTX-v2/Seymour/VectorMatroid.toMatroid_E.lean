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

/- Start of proof attempt -/
lemma round1_VectorMatroid_toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = Set.range M.emb := by
  simp [VectorMatroid.toMatroid, VectorMatroid.toIndepMatroid, VectorMatroid.E]
  <;> aesop

theorem VectorMatroid.toMatroid_E (M : VectorMatroid α R) : M.toMatroid.E = Set.range M.emb  := by

  exact round1_VectorMatroid_toMatroid_E M
