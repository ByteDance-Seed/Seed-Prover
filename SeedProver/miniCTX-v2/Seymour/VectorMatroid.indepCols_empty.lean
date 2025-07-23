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

/- Start of proof attempt -/
lemma round1_indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅ := by
  refine ⟨by simp,?_⟩
  simp [linearIndependent_empty_type]
  <;> aesop

/-- Empty set is independent. -/
theorem VectorMatroid.indepCols_empty (M : VectorMatroid α R) :
    M.IndepCols ∅  := by

  exact round1_indepCols_empty M
