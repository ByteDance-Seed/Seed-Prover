-- In Seymour/Seymour/Matroid/Classes/Graphic.lean

import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Matroid.Dual

import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Regular

section IsGraphic

/-- todo: desc -/
-- oriented incidence matrix of some graph, i.e.:
-- * one row for each vertex, and one column for each edge
-- * in each column, either: 1x `+1`, 1x `-1`, and `0` elsewhere
-- todo: unit and zero columns representing loops
def Matrix.IsGraphic {m n : Type} (A : Matrix m n ℚ) : Prop :=
  ∀ y : n, ∃ x₁ x₂ : m, A x₁ y = 1 ∧ A x₂ y = -1 ∧ ∀ x : m, x ≠ x₁ → x ≠ x₂ → A x y = 0

/-- Matroid is graphic iff it is represented by an incidence matrix of a graph. -/
def Matroid.IsGraphic {α : Type} [DecidableEq α] (M : Matroid α) : Prop :=
  ∃ X Y : Type, ∃ _ : Fintype Y, ∃ A : Matrix X Y ℚ, M.IsRepresentedBy A ∧ A.IsGraphic

/-- Graphic matroid can be represented only by a TU matrix. -/
lemma Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic {α X Y : Type} [DecidableEq α] {M : Matroid α}
    [Fintype Y] {A : Matrix X Y ℚ} (hMA : M.IsRepresentedBy A) (hA : A.IsGraphic) :
    A.IsTotallyUnimodular := by
  sorry

/- Start of proof attempt -/
lemma round1_h2 (α : Type)
  [DecidableEq α]
  (M : Matroid α)
  (hM : M.IsGraphic):
  M.HasTuRepr := by
  rcases hM with ⟨X, Y, hFintypeY, A, hMA, hA⟩
  have hA_tu : A.IsTotallyUnimodular := by
    exact Matroid.IsRepresentedBy.isTotallyUnimodular_of_isGraphic hMA hA
  refine' ⟨X, Y, hFintypeY, A, hA_tu, hMA⟩

/-- Graphic matroid is regular. -/
theorem Matroid.IsGraphic.isRegular {α : Type} [DecidableEq α] {M : Matroid α} (hM : M.IsGraphic) :
    M.IsRegular  := by

  have h2 : M.HasTuRepr := by
    exact round1_h2 α M hM
  have h3 : M.IsRegular ↔ M.HasTuRepr := Matroid.isRegular_iff_hasTuRepr M
  exact h3.mpr h2
