-- In Seymour/Seymour/ForMathlib/MatrixTU.lean

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.ForMathlib.Basic
import Seymour.ForMathlib.FunctionDecompose

variable {X₁ X₂ Z R : Type}

lemma Matrix.IsTotallyUnimodular.comp_rows [CommRing R] {A : Matrix X₁ X₂ R}
    (hA : A.IsTotallyUnimodular) (e : Z → X₁) :
    Matrix.IsTotallyUnimodular (A ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  exact hA k (e ∘ f) g

/- Start of proof attempt -/
lemma round1_Matrix_IsTotallyUnimodular_comp_cols [CommRing R] {A : Matrix X₁ X₂ R}
    (hA : A.IsTotallyUnimodular) (e : Z → X₂) :
    Matrix.IsTotallyUnimodular (A · ∘ e) := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  have h1 := hA k f (e ∘ g)
  simpa using h1

theorem Matrix.IsTotallyUnimodular.comp_cols [CommRing R] {A : Matrix X₁ X₂ R}
    (hA : A.IsTotallyUnimodular) (e : Z → X₂) :
    Matrix.IsTotallyUnimodular (A · ∘ e)  := by

  exact round1_Matrix_IsTotallyUnimodular_comp_cols hA e
