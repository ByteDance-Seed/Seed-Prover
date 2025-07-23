-- In Seymour/Seymour/ForMathlib/MatrixTU.lean

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Seymour.ForMathlib.Basic
import Seymour.ForMathlib.FunctionDecompose

variable {X₁ X₂ Z R : Type}

/- Start of proof attempt -/
lemma round1_h1 [CommRing R] {A : Matrix X₁ X₂ R} (hA : A.IsTotallyUnimodular) (e : Z → X₁) :
    (A.submatrix (fun i : Z => e i) (fun j : X₂ => j)).IsTotallyUnimodular := by
  exact hA.submatrix _ _

lemma round1_h2 (A : Matrix X₁ X₂ R) (e : Z → X₁) :
    (A ∘ e) = A.submatrix (fun i : Z => e i) (fun j : X₂ => j) := by
  ext i j
  <;> simp

theorem Matrix.IsTotallyUnimodular.comp_rows [CommRing R] {A : Matrix X₁ X₂ R}
    (hA : A.IsTotallyUnimodular) (e : Z → X₁) :
    Matrix.IsTotallyUnimodular (A ∘ e)  := by

  have h1 : (A.submatrix (fun i : Z => e i) (fun j : X₂ => j)).IsTotallyUnimodular := by
    exact round1_h1 hA e
  have h2 : (A ∘ e) = A.submatrix (fun i : Z => e i) (fun j : X₂ => j) := by
    exact round1_h2 A e
  rw [h2]
  exact h1
