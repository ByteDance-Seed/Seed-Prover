-- In FLT/FLT/Mathlib/LinearAlgebra/Determinant.lean

import Mathlib.LinearAlgebra.Determinant

namespace LinearMap
variable {R : Type*} [CommRing R]

/- Start of proof attempt -/
lemma round1_det_mul (a : R) : (mul R R a).det = a := by
  simp [mul_apply]

theorem det_mul (a : R) : (mul R R a).det = a  := by

  exact round1_det_mul a
