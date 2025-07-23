-- In FLT/FLT/Mathlib/NumberTheory/NumberField/Basic.lean

import Mathlib.NumberTheory.NumberField.Basic

open scoped NumberField

-- Mathlib PR #20544

/- Start of proof attempt -/
lemma round1_h1 :
  ∀ (n : ℤ), (Rat.ringOfIntegersEquiv.symm n : ℚ) = (n : ℚ) := by
  intro n
  simp [Rat.ringOfIntegersEquiv]
  <;> norm_cast

lemma round1_h2 (z : 𝓞 ℚ)
  (h1 : ∀ (n : ℤ), (Rat.ringOfIntegersEquiv.symm n : ℚ) = (n : ℚ)):
  (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv z) : ℚ) = ((Rat.ringOfIntegersEquiv z) : ℚ) := by
  specialize h1 (Rat.ringOfIntegersEquiv z)
  simpa using h1

lemma round1_h3 (z : 𝓞 ℚ):
  Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv z) = z := by
  exact?

theorem Rat.ringOfIntegersEquiv_eq_algebraMap (z : 𝓞 ℚ) :
    (Rat.ringOfIntegersEquiv z : ℚ) = algebraMap (𝓞 ℚ) ℚ z  := by

  have h1 : ∀ (n : ℤ), (Rat.ringOfIntegersEquiv.symm n : ℚ) = (n : ℚ) := by
    exact round1_h1
  have h2 : (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv z) : ℚ) = ((Rat.ringOfIntegersEquiv z) : ℚ) := by
    exact round1_h2 z h1
  have h3 : Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv z) = z := by
    exact round1_h3 z
  have h4 : (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv z) : ℚ) = (z : ℚ) := by
    rw [h3]
    <;> simp
  have h5 : ((Rat.ringOfIntegersEquiv z) : ℚ) = (z : ℚ) := by linarith
  norm_cast at h5 ⊢
  <;> simpa using h5.symm
