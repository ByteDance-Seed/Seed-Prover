-- In FLT/FLT/HaarMeasure/DistribHaarChar/RealComplex.lean

/-
Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Javier López-Contreras
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import FLT.HaarMeasure.DistribHaarChar.Basic
import FLT.Mathlib.LinearAlgebra.Determinant

/-!
# The distributive Haar characters of `ℝ` and `ℂ`

This file computes `distribHaarChar` in the case of the actions of `ℝˣ` on `ℝ` and of `ℂˣ` on `ℂ`.

This lets us know what `volume (x • s)` is in terms of `‖x‖` and `volume s`, when `x` is a
real/complex number and `s` is a set of reals/complex numbers.

## Main declarations

* `distribHaarChar_real`: `distribHaarChar ℝ` is the usual norm on `ℝ`.
* `distribHaarChar_complex`: `distribHaarChar ℂ` is the usual norm on `ℂ` squared.
* `Real.volume_real_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℝ` and `s : Set ℝ`.
* `Complex.volume_complex_smul`: `volume (z • s) = ‖z‖₊ ^ 2 * volume s` for all `z : ℂ` and
  `s : Set ℂ`.
-/

open Real Complex MeasureTheory Measure Set
open scoped Pointwise

lemma Real.volume_real_smul (x : ℝ) (s : Set ℝ) : volume (x • s) = ‖x‖₊ * volume s := by
  simp [← enorm_eq_ofReal_abs, enorm_eq_nnnorm]

/-- The distributive Haar character of the action of `ℝˣ` on `ℝ` is the usual norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℝ` and `s : Set ℝ`.
See `Real.volume_real_smul`. -/
lemma distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ :=
  -- We compute that `volume (x • [0, 1]) = ‖x‖₊ * volume [0, 1]`.
  distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp).ne' isCompact_Icc.measure_ne_top
      (Real.volume_real_smul ..)

/-- The distributive Haar character of the action of `ℂˣ` on `ℂ` is the usual norm squared.

This means that `volume (z • s) = ‖z‖ ^ 2 * volume s` for all `z : ℂ` and `s : Set ℂ`.
See `Complex.volume_complex_smul`. -/
lemma distribHaarChar_complex (z : ℂˣ) : distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  -- We compute that `volume (x • ([0, 1] × [0, 1])) = ‖x‖₊ ^ 2 * volume ([0, 1] × [0, 1])`.
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1 ×ℂ Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp [interior_reProdIm]).ne'
    (isCompact_Icc.reProdIm isCompact_Icc).measure_ne_top ?_
  -- The determinant of left multiplication by `z⁻¹` as a `ℝ`-linear map is `‖z‖₊ ^ (-2)`.
  have key : ((LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ).det = ‖z.val‖₊ ^ (-2 : ℤ) := by
    refine Complex.ofReal_injective ?_
    rw [LinearMap.det_restrictScalars]
    simp [Algebra.norm_complex_apply, normSq_eq_norm_sq, zpow_ofNat]
  -- Massaging, we find the result.
  convert addHaar_preimage_linearMap (E := ℂ) volume
    (f := (LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ) _ _ using 2
  · simpa [LinearMap.mul, LinearMap.mk₂, LinearMap.mk₂', LinearMap.mk₂'ₛₗ, Units.smul_def, eq_comm]
      using preimage_smul_inv z (Icc 0 1 ×ℂ Icc 0 1)
  · simp [key, ofReal_norm_eq_enorm, ← Complex.norm_eq_abs, ENNReal.ofReal_pow, zpow_ofNat]; rfl
  · simp [key, zpow_ofNat]

/- Start of proof attempt -/
lemma round1_case_z_eq_0 (s : Set ℂ) : volume ((0 : ℂ) • s) = 0 := by
  have h13 : (0 : ℂ) • s ⊆ ({0} : Set ℂ) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    simp
  have h15 : volume ({0} : Set ℂ) = 0 := by
    simp [MeasureTheory.measure_singleton]
  exact MeasureTheory.measure_mono_null h13 h15

lemma round1_case_z_ne_0 (z : ℂ) (hz : z ≠ 0) (s : Set ℂ) : volume (z • s) = (‖z‖₊ : ENNReal) ^ 2 * volume s := by
  have h21 : (Units.mk0 z hz : ℂ) = z := by simp
  have h22 : (Units.mk0 z hz : ℂ) • s = z • s := by
    rw [h21]
  have h23 : volume ((Units.mk0 z hz : ℂ) • s) = volume (z • s) := by rw [h22]
  have h24 : volume ((Units.mk0 z hz : ℂ) • s) = distribHaarChar ℂ (Units.mk0 z hz) * volume s := by
    exact?
  have h26 : distribHaarChar ℂ (Units.mk0 z hz) = ↑(‖(Units.mk0 z hz : ℂ)‖₊ ^ 2) := by
    rw [distribHaarChar_complex (Units.mk0 z hz)]
    <;> simp
  have h27 : (Units.mk0 z hz : ℂ) = z := by simp
  have h28 : distribHaarChar ℂ (Units.mk0 z hz) = ↑(‖z‖₊ ^ 2) := by
    rw [h26, h27]
    <;> simp
  have h29 : volume ((Units.mk0 z hz : ℂ) • s) = ↑(‖z‖₊ ^ 2) * volume s := by
    rw [h24, h28]
  have h30 : ∀ (a : NNReal), (↑(a ^ 2) : ENNReal) = (↑a : ENNReal) ^ 2 := by
    intro a
    simp [ENNReal.coe_pow]
    <;> ring
  have h31 : (↑(‖z‖₊ ^ 2) : ENNReal) = (↑‖z‖₊ : ENNReal) ^ 2 := by
    exact h30 ‖z‖₊
  have h32 : volume ((Units.mk0 z hz : ℂ) • s) = (↑‖z‖₊ : ENNReal) ^ 2 * volume s := by
    rw [h29, h31]
  have h33 : volume (z • s) = volume ((Units.mk0 z hz : ℂ) • s) := by
    rw [h23]
    <;> ring
  have h34 : volume (z • s) = (↑‖z‖₊ : ENNReal) ^ 2 * volume s := by
    rw [h33, h32]
  exact h34

theorem Complex.volume_complex_smul (z : ℂ) (s : Set ℂ) : volume (z • s) = ‖z‖₊ ^ 2 * volume s  := by

  by_cases hz : z = 0
  · -- Case 1: z = 0
    have h18 : volume ((0 : ℂ) • s) = 0 := round1_case_z_eq_0 s
    rw [hz]
    simp [h18]
    <;> ring
  · -- Case 2: z ≠ 0
    have h32 : volume (z • s) = (‖z‖₊ : ENNReal) ^ 2 * volume s := round1_case_z_ne_0 z hz s
    simpa using h32
