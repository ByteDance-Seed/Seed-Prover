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

/- Start of proof attempt -/
lemma round1_distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  have h1 : ∀ (s : Set ℝ), volume ((x : ℝ) • s) = (distribHaarChar ℝ x) * volume s := by
    intro s
    exact?
  have h2 : ∀ (s : Set ℝ), volume ((x : ℝ) • s) = ‖(x : ℝ)‖₊ * volume s := by
    intro s
    exact Real.volume_real_smul (x : ℝ) s
  have h1' : volume ((x : ℝ) • (Set.Icc (0 : ℝ) 1)) = (distribHaarChar ℝ x) * volume (Set.Icc (0 : ℝ) 1) := by
    specialize h1 (Set.Icc (0 : ℝ) 1)
    exact h1
  have h2' : volume ((x : ℝ) • (Set.Icc (0 : ℝ) 1)) = ‖(x : ℝ)‖₊ * volume (Set.Icc (0 : ℝ) 1) := by
    specialize h2 (Set.Icc (0 : ℝ) 1)
    exact h2
  have h4 : (distribHaarChar ℝ x) * volume (Set.Icc (0 : ℝ) 1) = ‖(x : ℝ)‖₊ * volume (Set.Icc (0 : ℝ) 1) := by
    rw [h1'.symm]
    exact h2'
  have h5 : volume (Set.Icc (0 : ℝ) 1) = 1 := by
    simp [Real.volume_Icc]
    <;> norm_num
  rw [h5] at h4
  simp at h4 ⊢
  <;> aesop

/-- The distributive Haar character of the action of `ℝˣ` on `ℝ` is the usual norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℝ` and `s : Set ℝ`.
See `Real.volume_real_smul`. -/
theorem distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊  := by

  exact round1_distribHaarChar_real x
