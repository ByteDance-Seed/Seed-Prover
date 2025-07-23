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


/- Start of proof attempt -/
lemma round1_h2 (x : ℝ)
  (s : Set ℝ):
  volume (x • s) = ENNReal.ofReal (|x|) * volume s := by
  have h21 : volume (x • s) = ENNReal.ofReal (|x|) * volume s := by
    simp [MeasureTheory.Measure.addHaar_smul]
    <;> ring_nf <;> simp_all [abs_mul] <;> ring
  exact h21

lemma round1_h10 (x : ℝ):
  ∀ (r : NNReal), ENNReal.ofReal (r : ℝ) = (r : ENNReal) := by
  intro r
  simp

lemma round1_h11 (x : ℝ):
  (‖x‖₊ : ℝ) = |x| := by
  simp [Real.coe_toNNReal, abs_nonneg]
  <;>
  ring

lemma round1_h12 (x : ℝ)
  (s : Set ℝ)
  (h11 : (‖x‖₊ : ℝ) = |x|):
  ENNReal.ofReal (|x|) = ENNReal.ofReal (‖x‖₊ : ℝ) := by
  rw [h11]
  <;> rfl

lemma round1_h13 (x : ℝ)
  (h10 : ∀ (r : NNReal), ENNReal.ofReal (r : ℝ) = (r : ENNReal)):
  ENNReal.ofReal (‖x‖₊ : ℝ) = (‖x‖₊ : ENNReal) := by
  exact h10 ‖x‖₊

lemma round1_h14 (x : ℝ)
  (s : Set ℝ)
  (h12 : ENNReal.ofReal (|x|) = ENNReal.ofReal (‖x‖₊ : ℝ))
  (h13 : ENNReal.ofReal (‖x‖₊ : ℝ) = (‖x‖₊ : ENNReal)):
  ENNReal.ofReal (|x|) = (‖x‖₊ : ENNReal) := by
  rw [h12, h13]
  <;> rfl

theorem Real.volume_real_smul (x : ℝ) (s : Set ℝ) : volume (x • s) = ‖x‖₊ * volume s  := by

  have h2 : volume (x • s) = ENNReal.ofReal (|x|) * volume s := round1_h2 x s
  have h10 : ∀ (r : NNReal), ENNReal.ofReal (r : ℝ) = (r : ENNReal) := round1_h10 x
  have h11 : (‖x‖₊ : ℝ) = |x| := round1_h11 x
  have h12 : ENNReal.ofReal (|x|) = ENNReal.ofReal (‖x‖₊ : ℝ) := round1_h12 x s h11
  have h13 : ENNReal.ofReal (‖x‖₊ : ℝ) = (‖x‖₊ : ENNReal) := round1_h13 x h10
  have h14 : ENNReal.ofReal (|x|) = (‖x‖₊ : ENNReal) := round1_h14 x s h12 h13
  calc
    volume (x • s) = ENNReal.ofReal (|x|) * volume s := h2
    _ = (‖x‖₊ : ENNReal) * volume s := by rw [h14]
    _ = ‖x‖₊ * volume s := by simp
