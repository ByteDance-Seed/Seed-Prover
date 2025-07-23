-- In FLT/FLT/Mathlib/Analysis/Normed/Ring/WithAbs.lean

import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.NumberTheory.NumberField.Basic

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

/- Start of proof attempt -/
lemma round1_h1 (K : Type*) [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] (w : AbsoluteValue L ℝ)
  (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x):
  ∀ (x : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x‖ = ‖x‖ := by
  intro x
  have h11 : ‖algebraMap (WithAbs v) (WithAbs w) x‖ = w (algebraMap (WithAbs v) (WithAbs w) x) := by
    simp [WithAbs.norm_eq_abs]
  have h12 : w (algebraMap (WithAbs v) (WithAbs w) x) = v x := h x
  have h13 : ‖x‖ = v x := by simp [WithAbs.norm_eq_abs]
  linarith

lemma round1_h2 (K : Type*) [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] (w : AbsoluteValue L ℝ)
  (h1 : ∀ (x : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x‖ = ‖x‖):
  ∀ (x y : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y‖ = ‖x - y‖ := by
  intro x y
  have h21 : algebraMap (WithAbs v) (WithAbs w) (x - y) = algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y := by
    exact?
  have h22 : algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y = algebraMap (WithAbs v) (WithAbs w) (x - y) := by rw [h21]
  rw [h22]
  have h23 : ‖algebraMap (WithAbs v) (WithAbs w) (x - y)‖ = ‖x - y‖ := h1 (x - y)
  exact h23

lemma round1_h3 (K : Type*) [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] (w : AbsoluteValue L ℝ)
  (h2 : ∀ (x y : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y‖ = ‖x - y‖):
  ∀ (x y : WithAbs v), dist (algebraMap (WithAbs v) (WithAbs w) x) (algebraMap (WithAbs v) (WithAbs w) y) = dist x y := by
  intro x y
  have h31 : dist (algebraMap (WithAbs v) (WithAbs w) x) (algebraMap (WithAbs v) (WithAbs w) y) = ‖algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y‖ := by
    simp [dist_eq_norm]
  have h32 : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
  rw [h31, h32]
  have h4 := h2 x y
  linarith

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w))  := by

  have h1 : ∀ (x : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x‖ = ‖x‖ := by
    exact round1_h1 K v L w h
  have h2 : ∀ (x y : WithAbs v), ‖algebraMap (WithAbs v) (WithAbs w) x - algebraMap (WithAbs v) (WithAbs w) y‖ = ‖x - y‖ := by
    exact round1_h2 K v L w h1
  have h3 : ∀ (x y : WithAbs v), dist (algebraMap (WithAbs v) (WithAbs w) x) (algebraMap (WithAbs v) (WithAbs w) y) = dist x y := by
    exact round1_h3 K v L w h2
  refine' Metric.uniformContinuous_iff.mpr _
  intro ε hε
  refine' ⟨ε, by linarith, _⟩
  intro x y h4
  have h5 : dist (algebraMap (WithAbs v) (WithAbs w) x) (algebraMap (WithAbs v) (WithAbs w) y) = dist x y := h3 x y
  linarith [h5, h4]
