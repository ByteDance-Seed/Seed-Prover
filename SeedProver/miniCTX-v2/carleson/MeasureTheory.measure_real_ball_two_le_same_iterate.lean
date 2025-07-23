-- In carleson/Carleson/ToMathlib/DoublingMeasure.lean

import Carleson.ToMathlib.CoverByBalls
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Measure NNReal ENNReal Metric Filter Topology TopologicalSpace
noncomputable section

namespace MeasureTheory

/-- A doubling measure is a measure on a metric space with the condition that doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)
export IsDoubling (measure_ball_two_le_same)

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

lemma ball_subset_ball_of_le {x x' : X} {r r' : ℝ}
    (hr : dist x x' + r' ≤ r) : ball x' r' ⊆ ball x r := by
  intro y h
  have h1 : dist x y < r := by
    calc dist x y ≤ dist x x' + dist x' y := dist_triangle _ _ _
        _ < dist x x' + r' := by gcongr; exact mem_ball'.mp h
        _ ≤ r := hr
  exact mem_ball'.mpr h1

variable {A : ℝ≥0} [MeasurableSpace X] {μ : Measure X} [μ.IsDoubling A]

lemma IsDoubling.mono {A'} (h : A ≤ A') : IsDoubling μ A' where
  measure_ball_two_le_same := by
    intro x r
    calc μ (Metric.ball x (2 * r))
      _ ≤ A * μ (Metric.ball x r) := measure_ball_two_le_same _ _
      _ ≤ A' * μ (Metric.ball x r) := by gcongr

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]

lemma measure_real_ball_two_le_same (x : X) (r : ℝ) :
    μ.real (ball x (2 * r)) ≤ A * μ.real (ball x r) := by
  simp_rw [Measure.real, ← ENNReal.coe_toReal, ← toReal_mul]
  gcongr
  · exact ENNReal.mul_ne_top coe_ne_top measure_ball_lt_top.ne
  · exact measure_ball_two_le_same x r

/- Start of proof attempt -/
lemma round1_measure_real_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ.real (ball x ((2 ^ n) * r)) ≤ A ^ n * μ.real (ball x r) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : (μ.real (ball x ((2 ^ (n + 1)) * r)) : ℝ) = μ.real (ball x (2 * ((2 ^ n) * r))) := by
      have h11 : (2 ^ (n + 1) : ℝ) * r = 2 * ((2 ^ n) * r) := by ring
      rw [h11]
    have h2 : μ.real (ball x (2 * ((2 ^ n) * r))) ≤ (A : ℝ) * μ.real (ball x ((2 ^ n) * r)) := by
      have h21 : μ.real (ball x (2 * ((2 ^ n) * r))) ≤ A * μ.real (ball x ((2 ^ n) * r)) := by
        exact measure_real_ball_two_le_same x ((2 ^ n) * r)
      simpa using h21
    have h3 : (μ.real (ball x (2 * ((2 ^ n) * r))) : ℝ) ≤ (A : ℝ) * ((A : ℝ) ^ n * μ.real (ball x r)) := by
      calc
        (μ.real (ball x (2 * ((2 ^ n) * r))) : ℝ) ≤ (A : ℝ) * μ.real (ball x ((2 ^ n) * r)) := h2
        _ ≤ (A : ℝ) * ((A : ℝ) ^ n * μ.real (ball x r)) := by
          have h4 : (μ.real (ball x ((2 ^ n) * r)) : ℝ) ≤ (A : ℝ) ^ n * μ.real (ball x r) := by simpa using ih
          have h5 : (A : ℝ) ≥ 0 := by exact_mod_cast (show (0 : ℝ≥0) ≤ A by positivity)
          have h6 : (A : ℝ) ^ n ≥ 0 := by positivity
          have h7 : μ.real (ball x r) ≥ 0 := by positivity
          have h8 : (A : ℝ) * μ.real (ball x ((2 ^ n) * r)) ≤ (A : ℝ) * ((A : ℝ) ^ n * μ.real (ball x r)) := by
            have h9 : μ.real (ball x ((2 ^ n) * r)) ≤ (A : ℝ) ^ n * μ.real (ball x r) := h4
            have h10 : 0 ≤ (A : ℝ) := by positivity
            nlinarith
          linarith
    have h4 : (A : ℝ) * ((A : ℝ) ^ n * μ.real (ball x r)) = (A : ℝ) ^ (n + 1) * μ.real (ball x r) := by
      ring
    have h5 : (μ.real (ball x (2 * ((2 ^ n) * r))) : ℝ) ≤ (A : ℝ) ^ (n + 1) * μ.real (ball x r) := by linarith
    rw [h1]
    simpa using h5

theorem measure_real_ball_two_le_same_iterate (x : X) (r : ℝ) (n : ℕ) :
    μ.real (ball x ((2 ^ n) * r)) ≤ A ^ n * μ.real (ball x r)  := by

  exact round1_measure_real_ball_two_le_same_iterate x r n
