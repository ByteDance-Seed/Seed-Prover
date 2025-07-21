import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by 
 
  have h₂ : 0 < b := by linarith
  have h₃ : 0 < a := by linarith
  have h₄ : 0 < a * b := by positivity
  have h₅ : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg (a * b)
  have h₆ : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
    have h₇ : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
    rw [le_div_iff (by positivity)]
    nlinarith [sq_sqrt (show 0 ≤ a * b by positivity),
      sq_nonneg (a - b),
      sq_nonneg (a + b),
      sq_nonneg (a + b - 2 * Real.sqrt (a * b))]
  linarith
#print axioms algebra_bleqa_apbon2msqrtableqambsqon8b