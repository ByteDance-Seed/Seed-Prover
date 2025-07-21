import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by 
 
  -- Establish the lower bound for a using non-linear arithmetic
  have h₃ : 0 ≤ a := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Establish the upper bound for a using non-linear arithmetic
  have h₄ : a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Establish the lower bound for b using non-linear arithmetic
  have h₅ : 1 / 3 ≤ b := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Establish the upper bound for b using non-linear arithmetic
  have h₆ : b ≤ 1 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Establish the lower bound for c using non-linear arithmetic
  have h₇ : 1 ≤ c := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Establish the upper bound for c using non-linear arithmetic
  have h₈ : c ≤ 4 / 3 := by
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  -- Combine all the established bounds into the final result
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩

#print axioms algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3