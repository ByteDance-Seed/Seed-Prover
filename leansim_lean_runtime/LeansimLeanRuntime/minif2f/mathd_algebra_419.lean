import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_419
  (a b : ℝ)
  (h₀ : a = -1)
  (h₁ : b = 5) :
  -a - b^2 + 3 * (a * b) = -39 := by 
  -- The goal is to prove the equality by substituting the given values of a and b.
  -- Use the hypothesis h₀ to substitute `a` with `-1`.
  rw [h₀]
  -- The goal is now -(-1) - b^2 + 3 * (-1 * b) = -39
  -- Use the hypothesis h₁ to substitute `b` with `5`.
  rw [h₁]
  -- The goal is now -(-1) - 5^2 + 3 * (-1 * 5) = -39
  -- Evaluate the resulting numerical expression.
  -- -(-1) = 1
  -- 5^2 = 25
  -- -1 * 5 = -5
  -- 3 * (-5) = -15
  -- The expression becomes 1 - 25 - 15 = -39
  -- 1 - 25 = -24
  -- -24 - 15 = -39
  -- So the goal simplifies to -39 = -39.
  norm_num
  -- norm_num verifies the numerical equality and closes the goal.


#print axioms mathd_algebra_419