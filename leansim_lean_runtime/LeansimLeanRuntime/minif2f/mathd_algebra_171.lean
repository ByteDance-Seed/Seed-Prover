import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_171
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 5 * x + 4) :
  f 1 = 9 := by 
  -- The goal is to prove that f 1 = 9
  -- We are given the definition of f x as h₀ : ∀x, f x = 5 * x + 4
  -- We can apply the hypothesis h₀ to the specific value x = 1
  rw [h₀ 1]
  -- After applying h₀, the goal becomes 5 * 1 + 4 = 9
  -- Now, we simplify the numerical expression 5 * 1 + 4
  norm_num
  -- The goal is now 9 = 9, which is true by definition and solved by norm_num

#print axioms mathd_algebra_171