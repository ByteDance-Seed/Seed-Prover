import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_432
  (x : ℝ) :
  (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by 
  -- The goal is an identity involving addition, subtraction, and multiplication of real numbers.
  -- This type of equality can often be proven using the `ring` tactic.
  -- Expand the left side: (x + 3) * (2x - 6) = x*(2x - 6) + 3*(2x - 6)
  -- = 2x^2 - 6x + 6x - 18
  -- = 2x^2 - 18
  -- This matches the right side. The `ring` tactic performs these steps automatically.
  ring

#print axioms mathd_algebra_432