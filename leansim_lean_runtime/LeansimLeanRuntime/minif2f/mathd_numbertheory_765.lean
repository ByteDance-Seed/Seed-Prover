import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_765
  (x : ℤ)
  (h₀ : x < 0)
  (h₁ : (24 * x) % 1199 = 15) :
  x ≤ -449 := by 
  -- We use the fact that the remainder of 24x divided by 1199 is 15 to find the general solution for x.
  have h₂ : x ≤ -449 := by
    -- We use the `omega` tactic to solve the linear integer arithmetic problem.
    -- This tactic will find the smallest integer x that satisfies the given conditions.
    omega
  -- The `omega` tactic has already found that x ≤ -449, so we can directly use this result.
  exact h₂

#print axioms mathd_numbertheory_765