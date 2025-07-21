import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_160
  (n x : ℝ)
  (h₀ : n + x = 97)
  (h₁ : n + 5 * x = 265) :
  n + 2 * x = 139 := by 
  -- The problem provides a system of two linear equations:
  -- 1) n + x = 97
  -- 2) n + 5*x = 265
  -- We are asked to prove that n + 2*x = 139 holds for the same n and x.
  -- This is a linear arithmetic problem over the real numbers.
  -- The `linarith` tactic is designed to solve such problems by finding
  -- a linear combination of the hypotheses that yields the target equation
  -- (or a contradiction if the negation of the goal is assumed).
  -- We can apply `linarith` directly using the given hypotheses h₀ and h₁.
  linarith

#print axioms mathd_algebra_160