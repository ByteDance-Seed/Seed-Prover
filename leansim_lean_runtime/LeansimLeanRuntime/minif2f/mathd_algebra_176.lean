import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_176
  (x : ℝ) :
  (x + 1)^2 * x = x^3 + 2 * x^2 + x := by 
  -- The goal is to prove a polynomial identity in the ring of real numbers.
  -- The `ring` tactic is designed to solve such goals by simplifying both sides of the equality.
  ring

#print axioms mathd_algebra_176