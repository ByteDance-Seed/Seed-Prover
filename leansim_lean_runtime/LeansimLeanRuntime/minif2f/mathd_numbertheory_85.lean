import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_85 :
  1 * 3^3 + 2 * 3^2 + 2*3 + 2 = 53 := by 
  -- The goal is a simple arithmetic equality.
  -- We can use the `norm_num` tactic to evaluate the numerical expression on the left side.
  norm_num

#print axioms mathd_numbertheory_85