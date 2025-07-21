import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_304 :
  91^2 = 8281 := by 
  -- The goal is a simple numerical equality.
  -- The `norm_num` tactic can evaluate this directly.
  norm_num

#print axioms mathd_algebra_304