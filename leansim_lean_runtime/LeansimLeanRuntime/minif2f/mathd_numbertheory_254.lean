import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_254 :
  (239 + 174 + 83) % 10 = 6 := by 
  -- The goal is to prove a specific numerical equality involving addition and modulo.
  -- The `norm_num` tactic is designed to evaluate and prove equalities for such numerical expressions.
  norm_num

#print axioms mathd_numbertheory_254