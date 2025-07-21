import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_235 :
  (29 * 79 + 31 * 81) % 10 = 2 := by 
  -- The goal is to prove a numerical equality involving integer multiplication, addition, and modulo.
  -- We need to evaluate the expression (29 * 79 + 31 * 81) and find its remainder when divided by 10.
  -- Let's calculate the value:
  -- 29 * 79 = 2291
  -- 31 * 81 = 2511
  -- 2291 + 2511 = 4802
  -- The goal is therefore equivalent to proving 4802 % 10 = 2.
  -- The `norm_num` tactic is specifically designed to normalize and prove equalities involving numerical expressions.
  -- It can handle integer arithmetic and modulo operations.
  norm_num -- This tactic evaluates the expression and checks the equality.

#print axioms mathd_numbertheory_235