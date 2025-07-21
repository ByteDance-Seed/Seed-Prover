import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_517 :
  (121 * 122 * 123) % 4 = 2 := by 
  -- We need to compute the remainder of (121 * 122 * 123) divided by 4.
  -- This is a direct numerical calculation. The `norm_num` tactic can evaluate
  -- numerical expressions and prove equalities between them.
  -- Let's have `norm_num` evaluate the left side of the equality.
  -- (121 * 122 * 123) = 1817106
  -- 1817106 % 4
  -- Dividing 1817106 by 4 gives a quotient of 454276 and a remainder of 2.
  -- 1817106 = 4 * 454276 + 2
  -- So, 1817106 % 4 = 2.
  -- The goal is `2 = 2`, which `norm_num` can verify.
  norm_num

#print axioms mathd_numbertheory_517