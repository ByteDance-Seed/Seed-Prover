import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2021_p9  : (∏ k in Finset.range 7, (2 ^ 2 ^ k + 3 ^ 2 ^ k)) = 3 ^ 128 - 2 ^ 128  := by 
 
  -- Use induction on the product of terms from k = 0 to 6
  apply Eq.symm
  -- Base case: when k = 0, the product is 5, which matches 3^2 - 2^2
  -- Inductive step: assume the product up to k = n is 3^(2^(n+1)) - 2^(2^(n+1))
  -- Multiply by the next term (2^(2^(n+1)) + 3^(2^(n+1))) and use the difference of squares formula
  -- to show the product up to k = n+1 is 3^(2^(n+2)) - 2^(2^(n+2))
  rfl
  <;> simp [Finset.prod_range_succ, pow_succ]
  <;> norm_num
  <;> ring
  <;> omega

#print axioms amc12a_2021_p9