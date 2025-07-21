import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_427
  (a : ℕ)
  (h₀ : a = (∑ k in (Nat.divisors 500), k)) :
  ∑ k in Finset.filter (λ x => Nat.Prime x) (Nat.divisors a), k = 25 := by 
 
  -- Step 1: Find the prime factorization of 500 and calculate the sum of its divisors.
  rw [h₀]
  -- Step 2: Verify the sum of divisors of 500 is 1092.
  norm_num
  -- Step 3: Find the prime divisors of 1092 and sum them.
  rfl
  <;> decide
  <;> norm_num
  <;> decide
  <;> norm_num
  <;> decide

#print axioms mathd_numbertheory_427