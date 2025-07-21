import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_3 :
  (∑ x in Finset.range 10, ((x + 1)^2)) % 10 = 5 := by
  -- The goal is to compute the sum of the first 10 squares (1^2 + 2^2 + ... + 10^2) modulo 10.
  -- The sum is expressed as ∑ x in Finset.range 10, (x + 1)^2.
  -- Finset.range 10 is the set {0, 1, ..., 9}.
  -- So the terms of the sum are (0+1)^2, (1+1)^2, ..., (9+1)^2, which are 1^2, 2^2, ..., 10^2.

  -- We can use the property that the sum modulo n is equal to the sum of the terms modulo n, all modulo n.
  -- This property is available for natural numbers as `Finset.sum_nat_mod`.
  -- `(∑ i in s, f i) % n = (∑ i in s, f i % n) % n`
  rw [Finset.sum_nat_mod]

  -- The goal is now `(∑ x in Finset.range 10, ((x + 1)^2 % 10)) % 10 = 5`.
  -- We can evaluate the inner sum `∑ x in Finset.range 10, ((x + 1)^2 % 10)` using `norm_num`.
  -- `norm_num` can evaluate sums over `Finset.range` and modulo operations on natural numbers.
  -- The terms being summed are (x+1)^2 % 10 for x from 0 to 9:
  -- x=0: (0+1)^2 % 10 = 1^2 % 10 = 1 % 10 = 1
  -- x=1: (1+1)^2 % 10 = 2^2 % 10 = 4 % 10 = 4
  -- x=2: (2+1)^2 % 10 = 3^2 % 10 = 9 % 10 = 9
  -- x=3: (3+1)^2 % 10 = 4^2 % 10 = 16 % 10 = 6
  -- x=4: (4+1)^2 % 10 = 5^2 % 10 = 25 % 10 = 5
  -- x=5: (5+1)^2 % 10 = 6^2 % 10 = 36 % 10 = 6
  -- x=6: (6+1)^2 % 10 = 7^2 % 10 = 49 % 10 = 9
  -- x=7: (7+1)^2 % 10 = 8^2 % 10 = 64 % 10 = 4
  -- x=8: (8+1)^2 % 10 = 9^2 % 10 = 81 % 10 = 1
  -- x=9: (9+1)^2 % 10 = 10^2 % 10 = 100 % 10 = 0
  -- The sum of these values is 1 + 4 + 9 + 6 + 5 + 6 + 9 + 4 + 1 + 0 = 45.
  -- So the inner sum `∑ x in Finset.range 10, ((x + 1)^2 % 10)` evaluates to 45.
  -- The goal becomes `45 % 10 = 5`.
  -- `norm_num` can evaluate this final numerical expression.
  norm_num

#print axioms mathd_numbertheory_3
