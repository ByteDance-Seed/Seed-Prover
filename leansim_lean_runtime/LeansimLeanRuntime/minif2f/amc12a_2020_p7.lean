import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2020_p7
  (a : ℕ → ℕ)
  (h₀ : (a 0)^3 = 1)
  (h₁ : (a 1)^3 = 8)
  (h₂ : (a 2)^3 = 27)
  (h₃ : (a 3)^3 = 64)
  (h₄ : (a 4)^3 = 125)
  (h₅ : (a 5)^3 = 216)
  (h₆ : (a 6)^3 = 343) :
  ∑ k in Finset.range 7, (6 * (a k)^2) - ↑(2 * ∑ k in Finset.range 6, (a k)^2) = 658 := by

  -- The hypotheses give us the cube of the first few terms of the sequence a.
  -- Since a k are natural numbers, we can find a k by taking the cube root.
  -- We know that for natural numbers x, y, if x^n = y^n for n ≠ 0, then x = y.
  -- We use the theorem pow_left_inj which states a^n = b^n ↔ a = b for a, b ≥ 0 and n ≠ 0 in a LinearOrderedSemiring.
  have h_pow3_ne_zero : 3 ≠ 0 := by norm_num
  -- We prove (a 0)^3 = 1^3 and use pow_left_inj to conclude a 0 = 1.
  -- We use the split proof structure.
  have h_a0_pow3 : (a 0)^3 = 1^3 := by rw [h₀]; norm_num
  -- Using `pow_left_inj`.
  have a0_eq : a 0 = 1 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a0_pow3
  -- We prove (a 1)^3 = 2^3 and use pow_left_inj to conclude a 1 = 2.
  -- We use the split proof structure.
  have h_a1_pow3 : (a 1)^3 = 2^3 := by rw [h₁]; norm_num
  -- Using `pow_left_inj`.
  have a1_eq : a 1 = 2 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a1_pow3
  -- We prove (a 2)^3 = 3^3 and use pow_left_inj to conclude a 2 = 3.
  -- We use the split proof structure.
  have h_a2_pow3 : (a 2)^3 = 3^3 := by rw [h₂]; norm_num
  -- Using `pow_left_inj`.
  have a2_eq : a 2 = 3 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a2_pow3
  -- We prove (a 3)^3 = 4^3 and use pow_left_inj to conclude a 3 = 4.
  -- We split the proof into two steps: first prove the equality of cubes, then use the theorem to get equality of bases.
  have h_a3_pow3 : (a 3)^3 = 4^3 := by rw [h₃]; norm_num
  -- Using `pow_left_inj`.
  have a3_eq : a 3 = 4 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a3_pow3
  -- We prove (a 4)^3 = 5^3 and use pow_left_inj to conclude a 4 = 5.
  -- Using the same split proof structure.
  have h_a4_pow3 : (a 4)^3 = 5^3 := by rw [h₄]; norm_num
  -- Using `pow_left_inj`.
  have a4_eq : a 4 = 5 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a4_pow3
  -- We prove (a 5)^3 = 6^3 and use pow_left_inj to conclude a 5 = 6.
  -- Using the same split proof structure.
  have h_a5_pow3 : (a 5)^3 = 6^3 := by rw [h₅]; norm_num
  -- Using `pow_left_inj`.
  have a5_eq : a 5 = 6 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a5_pow3
  -- We prove (a 6)^3 = 7^3 and use pow_left_inj to conclude a 6 = 7.
  -- Using the same split proof structure.
  have h_a6_pow3 : (a 6)^3 = 7^3 := by rw [h₆]; norm_num
  -- Using `pow_left_inj`.
  have a6_eq : a 6 = 7 := (pow_left_inj (by simp) (by simp) h_pow3_ne_zero).mp h_a6_pow3

  -- The goal involves sums of squares. We need the value of the sum of squares from k=0 to k=5.
  -- ∑ k in Finset.range 6, (a k)^2 = (a 0)^2 + (a 1)^2 + (a 2)^2 + (a 3)^2 + (a 4)^2 + (a 5)^2
  -- Using the equalities we derived: 1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 = 1 + 4 + 9 + 16 + 25 + 36 = 91.
  -- This sum is a natural number.
  -- Define the sum of squares from 0 to 5.
  let sum_val := ∑ k in Finset.range 6, (a k)^2
  -- Prove its value.
  have sum_a_sq_0_to_5 : sum_val = 91 := by
    -- Expand sum_val definition.
    simp only [sum_val]
    -- Expand the sum using Finset.sum_range_succ repeatedly and simplify the empty sum.
    simp only [Finset.sum_range_zero, Finset.sum_range_succ]
    -- Now substitute the values of (a k)^2 using the derived equalities.
    simp only [a0_eq, a1_eq, a2_eq, a3_eq, a4_eq, a5_eq]
    -- Evaluate the numerical sum.
    norm_num

  -- The goal is of type Nat, involving natural number subtraction.
  -- Expand the first sum over range 7 into sum over range 6 plus the term at 6.
  rw [Finset.sum_range_succ (fun k => 6 * a k ^ 2) 6]

  -- Factor out 6 from the sum over range 6.
  -- We use the theorem Finset.mul_sum in the reverse direction: ∑ x in s, c * f x = c * ∑ x in s, f x.
  rw [← Finset.mul_sum]

  -- The goal is now: (6 * ∑ k ∈ Finset.range 6, a k ^ 2) + (6 * a 6 ^ 2) - ↑(2 * ∑ k ∈ Finset.range 6, a k ^ 2) = 658
  -- The cast ↑ from Nat to Nat is definitionally the identity.
  -- Goal: (6 * ∑ k ∈ Finset.range 6, a k ^ 2) + (6 * a 6 ^ 2) - (2 * ∑ k ∈ Finset.range 6, a k ^ 2) = 658.

  -- Use `change` to make the sums syntactically match `sum_val` to help `rw`.
  -- This resolves the unification issue where the variable name in the sum (k) was preventing `rw` from applying the equality from `Nat.add_sub_assoc_of_le`.
  change (6 * sum_val) + (6 * a 6 ^ 2) - (2 * sum_val) = 658

  -- The goal is now: (6 * sum_val) + (6 * a 6 ^ 2) - (2 * sum_val) = 658
  -- We want to rearrange this to ((6*sum_val) - (2*sum_val)) + (6*a6^2) = 658.
  -- The theorem `Nat.add_sub_assoc_of_le` was not found. We manually prove the required equality:
  -- (a + b) - c = (a - c) + b given c ≤ a for natural numbers.
  -- Here a = (6 * sum_val), b = (6 * a6^2), c = (2 * sum_val). We need c ≤ a.

  -- We keep the proof that 2*sum_val ≤ 6*sum_val (h_2S_le_6S) as it's needed to show the subtraction (6*sum_val - 2*sum_val) is valid.
  have h_2S_le_6S : (2 : ℕ) * sum_val ≤ (6 : ℕ) * sum_val :=
    -- Apply Nat.mul_le_mul_right with the multiplier sum_val first, and then the proof of the inequality (2 ≤ 6).
    Nat.mul_le_mul_right sum_val (by norm_num : 2 ≤ 6)

  -- Let A := 6 * sum_val, B := 6 * a 6 ^ 2, C := 2 * sum_val. We want (A + B) - C = (A - C) + B.
  -- Since C ≤ A (h_2S_le_6S), we have A = (A - C) + C. We prove this equality.
  have h_6S_eq_diff_sum : (6 * sum_val) = (6 * sum_val - 2 * sum_val) + (2 * sum_val) := by omega

  -- Rewrite the LHS (6 * sum_val) + (6 * a 6 ^ 2) - (2 * sum_val)
  -- (A + B) - C becomes ((A - C) + C + B) - C by substituting A
  rw [h_6S_eq_diff_sum]
  -- Goal: ((6 * sum_val - 2 * sum_val) + 2 * sum_val + 6 * a 6 ^ 2) - (2 * sum_val) = 658
  -- Rearrange terms using associativity and commutativity of addition to get (((A-C)+B)+C)-C
  rw [Nat.add_assoc] -- Apply Nat.add_assoc to rearrange the first three terms inside the parentheses: (A-C) + C + B becomes (A-C) + (C+B)
  rw [Nat.add_comm (2 * sum_val) (6 * a 6 ^ 2)] -- Apply Nat.add_comm to swap C and B: (A-C) + (C+B) becomes (A-C) + (B+C)
  rw [← Nat.add_assoc (6 * sum_val - 2 * sum_val) (6 * a 6 ^ 2) (2 * sum_val)] -- Apply Nat.add_assoc in reverse to group (A-C) and B: (A-C) + (B+C) becomes ((A-C)+B)+C

  -- Use Nat.add_sub_cancel_right to simplify (X + C) - C = X where X = (A-C)+B and C = 2*sum_val.
  -- This requires C ≤ X + C, which is true since X is a sum of natural numbers and thus non-negative.
  -- The theorem Nat.add_sub_cancel_right (n m : ℕ) : (n + m) - m = n can be applied directly.
  -- -- The argument name 'C' is not valid for `Nat.add_sub_cancel_right`.
  rw [Nat.add_sub_cancel_right]

  -- The goal is now: (6 * sum_val - 2 * sum_val) + (6 * a 6 ^ 2) = 658

  -- Use Nat.sub_mul to simplify (6*sum_val) - (2*sum_val) to (6-2)*sum_val.
  -- The previous attempt used the wrong theorem (`Nat.mul_sub_left_distrib`) and passed a proof argument where a Nat was expected.
  rw [← Nat.sub_mul 6 2 sum_val]

  -- The goal is now: (4 * sum_val) + (6 * a 6 ^ 2) = 658
  -- Substitute the value of the sum from k=0 to 5.
  rw [sum_a_sq_0_to_5]

  -- Substitute the value of a 6.
  rw [a6_eq]

  -- The goal is now a numerical expression in Nat. Use norm_num to evaluate both sides.
  norm_num

#print axioms amc12a_2020_p7
