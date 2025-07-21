import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_208 : √(1000000 : ℝ) - (1000000 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) = (900 : ℝ) :=
  by
  have subprob_1M_is_10_pow_6_proof : (1000000 : ℝ) = (10 : ℝ) ^ (6 : ℝ) := by
    mkOpaque
    have h_exponent_type_conversion : (10 : ℝ) ^ (6 : ℝ) = (10 : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_nat_cast 10 6]
      rfl
    rw [h_exponent_type_conversion]
    norm_cast
  have subprob_sqrt_1M_eq_1M_rpow_half_proof : Real.sqrt (1000000 : ℝ) = (1000000 : ℝ) ^ ((1 : ℝ) / 2) := by
    mkOpaque
    have h_nonneg : (1000000 : ℝ) ≥ 0 := by norm_num
    rw [Real.sqrt_eq_rpow (1000000 : ℝ)]
  have subprob_1M_rpow_half_eq_10_pow_6_rpow_half_proof : (1000000 : ℝ) ^ ((1 : ℝ) / 2) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2) := by
    mkOpaque
    rw [subprob_1M_is_10_pow_6_proof]
  have subprob_10_pos_proof : (0 : ℝ) < (10 : ℝ) := by
    mkOpaque
    have h_zero_is_cast_zero_nat : (0 : ℝ) = (↑(0 : ℕ) : ℝ) := by exact Nat.cast_zero.symm
    have h_ten_is_cast_ten_nat : (10 : ℝ) = (↑(10 : ℕ) : ℝ) := by exact Eq.symm Nat.cast_ofNat
    rw [h_zero_is_cast_zero_nat]
    rw [h_ten_is_cast_ten_nat]
    apply Nat.cast_lt.mpr
    have h_ten_nat_is_succ_nine : (10 : ℕ) = Nat.succ (9 : ℕ) := by rfl
    rw [h_ten_nat_is_succ_nine]
    apply Nat.zero_lt_succ
  have subprob_pow6_pow_half_eq_pow_6_mul_half_proof : ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2)) := by
    mkOpaque
    rw [← Real.rpow_mul]
    linarith [subprob_10_pos_proof]
  have subprob_6_mul_half_eq_3_proof : (6 : ℝ) * ((1 : ℝ) / 2) = (3 : ℝ) := by
    mkOpaque
    have h_lhs_simplified : (6 : ℝ) * ((1 : ℝ) / 2) = (6 : ℝ) / (2 : ℝ) := by rw [mul_one_div (6 : ℝ) (2 : ℝ)]
    rw [h_lhs_simplified]
    norm_num
  have subprob_pow_6_mul_half_eq_pow_3_proof : (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2)) = (10 : ℝ) ^ (3 : ℝ) := by
    mkOpaque
    rw [subprob_6_mul_half_eq_3_proof]
  have subprob_term1_is_10_pow_3_proof : Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ (3 : ℝ) := by
    mkOpaque
    have h_AB : Real.sqrt (1000000 : ℝ) = (1000000 : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) := by exact subprob_sqrt_1M_eq_1M_rpow_half_proof
    have h_AC : Real.sqrt (1000000 : ℝ) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)) := by exact Eq.trans h_AB subprob_1M_rpow_half_eq_10_pow_6_rpow_half_proof
    have h_AD : Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (2 : ℝ))) := by exact Eq.trans h_AC subprob_pow6_pow_half_eq_pow_6_mul_half_proof
    have h_AE : Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ (3 : ℝ) := by exact Eq.trans h_AD subprob_pow_6_mul_half_eq_pow_3_proof
    exact h_AE
  have subprob_1M_rpow_third_eq_10_pow_6_rpow_third_proof : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) := by
    mkOpaque
    rw [subprob_1M_is_10_pow_6_proof]
  have subprob_pow6_pow_third_eq_pow_6_mul_third_proof : ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) := by
    mkOpaque
    have h_10_pos : 0 < (10 : ℝ) := subprob_10_pos_proof
    have h_10_pow_6_pos : 0 < (10 : ℝ) ^ (6 : ℝ) := by apply Real.rpow_pos_of_pos h_10_pos
    have h_LHS_pos : 0 < ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) := by apply Real.rpow_pos_of_pos h_10_pow_6_pos
    have h_RHS_pos : 0 < (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) := by apply Real.rpow_pos_of_pos h_10_pos
    apply (Real.log_injOn_pos.eq_iff h_LHS_pos h_RHS_pos).mp
    rw [Real.log_rpow h_10_pow_6_pos]
    rw [Real.log_rpow h_10_pos]
    rw [Real.log_rpow h_10_pos]
    ring
  have subprob_6_mul_third_eq_2_proof : (6 : ℝ) * ((1 : ℝ) / 3) = (2 : ℝ) := by
    mkOpaque
    norm_num
  have subprob_pow_6_mul_third_eq_pow_2_proof : (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) = (10 : ℝ) ^ (2 : ℝ) := by
    mkOpaque
    rw [subprob_6_mul_third_eq_2_proof]
  have subprob_term2_is_10_pow_2_proof : (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (2 : ℝ) := by
    mkOpaque
    have h_step1 : (1000000 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (3 : ℝ)) := by exact subprob_1M_rpow_third_eq_10_pow_6_rpow_third_proof
    have h_step2 : ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (3 : ℝ)) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (3 : ℝ))) := by exact subprob_pow6_pow_third_eq_pow_6_mul_third_proof
    have h_step3 : (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (3 : ℝ))) = (10 : ℝ) ^ (2 : ℝ) := by exact subprob_pow_6_mul_third_eq_pow_2_proof
    have h_final_equality : (1000000 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) = (10 : ℝ) ^ (2 : ℝ) := by
      apply Eq.trans h_step1
      apply Eq.trans h_step2
      exact h_step3
    exact h_final_equality
  have subprob_LHS_eq_10_pow_3_minus_10_pow_2_proof : Real.sqrt (1000000 : ℝ) - (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) := by
    mkOpaque
    rw [subprob_term1_is_10_pow_3_proof]
    rw [subprob_term2_is_10_pow_2_proof]
  have subprob_10_pow_3_is_1000_proof : (10 : ℝ) ^ (3 : ℝ) = (1000 : ℝ) := by
    mkOpaque
    have h_rpow_eq_pow_nat : (10 : ℝ) ^ (3 : ℝ) = (10 : ℝ) ^ (3 : ℕ) := by exact Real.rpow_natCast 10 3
    rw [h_rpow_eq_pow_nat]
    norm_num
  have subprob_10_pow_2_is_100_proof : (10 : ℝ) ^ (2 : ℝ) = (100 : ℝ) := by
    mkOpaque
    rw [← subprob_term2_is_10_pow_2_proof]
    have h_1M_nonneg : (0 : ℝ) ≤ (1000000 : ℝ) := by norm_num
    have h_100_nonneg : (0 : ℝ) ≤ (100 : ℝ) := by norm_num
    have h_3r_ne_zero : (3 : ℝ) ≠ 0 := by norm_num
    rw [one_div]
    apply (Real.rpow_inv_eq h_1M_nonneg h_100_nonneg h_3r_ne_zero).mpr
    norm_num
  have subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100_proof : (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) = (1000 : ℝ) - (100 : ℝ) := by
    mkOpaque
    rw [subprob_10_pow_3_is_1000_proof]
    rw [subprob_10_pow_2_is_100_proof]
  have subprob_1000_minus_100_is_900_proof : (1000 : ℝ) - (100 : ℝ) = (900 : ℝ) := by
    mkOpaque
    norm_num
  exact
    show Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = 900 by
      mkOpaque
      have h_A_eq_B : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) := by exact subprob_LHS_eq_10_pow_3_minus_10_pow_2_proof
      have h_B_eq_C : (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) = (1000 : ℝ) - (100 : ℝ) := by exact subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100_proof
      have h_C_eq_D : (1000 : ℝ) - (100 : ℝ) = (900 : ℝ) := by exact subprob_1000_minus_100_is_900_proof
      have h_A_eq_C : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (1000 : ℝ) - (100 : ℝ) := by exact Eq.trans h_A_eq_B h_B_eq_C
      have h_A_eq_D : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (900 : ℝ) := by exact Eq.trans h_A_eq_C h_C_eq_D
      exact h_A_eq_D

#print axioms mathd_algebra_208

/-Sketch
play
  -- Step 1: Express 1,000,000 as 10^6.
  subprob_1M_is_10_pow_6 :≡ (1000000 : ℝ) = (10 : ℝ) ^ (6 : ℝ)
  subprob_1M_is_10_pow_6_proof ⇐ show subprob_1M_is_10_pow_6 by sorry

  -- Step 2: Process the first term, Real.sqrt 1000000.
  -- Step 2a: Rewrite Real.sqrt 1000000 using rpow, i.e., Real.sqrt x = x^(1/2).
  subprob_sqrt_1M_eq_1M_rpow_half :≡ Real.sqrt (1000000 : ℝ) = (1000000 : ℝ) ^ ((1 : ℝ) / 2)
  subprob_sqrt_1M_eq_1M_rpow_half_proof ⇐ show subprob_sqrt_1M_eq_1M_rpow_half by sorry

  -- Step 2b: Substitute 1000000 = 10^6 into the expression from 2a.
  -- (1000000 : ℝ)^(1/2) = ((10 : ℝ)^6)^(1/2)
  subprob_1M_rpow_half_eq_10_pow_6_rpow_half :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 2) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2)
  subprob_1M_rpow_half_eq_10_pow_6_rpow_half_proof ⇐ show subprob_1M_rpow_half_eq_10_pow_6_rpow_half by sorry

  -- For applying (x^y)^z = x^(y*z), we need x > 0.
  subprob_10_pos :≡ (0 : ℝ) < (10 : ℝ)
  subprob_10_pos_proof ⇐ show subprob_10_pos by sorry

  -- Step 2c: Apply the exponent rule (x^y)^z = x^(y*z).
  -- ((10 : ℝ)^6)^(1/2) = (10 : ℝ)^(6 * 1/2)
  subprob_pow6_pow_half_eq_pow_6_mul_half :≡ ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2))
  subprob_pow6_pow_half_eq_pow_6_mul_half_proof ⇐ show subprob_pow6_pow_half_eq_pow_6_mul_half by sorry

  -- Step 2d: Calculate the new exponent 6 * (1/2).
  subprob_6_mul_half_eq_3 :≡ (6 : ℝ) * ((1 : ℝ) / 2) = (3 : ℝ)
  subprob_6_mul_half_eq_3_proof ⇐ show subprob_6_mul_half_eq_3 by sorry

  -- Step 2e: Substitute the calculated exponent back.
  -- (10 : ℝ)^(6 * 1/2) = (10 : ℝ)^3
  subprob_pow_6_mul_half_eq_pow_3 :≡ (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2)) = (10 : ℝ) ^ (3 : ℝ)
  subprob_pow_6_mul_half_eq_pow_3_proof ⇐ show subprob_pow_6_mul_half_eq_pow_3 by sorry

  -- Step 2f: Combine steps 2a-2e to find the value of Real.sqrt 1000000.
  -- Real.sqrt 1000000 = (10 : ℝ)^3
  -- This follows by transitivity from:
  -- Real.sqrt 1000000 = 1000000^(1/2) (by 2a)
  -- = (10^6)^(1/2) (by 2b)
  -- = 10^(6 * 1/2) (by 2c)
  -- = 10^3 (by 2e, using 2d)
  subprob_term1_is_10_pow_3 :≡ Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ (3 : ℝ)
  subprob_term1_is_10_pow_3_proof ⇐ show subprob_term1_is_10_pow_3 by sorry

  -- Step 3: Process the second term, 1000000^((1:ℝ)/3).
  -- Step 3a: Substitute 1000000 = 10^6.
  -- 1000000^(1/3) = (10^6)^(1/3)
  subprob_1M_rpow_third_eq_10_pow_6_rpow_third :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 3) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3)
  subprob_1M_rpow_third_eq_10_pow_6_rpow_third_proof ⇐ show subprob_1M_rpow_third_eq_10_pow_6_rpow_third by sorry

  -- Step 3b: Apply the exponent rule (x^y)^z = x^(y*z).
  -- ((10 : ℝ)^6)^(1/3) = (10 : ℝ)^(6 * 1/3)
  subprob_pow6_pow_third_eq_pow_6_mul_third :≡ ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3))
  subprob_pow6_pow_third_eq_pow_6_mul_third_proof ⇐ show subprob_pow6_pow_third_eq_pow_6_mul_third by sorry

  -- Step 3c: Calculate the new exponent 6 * (1/3).
  subprob_6_mul_third_eq_2 :≡ (6 : ℝ) * ((1 : ℝ) / 3) = (2 : ℝ)
  subprob_6_mul_third_eq_2_proof ⇐ show subprob_6_mul_third_eq_2 by sorry

  -- Step 3d: Substitute the calculated exponent back.
  -- (10 : ℝ)^(6 * 1/3) = (10 : ℝ)^2
  subprob_pow_6_mul_third_eq_pow_2 :≡ (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) = (10 : ℝ) ^ (2 : ℝ)
  subprob_pow_6_mul_third_eq_pow_2_proof ⇐ show subprob_pow_6_mul_third_eq_pow_2 by sorry

  -- Step 3e: Combine steps 3a-3d to find the value of 1000000^((1:ℝ)/3).
  -- 1000000^(1/3) = (10 : ℝ)^2
  -- This follows by transitivity from:
  -- 1000000^(1/3) = (10^6)^(1/3) (by 3a)
  -- = 10^(6 * 1/3) (by 3b)
  -- = 10^2 (by 3d, using 3c)
  subprob_term2_is_10_pow_2 :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (2 : ℝ)
  subprob_term2_is_10_pow_2_proof ⇐ show subprob_term2_is_10_pow_2 by sorry

  -- Step 4: Perform the subtraction.
  -- Step 4a: Substitute the results for term1 and term2 into the original expression's LHS.
  -- Real.sqrt 1000000 - 1000000^(1/3) = 10^3 - 10^2
  subprob_LHS_eq_10_pow_3_minus_10_pow_2 :≡ Real.sqrt (1000000 : ℝ) - (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ)
  subprob_LHS_eq_10_pow_3_minus_10_pow_2_proof ⇐ show subprob_LHS_eq_10_pow_3_minus_10_pow_2 by sorry

  -- Step 4b: Evaluate 10^3 and 10^2.
  subprob_10_pow_3_is_1000 :≡ (10 : ℝ) ^ (3 : ℝ) = (1000 : ℝ)
  subprob_10_pow_3_is_1000_proof ⇐ show subprob_10_pow_3_is_1000 by sorry
  subprob_10_pow_2_is_100 :≡ (10 : ℝ) ^ (2 : ℝ) = (100 : ℝ)
  subprob_10_pow_2_is_100_proof ⇐ show subprob_10_pow_2_is_100 by sorry

  -- Step 4c: Substitute these evaluations into the RHS of 4a.
  -- 10^3 - 10^2 = 1000 - 100
  subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100 :≡ (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) = (1000 : ℝ) - (100 : ℝ)
  subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100_proof ⇐ show subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100 by sorry

  -- Step 4d: Calculate the final subtraction.
  subprob_1000_minus_100_is_900 :≡ (1000 : ℝ) - (100 : ℝ) = (900 : ℝ)
  subprob_1000_minus_100_is_900_proof ⇐ show subprob_1000_minus_100_is_900 by sorry

  -- Step 5: Conclusion by transitivity.
  -- Real.sqrt 1000000 - 1000000^(1/3)
  -- = 10^3 - 10^2 (by 4a)
  -- = 1000 - 100 (by 4c)
  -- = 900 (by 4d)
  subprob_final_goal :≡ Real.sqrt 1000000 - 1000000^((1 : ℝ)/3) = 900
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
play
  subprob_1M_is_10_pow_6 :≡ (1000000 : ℝ) = (10 : ℝ) ^ (6 : ℝ)
  subprob_1M_is_10_pow_6_proof ⇐ show subprob_1M_is_10_pow_6 by





    have h_exponent_type_conversion : (10 : ℝ) ^ (6 : ℝ) = (10 : ℝ) ^ (6 : ℕ) := by
      rw [← Real.rpow_nat_cast 10 6]
      rfl

    rw [h_exponent_type_conversion]

    norm_cast

  subprob_sqrt_1M_eq_1M_rpow_half :≡ Real.sqrt (1000000 : ℝ) = (1000000 : ℝ) ^ ((1 : ℝ) / 2)
  subprob_sqrt_1M_eq_1M_rpow_half_proof ⇐ show subprob_sqrt_1M_eq_1M_rpow_half by



    have h_nonneg : (1000000 : ℝ) ≥ 0 := by
      norm_num

    rw [Real.sqrt_eq_rpow (1000000 : ℝ)]



  subprob_1M_rpow_half_eq_10_pow_6_rpow_half :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 2) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2)
  subprob_1M_rpow_half_eq_10_pow_6_rpow_half_proof ⇐ show subprob_1M_rpow_half_eq_10_pow_6_rpow_half by

    rw [subprob_1M_is_10_pow_6_proof]

  subprob_10_pos :≡ (0 : ℝ) < (10 : ℝ)
  subprob_10_pos_proof ⇐ show subprob_10_pos by


    have h_zero_is_cast_zero_nat : (0 : ℝ) = (↑(0 : ℕ) : ℝ) := by
      exact Nat.cast_zero.symm

    have h_ten_is_cast_ten_nat : (10 : ℝ) = (↑(10 : ℕ) : ℝ) := by
      exact Eq.symm Nat.cast_ofNat

    rw [h_zero_is_cast_zero_nat]
    rw [h_ten_is_cast_ten_nat]

    apply Nat.cast_lt.mpr

    have h_ten_nat_is_succ_nine : (10 : ℕ) = Nat.succ (9 : ℕ) := by
      rfl
    rw [h_ten_nat_is_succ_nine]

    apply Nat.zero_lt_succ


  subprob_pow6_pow_half_eq_pow_6_mul_half :≡ ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 2) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2))
  subprob_pow6_pow_half_eq_pow_6_mul_half_proof ⇐ show subprob_pow6_pow_half_eq_pow_6_mul_half by


    rw [← Real.rpow_mul]

    linarith [subprob_10_pos_proof]



  subprob_6_mul_half_eq_3 :≡ (6 : ℝ) * ((1 : ℝ) / 2) = (3 : ℝ)
  subprob_6_mul_half_eq_3_proof ⇐ show subprob_6_mul_half_eq_3 by

    have h_lhs_simplified : (6 : ℝ) * ((1 : ℝ) / 2) = (6 : ℝ) / (2 : ℝ) := by
      rw [mul_one_div (6 : ℝ) (2 : ℝ)]

    rw [h_lhs_simplified]

    norm_num


  subprob_pow_6_mul_half_eq_pow_3 :≡ (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 2)) = (10 : ℝ) ^ (3 : ℝ)
  subprob_pow_6_mul_half_eq_pow_3_proof ⇐ show subprob_pow_6_mul_half_eq_pow_3 by


    rw [subprob_6_mul_half_eq_3_proof]



  subprob_term1_is_10_pow_3 :≡ Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ (3 : ℝ)
  subprob_term1_is_10_pow_3_proof ⇐ show subprob_term1_is_10_pow_3 by




    have h_AB : Real.sqrt (1000000 : ℝ) = (1000000 : ℝ) ^ ((1 : ℝ) / (2 : ℝ)) := by
      exact subprob_sqrt_1M_eq_1M_rpow_half_proof

    have h_AC : Real.sqrt (1000000 : ℝ) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (2 : ℝ)) := by
      exact Eq.trans h_AB subprob_1M_rpow_half_eq_10_pow_6_rpow_half_proof

    have h_AD : Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (2 : ℝ))) := by
      exact Eq.trans h_AC subprob_pow6_pow_half_eq_pow_6_mul_half_proof

    have h_AE : Real.sqrt (1000000 : ℝ) = (10 : ℝ) ^ (3 : ℝ) := by
      exact Eq.trans h_AD subprob_pow_6_mul_half_eq_pow_3_proof

    exact h_AE

  subprob_1M_rpow_third_eq_10_pow_6_rpow_third :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 3) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3)
  subprob_1M_rpow_third_eq_10_pow_6_rpow_third_proof ⇐ show subprob_1M_rpow_third_eq_10_pow_6_rpow_third by
    rw [subprob_1M_is_10_pow_6_proof]

  subprob_pow6_pow_third_eq_pow_6_mul_third :≡ ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3))
  subprob_pow6_pow_third_eq_pow_6_mul_third_proof ⇐ show subprob_pow6_pow_third_eq_pow_6_mul_third by



































    have h_10_pos : 0 < (10 : ℝ) := subprob_10_pos_proof


    have h_10_pow_6_pos : 0 < (10 : ℝ) ^ (6 : ℝ) := by
      apply Real.rpow_pos_of_pos h_10_pos

    have h_LHS_pos : 0 < ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / 3) := by
      apply Real.rpow_pos_of_pos h_10_pow_6_pos

    have h_RHS_pos : 0 < (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) := by
      apply Real.rpow_pos_of_pos h_10_pos

    apply (Real.log_injOn_pos.eq_iff h_LHS_pos h_RHS_pos).mp


    rw [Real.log_rpow h_10_pow_6_pos]

    rw [Real.log_rpow h_10_pos]

    rw [Real.log_rpow h_10_pos]

    ring


  subprob_6_mul_third_eq_2 :≡ (6 : ℝ) * ((1 : ℝ) / 3) = (2 : ℝ)
  subprob_6_mul_third_eq_2_proof ⇐ show subprob_6_mul_third_eq_2 by

    norm_num

  subprob_pow_6_mul_third_eq_pow_2 :≡ (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / 3)) = (10 : ℝ) ^ (2 : ℝ)
  subprob_pow_6_mul_third_eq_pow_2_proof ⇐ show subprob_pow_6_mul_third_eq_pow_2 by


    rw [subprob_6_mul_third_eq_2_proof]


  subprob_term2_is_10_pow_2 :≡ (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (2 : ℝ)
  subprob_term2_is_10_pow_2_proof ⇐ show subprob_term2_is_10_pow_2 by


    have h_step1 : (1000000 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) = ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (3 : ℝ)) := by
      exact subprob_1M_rpow_third_eq_10_pow_6_rpow_third_proof

    have h_step2 : ((10 : ℝ) ^ (6 : ℝ)) ^ ((1 : ℝ) / (3 : ℝ)) = (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (3 : ℝ))) := by
      exact subprob_pow6_pow_third_eq_pow_6_mul_third_proof

    have h_step3 : (10 : ℝ) ^ ((6 : ℝ) * ((1 : ℝ) / (3 : ℝ))) = (10 : ℝ) ^ (2 : ℝ) := by
      exact subprob_pow_6_mul_third_eq_pow_2_proof

    have h_final_equality : (1000000 : ℝ) ^ ((1 : ℝ) / (3 : ℝ)) = (10 : ℝ) ^ (2 : ℝ) := by
      apply Eq.trans h_step1
      apply Eq.trans h_step2
      exact h_step3

    exact h_final_equality

  subprob_LHS_eq_10_pow_3_minus_10_pow_2 :≡ Real.sqrt (1000000 : ℝ) - (1000000 : ℝ) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ)
  subprob_LHS_eq_10_pow_3_minus_10_pow_2_proof ⇐ show subprob_LHS_eq_10_pow_3_minus_10_pow_2 by




    rw [subprob_term1_is_10_pow_3_proof]

    rw [subprob_term2_is_10_pow_2_proof]



  subprob_10_pow_3_is_1000 :≡ (10 : ℝ) ^ (3 : ℝ) = (1000 : ℝ)
  subprob_10_pow_3_is_1000_proof ⇐ show subprob_10_pow_3_is_1000 by






    have h_rpow_eq_pow_nat : (10 : ℝ) ^ (3 : ℝ) = (10 : ℝ) ^ (3 : ℕ) := by
      exact Real.rpow_natCast 10 3

    rw [h_rpow_eq_pow_nat]

    norm_num

  subprob_10_pow_2_is_100 :≡ (10 : ℝ) ^ (2 : ℝ) = (100 : ℝ)
  subprob_10_pow_2_is_100_proof ⇐ show subprob_10_pow_2_is_100 by

    rw [← subprob_term2_is_10_pow_2_proof]


    have h_1M_nonneg : (0 : ℝ) ≤ (1000000 : ℝ) := by
      norm_num
    have h_100_nonneg : (0 : ℝ) ≤ (100 : ℝ) := by
      norm_num
    have h_3r_ne_zero : (3 : ℝ) ≠ 0 := by
      norm_num

    rw [one_div]
    apply (Real.rpow_inv_eq h_1M_nonneg h_100_nonneg h_3r_ne_zero).mpr
    norm_num


  subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100 :≡ (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) = (1000 : ℝ) - (100 : ℝ)
  subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100_proof ⇐ show subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100 by


    rw [subprob_10_pow_3_is_1000_proof]

    rw [subprob_10_pow_2_is_100_proof]


  subprob_1000_minus_100_is_900 :≡ (1000 : ℝ) - (100 : ℝ) = (900 : ℝ)
  subprob_1000_minus_100_is_900_proof ⇐ show subprob_1000_minus_100_is_900 by
    norm_num

  subprob_final_goal :≡ Real.sqrt 1000000 - 1000000^((1 : ℝ)/3) = 900
  subprob_final_goal_proof ⇐ show subprob_final_goal by





    have h_A_eq_B : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) := by
      exact subprob_LHS_eq_10_pow_3_minus_10_pow_2_proof

    have h_B_eq_C : (10 : ℝ) ^ (3 : ℝ) - (10 : ℝ) ^ (2 : ℝ) = (1000 : ℝ) - (100 : ℝ) := by
      exact subprob_10_pow_3_minus_10_pow_2_eq_1000_minus_100_proof

    have h_C_eq_D : (1000 : ℝ) - (100 : ℝ) = (900 : ℝ) := by
      exact subprob_1000_minus_100_is_900_proof

    have h_A_eq_C : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (1000 : ℝ) - (100 : ℝ) := by
      exact Eq.trans h_A_eq_B h_B_eq_C

    have h_A_eq_D : Real.sqrt 1000000 - 1000000 ^ ((1 : ℝ) / 3) = (900 : ℝ) := by
      exact Eq.trans h_A_eq_C h_C_eq_D

    exact h_A_eq_D
-/
