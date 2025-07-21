import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2020_p10 (n : ℕ) (h₀ : 0 < n) (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) (h₂ : n ≠ 1) : List.sum (digits (10 : ℕ) n) = (13 : ℕ) :=
  by
  have subprob_n_ge_1_nat_proof : n ≥ 1 := by
    mkOpaque
    apply Nat.one_le_of_lt
    exact h₀
  have subprob_n_ge_2_nat_proof : n ≥ 2 := by
    mkOpaque
    have h_n_ge_1 : n ≥ 1 := subprob_n_ge_1_nat_proof
    cases Nat.eq_or_lt_of_le h_n_ge_1 with
    | inl h_n_eq_1 =>
      rw [← h_n_eq_1] at h₂
      contradiction
    | inr h_n_gt_1 => exact Nat.succ_le_of_lt h_n_gt_1
  letI n_cast_real := (n : ℝ)
  retro' n_cast_real_def : n_cast_real = (↑(n) : ℝ) := by funext; rfl
  have subprob_n_cast_real_def_proof : n_cast_real = (n : ℝ) := by
    mkOpaque
    rw [n_cast_real_def]
  have subprob_n_cast_real_ge_2_proof : n_cast_real ≥ 2 := by
    mkOpaque
    have h_n_cast_pos : (0 : ℝ) < (n : ℝ) := by
      have h_n_ge_1 : n ≥ 1 := Nat.succ_le_iff.mpr h₀
      have h_n_cast_ge_1 : (n : ℝ) ≥ (1 : ℝ) := (@Nat.cast_one ℝ _) ▸ (Nat.cast_le.mpr h_n_ge_1)
      linarith
    have h_log16_n_gt_0 : logb 16 (n : ℝ) > 0 := by
      apply Decidable.byContradiction
      intro h_not_gt_log16_n_zero
      have h_log16_n_le_0 : logb 16 (n : ℝ) ≤ 0 := le_of_not_lt h_not_gt_log16_n_zero
      have h_base_16_gt_1 : (16 : ℝ) > 1 := by norm_num
      have h_n_cast_le_1 : (n : ℝ) ≤ 1 := by
        rw [← (Real.logb_nonpos_iff h_base_16_gt_1 h_n_cast_pos)]
        exact h_log16_n_le_0
      have h_n_ge_1_nat : n ≥ 1 := Nat.succ_le_of_lt h₀
      have h_n_cast_ge_1 : (n : ℝ) ≥ 1 := by exact (@Nat.cast_one ℝ _) ▸ (Nat.cast_le.mpr h_n_ge_1_nat)
      have h_n_cast_eq_1 : (n : ℝ) = 1 := le_antisymm h_n_cast_le_1 h_n_cast_ge_1
      have h_n_eq_1 : n = 1 := Nat.cast_inj.mp ((@Nat.cast_one ℝ _).symm ▸ h_n_cast_eq_1)
      exact h₂ h_n_eq_1
    have h_base_16_gt_1_for_pos : (16 : ℝ) > 1 := by norm_num
    have h_n_cast_gt_1 : (n : ℝ) > 1 := by
      apply (Real.logb_pos_iff h_base_16_gt_1_for_pos h_n_cast_pos).mp
      exact h_log16_n_gt_0
    have h_n_gt_1_nat : n > 1 := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num] at h_n_cast_gt_1
      exact Nat.cast_lt.mp h_n_cast_gt_1
    have h_n_ge_2_nat : n ≥ 2 := Nat.succ_le_of_lt h_n_gt_1_nat
    rw [n_cast_real_def]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    apply Nat.cast_le.mpr
    exact h_n_ge_2_nat
  have subprob_n_cast_real_gt_0_proof : n_cast_real > 0 := by
    mkOpaque
    have h_two_is_positive : (2 : ℝ) > (0 : ℝ) := by norm_num
    exact gt_of_ge_of_gt subprob_n_cast_real_ge_2_proof h_two_is_positive
  letI X_n := Real.logb 2 n_cast_real
  retro' X_n_def : X_n = logb (2 : ℝ) n_cast_real := by funext; rfl
  have subprob_Xn_def_proof : X_n = Real.logb 2 n_cast_real := by
    mkOpaque
    exact X_n_def
  have subprob_base_2_gt_1_proof : (2 : ℝ) > 1 := by
    mkOpaque
    norm_num
  have subprob_log2_2_eq_1_proof : Real.logb 2 2 = 1 := by
    mkOpaque
    have h_two_gt_zero : (2 : ℝ) > 0 := by norm_num
    have h_two_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    apply Real.logb_self_eq_one
    exact subprob_base_2_gt_1_proof
  have subprob_Xn_ge_1_proof : X_n ≥ 1 := by
    mkOpaque
    rw [X_n_def]
    apply (Real.le_logb_iff_rpow_le subprob_base_2_gt_1_proof subprob_n_cast_real_gt_0_proof).mpr
    rw [rpow_one]
    exact subprob_n_cast_real_ge_2_proof
  have subprob_log16_n_eq_Xn_div_4_proof : Real.logb 16 n_cast_real = X_n / 4 := by
    mkOpaque
    have h_16_pos : (16 : ℝ) > 0 := by norm_num
    have h_16_ne_one : (16 : ℝ) ≠ 1 := by norm_num
    have h_2_pos : (2 : ℝ) > 0 := by norm_num
    have h_2_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h_16_eq_2_pow_4 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    have h_logb_2_16_eq_4 : Real.logb 2 16 = 4 := by
      rw [h_16_eq_2_pow_4]
      apply Real.logb_rpow h_2_pos h_2_ne_one
    have h_logb_2_16_ne_zero : Real.logb 2 16 ≠ 0 := by
      rw [h_logb_2_16_eq_4]
      norm_num
    have h_change_base : Real.logb 16 n_cast_real = (Real.logb 2 n_cast_real) / (Real.logb 2 16) :=
      by
      have h_log_chain_rule : Real.logb 2 16 * Real.logb 16 n_cast_real = Real.logb 2 n_cast_real := by
        have cond_16_ne_0 : (16 : ℝ) ≠ 0 := ne_of_gt h_16_pos
        have cond_16_ne_neg_1 : (16 : ℝ) ≠ -1 := by norm_num
        apply Real.mul_logb cond_16_ne_0 h_16_ne_one cond_16_ne_neg_1
      have h_commuted_log_chain_rule : (Real.logb 16 n_cast_real) * (Real.logb 2 16) = Real.logb 2 n_cast_real := by
        rw [mul_comm]
        exact h_log_chain_rule
      exact eq_div_of_mul_eq h_logb_2_16_ne_zero h_commuted_log_chain_rule
    rw [h_change_base]
    rw [X_n_def]
    rw [h_logb_2_16_eq_4]
  letI arg_LHS := Real.logb 16 n_cast_real
  retro' arg_LHS_def : arg_LHS = logb (16 : ℝ) n_cast_real := by funext; rfl
  have subprob_arg_LHS_def_proof : arg_LHS = X_n / 4 := by
    mkOpaque
    rw [arg_LHS_def]
    exact subprob_log16_n_eq_Xn_div_4_proof
  have subprob_Xn_div_4_ge_1_div_4_proof : X_n / 4 ≥ 1 / 4 := by
    mkOpaque
    have h_four_pos : (4 : ℝ) > 0 := by norm_num
    apply (div_le_div_right h_four_pos).mpr
    exact subprob_Xn_ge_1_proof
  have subprob_1_div_4_gt_0_proof : (1 / 4 : ℝ) > 0 := by
    mkOpaque
    norm_num
  have subprob_arg_LHS_gt_0_proof : arg_LHS > 0 := by
    mkOpaque
    have h_arg_LHS_is_Xn_div_4 : arg_LHS = X_n / (4 : ℝ) := by exact subprob_arg_LHS_def_proof
    rw [h_arg_LHS_is_Xn_div_4]
    have h_Xn_div_4_ge_one_div_4 : X_n / (4 : ℝ) ≥ (1 : ℝ) / (4 : ℝ) := by exact subprob_Xn_div_4_ge_1_div_4_proof
    have h_one_div_4_gt_zero : (1 : ℝ) / (4 : ℝ) > (0 : ℝ) := by exact subprob_1_div_4_gt_0_proof
    apply gt_of_ge_of_gt h_Xn_div_4_ge_one_div_4 h_one_div_4_gt_zero
  have subprob_log4_n_eq_Xn_div_2_proof : Real.logb 4 n_cast_real = X_n / 2 := by
    mkOpaque
    have h_four_eq_two_sq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h_four_eq_two_sq]
    have h_target_transform : logb ((2 : ℝ) ^ (2 : ℕ)) n_cast_real = (logb (2 : ℝ) n_cast_real) / (2 : ℝ) := by
      let B := (2 : ℝ)
      let K_nat := (2 : ℕ)
      let K_real : ℝ := ↑K_nat
      let X := n_cast_real
      have hB_pos : 0 < B := by
        dsimp only [B]
        linarith [subprob_base_2_gt_1_proof]
      have hB_ne_one : B ≠ 1 := by
        dsimp only [B]
        linarith [subprob_base_2_gt_1_proof]
      have hX_pos : 0 < X := subprob_n_cast_real_gt_0_proof
      have hBK_pos : 0 < B ^ K_nat := by apply pow_pos hB_pos
      have hBK_ne_one : B ^ K_nat ≠ 1 :=
        by
        suffices h_eq_4 : B ^ K_nat = (4 : ℝ) by {linarith [h_eq_4]
        }
        dsimp only [B, K_nat]
        norm_num
      rw [Real.logb_eq_iff_rpow_eq hBK_pos hBK_ne_one hX_pos]
      rw [← Real.rpow_natCast B K_nat]
      have h_rpow_applied : (B ^ (↑K_nat : ℝ)) ^ (logb (2 : ℝ) n_cast_real / (2 : ℝ)) = B ^ ((↑K_nat : ℝ) * (logb (2 : ℝ) n_cast_real / (2 : ℝ))) := Eq.symm (Real.rpow_mul (le_of_lt hB_pos) _ _)
      rw [h_rpow_applied]
      have hK_real_ne_zero : K_real ≠ 0 := by
        simp only [K_real, K_nat]
        norm_num
      simp only [K_real, K_nat, B, X] at *
      have h_exponent_simpl : ((↑(2 : ℕ)) : ℝ) * (logb (2 : ℝ) n_cast_real / (2 : ℝ)) = logb (2 : ℝ) n_cast_real := by
        have h_coeff_cast_eq_literal : ((↑(2 : ℕ)) : ℝ) = (2 : ℝ) := by norm_cast
        rw [h_coeff_cast_eq_literal]
        rw [← mul_div_assoc]
        apply mul_div_cancel_left₀ (logb (2 : ℝ) n_cast_real)
        norm_num
      rw [h_exponent_simpl]
      rw [Real.rpow_logb hB_pos hB_ne_one hX_pos]
    rw [h_target_transform]
    rw [X_n_def]
  letI arg_RHS_inner := Real.logb 4 n_cast_real
  retro' arg_RHS_inner_def : arg_RHS_inner = logb (4 : ℝ) n_cast_real := by funext; rfl
  have subprob_arg_RHS_inner_def_proof : arg_RHS_inner = X_n / 2 := by
    mkOpaque
    rw [arg_RHS_inner_def]
    exact subprob_log4_n_eq_Xn_div_2_proof
  have subprob_Xn_div_2_ge_1_div_2_proof : X_n / 2 ≥ 1 / 2 := by
    mkOpaque
    have h_two_pos : (2 : ℝ) > 0 := by norm_num
    rw [ge_iff_le]
    apply (div_le_div_right h_two_pos).mpr
    exact subprob_Xn_ge_1_proof
  have subprob_1_div_2_gt_0_proof : (1 / 2 : ℝ) > 0 := by
    mkOpaque
    norm_num
  have subprob_arg_RHS_inner_gt_0_proof : arg_RHS_inner > 0 := by
    mkOpaque
    rw [subprob_arg_RHS_inner_def_proof]
    apply gt_of_ge_of_gt
    . exact subprob_Xn_div_2_ge_1_div_2_proof
    . exact subprob_1_div_2_gt_0_proof
  have subprob_h1_transformed_1_proof : Real.logb 2 (X_n / 4) = Real.logb 4 (X_n / 2) := by
    mkOpaque
    rw [← subprob_log16_n_eq_Xn_div_4_proof]
    rw [← subprob_log4_n_eq_Xn_div_2_proof]
    rw [n_cast_real_def]
    exact h₁
  letI val_for_log4 := X_n / 2
  retro' val_for_log4_def : val_for_log4 = X_n / (2 : ℝ) := by funext; rfl
  have subprob_val_for_log4_def_proof :
    val_for_log4 = X_n / 2 :=
    by
      mkOpaque
      exact val_for_log4_def
  have subprob_val_for_log4_gt_0_proof : val_for_log4 > 0 := by
    mkOpaque
    rw [val_for_log4_def]
    rw [← subprob_arg_RHS_inner_def_proof]
    exact subprob_arg_RHS_inner_gt_0_proof
  have subprob_log4_val_for_log4_eq_log2_div_2_proof : Real.logb 4 val_for_log4 = (Real.logb 2 val_for_log4) / 2 := by
    mkOpaque
    have h_four_eq_two_pow_two : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h_four_eq_two_pow_two]
    have h_val_gt_0 : (0 : ℝ) < val_for_log4 := subprob_val_for_log4_gt_0_proof
    have h2_gt_0 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h2_ne_1 : (2 : ℝ) ≠ (1 : ℝ) := by norm_num
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (2 : ℝ) > 1)
    have h_log2_ne_0 : Real.log 2 ≠ 0 := ne_of_gt h_log2_pos
    have h_base_lhs_pos : 0 < (2 : ℝ) ^ (2 : ℕ) := by
      rw [← h_four_eq_two_pow_two]
      norm_num
    have h_base_lhs_ne_1 : (2 : ℝ) ^ (2 : ℕ) ≠ 1 := by
      rw [← h_four_eq_two_pow_two]
      norm_num
    have h_logb_lhs_eq_log_div_log : logb ((2 : ℝ) ^ (2 : ℕ)) val_for_log4 = Real.log val_for_log4 / Real.log ((2 : ℝ) ^ (2 : ℕ)) := by rfl
    rw [h_logb_lhs_eq_log_div_log]
    have h_log_of_2_pow_2_eq_2log2 : Real.log ((2 : ℝ) ^ (2 : ℕ)) = ↑(2 : ℕ) * Real.log 2 := by exact Real.log_pow (2 : ℝ) (2 : ℕ)
    rw [h_log_of_2_pow_2_eq_2log2]
    rw [Nat.cast_two]
    have h_logb_rhs_num_eq_log_div_log : logb (2 : ℝ) val_for_log4 = Real.log val_for_log4 / Real.log (2 : ℝ) := by rfl
    rw [h_logb_rhs_num_eq_log_div_log]
    rw [← div_mul_eq_div_div]
    rw [mul_comm (Real.log 2) (2 : ℝ)]
      -- Uses Real.logb_rpow_base
  have subprob_h1_transformed_2_proof : Real.logb 2 (X_n / 4) = (Real.logb 2 (X_n / 2)) / 2 := by
    mkOpaque
    rw [subprob_h1_transformed_1_proof]
    rw [← val_for_log4_def]
    exact subprob_log4_val_for_log4_eq_log2_div_2_proof
  have subprob_Xn_gt_0_proof : X_n > 0 := by
    mkOpaque
    have h_one_gt_zero : (1 : ℝ) > (0 : ℝ) := by norm_num
    exact gt_of_ge_of_gt subprob_Xn_ge_1_proof h_one_gt_zero
  have subprob_LHS_expanded_proof : Real.logb 2 (X_n / 4) = Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 X_n := by
    mkOpaque
    have h_base_gt_1 : (2 : ℝ) > 1 := subprob_base_2_gt_1_proof
    have h_one_div_4_pos : (1 / 4 : ℝ) > 0 := subprob_1_div_4_gt_0_proof
    have h_Xn_pos : X_n > 0 := subprob_Xn_gt_0_proof
    rw [div_eq_mul_one_div X_n (4 : ℝ)]
    rw [mul_comm X_n (1 / (4 : ℝ))]
    have h_base_pos : (2 : ℝ) > 0 := lt_trans (by norm_num : (0 : ℝ) < 1) h_base_gt_1
    have h_base_ne_one : (2 : ℝ) ≠ 1 := ne_of_gt h_base_gt_1
    have h_one_div_4_ne_zero : (1 / 4 : ℝ) ≠ 0 := ne_of_gt h_one_div_4_pos
    have h_Xn_ne_zero : X_n ≠ 0 := ne_of_gt h_Xn_pos
    rw [show Real.logb (2 : ℝ) ((1 / 4 : ℝ) * X_n) = Real.logb (2 : ℝ) (1 / 4 : ℝ) + Real.logb (2 : ℝ) X_n from Real.logb_mul h_one_div_4_ne_zero h_Xn_ne_zero]
  have subprob_RHS_term_expanded_proof : Real.logb 2 (X_n / 2) = Real.logb 2 (1 / 2 : ℝ) + Real.logb 2 X_n := by
    mkOpaque
    rw [div_eq_inv_mul X_n (2 : ℝ)]
    have hb_pos : (0 : ℝ) < 2 := by norm_num
    have hb_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have hx1_pos : (0 : ℝ) < (2 : ℝ)⁻¹ := by
      simp only [inv_eq_one_div]
      norm_num
    have h_factor1_ne_zero : (2 : ℝ)⁻¹ ≠ 0 := ne_of_gt hx1_pos
    have hx2_pos : (0 : ℝ) < X_n := subprob_Xn_gt_0_proof
    have h_factor2_ne_zero : X_n ≠ 0 := ne_of_gt hx2_pos
    rw [Real.logb_mul h_factor1_ne_zero h_factor2_ne_zero]
    rw [inv_eq_one_div (2 : ℝ)]
      -- Needs Real.logb_mul, X_n > 0, 1/2 > 0. val_for_log4_gt_0 ensures X_n/2 > 0.
  have subprob_h1_expanded_proof : Real.logb 2 (1 / 4 : ℝ) + Real.logb 2 X_n = (Real.logb 2 (1 / 2 : ℝ) + Real.logb 2 X_n) / 2 := by
    mkOpaque
    rw [← subprob_LHS_expanded_proof]
    rw [← subprob_RHS_term_expanded_proof]
    exact subprob_h1_transformed_2_proof
  have subprob_log2_of_1_div_4_proof : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    mkOpaque
    have h_base_pos : (2 : ℝ) > 0 := by norm_num
    have h_base_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h_num_pos : (1 : ℝ) > 0 := by norm_num
    have h_den_pos : (4 : ℝ) > 0 := by norm_num
    have h_num_ne_zero : (1 : ℝ) ≠ 0 := by apply _root_.ne_of_gt h_num_pos
    have h_den_ne_zero : (4 : ℝ) ≠ 0 := by apply _root_.ne_of_gt h_den_pos
    have h_log_div : Real.logb (2 : ℝ) ((1 : ℝ) / (4 : ℝ)) = Real.logb (2 : ℝ) (1 : ℝ) - Real.logb (2 : ℝ) (4 : ℝ) := by apply Real.logb_div h_num_ne_zero h_den_ne_zero
    rw [h_log_div]
    have h_log_one : Real.logb (2 : ℝ) (1 : ℝ) = 0 := by apply Real.logb_one
    rw [h_log_one]
    have h_four_eq_two_sq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h_four_eq_two_sq]
    have h_log_self_pow : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 : ℕ)) = ↑(2 : ℕ) := by
      rw [Real.logb_pow h_base_pos]
      rw [Real.logb_self_eq_one subprob_base_2_gt_1_proof]
      simp
    rw [h_log_self_pow]
    norm_num
  have subprob_log2_of_1_div_2_proof : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    mkOpaque
    have h_logb_div_applied : Real.logb 2 (1 / 2 : ℝ) = Real.logb 2 1 - Real.logb 2 2 := by
      apply Real.logb_div
      · norm_num
      · norm_num
    rw [h_logb_div_applied]
    have h_logb_one_applied : Real.logb 2 1 = 0 := by apply Real.logb_one
    rw [h_logb_one_applied]
    have h_logb_self_applied : Real.logb 2 2 = 1 := by
      apply Real.logb_self_eq_one
      · exact subprob_base_2_gt_1_proof
    rw [h_logb_self_applied]
    simp
  letI L2X_n := Real.logb 2 X_n
  retro' L2X_n_def : L2X_n = logb (2 : ℝ) X_n := by funext; rfl
  have subprob_L2Xn_def_proof : L2X_n = Real.logb 2 X_n := by
    mkOpaque
    rw [L2X_n_def]
  have subprob_h1_subs_log_vals_proof : -2 + L2X_n = (-1 + L2X_n) / 2 := by
    mkOpaque
    rw [← subprob_log2_of_1_div_4_proof]
    rw [← subprob_log2_of_1_div_2_proof]
    rw [L2X_n_def]
    exact subprob_h1_expanded_proof
  have subprob_h1_subs_log_vals_distrib_RHS_proof : -2 + L2X_n = -1 / 2 + L2X_n / 2 := by
    mkOpaque
    rw [subprob_h1_subs_log_vals_proof]
    rw [add_div (-(1 : ℝ)) L2X_n (2 : ℝ)]
      -- from subprob_h1_subs_log_vals by algebra (distributing /2)
  have subprob_L2Xn_intermediate_solve_proof : (1 / 2 : ℝ) * L2X_n = (3 / 2 : ℝ) := by
    mkOpaque
    let h_eq := subprob_h1_subs_log_vals_distrib_RHS_proof
    have h_rearranged : L2X_n - L2X_n / (2 : ℝ) = (2 : ℝ) - (1 : ℝ) / (2 : ℝ) := by linarith [h_eq]
    have h_lhs_simplified : L2X_n - L2X_n / (2 : ℝ) = (1 / 2 : ℝ) * L2X_n := by ring
    have h_rhs_simplified : (2 : ℝ) - (1 : ℝ) / (2 : ℝ) = (3 / 2 : ℝ) := by norm_num
    rw [h_lhs_simplified, h_rhs_simplified] at h_rearranged
    exact h_rearranged
  have subprob_L2Xn_eq_3_proof : L2X_n = 3 := by
    mkOpaque
    have h_eq : (1 : ℝ) / (2 : ℝ) * L2X_n = (3 : ℝ) / (2 : ℝ) := subprob_L2Xn_intermediate_solve_proof
    have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    rw [one_div_mul_eq_div (2 : ℝ) L2X_n] at h_eq
    exact (div_left_inj' h_two_ne_zero).mp h_eq
  have subprob_Xn_eq_2_pow_3_proof : X_n = (2 : ℝ) ^ 3 := by
    mkOpaque
    have h_log_Xn_eq_3 : logb (2 : ℝ) X_n = (3 : ℝ) := by
      rw [← L2X_n_def]
      exact subprob_L2Xn_eq_3_proof
    have h_Xn_eq_rpow_real_exp : X_n = (2 : ℝ) ^ (3 : ℝ) := by
      apply Eq.symm
      apply (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) subprob_Xn_gt_0_proof).mp
      exact h_log_Xn_eq_3
    rw [h_Xn_eq_rpow_real_exp]
    exact Real.rpow_nat_cast (2 : ℝ) 3
  have subprob_2_pow_3_is_8_proof : (2 : ℝ) ^ 3 = 8 := by
    mkOpaque
    norm_num
  have subprob_Xn_eq_8_proof : X_n = 8 := by
    mkOpaque
    rw [subprob_Xn_eq_2_pow_3_proof]
    exact subprob_2_pow_3_is_8_proof
  have subprob_n_cast_real_eq_2_pow_8_proof : n_cast_real = (2 : ℝ) ^ 8 := by
    mkOpaque
    have h_log_eq : logb (2 : ℝ) n_cast_real = (8 : ℝ) := by
      rw [← X_n_def]
      exact subprob_Xn_eq_8_proof
    have h_base_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_base_ne_one : (2 : ℝ) ≠ 1 := by norm_num
    have h_n_cast_real_eq_rpow : n_cast_real = Real.rpow (2 : ℝ) (8 : ℝ) := by
      rw [eq_comm]
      apply (Real.logb_eq_iff_rpow_eq h_base_pos h_base_ne_one subprob_n_cast_real_gt_0_proof).mp
      exact h_log_eq
    rw [h_n_cast_real_eq_rpow]
    rw [← Real.rpow_nat_cast (2 : ℝ) 8]
    rfl
  have subprob_2_pow_8_is_256_proof : (2 : ℝ) ^ 8 = 256 := by
    mkOpaque
    norm_num
  have subprob_n_cast_real_eq_256_proof : n_cast_real = 256 := by
    mkOpaque
    rw [subprob_n_cast_real_eq_2_pow_8_proof]
    exact subprob_2_pow_8_is_256_proof
  have subprob_n_eq_256_proof : n = 256 := by
    mkOpaque
    have h_final_eq_real : (↑n : ℝ) = (256 : ℝ) := by
      rw [Eq.symm n_cast_real_def]
      exact subprob_n_cast_real_eq_256_proof
    apply (Nat.cast_inj (R := ℝ)).mp
    exact h_final_eq_real
  have subprob_digits_n_is_digits_256_proof : Nat.digits 10 n = Nat.digits 10 256 := by
    mkOpaque
    rw [subprob_n_eq_256_proof]
  have subprob_digits_256_list_proof : Nat.digits 10 256 = [6, 5, 2] := by
    mkOpaque
    rfl
  have subprob_sum_list_652_proof : ([6, 5, 2] : List ℕ).sum = 13 := by
    mkOpaque
    rfl
  exact
    show (Nat.digits 10 n).sum = 13 by
      mkOpaque
      rw [subprob_n_eq_256_proof]
      rw [subprob_digits_256_list_proof]
      exact subprob_sum_list_652_proof

#print axioms amc12a_2020_p10

/-Sketch
variable (n : ℕ) (h₀ : 0 < n) (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) (h₂ : n ≠ 1)
play
  -- Step 1: Handle n and its properties
  subprob_n_ge_1_nat :≡ n ≥ 1
  subprob_n_ge_1_nat_proof ⇐ show subprob_n_ge_1_nat by sorry -- from h₀
  subprob_n_ge_2_nat :≡ n ≥ 2
  subprob_n_ge_2_nat_proof ⇐ show subprob_n_ge_2_nat by sorry -- from subprob_n_ge_1_nat and h₂

  n_cast_real := (n : ℝ)
  subprob_n_cast_real_def :≡ n_cast_real = (n : ℝ) -- This is a definition, not a proposition to prove
  subprob_n_cast_real_def_proof ⇐ show subprob_n_cast_real_def by sorry

  subprob_n_cast_real_ge_2 :≡ n_cast_real ≥ 2
  subprob_n_cast_real_ge_2_proof ⇐ show subprob_n_cast_real_ge_2 by sorry -- from subprob_n_ge_2_nat and Nat.cast_le
  subprob_n_cast_real_gt_0 :≡ n_cast_real > 0
  subprob_n_cast_real_gt_0_proof ⇐ show subprob_n_cast_real_gt_0 by sorry -- from subprob_n_cast_real_ge_2 (since 2 > 0)

  -- Step 2: Define X_n = log₂(n) and prove X_n ≥ 1
  X_n := Real.logb 2 n_cast_real
  subprob_Xn_def :≡ X_n = Real.logb 2 n_cast_real -- Definition
  subprob_Xn_def_proof ⇐ show subprob_Xn_def by sorry

  subprob_base_2_gt_1 :≡ (2 : ℝ) > 1
  subprob_base_2_gt_1_proof ⇐ show subprob_base_2_gt_1 by sorry
  subprob_log2_2_eq_1 :≡ Real.logb 2 2 = 1
  subprob_log2_2_eq_1_proof ⇐ show subprob_log2_2_eq_1 by sorry
  subprob_Xn_ge_1 :≡ X_n ≥ 1
  subprob_Xn_ge_1_proof ⇐ show subprob_Xn_ge_1 by sorry -- from subprob_n_cast_real_ge_2, Real.logb_le_logb_of_le (needs monotonic property of logb), subprob_base_2_gt_1, subprob_log2_2_eq_1

  -- Step 3: Transform logarithm bases to 2
  -- Arguments for outer logs need to be positive.
  -- For log₁₆ n = X_n / 4
  subprob_log16_n_eq_Xn_div_4 :≡ Real.logb 16 n_cast_real = X_n / 4
  subprob_log16_n_eq_Xn_div_4_proof ⇐ show subprob_log16_n_eq_Xn_div_4 by sorry -- Uses Real.logb_rpow_base (16 = 2^4), requires n_cast_real > 0
  arg_LHS := Real.logb 16 n_cast_real
  subprob_arg_LHS_def :≡ arg_LHS = X_n / 4
  subprob_arg_LHS_def_proof ⇐ show subprob_arg_LHS_def by sorry

  subprob_Xn_div_4_ge_1_div_4 :≡ X_n / 4 ≥ 1/4
  subprob_Xn_div_4_ge_1_div_4_proof ⇐ show subprob_Xn_div_4_ge_1_div_4 by sorry -- From subprob_Xn_ge_1
  subprob_1_div_4_gt_0 :≡ (1/4 : ℝ) > 0
  subprob_1_div_4_gt_0_proof ⇐ show subprob_1_div_4_gt_0 by sorry
  subprob_arg_LHS_gt_0 :≡ arg_LHS > 0
  subprob_arg_LHS_gt_0_proof ⇐ show subprob_arg_LHS_gt_0 by sorry -- From subprob_arg_LHS_def, subprob_Xn_div_4_ge_1_div_4, subprob_1_div_4_gt_0

  -- For log₄ n = X_n / 2
  subprob_log4_n_eq_Xn_div_2 :≡ Real.logb 4 n_cast_real = X_n / 2
  subprob_log4_n_eq_Xn_div_2_proof ⇐ show subprob_log4_n_eq_Xn_div_2 by sorry -- Uses Real.logb_rpow_base (4 = 2^2)
  arg_RHS_inner := Real.logb 4 n_cast_real
  subprob_arg_RHS_inner_def :≡ arg_RHS_inner = X_n / 2
  subprob_arg_RHS_inner_def_proof ⇐ show subprob_arg_RHS_inner_def by sorry

  subprob_Xn_div_2_ge_1_div_2 :≡ X_n / 2 ≥ 1/2
  subprob_Xn_div_2_ge_1_div_2_proof ⇐ show subprob_Xn_div_2_ge_1_div_2 by sorry -- From subprob_Xn_ge_1
  subprob_1_div_2_gt_0 :≡ (1/2 : ℝ) > 0
  subprob_1_div_2_gt_0_proof ⇐ show subprob_1_div_2_gt_0 by sorry
  subprob_arg_RHS_inner_gt_0 :≡ arg_RHS_inner > 0
  subprob_arg_RHS_inner_gt_0_proof ⇐ show subprob_arg_RHS_inner_gt_0 by sorry

  -- Substitute into h₁: log₂(X_n / 4) = log₄(X_n / 2)
  subprob_h1_transformed_1 :≡ Real.logb 2 (X_n / 4) = Real.logb 4 (X_n / 2)
  subprob_h1_transformed_1_proof ⇐ show subprob_h1_transformed_1 by sorry -- from h₁, subprob_log16_n_eq_Xn_div_4, subprob_log4_n_eq_Xn_div_2 using arg_LHS_def, arg_RHS_inner_def

  -- Transform RHS outer log: log₄(X_n / 2) = (1/2) log₂(X_n / 2)
  val_for_log4 := X_n / 2
  subprob_val_for_log4_def :≡ val_for_log4 = X_n / 2 -- Definition
  subprob_val_for_log4_def_proof ⇐ show subprob_val_for_log4_def by sorry
  subprob_val_for_log4_gt_0 :≡ val_for_log4 > 0
  subprob_val_for_log4_gt_0_proof ⇐ show subprob_val_for_log4_gt_0 by sorry -- from subprob_Xn_ge_1 (implies X_n/2 >= 1/2 > 0)
  subprob_log4_val_for_log4_eq_log2_div_2 :≡ Real.logb 4 val_for_log4 = (Real.logb 2 val_for_log4) / 2
  subprob_log4_val_for_log4_eq_log2_div_2_proof ⇐ show subprob_log4_val_for_log4_eq_log2_div_2 by sorry -- Uses Real.logb_rpow_base

  -- Equation becomes: log₂(X_n / 4) = (log₂(X_n / 2)) / 2
  subprob_h1_transformed_2 :≡ Real.logb 2 (X_n / 4) = (Real.logb 2 (X_n / 2)) / 2
  subprob_h1_transformed_2_proof ⇐ show subprob_h1_transformed_2 by sorry -- from subprob_h1_transformed_1, subprob_log4_val_for_log4_eq_log2_div_2, subprob_val_for_log4_def

  -- Step 4: Expand logarithms
  subprob_Xn_gt_0 :≡ X_n > 0
  subprob_Xn_gt_0_proof ⇐ show subprob_Xn_gt_0 by sorry -- from subprob_Xn_ge_1

  subprob_LHS_expanded :≡ Real.logb 2 (X_n / 4) = Real.logb 2 (1/4 : ℝ) + Real.logb 2 X_n
  subprob_LHS_expanded_proof ⇐ show subprob_LHS_expanded by sorry -- Needs Real.logb_mul (or div), X_n > 0, 1/4 > 0. arg_LHS_gt_0 ensures X_n/4 > 0.
  subprob_RHS_term_expanded :≡ Real.logb 2 (X_n / 2) = Real.logb 2 (1/2 : ℝ) + Real.logb 2 X_n
  subprob_RHS_term_expanded_proof ⇐ show subprob_RHS_term_expanded by sorry -- Needs Real.logb_mul, X_n > 0, 1/2 > 0. val_for_log4_gt_0 ensures X_n/2 > 0.

  subprob_h1_expanded :≡ Real.logb 2 (1/4 : ℝ) + Real.logb 2 X_n = (Real.logb 2 (1/2 : ℝ) + Real.logb 2 X_n) / 2
  subprob_h1_expanded_proof ⇐ show subprob_h1_expanded by sorry -- from subprob_h1_transformed_2, subprob_LHS_expanded, subprob_RHS_term_expanded.

  -- Step 5: Substitute known log values
  subprob_log2_of_1_div_4 :≡ Real.logb 2 (1/4 : ℝ) = -2
  subprob_log2_of_1_div_4_proof ⇐ show subprob_log2_of_1_div_4 by sorry
  subprob_log2_of_1_div_2 :≡ Real.logb 2 (1/2 : ℝ) = -1
  subprob_log2_of_1_div_2_proof ⇐ show subprob_log2_of_1_div_2 by sorry

  L2X_n := Real.logb 2 X_n
  subprob_L2Xn_def :≡ L2X_n = Real.logb 2 X_n -- Definition
  subprob_L2Xn_def_proof ⇐ show subprob_L2Xn_def by sorry

  subprob_h1_subs_log_vals :≡ -2 + L2X_n = (-1 + L2X_n) / 2
  subprob_h1_subs_log_vals_proof ⇐ show subprob_h1_subs_log_vals by sorry -- from subprob_h1_expanded, subprob_log2_of_1_div_4, subprob_log2_of_1_div_2, subprob_L2Xn_def.

  -- Step 6: Solve for L2X_n
  subprob_h1_subs_log_vals_distrib_RHS :≡ -2 + L2X_n = -1/2 + L2X_n / 2
  subprob_h1_subs_log_vals_distrib_RHS_proof ⇐ show subprob_h1_subs_log_vals_distrib_RHS by sorry -- from subprob_h1_subs_log_vals by algebra (distributing /2)
  subprob_L2Xn_intermediate_solve :≡ (1/2 : ℝ) * L2X_n = (3/2 : ℝ)
  subprob_L2Xn_intermediate_solve_proof ⇐ show subprob_L2Xn_intermediate_solve by sorry -- from subprob_h1_subs_log_vals_distrib_RHS by algebraic rearrangement
  subprob_L2Xn_eq_3 :≡ L2X_n = 3
  subprob_L2Xn_eq_3_proof ⇐ show subprob_L2Xn_eq_3 by sorry -- from subprob_L2Xn_intermediate_solve by multiplying by 2

  -- Step 7: Solve for n
  subprob_Xn_eq_2_pow_3 :≡ X_n = (2 : ℝ) ^ 3
  subprob_Xn_eq_2_pow_3_proof ⇐ show subprob_Xn_eq_2_pow_3 by sorry -- From subprob_L2Xn_eq_3, subprob_L2Xn_def, Real.logb_eq_iff_eq_rpow, subprob_Xn_gt_0.
  subprob_2_pow_3_is_8 :≡ (2 : ℝ) ^ 3 = 8
  subprob_2_pow_3_is_8_proof ⇐ show subprob_2_pow_3_is_8 by sorry
  subprob_Xn_eq_8 :≡ X_n = 8
  subprob_Xn_eq_8_proof ⇐ show subprob_Xn_eq_8 by sorry -- from subprob_Xn_eq_2_pow_3 and subprob_2_pow_3_is_8

  subprob_n_cast_real_eq_2_pow_8 :≡ n_cast_real = (2 : ℝ) ^ 8
  subprob_n_cast_real_eq_2_pow_8_proof ⇐ show subprob_n_cast_real_eq_2_pow_8 by sorry -- From subprob_Xn_eq_8, subprob_Xn_def, Real.logb_eq_iff_eq_rpow, subprob_n_cast_real_gt_0.
  subprob_2_pow_8_is_256 :≡ (2 : ℝ) ^ 8 = 256
  subprob_2_pow_8_is_256_proof ⇐ show subprob_2_pow_8_is_256 by sorry
  subprob_n_cast_real_eq_256 :≡ n_cast_real = 256
  subprob_n_cast_real_eq_256_proof ⇐ show subprob_n_cast_real_eq_256 by sorry

  subprob_n_eq_256 :≡ n = 256
  subprob_n_eq_256_proof ⇐ show subprob_n_eq_256 by sorry -- from subprob_n_cast_real_eq_256, subprob_n_cast_real_def, and Nat.cast_inj.

  -- Step 8: Sum of digits
  subprob_digits_n_is_digits_256 :≡ Nat.digits 10 n = Nat.digits 10 256
  subprob_digits_n_is_digits_256_proof ⇐ show subprob_digits_n_is_digits_256 by sorry -- from subprob_n_eq_256
  subprob_digits_256_list :≡ Nat.digits 10 256 = [6, 5, 2]
  subprob_digits_256_list_proof ⇐ show subprob_digits_256_list by sorry
  subprob_sum_list_652 :≡ ([6, 5, 2] : List ℕ).sum = 13
  subprob_sum_list_652_proof ⇐ show subprob_sum_list_652 by sorry

  subprob_final_goal :≡ (Nat.digits 10 n).sum = 13
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
variable (n : ℕ) (h₀ : 0 < n) (h₁ : Real.logb 2 (Real.logb 16 n) = Real.logb 4 (Real.logb 4 n)) (h₂ : n ≠ 1)
play
  subprob_n_ge_1_nat :≡ n ≥ 1
  subprob_n_ge_1_nat_proof ⇐ show subprob_n_ge_1_nat by


    apply Nat.one_le_of_lt
    exact h₀
 -- from h₀
  subprob_n_ge_2_nat :≡ n ≥ 2
  subprob_n_ge_2_nat_proof ⇐ show subprob_n_ge_2_nat by


    have h_n_ge_1 : n ≥ 1 := subprob_n_ge_1_nat_proof
    cases Nat.eq_or_lt_of_le h_n_ge_1 with
    | inl h_n_eq_1 =>
      rw [←h_n_eq_1] at h₂
      contradiction
    | inr h_n_gt_1 =>
      exact Nat.succ_le_of_lt h_n_gt_1
 -- from subprob_n_ge_1_nat and h₂

  n_cast_real := (n : ℝ)
  subprob_n_cast_real_def :≡ n_cast_real = (n : ℝ) -- This is a definition, not a proposition to prove
  subprob_n_cast_real_def_proof ⇐ show subprob_n_cast_real_def by

    rw [n_cast_real_def]



  subprob_n_cast_real_ge_2 :≡ n_cast_real ≥ 2
  subprob_n_cast_real_ge_2_proof ⇐ show subprob_n_cast_real_ge_2 by











    have h_n_cast_pos : (0 : ℝ) < (n : ℝ) := by
      have h_n_ge_1 : n ≥ 1 := Nat.succ_le_iff.mpr h₀
      have h_n_cast_ge_1 : (n : ℝ) ≥ (1 : ℝ) :=
        (@Nat.cast_one ℝ _) ▸ (Nat.cast_le.mpr h_n_ge_1)
      linarith

    have h_log16_n_gt_0 : logb 16 (n : ℝ) > 0 := by
      apply Decidable.byContradiction
      intro h_not_gt_log16_n_zero
      have h_log16_n_le_0 : logb 16 (n:ℝ) ≤ 0 := le_of_not_lt h_not_gt_log16_n_zero
      have h_base_16_gt_1 : (16 : ℝ) > 1 := by norm_num
      have h_n_cast_le_1 : (n : ℝ) ≤ 1 := by
        rw [← (Real.logb_nonpos_iff h_base_16_gt_1 h_n_cast_pos)]
        exact h_log16_n_le_0
      have h_n_ge_1_nat : n ≥ 1 := Nat.succ_le_of_lt h₀
      have h_n_cast_ge_1 : (n : ℝ) ≥ 1 := by
        exact (@Nat.cast_one ℝ _) ▸ (Nat.cast_le.mpr h_n_ge_1_nat)
      have h_n_cast_eq_1 : (n : ℝ) = 1 := le_antisymm h_n_cast_le_1 h_n_cast_ge_1
      have h_n_eq_1 : n = 1 := Nat.cast_inj.mp ((@Nat.cast_one ℝ _).symm ▸ h_n_cast_eq_1)
      exact h₂ h_n_eq_1

    have h_base_16_gt_1_for_pos : (16 : ℝ) > 1 := by norm_num
    have h_n_cast_gt_1 : (n : ℝ) > 1 := by
      apply (Real.logb_pos_iff h_base_16_gt_1_for_pos h_n_cast_pos).mp
      exact h_log16_n_gt_0

    have h_n_gt_1_nat : n > 1 := by
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num] at h_n_cast_gt_1
      exact Nat.cast_lt.mp h_n_cast_gt_1

    have h_n_ge_2_nat : n ≥ 2 := Nat.succ_le_of_lt h_n_gt_1_nat

    rw [n_cast_real_def]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    apply Nat.cast_le.mpr
    exact h_n_ge_2_nat

 -- from subprob_n_ge_2_nat and Nat.cast_le
  subprob_n_cast_real_gt_0 :≡ n_cast_real > 0
  subprob_n_cast_real_gt_0_proof ⇐ show subprob_n_cast_real_gt_0 by

    have h_two_is_positive : (2 : ℝ) > (0 : ℝ) := by
      norm_num

    exact gt_of_ge_of_gt subprob_n_cast_real_ge_2_proof h_two_is_positive -- from subprob_n_cast_real_ge_2 (since 2 > 0)

  X_n := Real.logb 2 n_cast_real
  subprob_Xn_def :≡ X_n = Real.logb 2 n_cast_real -- Definition
  subprob_Xn_def_proof ⇐ show subprob_Xn_def by

    exact X_n_def


  subprob_base_2_gt_1 :≡ (2 : ℝ) > 1
  subprob_base_2_gt_1_proof ⇐ show subprob_base_2_gt_1 by
    norm_num
  subprob_log2_2_eq_1 :≡ Real.logb 2 2 = 1
  subprob_log2_2_eq_1_proof ⇐ show subprob_log2_2_eq_1 by


    have h_two_gt_zero : (2 : ℝ) > 0 := by
      norm_num

    have h_two_ne_one : (2 : ℝ) ≠ 1 := by
      norm_num

    apply Real.logb_self_eq_one
    exact subprob_base_2_gt_1_proof

  subprob_Xn_ge_1 :≡ X_n ≥ 1
  subprob_Xn_ge_1_proof ⇐ show subprob_Xn_ge_1 by




    rw [X_n_def]



    apply (Real.le_logb_iff_rpow_le subprob_base_2_gt_1_proof subprob_n_cast_real_gt_0_proof).mpr

    rw [rpow_one]

    exact subprob_n_cast_real_ge_2_proof

 -- from subprob_n_cast_real_ge_2, Real.logb_le_logb_of_le (needs monotonic property of logb), subprob_base_2_gt_1, subprob_log2_2_eq_1

  subprob_log16_n_eq_Xn_div_4 :≡ Real.logb 16 n_cast_real = X_n / 4
  subprob_log16_n_eq_Xn_div_4_proof ⇐ show subprob_log16_n_eq_Xn_div_4 by











    have h_16_pos : (16 : ℝ) > 0 := by
      norm_num
    have h_16_ne_one : (16 : ℝ) ≠ 1 := by
      norm_num
    have h_2_pos : (2 : ℝ) > 0 := by
      norm_num
    have h_2_ne_one : (2 : ℝ) ≠ 1 := by
      norm_num

    have h_16_eq_2_pow_4 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
      norm_num
    have h_logb_2_16_eq_4 : Real.logb 2 16 = 4 := by
      rw [h_16_eq_2_pow_4]
      apply Real.logb_rpow h_2_pos h_2_ne_one

    have h_logb_2_16_ne_zero : Real.logb 2 16 ≠ 0 := by
      rw [h_logb_2_16_eq_4]
      norm_num

    have h_change_base : Real.logb 16 n_cast_real = (Real.logb 2 n_cast_real) / (Real.logb 2 16) := by
      have h_log_chain_rule : Real.logb 2 16 * Real.logb 16 n_cast_real = Real.logb 2 n_cast_real := by
        have cond_16_ne_0 : (16 : ℝ) ≠ 0 := ne_of_gt h_16_pos
        have cond_16_ne_neg_1 : (16 : ℝ) ≠ -1 := by norm_num
        apply Real.mul_logb cond_16_ne_0 h_16_ne_one cond_16_ne_neg_1
      have h_commuted_log_chain_rule : (Real.logb 16 n_cast_real) * (Real.logb 2 16) = Real.logb 2 n_cast_real := by
        rw [mul_comm]
        exact h_log_chain_rule
      exact eq_div_of_mul_eq h_logb_2_16_ne_zero h_commuted_log_chain_rule

    rw [h_change_base]

    rw [X_n_def]

    rw [h_logb_2_16_eq_4]






 -- Uses Real.logb_rpow_base (16 = 2^4), requires n_cast_real > 0
  arg_LHS := Real.logb 16 n_cast_real
  subprob_arg_LHS_def :≡ arg_LHS = X_n / 4
  subprob_arg_LHS_def_proof ⇐ show subprob_arg_LHS_def by


    rw [arg_LHS_def]

    exact subprob_log16_n_eq_Xn_div_4_proof

  subprob_Xn_div_4_ge_1_div_4 :≡ X_n / 4 ≥ 1/4
  subprob_Xn_div_4_ge_1_div_4_proof ⇐ show subprob_Xn_div_4_ge_1_div_4 by



    have h_four_pos : (4 : ℝ) > 0 := by
      norm_num

    apply (div_le_div_right h_four_pos).mpr

    exact subprob_Xn_ge_1_proof -- From subprob_Xn_ge_1
  subprob_1_div_4_gt_0 :≡ (1/4 : ℝ) > 0
  subprob_1_div_4_gt_0_proof ⇐ show subprob_1_div_4_gt_0 by
    norm_num
  subprob_arg_LHS_gt_0 :≡ arg_LHS > 0
  subprob_arg_LHS_gt_0_proof ⇐ show subprob_arg_LHS_gt_0 by

    have h_arg_LHS_is_Xn_div_4 : arg_LHS = X_n / (4 : ℝ) := by
      exact subprob_arg_LHS_def_proof

    rw [h_arg_LHS_is_Xn_div_4]

    have h_Xn_div_4_ge_one_div_4 : X_n / (4 : ℝ) ≥ (1 : ℝ) / (4 : ℝ) := by
      exact subprob_Xn_div_4_ge_1_div_4_proof

    have h_one_div_4_gt_zero : (1 : ℝ) / (4 : ℝ) > (0 : ℝ) := by
      exact subprob_1_div_4_gt_0_proof

    apply gt_of_ge_of_gt h_Xn_div_4_ge_one_div_4 h_one_div_4_gt_zero -- From subprob_arg_LHS_def, subprob_Xn_div_4_ge_1_div_4, subprob_1_div_4_gt_0

  subprob_log4_n_eq_Xn_div_2 :≡ Real.logb 4 n_cast_real = X_n / 2
  subprob_log4_n_eq_Xn_div_2_proof ⇐ show subprob_log4_n_eq_Xn_div_2 by


    have h_four_eq_two_sq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by
      norm_num

    rw [h_four_eq_two_sq]

    have h_target_transform : logb ((2 : ℝ) ^ (2 : ℕ)) n_cast_real = (logb (2 : ℝ) n_cast_real) / (2 : ℝ) := by
      let B := (2 : ℝ)
      let K_nat := (2 : ℕ)
      let K_real : ℝ := ↑K_nat
      let X := n_cast_real

      have hB_pos : 0 < B := by
        dsimp only [B]
        linarith [subprob_base_2_gt_1_proof]
      have hB_ne_one : B ≠ 1 := by
        dsimp only [B]
        linarith [subprob_base_2_gt_1_proof]

      have hX_pos : 0 < X := subprob_n_cast_real_gt_0_proof

      have hBK_pos : 0 < B ^ K_nat := by
        apply pow_pos hB_pos
      have hBK_ne_one : B ^ K_nat ≠ 1 := by
        suffices h_eq_4 : B ^ K_nat = (4 : ℝ) by {
          linarith [h_eq_4]
        }
        dsimp only [B, K_nat]
        norm_num

      rw [Real.logb_eq_iff_rpow_eq hBK_pos hBK_ne_one hX_pos]

      rw [← Real.rpow_natCast B K_nat]
      have h_rpow_applied : (B ^ (↑K_nat : ℝ)) ^ (logb (2 : ℝ) n_cast_real / (2 : ℝ)) =
                              B ^ ((↑K_nat : ℝ) * (logb (2 : ℝ) n_cast_real / (2 : ℝ))) :=
        Eq.symm (Real.rpow_mul (le_of_lt hB_pos) _ _)
      rw [h_rpow_applied]

      have hK_real_ne_zero : K_real ≠ 0 := by
        simp only [K_real, K_nat]
        norm_num

      simp only [K_real, K_nat, B, X] at *

      have h_exponent_simpl : ((↑(2 : ℕ)) : ℝ) * (logb (2 : ℝ) n_cast_real / (2 : ℝ)) = logb (2 : ℝ) n_cast_real := by
        have h_coeff_cast_eq_literal : ((↑(2 : ℕ)) : ℝ) = (2 : ℝ) := by norm_cast
        rw [h_coeff_cast_eq_literal]
        rw [← mul_div_assoc]
        apply mul_div_cancel_left₀ (logb (2:ℝ) n_cast_real)
        norm_num

      rw [h_exponent_simpl]

      rw [Real.rpow_logb hB_pos hB_ne_one hX_pos]


    rw [h_target_transform]

    rw [X_n_def]



 -- Uses Real.logb_rpow_base (4 = 2^2)
  arg_RHS_inner := Real.logb 4 n_cast_real
  subprob_arg_RHS_inner_def :≡ arg_RHS_inner = X_n / 2
  subprob_arg_RHS_inner_def_proof ⇐ show subprob_arg_RHS_inner_def by

    rw [arg_RHS_inner_def]

    exact subprob_log4_n_eq_Xn_div_2_proof


  subprob_Xn_div_2_ge_1_div_2 :≡ X_n / 2 ≥ 1/2
  subprob_Xn_div_2_ge_1_div_2_proof ⇐ show subprob_Xn_div_2_ge_1_div_2 by

    have h_two_pos : (2 : ℝ) > 0 := by
      norm_num

    rw [ge_iff_le]

    apply (div_le_div_right h_two_pos).mpr

    exact subprob_Xn_ge_1_proof -- From subprob_Xn_ge_1
  subprob_1_div_2_gt_0 :≡ (1/2 : ℝ) > 0
  subprob_1_div_2_gt_0_proof ⇐ show subprob_1_div_2_gt_0 by
    norm_num

  subprob_arg_RHS_inner_gt_0 :≡ arg_RHS_inner > 0
  subprob_arg_RHS_inner_gt_0_proof ⇐ show subprob_arg_RHS_inner_gt_0 by

    rw [subprob_arg_RHS_inner_def_proof]
    apply gt_of_ge_of_gt
    . exact subprob_Xn_div_2_ge_1_div_2_proof
    . exact subprob_1_div_2_gt_0_proof

  subprob_h1_transformed_1 :≡ Real.logb 2 (X_n / 4) = Real.logb 4 (X_n / 2)
  subprob_h1_transformed_1_proof ⇐ show subprob_h1_transformed_1 by


    rw [←subprob_log16_n_eq_Xn_div_4_proof]

    rw [←subprob_log4_n_eq_Xn_div_2_proof]

    rw [n_cast_real_def]

    exact h₁ -- from h₁, subprob_log16_n_eq_Xn_div_4, subprob_log4_n_eq_Xn_div_2 using arg_LHS_def, arg_RHS_inner_def

  val_for_log4 := X_n / 2
  subprob_val_for_log4_def :≡ val_for_log4 = X_n / 2 -- Definition
  subprob_val_for_log4_def_proof ⇐ show subprob_val_for_log4_def by
    exact val_for_log4_def
  subprob_val_for_log4_gt_0 :≡ val_for_log4 > 0
  subprob_val_for_log4_gt_0_proof ⇐ show subprob_val_for_log4_gt_0 by

    rw [val_for_log4_def]

    rw [← subprob_arg_RHS_inner_def_proof]

    exact subprob_arg_RHS_inner_gt_0_proof -- from subprob_Xn_ge_1 (implies X_n/2 >= 1/2 > 0)
  subprob_log4_val_for_log4_eq_log2_div_2 :≡ Real.logb 4 val_for_log4 = (Real.logb 2 val_for_log4) / 2
  subprob_log4_val_for_log4_eq_log2_div_2_proof ⇐ show subprob_log4_val_for_log4_eq_log2_div_2 by










    have h_four_eq_two_pow_two : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by
      norm_num

    rw [h_four_eq_two_pow_two]

    have h_val_gt_0 : (0 : ℝ) < val_for_log4 := subprob_val_for_log4_gt_0_proof
    have h2_gt_0 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h2_ne_1 : (2 : ℝ) ≠ (1 : ℝ) := by norm_num

    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (2:ℝ) > 1)
    have h_log2_ne_0 : Real.log 2 ≠ 0 := ne_of_gt h_log2_pos

    have h_base_lhs_pos : 0 < (2:ℝ)^(2:ℕ) := by
      rw [←h_four_eq_two_pow_two]
      norm_num
    have h_base_lhs_ne_1 : (2:ℝ)^(2:ℕ) ≠ 1 := by
      rw [←h_four_eq_two_pow_two]
      norm_num

    have h_logb_lhs_eq_log_div_log : logb ((2 : ℝ) ^ (2 : ℕ)) val_for_log4 = Real.log val_for_log4 / Real.log ((2 : ℝ) ^ (2 : ℕ)) := by
      rfl
    rw [h_logb_lhs_eq_log_div_log]

    have h_log_of_2_pow_2_eq_2log2 : Real.log ((2:ℝ)^(2:ℕ)) = ↑(2:ℕ) * Real.log 2 := by
      exact Real.log_pow (2 : ℝ) (2 : ℕ)
    rw [h_log_of_2_pow_2_eq_2log2]
    rw [Nat.cast_two]

    have h_logb_rhs_num_eq_log_div_log : logb (2 : ℝ) val_for_log4 = Real.log val_for_log4 / Real.log (2 : ℝ) := by
      rfl
    rw [h_logb_rhs_num_eq_log_div_log]

    rw [← div_mul_eq_div_div]

    rw [mul_comm (Real.log 2) (2:ℝ)]
 -- Uses Real.logb_rpow_base

  subprob_h1_transformed_2 :≡ Real.logb 2 (X_n / 4) = (Real.logb 2 (X_n / 2)) / 2
  subprob_h1_transformed_2_proof ⇐ show subprob_h1_transformed_2 by

    rw [subprob_h1_transformed_1_proof]

    rw [← val_for_log4_def]

    exact subprob_log4_val_for_log4_eq_log2_div_2_proof -- from subprob_h1_transformed_1, subprob_log4_val_for_log4_eq_log2_div_2, subprob_val_for_log4_def

  subprob_Xn_gt_0 :≡ X_n > 0
  subprob_Xn_gt_0_proof ⇐ show subprob_Xn_gt_0 by

    have h_one_gt_zero : (1 : ℝ) > (0 : ℝ) := by
      norm_num

    exact gt_of_ge_of_gt subprob_Xn_ge_1_proof h_one_gt_zero
 -- from subprob_Xn_ge_1

  subprob_LHS_expanded :≡ Real.logb 2 (X_n / 4) = Real.logb 2 (1/4 : ℝ) + Real.logb 2 X_n
  subprob_LHS_expanded_proof ⇐ show subprob_LHS_expanded by








    have h_base_gt_1 : (2 : ℝ) > 1 := subprob_base_2_gt_1_proof
    have h_one_div_4_pos : (1 / 4 : ℝ) > 0 := subprob_1_div_4_gt_0_proof
    have h_Xn_pos : X_n > 0 := subprob_Xn_gt_0_proof

    rw [div_eq_mul_one_div X_n (4 : ℝ)]
    rw [mul_comm X_n (1 / (4 : ℝ))]


    have h_base_pos : (2 : ℝ) > 0 := lt_trans (by norm_num : (0 : ℝ) < 1) h_base_gt_1
    have h_base_ne_one : (2 : ℝ) ≠ 1 := ne_of_gt h_base_gt_1

    have h_one_div_4_ne_zero : (1 / 4 : ℝ) ≠ 0 := ne_of_gt h_one_div_4_pos
    have h_Xn_ne_zero : X_n ≠ 0 := ne_of_gt h_Xn_pos

    rw [show Real.logb (2 : ℝ) ((1 / 4 : ℝ) * X_n) = Real.logb (2 : ℝ) (1 / 4 : ℝ) + Real.logb (2 : ℝ) X_n from Real.logb_mul h_one_div_4_ne_zero h_Xn_ne_zero]


 -- Needs Real.logb_mul (or div), X_n > 0, 1/4 > 0. arg_LHS_gt_0 ensures X_n/4 > 0.
  subprob_RHS_term_expanded :≡ Real.logb 2 (X_n / 2) = Real.logb 2 (1/2 : ℝ) + Real.logb 2 X_n
  subprob_RHS_term_expanded_proof ⇐ show subprob_RHS_term_expanded by





    rw [div_eq_inv_mul X_n (2 : ℝ)]



    have hb_pos : (0 : ℝ) < 2 := by norm_num
    have hb_ne_one : (2 : ℝ) ≠ 1 := by norm_num

    have hx1_pos : (0 : ℝ) < (2 : ℝ)⁻¹ := by
      simp only [inv_eq_one_div]
      norm_num
    have h_factor1_ne_zero : (2 : ℝ)⁻¹ ≠ 0 := ne_of_gt hx1_pos

    have hx2_pos : (0 : ℝ) < X_n := subprob_Xn_gt_0_proof
    have h_factor2_ne_zero : X_n ≠ 0 := ne_of_gt hx2_pos

    rw [Real.logb_mul h_factor1_ne_zero h_factor2_ne_zero]

    rw [inv_eq_one_div (2 : ℝ)]
 -- Needs Real.logb_mul, X_n > 0, 1/2 > 0. val_for_log4_gt_0 ensures X_n/2 > 0.

  subprob_h1_expanded :≡ Real.logb 2 (1/4 : ℝ) + Real.logb 2 X_n = (Real.logb 2 (1/2 : ℝ) + Real.logb 2 X_n) / 2
  subprob_h1_expanded_proof ⇐ show subprob_h1_expanded by



    rw [← subprob_LHS_expanded_proof]

    rw [← subprob_RHS_term_expanded_proof]

    exact subprob_h1_transformed_2_proof -- from subprob_h1_transformed_2, subprob_LHS_expanded, subprob_RHS_term_expanded.

  subprob_log2_of_1_div_4 :≡ Real.logb 2 (1/4 : ℝ) = -2
  subprob_log2_of_1_div_4_proof ⇐ show subprob_log2_of_1_div_4 by







    have h_base_pos : (2 : ℝ) > 0 := by norm_num
    have h_base_ne_one : (2 : ℝ) ≠ 1 := by norm_num

    have h_num_pos : (1 : ℝ) > 0 := by norm_num
    have h_den_pos : (4 : ℝ) > 0 := by norm_num

    have h_num_ne_zero : (1 : ℝ) ≠ 0 := by
      apply _root_.ne_of_gt h_num_pos
    have h_den_ne_zero : (4 : ℝ) ≠ 0 := by
      apply _root_.ne_of_gt h_den_pos

    have h_log_div : Real.logb (2 : ℝ) ((1 : ℝ) / (4 : ℝ)) = Real.logb (2 : ℝ) (1 : ℝ) - Real.logb (2 : ℝ) (4 : ℝ) := by
      apply Real.logb_div h_num_ne_zero h_den_ne_zero
    rw [h_log_div]

    have h_log_one : Real.logb (2 : ℝ) (1 : ℝ) = 0 := by
      apply Real.logb_one
    rw [h_log_one]

    have h_four_eq_two_sq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h_four_eq_two_sq]

    have h_log_self_pow : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 : ℕ)) = ↑(2 : ℕ) := by
      rw [Real.logb_pow h_base_pos]
      rw [Real.logb_self_eq_one subprob_base_2_gt_1_proof]
      simp
    rw [h_log_self_pow]

    norm_num


  subprob_log2_of_1_div_2 :≡ Real.logb 2 (1/2 : ℝ) = -1
  subprob_log2_of_1_div_2_proof ⇐ show subprob_log2_of_1_div_2 by














    have h_logb_div_applied : Real.logb 2 (1 / 2 : ℝ) = Real.logb 2 1 - Real.logb 2 2 := by
      apply Real.logb_div
      · norm_num
      · norm_num

    rw [h_logb_div_applied]


    have h_logb_one_applied : Real.logb 2 1 = 0 := by
      apply Real.logb_one

    rw [h_logb_one_applied]


    have h_logb_self_applied : Real.logb 2 2 = 1 := by
      apply Real.logb_self_eq_one
      · exact subprob_base_2_gt_1_proof

    rw [h_logb_self_applied]


    simp

  L2X_n := Real.logb 2 X_n
  subprob_L2Xn_def :≡ L2X_n = Real.logb 2 X_n -- Definition
  subprob_L2Xn_def_proof ⇐ show subprob_L2Xn_def by


    rw [L2X_n_def]


  subprob_h1_subs_log_vals :≡ -2 + L2X_n = (-1 + L2X_n) / 2
  subprob_h1_subs_log_vals_proof ⇐ show subprob_h1_subs_log_vals by


    rw [← subprob_log2_of_1_div_4_proof]

    rw [← subprob_log2_of_1_div_2_proof]

    rw [L2X_n_def]

    exact subprob_h1_expanded_proof -- from subprob_h1_expanded, subprob_log2_of_1_div_4, subprob_log2_of_1_div_2, subprob_L2Xn_def.

  subprob_h1_subs_log_vals_distrib_RHS :≡ -2 + L2X_n = -1/2 + L2X_n / 2
  subprob_h1_subs_log_vals_distrib_RHS_proof ⇐ show subprob_h1_subs_log_vals_distrib_RHS by



    rw [subprob_h1_subs_log_vals_proof]

    rw [add_div (-(1 : ℝ)) L2X_n (2 : ℝ)]

 -- from subprob_h1_subs_log_vals by algebra (distributing /2)
  subprob_L2Xn_intermediate_solve :≡ (1/2 : ℝ) * L2X_n = (3/2 : ℝ)
  subprob_L2Xn_intermediate_solve_proof ⇐ show subprob_L2Xn_intermediate_solve by

    let h_eq := subprob_h1_subs_log_vals_distrib_RHS_proof

    have h_rearranged : L2X_n - L2X_n / (2 : ℝ) = (2 : ℝ) - (1 : ℝ) / (2 : ℝ) := by
      linarith [h_eq]

    have h_lhs_simplified : L2X_n - L2X_n / (2 : ℝ) = (1 / 2 : ℝ) * L2X_n := by
      ring

    have h_rhs_simplified : (2 : ℝ) - (1 : ℝ) / (2 : ℝ) = (3 / 2 : ℝ) := by
      norm_num

    rw [h_lhs_simplified, h_rhs_simplified] at h_rearranged

    exact h_rearranged -- from subprob_h1_subs_log_vals_distrib_RHS by algebraic rearrangement
  subprob_L2Xn_eq_3 :≡ L2X_n = 3
  subprob_L2Xn_eq_3_proof ⇐ show subprob_L2Xn_eq_3 by


    have h_eq : (1 : ℝ) / (2 : ℝ) * L2X_n = (3 : ℝ) / (2 : ℝ) := subprob_L2Xn_intermediate_solve_proof

    have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num

    rw [one_div_mul_eq_div (2 : ℝ) L2X_n] at h_eq

    exact (div_left_inj' h_two_ne_zero).mp h_eq -- from subprob_L2Xn_intermediate_solve by multiplying by 2

  subprob_Xn_eq_2_pow_3 :≡ X_n = (2 : ℝ) ^ 3
  subprob_Xn_eq_2_pow_3_proof ⇐ show subprob_Xn_eq_2_pow_3 by


    have h_log_Xn_eq_3 : logb (2 : ℝ) X_n = (3 : ℝ) := by
      rw [← L2X_n_def]
      exact subprob_L2Xn_eq_3_proof

    have h_Xn_eq_rpow_real_exp : X_n = (2 : ℝ) ^ (3 : ℝ) := by
      apply Eq.symm
      apply (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) subprob_Xn_gt_0_proof).mp
      exact h_log_Xn_eq_3

    rw [h_Xn_eq_rpow_real_exp]

    exact Real.rpow_nat_cast (2 : ℝ) 3
 -- From subprob_L2Xn_eq_3, subprob_L2Xn_def, Real.logb_eq_iff_eq_rpow, subprob_Xn_gt_0.
  subprob_2_pow_3_is_8 :≡ (2 : ℝ) ^ 3 = 8
  subprob_2_pow_3_is_8_proof ⇐ show subprob_2_pow_3_is_8 by
    norm_num
  subprob_Xn_eq_8 :≡ X_n = 8
  subprob_Xn_eq_8_proof ⇐ show subprob_Xn_eq_8 by


    rw [subprob_Xn_eq_2_pow_3_proof]
    exact subprob_2_pow_3_is_8_proof -- from subprob_Xn_eq_2_pow_3 and subprob_2_pow_3_is_8

  subprob_n_cast_real_eq_2_pow_8 :≡ n_cast_real = (2 : ℝ) ^ 8
  subprob_n_cast_real_eq_2_pow_8_proof ⇐ show subprob_n_cast_real_eq_2_pow_8 by


    have h_log_eq : logb (2 : ℝ) n_cast_real = (8 : ℝ) := by
      rw [← X_n_def]
      exact subprob_Xn_eq_8_proof


    have h_base_pos : (0 : ℝ) < (2 : ℝ) := by
      norm_num

    have h_base_ne_one : (2 : ℝ) ≠ 1 := by
      norm_num

    have h_n_cast_real_eq_rpow : n_cast_real = Real.rpow (2 : ℝ) (8 : ℝ) := by
      rw [eq_comm]
      apply (Real.logb_eq_iff_rpow_eq h_base_pos h_base_ne_one subprob_n_cast_real_gt_0_proof).mp
      exact h_log_eq


    rw [h_n_cast_real_eq_rpow]

    rw [← Real.rpow_nat_cast (2 : ℝ) 8]
    rfl
 -- From subprob_Xn_eq_8, subprob_Xn_def, Real.logb_eq_iff_eq_rpow, subprob_n_cast_real_gt_0.
  subprob_2_pow_8_is_256 :≡ (2 : ℝ) ^ 8 = 256
  subprob_2_pow_8_is_256_proof ⇐ show subprob_2_pow_8_is_256 by
    norm_num
  subprob_n_cast_real_eq_256 :≡ n_cast_real = 256
  subprob_n_cast_real_eq_256_proof ⇐ show subprob_n_cast_real_eq_256 by


    rw [subprob_n_cast_real_eq_2_pow_8_proof]

    exact subprob_2_pow_8_is_256_proof

  subprob_n_eq_256 :≡ n = 256
  subprob_n_eq_256_proof ⇐ show subprob_n_eq_256 by



    have h_final_eq_real : (↑n : ℝ) = (256 : ℝ) := by
      rw [Eq.symm n_cast_real_def]
      exact subprob_n_cast_real_eq_256_proof

    apply (Nat.cast_inj (R := ℝ)).mp
    exact h_final_eq_real

 -- from subprob_n_cast_real_eq_256, subprob_n_cast_real_def, and Nat.cast_inj.

  subprob_digits_n_is_digits_256 :≡ Nat.digits 10 n = Nat.digits 10 256
  subprob_digits_n_is_digits_256_proof ⇐ show subprob_digits_n_is_digits_256 by


    rw [subprob_n_eq_256_proof]
 -- from subprob_n_eq_256
  subprob_digits_256_list :≡ Nat.digits 10 256 = [6, 5, 2]
  subprob_digits_256_list_proof ⇐ show subprob_digits_256_list by






    rfl
  subprob_sum_list_652 :≡ ([6, 5, 2] : List ℕ).sum = 13
  subprob_sum_list_652_proof ⇐ show subprob_sum_list_652 by
    rfl

  subprob_final_goal :≡ (Nat.digits 10 n).sum = 13
  subprob_final_goal_proof ⇐ show subprob_final_goal by

    rw [subprob_n_eq_256_proof]

    rw [subprob_digits_256_list_proof]

    exact subprob_sum_list_652_proof
-/
