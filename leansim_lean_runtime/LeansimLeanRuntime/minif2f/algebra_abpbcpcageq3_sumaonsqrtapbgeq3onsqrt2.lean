import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 3 ≤ a * b + b * c + c * a) : (3 : ℝ) / √(2 : ℝ) ≤ a / √(a + b) + b / √(b + c) + c / √(c + a) := by
  letI ha_pos := h₀.1
  letI hb_pos := h₀.2.1
  letI hc_pos := h₀.2.2
  letI S1 := a / Real.sqrt (a + b) + b / Real.sqrt (b + c) + c / Real.sqrt (c + a)
  retro' S1_def : S1 = a / √(a + b) + b / √(b + c) + c / √(c + a) := by funext; rfl
  letI Sa := a + b + c
  retro' Sa_def : Sa = a + b + c := by funext; rfl
  letI S_sum_a_ab := a * (a + b) + b * (b + c) + c * (c + a)
  retro' S_sum_a_ab_def : S_sum_a_ab = a * (a + b) + b * (b + c) + c * (c + a) := by funext; rfl
  have subprob_S1_pos_proof : S1 > 0 := by
    mkOpaque
    rw [S1_def]
    have h_term1_pos : a / √(a + b) > 0 := by
      have h_apb_pos : a + b > 0 := by apply add_pos ha_pos hb_pos
      have h_sqrt_apb_pos : √(a + b) > 0 := by
        apply Real.sqrt_pos.mpr
        exact h_apb_pos
      apply div_pos ha_pos h_sqrt_apb_pos
    have h_term2_pos : b / √(b + c) > 0 := by
      have h_bpc_pos : b + c > 0 := by apply add_pos hb_pos hc_pos
      have h_sqrt_bpc_pos : √(b + c) > 0 := by
        apply Real.sqrt_pos.mpr
        exact h_bpc_pos
      apply div_pos hb_pos h_sqrt_bpc_pos
    have h_term3_pos : c / √(c + a) > 0 := by
      have h_cpa_pos : c + a > 0 := by apply add_pos hc_pos ha_pos
      have h_sqrt_cpa_pos : √(c + a) > 0 := by
        apply Real.sqrt_pos.mpr
        exact h_cpa_pos
      apply div_pos hc_pos h_sqrt_cpa_pos
    apply add_pos
    apply add_pos
    exact h_term1_pos
    exact h_term2_pos
    exact h_term3_pos
  have subprob_Sa_pos_proof : Sa > 0 := by
    mkOpaque
    rw [Sa_def]
    apply add_pos
    . apply add_pos
      . exact ha_pos
      . exact hb_pos
    . exact hc_pos
  have subprob_S_sum_a_ab_pos_proof : S_sum_a_ab > 0 := by
    mkOpaque
    rw [S_sum_a_ab_def]
    have h_a_plus_b_pos : a + b > 0 := by
      apply add_pos
      exact ha_pos
      exact hb_pos
    have h_b_plus_c_pos : b + c > 0 := by
      apply add_pos
      exact hb_pos
      exact hc_pos
    have h_c_plus_a_pos : c + a > 0 := by
      apply add_pos
      exact hc_pos
      exact ha_pos
    have h_term1_pos : a * (a + b) > 0 := by
      apply mul_pos
      exact ha_pos
      exact h_a_plus_b_pos
    have h_term2_pos : b * (b + c) > 0 := by
      apply mul_pos
      exact hb_pos
      exact h_b_plus_c_pos
    have h_term3_pos : c * (c + a) > 0 := by
      apply mul_pos
      exact hc_pos
      exact h_c_plus_a_pos
    have h_sum_term1_term2_pos : a * (a + b) + b * (b + c) > 0 := by
      apply add_pos
      exact h_term1_pos
      exact h_term2_pos
    have h_final_sum_pos : (a * (a + b) + b * (b + c)) + c * (c + a) > 0 := by
      apply add_pos
      exact h_sum_term1_term2_pos
      exact h_term3_pos
    exact h_final_sum_pos
  have subprob_holder_proof : Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3) ≥ Sa := by
    mkOpaque
    let u_fn : Fin 3 → ℝ := fun i => (![a, b, c]) i
    let p₀ : ℝ := 3 / 2
    let q₀ : ℝ := 3
    have hp₀_gt_1 : 1 < p₀ := by norm_num
    have hq₀_gt_1 : 1 < q₀ := by norm_num
    have hp₀_inv_add_hq₀_inv_eq_1 : p₀⁻¹ + q₀⁻¹ = 1 := by
      field_simp
      norm_num
    have my_eq_of_log_eq_log_of_pos_for_apply {A B : ℝ} (hA_pos : 0 < A) (hB_pos : 0 < B) (h_log_eq : Real.log A = Real.log B) : A = B := by
      have h_log_A_le_log_B : Real.log A ≤ Real.log B := Eq.le h_log_eq
      have h_log_B_le_log_A : Real.log B ≤ Real.log A := Eq.le h_log_eq.symm
      have hA_le_B : A ≤ B := (Real.log_le_log_iff hA_pos hB_pos).mp h_log_A_le_log_B
      have hB_le_A : B ≤ A := (Real.log_le_log_iff hB_pos hA_pos).mp h_log_B_le_log_A
      exact le_antisymm hA_le_B hB_le_A
    have my_rpow_rpow {x : ℝ} (hx_pos : 0 < x) (y z : ℝ) : Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
      apply my_eq_of_log_eq_log_of_pos_for_apply
      · exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx_pos y) z
      · exact Real.rpow_pos_of_pos hx_pos (y * z)
      erw [Real.log_rpow (Real.rpow_pos_of_pos hx_pos y) z]
      rw [Real.log_rpow hx_pos y]
      erw [Real.log_rpow hx_pos (y * z)]
      ring
    have hu_fn_pos : ∀ (i : Fin 3), 0 < u_fn i := by
      intro i
      fin_cases i
      . exact h₀.1
      . exact h₀.2.1
      . exact h₀.2.2
    have hu_fn_sum_pos : ∀ (i : Fin 3), 0 < u_fn i + u_fn (i + 1) := by
      intro i
      fin_cases i
      . simp [u_fn]; linarith [h₀.1, h₀.2.1]
      . simp [u_fn]; linarith [h₀.2.1, h₀.2.2]
      . simp [u_fn]; linarith [h₀.2.2, h₀.1]
    let base_U_fn : Fin 3 → ℝ := fun i => u_fn i / Real.sqrt (u_fn i + u_fn (i + 1))
    let base_V_fn : Fin 3 → ℝ := fun i => u_fn i * (u_fn i + u_fn (i + 1))
    have hbase_U_fn_pos : ∀ (i : Fin 3), 0 < base_U_fn i := by
      intro i
      simp [base_U_fn]
      apply div_pos (hu_fn_pos i) (Real.sqrt_pos.mpr (hu_fn_sum_pos i))
    have hbase_V_fn_pos : ∀ (i : Fin 3), 0 < base_V_fn i := by
      intro i
      simp [base_V_fn]
      apply mul_pos (hu_fn_pos i) (hu_fn_sum_pos i)
    let U_holder : Fin 3 → ℝ := fun i => Real.rpow (base_U_fn i) (2 / 3)
    let V_holder : Fin 3 → ℝ := fun i => Real.rpow (base_V_fn i) ((1 : ℝ) / (3 : ℝ))
    have hU_holder_pos : ∀ (i : Fin 3), 0 < U_holder i := by intro i; simp [U_holder]; apply Real.rpow_pos_of_pos (hbase_U_fn_pos i)
    have hV_holder_pos : ∀ (i : Fin 3), 0 < V_holder i := by intro i; simp [V_holder]; apply Real.rpow_pos_of_pos (hbase_V_fn_pos i)
    have h_conj_exp : Real.IsConjExponent p₀ q₀ := Real.IsConjExponent.mk hp₀_gt_1 hp₀_inv_add_hq₀_inv_eq_1
    have holder_ineq : _ := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin 3)) h_conj_exp (fun i _ => (hU_holder_pos i).le) (fun i _ => (hV_holder_pos i).le)
    have sum_UV_term : ∀ i, U_holder i * V_holder i = u_fn i := by
      intro i
      simp only [U_holder, V_holder, base_U_fn, base_V_fn, Real.sqrt_eq_rpow]
      have h_sum_pos := hu_fn_sum_pos i
      have h_fn_pos := hu_fn_pos i
      have h_u_fn_ge_0 : 0 ≤ u_fn i := (hu_fn_pos i).le
      have h_u_fn_sum_ge_0 : 0 ≤ u_fn i + u_fn (i + (1 : Fin (3 : ℕ))) := (hu_fn_sum_pos i).le
      have h_term_U_transformed : rpow (u_fn i / ((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ) / (2 : ℝ)))) ((2 : ℝ) / (3 : ℝ)) = rpow (u_fn i) ((2 : ℝ) / (3 : ℝ)) / rpow (((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ) / (2 : ℝ)))) ((2 : ℝ) / (3 : ℝ)) := by apply Real.div_rpow h_u_fn_ge_0 (Real.rpow_nonneg (h_u_fn_sum_ge_0) _)
      rw [h_term_U_transformed]
      have h_V_factor_expanded : rpow (u_fn i * (u_fn i + u_fn (i + (1 : Fin (3 : ℕ))))) ((1 : ℝ) / (3 : ℝ)) = rpow (u_fn i) ((1 : ℝ) / (3 : ℝ)) * rpow (u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ((1 : ℝ) / (3 : ℝ)) := by exact Real.mul_rpow h_u_fn_ge_0 h_u_fn_sum_ge_0
      rw [h_V_factor_expanded]
      have h_inner_rpow_nonneg : 0 ≤ (u_fn i + u_fn (i + 1)) ^ ((1 : ℝ) / (2 : ℝ)) := Real.rpow_nonneg h_u_fn_sum_ge_0 ((1 : ℝ) / (2 : ℝ))
      have h_rpow_chain_rule_application : rpow ((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ) / (2 : ℝ))) ((2 : ℝ) / (3 : ℝ)) = rpow (u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) (((1 : ℝ) / (2 : ℝ)) * ((2 : ℝ) / (3 : ℝ))) := by exact my_rpow_rpow (hu_fn_sum_pos i) ((1 : ℝ) / (2 : ℝ)) ((2 : ℝ) / (3 : ℝ))
      rw [h_rpow_chain_rule_application]
      have h_exponent_mult : ((1 : ℝ) / (2 : ℝ)) * ((2 : ℝ) / (3 : ℝ)) = (1 : ℝ) / (3 : ℝ) := by norm_num
      rw [h_exponent_mult]
      rw [mul_comm (rpow (u_fn i) (1 / 3)) (rpow (u_fn i + u_fn (i + 1)) (1 / 3))]
      rw [← mul_assoc]
      have h_denom_term_ne_zero : rpow (u_fn i + u_fn (i + 1)) (1 / 3) ≠ 0 := (Real.rpow_pos_of_pos (hu_fn_sum_pos i) _).ne'
      rw [div_mul_cancel₀ _ h_denom_term_ne_zero]
      have h_lhs_step1 : rpow (u_fn i) ((2 : ℝ) / (3 : ℝ)) * rpow (u_fn i) ((1 : ℝ) / (3 : ℝ)) = rpow (u_fn i) (((2 : ℝ) / (3 : ℝ)) + ((1 : ℝ) / (3 : ℝ))) := by exact (Real.rpow_add (hu_fn_pos i) _ _).symm
      rw [h_lhs_step1]
      have h_exp_simplified : ((2 : ℝ) / (3 : ℝ)) + ((1 : ℝ) / (3 : ℝ)) = 1 := by norm_num
      rw [h_exp_simplified]
      apply Real.rpow_one
    have sum_UV_eq_Sa : Finset.sum Finset.univ (fun i => U_holder i * V_holder i) = Sa := by
      simp_rw [sum_UV_term]
      rw [Sa_def]
      rw [Fin.sum_univ_three u_fn]
      simp [u_fn]
    have sum_U_pow_p0_term : ∀ i, U_holder i ^ p₀ = base_U_fn i := by
      intro i
      simp only [U_holder, p₀]
      change Real.rpow (Real.rpow (base_U_fn i) (2 / 3)) (3 / 2) = base_U_fn i
      rw [my_rpow_rpow (hbase_U_fn_pos i) (2 / 3) (3 / 2)]
      have h_exponent_is_one : (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 := by norm_num
      rw [h_exponent_is_one]
      apply Real.rpow_one
    have sum_U_pow_p0_eq_S1 : Finset.sum Finset.univ (fun i => U_holder i ^ p₀) = S1 := by
      simp_rw [sum_U_pow_p0_term]
      rw [S1_def]
      rw [Fin.sum_univ_three base_U_fn]
      simp [base_U_fn, u_fn, Real.sqrt_eq_rpow]
    have sum_V_pow_q0_term : ∀ i, V_holder i ^ q₀ = base_V_fn i := by
      intro i
      simp only [V_holder, q₀]
      change Real.rpow (Real.rpow (base_V_fn i) (1 / 3)) 3 = base_V_fn i
      rw [my_rpow_rpow (hbase_V_fn_pos i) (1 / 3) 3]
      have h_exponent_is_one : (1 / 3 : ℝ) * (3 : ℝ) = 1 := by norm_num
      rw [h_exponent_is_one]
      apply Real.rpow_one
    have sum_V_pow_q0_eq_S_sum_a_ab : Finset.sum Finset.univ (fun i => V_holder i ^ q₀) = S_sum_a_ab := by
      simp_rw [sum_V_pow_q0_term]
      rw [S_sum_a_ab_def]
      rw [Fin.sum_univ_three base_V_fn]
      simp [base_V_fn, u_fn]
    have h_one_div_p₀ : 1 / p₀ = 2 / 3 := by simp only [p₀, one_div_div]
    have h_one_div_q₀ : 1 / q₀ = 1 / 3 := by simp only [q₀]
    rw [sum_UV_eq_Sa] at holder_ineq
    rw [sum_U_pow_p0_eq_S1] at holder_ineq
    rw [sum_V_pow_q0_eq_S_sum_a_ab] at holder_ineq
    rw [h_one_div_p₀] at holder_ineq
    rw [h_one_div_q₀] at holder_ineq
    apply ge_iff_le.mpr
    exact holder_ineq
  have subprob_isolate_S1_proof : S1 ≥ Real.rpow Sa (3 / 2) / Real.rpow S_sum_a_ab (1 / 2) := by
    mkOpaque
    have h_denom_pos : 0 < Real.rpow S_sum_a_ab (1 / 2) := by apply Real.rpow_pos_of_pos subprob_S_sum_a_ab_pos_proof
    rw [ge_iff_le, div_le_iff h_denom_pos]
    let LHS_holder := Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3)
    have h_holder_ineq : LHS_holder ≥ Sa := subprob_holder_proof
    have h_Sa_nn : 0 ≤ Sa := by exact le_of_lt subprob_Sa_pos_proof
    have h_S1_nn : 0 ≤ S1 := by exact le_of_lt subprob_S1_pos_proof
    have h_S_sum_a_ab_nn : 0 ≤ S_sum_a_ab := by exact le_of_lt subprob_S_sum_a_ab_pos_proof
    have h_rpow_S1_nn : 0 ≤ Real.rpow S1 (2 / 3) := by apply Real.rpow_nonneg h_S1_nn
    have h_rpow_S_sum_a_ab_nn : 0 ≤ Real.rpow S_sum_a_ab (1 / 3) := by apply Real.rpow_nonneg h_S_sum_a_ab_nn
    have h_LHS_holder_nn : 0 ≤ LHS_holder := by exact mul_nonneg h_rpow_S1_nn h_rpow_S_sum_a_ab_nn
    have h_exp_nn : 0 ≤ (3 / 2 : ℝ) := by norm_num
    have h_raised_ineq : Real.rpow Sa (3 / 2) ≤ Real.rpow LHS_holder (3 / 2) := by apply Real.rpow_le_rpow h_Sa_nn h_holder_ineq h_exp_nn
    have h_simplify_rhs : Real.rpow LHS_holder (3 / 2) = S1 * Real.rpow S_sum_a_ab (1 / 2) := by
      dsimp only [LHS_holder]
      have h_mul_rpow_step : Real.rpow (Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) = Real.rpow (Real.rpow S1 (2 / 3)) (3 / 2) * Real.rpow (Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) := by exact Real.mul_rpow h_rpow_S1_nn h_rpow_S_sum_a_ab_nn
      rw [h_mul_rpow_step]
      have h_S1_rpow_rpow : Real.rpow (Real.rpow S1 (2 / 3)) (3 / 2) = Real.rpow S1 ((2 / 3 : ℝ) * (3 / 2 : ℝ)) := by
        let x := S1
        let y_exp := (2 / 3 : ℝ)
        let z_exp := (3 / 2 : ℝ)
        have hx_pos : 0 < x := subprob_S1_pos_proof
        have h_xy_pos : 0 < Real.rpow x y_exp := Real.rpow_pos_of_pos hx_pos y_exp
        have h_lhs_pos : 0 < Real.rpow (Real.rpow x y_exp) z_exp := Real.rpow_pos_of_pos h_xy_pos z_exp
        have h_rhs_pos : 0 < Real.rpow x (y_exp * z_exp) := Real.rpow_pos_of_pos hx_pos (y_exp * z_exp)
        suffices h_log_eq : Real.log (Real.rpow (Real.rpow x y_exp) z_exp) = Real.log (Real.rpow x (y_exp * z_exp)) by
          rw [(Real.exp_log h_lhs_pos).symm]
          rw [h_log_eq]
          rw [Real.exp_log h_rhs_pos]
        erw [@Real.log_rpow (Real.rpow x y_exp) h_xy_pos z_exp]
        erw [@Real.log_rpow x hx_pos y_exp]
        erw [@Real.log_rpow x hx_pos (y_exp * z_exp)]
        rw [← mul_assoc z_exp y_exp (Real.log x)]
        rw [mul_comm z_exp y_exp]
      have h_S_sum_a_ab_rpow_rpow : Real.rpow (Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) = Real.rpow S_sum_a_ab ((1 / 3 : ℝ) * (3 / 2 : ℝ)) := by
        let x := S_sum_a_ab
        let y_exp := (1 / 3 : ℝ)
        let z_exp := (3 / 2 : ℝ)
        have hx_pos : 0 < x := subprob_S_sum_a_ab_pos_proof
        have h_xy_pos : 0 < Real.rpow x y_exp := Real.rpow_pos_of_pos hx_pos y_exp
        have h_lhs_pos : 0 < Real.rpow (Real.rpow x y_exp) z_exp := Real.rpow_pos_of_pos h_xy_pos z_exp
        have h_rhs_pos : 0 < Real.rpow x (y_exp * z_exp) := Real.rpow_pos_of_pos hx_pos (y_exp * z_exp)
        suffices h_log_eq : Real.log (Real.rpow (Real.rpow x y_exp) z_exp) = Real.log (Real.rpow x (y_exp * z_exp)) by
          rw [(Real.exp_log h_lhs_pos).symm]
          rw [h_log_eq]
          rw [Real.exp_log h_rhs_pos]
        erw [@Real.log_rpow (Real.rpow x y_exp) h_xy_pos z_exp]
        erw [@Real.log_rpow x hx_pos y_exp]
        erw [@Real.log_rpow x hx_pos (y_exp * z_exp)]
        rw [← mul_assoc z_exp y_exp (Real.log x)]
        rw [mul_comm z_exp y_exp]
      rw [h_S1_rpow_rpow, h_S_sum_a_ab_rpow_rpow]
      have exp1_val : (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 := by norm_num
      have exp2_val : (1 / 3 : ℝ) * (3 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [exp1_val, exp2_val]
      rw [show Real.rpow S1 (1 : ℝ) = S1 from Real.rpow_one S1]
    rw [h_simplify_rhs] at h_raised_ineq
    exact h_raised_ineq
  letI target_ineq_rhs := Real.rpow Sa (3 / 2) / Real.rpow S_sum_a_ab (1 / 2)
  retro' target_ineq_rhs_def : target_ineq_rhs = rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) := by funext; rfl
  letI target_ineq := target_ineq_rhs ≥ 3 / Real.sqrt 2
  retro' target_ineq_def : target_ineq = (target_ineq_rhs ≥ (3 : ℝ) / √(2 : ℝ)) := by funext; rfl
  have subprob_suffices_step_proof : target_ineq → S1 ≥ 3 / Real.sqrt 2 := by
    mkOpaque
    intro htiq
    have ineq_rhs_ge_const : target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2 := by
      rw [target_ineq_def] at htiq
      exact htiq
    have S1_ge_ineq_rhs : S1 ≥ target_ineq_rhs := by
      rw [target_ineq_rhs_def]
      exact subprob_isolate_S1_proof
    exact ge_trans S1_ge_ineq_rhs ineq_rhs_ge_const
  have subprob_sqrt2_pos_proof : Real.sqrt 2 > 0 := by
    mkOpaque
    rw [gt_iff_lt, Real.sqrt_pos]
    exact zero_lt_two
  have subprob_target_rhs_pos_proof : 3 / Real.sqrt 2 ≥ 0 := by
    mkOpaque
    apply div_nonneg
    · norm_num
    · exact le_of_lt subprob_sqrt2_pos_proof
  have subprob_target_lhs_pos_proof : target_ineq_rhs ≥ 0 := by
    mkOpaque
    rw [target_ineq_rhs_def]
    have h_numerator_pos : rpow Sa ((3 : ℝ) / (2 : ℝ)) > 0 := by
      apply Real.rpow_pos_of_pos
      exact subprob_Sa_pos_proof
    have h_denominator_pos : rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) > 0 := by
      apply Real.rpow_pos_of_pos
      exact subprob_S_sum_a_ab_pos_proof
    have h_fraction_pos : rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) > 0 := by
      apply div_pos
      exact h_numerator_pos
      exact h_denominator_pos
    apply le_of_lt
    exact h_fraction_pos
  have subprob_target_equiv_sq_proof : target_ineq ↔ (Sa ^ 3 / S_sum_a_ab ≥ (3 / Real.sqrt 2) ^ 2) := by
    mkOpaque
    rw [target_ineq_def, target_ineq_rhs_def]
    conv =>
      lhs
      rw [ge_iff_le]
    have hX_nonneg : 0 ≤ rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2) := by {
      rw [← target_ineq_rhs_def]
      exact subprob_target_lhs_pos_proof
    }
    have h_sq_le_sq_symm : ((3 : ℝ) / √(2 : ℝ)) ≤ (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ↔ ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ) ≤ (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ^ (2 : ℕ) :=
      (pow_le_pow_iff_left subprob_target_rhs_pos_proof hX_nonneg
          (by {norm_num
          } : (2 : ℕ) ≠ (0 : ℕ))).symm
    rw [h_sq_le_sq_symm]
    rw [div_pow (rpow Sa (3 / 2)) (rpow S_sum_a_ab (1 / 2)) 2]
    have hSa_nonneg : 0 ≤ Sa := le_of_lt subprob_Sa_pos_proof
    have h_num_simpl : (rpow Sa ((3 : ℝ) / (2 : ℝ))) ^ (2 : ℕ) = rpow Sa (((3 : ℝ) / (2 : ℝ)) * (2 : ℝ)) := by
      have hSa_pos : Sa > 0 := subprob_Sa_pos_proof
      let p_exp := (3 : ℝ) / (2 : ℝ)
      let n_exp := (2 : ℕ)
      have h_Sap_pos : Sa ^ p_exp > 0 := Real.rpow_pos_of_pos hSa_pos p_exp
      have h_LHS_val_pos : (Sa ^ p_exp) ^ n_exp > 0 := pow_pos h_Sap_pos n_exp
      have h_RHS_val_pos : Sa ^ (p_exp * (2 : ℝ)) > 0 := Real.rpow_pos_of_pos hSa_pos (p_exp * (2 : ℝ))
      have h_log_eq : Real.log ((Sa ^ p_exp) ^ n_exp) = Real.log (Sa ^ (p_exp * (2 : ℝ))) := by
        rw [Real.log_pow (Sa ^ p_exp) n_exp]
        rw [Real.log_rpow hSa_pos p_exp]
        rw [Real.log_rpow hSa_pos (p_exp * (2 : ℝ))]
        simp
        ring
      apply le_antisymm
      · apply (Real.log_le_log_iff h_LHS_val_pos h_RHS_val_pos).mp
        exact h_log_eq.le
      · apply (Real.log_le_log_iff h_RHS_val_pos h_LHS_val_pos).mp
        exact h_log_eq.symm.le
    rw [h_num_simpl]
    have hS_sum_a_ab_nonneg : 0 ≤ S_sum_a_ab := le_of_lt subprob_S_sum_a_ab_pos_proof
    have h_den_simpl : (rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))) ^ (2 : ℕ) = rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) := by
      have h_sqrt_id_local : Real.rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) = Real.sqrt S_sum_a_ab := (Real.sqrt_eq_rpow S_sum_a_ab).symm
      rw [h_sqrt_id_local]
      rw [Real.sq_sqrt hS_sum_a_ab_nonneg]
      have h_exp_eq_one : ((1 : ℝ) / (2 : ℝ)) * (2 : ℝ) = 1 := by norm_num
      rw [h_exp_eq_one]
      exact (Real.rpow_one S_sum_a_ab).symm
    rw [h_den_simpl]
    have h_exp_numer : (3 / 2 : ℝ) * (2 : ℝ) = 3 := by norm_num
    rw [h_exp_numer]
    have h_exp_denom : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
    have h_simplify_denom_rpow : rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) = S_sum_a_ab := by
      rw [h_exp_denom]
      exact Real.rpow_one S_sum_a_ab
    rw [h_simplify_denom_rpow]
    have h_three_is_cast : (3 : ℝ) = (↑(3 : ℕ) : ℝ) := by simp
    rw [h_three_is_cast]
    have h_sa_rpow_eq_pow : rpow Sa (↑(3 : ℕ) : ℝ) = Sa ^ (3 : ℕ) := by exact Real.rpow_nat_cast Sa (3 : ℕ)
    rw [h_sa_rpow_eq_pow]
  have subprob_rhs_sq_eval_proof : (3 / Real.sqrt 2) ^ 2 = 9 / 2 := by
    mkOpaque
    rw [div_pow]
    have h_two_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    rw [Real.sq_sqrt h_two_nonneg]
    norm_num
  letI reduced_target_ineq := Sa ^ 3 / S_sum_a_ab ≥ 9 / 2
  retro' reduced_target_ineq_def : reduced_target_ineq = (Sa ^ (3 : ℕ) / S_sum_a_ab ≥ (9 : ℝ) / (2 : ℝ)) := by funext; rfl
  letI p_val := Sa
  retro' p_val_def : p_val = Sa := by funext; rfl
  letI q_val := a * b + b * c + c * a
  retro' q_val_def : q_val = a * b + b * c + c * a := by funext; rfl
  have subprob_S_sum_a_ab_rewrite_pq_proof : S_sum_a_ab = p_val ^ 2 - q_val := by
    mkOpaque
    rw [S_sum_a_ab_def]
    rw [p_val_def]
    rw [q_val_def]
    rw [Sa_def]
    ring
  letI ineq_pq_form := p_val ^ 3 / (p_val ^ 2 - q_val) ≥ 9 / 2
  retro' ineq_pq_form_def : ineq_pq_form = (p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)) := by funext; rfl
  have subprob_reduced_target_equiv_pq_form_proof : reduced_target_ineq ↔ ineq_pq_form := by
    mkOpaque
    rw [reduced_target_ineq_def]
    rw [ineq_pq_form_def]
    rw [p_val_def]
    have h_S_sum_a_ab_eq_Sa_q_val : S_sum_a_ab = Sa ^ (2 : ℕ) - q_val := by
      rw [subprob_S_sum_a_ab_rewrite_pq_proof]
      rw [p_val_def]
    rw [h_S_sum_a_ab_eq_Sa_q_val]
  have subprob_ineq_pq_clear_den_proof : ineq_pq_form ↔ 2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val) := by
    mkOpaque
    rw [ineq_pq_form_def]
    have h_denom_pos : p_val ^ (2 : ℕ) - q_val > 0 := by
      rw [← subprob_S_sum_a_ab_rewrite_pq_proof]
      exact subprob_S_sum_a_ab_pos_proof
    have h_two_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_div_iff : (p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)) ↔ (p_val ^ (3 : ℕ) * (2 : ℝ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)) := by
      apply div_le_div_iff
      . exact h_two_pos
      . exact h_denom_pos
    rw [h_div_iff]
    rw [mul_comm (p_val ^ (3 : ℕ)) (2 : ℝ)]
  letI ineq_rearranged := 2 * p_val ^ 3 + 9 * q_val ≥ 9 * p_val ^ 2
  retro' ineq_rearranged_def : ineq_rearranged = ((2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (9 : ℝ) * p_val ^ (2 : ℕ)) := by funext; rfl
  have subprob_ineq_rearranged_equiv_proof : (2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val)) ↔ ineq_rearranged := by
    mkOpaque
    rw [ineq_rearranged_def]
    have h_distrib : 9 * (p_val ^ 2 - q_val) = 9 * p_val ^ 2 - 9 * q_val := by ring
    rw [h_distrib]
    apply sub_le_iff_le_add
  have subprob_9q_ge_27_proof : 9 * q_val ≥ 27 := by
    mkOpaque
    rw [q_val_def]
    have h_27_eq_9_times_3 : (27 : ℝ) = 9 * 3 := by norm_num
    rw [h_27_eq_9_times_3]
    have nine_pos : (0 : ℝ) < 9 := by norm_num
    apply (mul_le_mul_left nine_pos).mpr
    exact h₁
  have subprob_use_hypothesis_h1_proof : 2 * p_val ^ 3 + 9 * q_val ≥ 2 * p_val ^ 3 + 27 := by
    mkOpaque
    linarith [subprob_9q_ge_27_proof]
  have subprob_p_val_cubed_pos_proof : p_val ^ 3 > 0 := by
    mkOpaque
    rw [p_val_def]
    apply pow_pos
    exact subprob_Sa_pos_proof
  have subprob_amgm_rhs_eval_proof : Real.rpow (p_val ^ 3 * p_val ^ 3 * 27) (1 / 3) = 3 * p_val ^ 2 := by
    mkOpaque
    have h_p_val_pos : p_val > 0 := by
      apply (Odd.pow_pos_iff (by decide : Odd 3)).mp
      exact subprob_p_val_cubed_pos_proof
    have h_p_val_nonneg : p_val ≥ 0 := le_of_lt h_p_val_pos
    have h_pow_combo : p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) = p_val ^ (6 : ℕ) := by rw [← pow_add p_val 3 3]
    rw [h_pow_combo]
    have h_27_is_3_cubed : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h_27_is_3_cubed]
    have h_pval6_nonneg : p_val ^ (6 : ℕ) ≥ 0 := by apply pow_nonneg h_p_val_nonneg
    have h_3_cubed_nonneg : (3 : ℝ) ^ (3 : ℕ) ≥ 0 := by
      apply pow_nonneg
      norm_num
    have my_mul_rpow (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z := Real.mul_rpow hx hy
    have actual_lemma_to_apply := my_mul_rpow (p_val ^ (6 : ℕ)) ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) h_pval6_nonneg h_3_cubed_nonneg
    rw [actual_lemma_to_apply]
    have h_term1_simplify : Real.rpow (p_val ^ (6 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = p_val ^ (2 : ℕ) :=
      by
      have rpp_eq : Real.rpow (p_val ^ (6 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = Real.rpow p_val (↑(6 : ℕ) * ((1 : ℝ) / (3 : ℝ))) := by
        rw [← Real.rpow_natCast p_val 6]
        exact Eq.symm (Real.rpow_mul h_p_val_nonneg (Nat.cast 6) ((1 : ℝ) / (3 : ℝ)))
      rw [rpp_eq]
      have h_exponent_val : (↑(6 : ℕ) : ℝ) * (1 / 3) = 2 := by norm_num
      rw [h_exponent_val]
      exact (Real.rpow_natCast p_val 2)
    rw [h_term1_simplify]
    have h_term2_simplify : Real.rpow ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = (3 : ℝ) := by
      have h_3_nonneg : (3 : ℝ) ≥ 0 := by norm_num
      have rpp_instance : Real.rpow ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = Real.rpow (3 : ℝ) (↑(3 : ℕ) * ((1 : ℝ) / (3 : ℝ))) := by
        rw [← Real.rpow_natCast (3 : ℝ) 3]
        exact Eq.symm (Real.rpow_mul h_3_nonneg (Nat.cast 3) ((1 : ℝ) / (3 : ℝ)))
      rw [rpp_instance]
      have h_exponent_val_3 : (↑(3 : ℕ) : ℝ) * ((1 : ℝ) / (3 : ℝ)) = (1 : ℝ) := by norm_num
      rw [h_exponent_val_3]
      apply Real.rpow_one
    rw [h_term2_simplify]
    rw [mul_comm]
  have subprob_amgm_apply_proof : (p_val ^ 3 + p_val ^ 3 + 27) / 3 ≥ Real.rpow (p_val ^ 3 * p_val ^ 3 * 27) (1 / 3) := by
    mkOpaque
    have h_p_val_cubed_nonneg : 0 ≤ p_val ^ (3 : ℕ) := by exact le_of_lt subprob_p_val_cubed_pos_proof
    have h_27_nonneg : 0 ≤ (27 : ℝ) := by norm_num
    have am_gm_ineq : Real.rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * (27 : ℝ)) ((1 : ℝ) / (3 : ℝ)) ≤ (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) := by
      let p₁ := p_val ^ (3 : ℕ)
      let p₂ := p_val ^ (3 : ℕ)
      let p₃ := (27 : ℝ)
      let w : ℝ := (1 : ℝ) / 3
      have hw_nonneg : 0 ≤ w := by norm_num
      have hw_sum_eq_1 : w + w + w = 1 := by norm_num
      have H := Real.geom_mean_le_arith_mean3_weighted hw_nonneg hw_nonneg hw_nonneg h_p_val_cubed_nonneg h_p_val_cubed_nonneg h_27_nonneg hw_sum_eq_1
      rw [← Real.mul_rpow h_p_val_cubed_nonneg h_p_val_cubed_nonneg] at H
      rw [← Real.mul_rpow (mul_nonneg h_p_val_cubed_nonneg h_p_val_cubed_nonneg) h_27_nonneg] at H
      rw [show ((1 : ℝ) / (3 : ℝ)) * p₁ + ((1 : ℝ) / (3 : ℝ)) * p₂ + ((1 : ℝ) / (3 : ℝ)) * p₃ = (p₁ + p₂ + p₃) / (3 : ℝ) by ring] at H
      exact H
    exact am_gm_ineq
  have subprob_amgm_implies_ineq_proof : 2 * p_val ^ 3 + 27 ≥ 9 * p_val ^ 2 := by
    mkOpaque
    have h_amgm_combined : (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ (3 : ℝ) * p_val ^ (2 : ℕ) := by
      have h_lhs_rewrite : (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) = (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) := by ring
      rw [← h_lhs_rewrite, ← subprob_amgm_rhs_eval_proof]
      exact subprob_amgm_apply_proof
    have h_three_pos : (0 : ℝ) < 3 := by norm_num
    have h_multiplied : 2 * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ ((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ) := by
      apply (le_div_iff h_three_pos).mp
      exact h_amgm_combined
    have h_rhs_simplified : ((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ) = (9 : ℝ) * p_val ^ (2 : ℕ) := by ring
    rw [h_rhs_simplified] at h_multiplied
    exact h_multiplied
  have subprob_ineq_rearranged_is_true_proof : ineq_rearranged := by
    mkOpaque
    rw [ineq_rearranged_def]
    have h_lhs_ge_mid : (2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ) := by exact subprob_use_hypothesis_h1_proof
    have h_mid_ge_rhs : (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ (9 : ℝ) * p_val ^ (2 : ℕ) := by exact subprob_amgm_implies_ineq_proof
    exact ge_trans h_lhs_ge_mid h_mid_ge_rhs
  exact
    show 3 / Real.sqrt 2 ≤ S1 by
      mkOpaque
      apply subprob_suffices_step_proof
      apply subprob_target_equiv_sq_proof.mpr
      rw [subprob_rhs_sq_eval_proof]
      rw [← reduced_target_ineq_def]
      rw [subprob_reduced_target_equiv_pq_form_proof]
      rw [subprob_ineq_pq_clear_den_proof]
      rw [subprob_ineq_rearranged_equiv_proof]
      exact subprob_ineq_rearranged_is_true_proof

#print axioms algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2

/-Sketch
variable (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 3 ≤ a * b + b * c + c * a)
play
  ha_pos := h₀.1
  hb_pos := h₀.2.1
  hc_pos := h₀.2.2

  S1 := a / Real.sqrt (a+b) + b / Real.sqrt (b+c) + c / Real.sqrt (c+a)
  Sa := a+b+c
  S_sum_a_ab := a*(a+b) + b*(b+c) + c*(c+a)

  subprob_S1_pos :≡ S1 > 0
  subprob_S1_pos_proof ⇐ show subprob_S1_pos by sorry
  subprob_Sa_pos :≡ Sa > 0
  subprob_Sa_pos_proof ⇐ show subprob_Sa_pos by sorry
  subprob_S_sum_a_ab_pos :≡ S_sum_a_ab > 0
  subprob_S_sum_a_ab_pos_proof ⇐ show subprob_S_sum_a_ab_pos by sorry

  -- Step 1. (Application of Hölder’s Inequality)
  -- Hölder's inequality states: (∑ x_i^(2/3) y_i^(1/3)) ≤ (∑ x_i)^(2/3) (∑ y_i)^(1/3)
  -- Here x_i are terms like a/√(a+b) and y_i are terms like a(a+b).
  -- Then x_i^(2/3)y_i^(1/3) becomes (a/√(a+b))^(2/3) * (a(a+b))^(1/3) = a.
  -- So, Sa ≤ (S1)^(2/3) * (S_sum_a_ab)^(1/3), which is (S1)^(2/3) * (S_sum_a_ab)^(1/3) ≥ Sa.
  subprob_holder :≡ Real.rpow S1 (2/3) * Real.rpow S_sum_a_ab (1/3) ≥ Sa
  subprob_holder_proof ⇐ show subprob_holder by sorry

  -- Step 2. (Isolating the Sum S1)
  -- From subprob_holder, raise both sides to power 3/2.
  -- ( (S1)^(2/3) * (S_sum_a_ab)^(1/3) )^(3/2) ≥ Sa^(3/2)
  -- S1 * (S_sum_a_ab)^(1/2) ≥ Sa^(3/2)
  -- S1 ≥ Sa^(3/2) / (S_sum_a_ab)^(1/2)
  -- This step requires all bases Sa, S1, S_sum_a_ab to be non-negative for rpow, and S_sum_a_ab > 0 for division.
  -- These are guaranteed by subprob_Sa_pos, subprob_S1_pos, subprob_S_sum_a_ab_pos.
  subprob_isolate_S1 :≡ S1 ≥ Real.rpow Sa (3/2) / Real.rpow S_sum_a_ab (1/2)
  subprob_isolate_S1_proof ⇐ show subprob_isolate_S1 by sorry

  -- To prove S1 ≥ 3 / Real.sqrt 2, it suffices to prove that the lower bound of S1 is ≥ 3 / Real.sqrt 2.
  target_ineq_rhs := Real.rpow Sa (3/2) / Real.rpow S_sum_a_ab (1/2)
  target_ineq := target_ineq_rhs ≥ 3 / Real.sqrt 2
  subprob_suffices_step :≡ target_ineq → S1 ≥ 3 / Real.sqrt 2
  subprob_suffices_step_proof ⇐ show subprob_suffices_step by sorry

  -- Now we need to prove target_ineq.
  -- target_ineq is Sa^(3/2) / S_sum_a_ab^(1/2) ≥ 3 / Real.sqrt 2.
  -- Square both sides. This is valid as both sides are non-negative.
  -- (Sa^(3/2) / S_sum_a_ab^(1/2))^2 ≥ (3 / Real.sqrt 2)^2
  -- Sa^3 / S_sum_a_ab ≥ 9/2
  subprob_sqrt2_pos :≡ Real.sqrt 2 > 0
  subprob_sqrt2_pos_proof ⇐ show subprob_sqrt2_pos by sorry
  subprob_target_rhs_pos :≡ 3 / Real.sqrt 2 ≥ 0
  subprob_target_rhs_pos_proof ⇐ show subprob_target_rhs_pos by sorry
  subprob_target_lhs_pos :≡ target_ineq_rhs ≥ 0
  subprob_target_lhs_pos_proof ⇐ show subprob_target_lhs_pos by sorry

  subprob_target_equiv_sq :≡ target_ineq ↔ (Sa^3 / S_sum_a_ab ≥ (3 / Real.sqrt 2)^2)
  subprob_target_equiv_sq_proof ⇐ show subprob_target_equiv_sq by sorry

  subprob_rhs_sq_eval :≡ (3 / Real.sqrt 2)^2 = 9/2
  subprob_rhs_sq_eval_proof ⇐ show subprob_rhs_sq_eval by sorry

  reduced_target_ineq := Sa^3 / S_sum_a_ab ≥ 9/2

  -- Step 3. (Rewriting ∑a(a+b))
  p_val := Sa -- p_val to avoid conflict if p is a Prop
  q_val := a*b + b*c + c*a

  -- S_sum_a_ab = a(a+b)+b(b+c)+c(c+a) = a^2+ab+b^2+bc+c^2+ca.
  -- p_val^2 - q_val = (a+b+c)^2 - (ab+bc+ca) = (a^2+b^2+c^2+2(ab+bc+ca)) - (ab+bc+ca) = a^2+b^2+c^2+ab+bc+ca.
  -- The proof states S_sum_a_ab = (p_val^2 - 2*q_val) + q_val = p_val^2 - q_val.
  subprob_S_sum_a_ab_rewrite_pq :≡ S_sum_a_ab = p_val^2 - q_val
  subprob_S_sum_a_ab_rewrite_pq_proof ⇐ show subprob_S_sum_a_ab_rewrite_pq by sorry

  -- The inequality `reduced_target_ineq` becomes p_val^3 / (p_val^2 - q_val) ≥ 9/2.
  ineq_pq_form := p_val^3 / (p_val^2 - q_val) ≥ 9/2
  subprob_reduced_target_equiv_pq_form :≡ reduced_target_ineq ↔ ineq_pq_form
  subprob_reduced_target_equiv_pq_form_proof ⇐ show subprob_reduced_target_equiv_pq_form by sorry

  -- Step 4. (Clearing the Denominator and Rearranging)
  -- Since p_val^2 - q_val = S_sum_a_ab > 0 (from subprob_S_sum_a_ab_pos).
  -- p_val^3 / (p_val^2 - q_val) ≥ 9/2  ⇔  2 * p_val^3 ≥ 9 * (p_val^2 - q_val)
  subprob_ineq_pq_clear_den :≡ ineq_pq_form ↔ 2 * p_val^3 ≥ 9 * (p_val^2 - q_val)
  subprob_ineq_pq_clear_den_proof ⇐ show subprob_ineq_pq_clear_den by sorry

  -- Rearrange: 2 * p_val^3 ≥ 9 * p_val^2 - 9 * q_val  ⇔  2 * p_val^3 + 9 * q_val ≥ 9 * p_val^2
  ineq_rearranged := 2 * p_val^3 + 9 * q_val ≥ 9 * p_val^2
  subprob_ineq_rearranged_equiv :≡ (2 * p_val^3 ≥ 9 * (p_val^2 - q_val)) ↔ ineq_rearranged
  subprob_ineq_rearranged_equiv_proof ⇐ show subprob_ineq_rearranged_equiv by sorry

  -- Step 5. (Using the Hypothesis and AM–GM Inequality)
  -- Hypothesis h₁: 3 ≤ q_val. So 27 ≤ 9 * q_val.
  subprob_9q_ge_27 :≡ 9 * q_val ≥ 27
  subprob_9q_ge_27_proof ⇐ show subprob_9q_ge_27 by sorry

  -- So 2 * p_val^3 + 9 * q_val ≥ 2 * p_val^3 + 27.
  subprob_use_hypothesis_h1 :≡ 2 * p_val^3 + 9 * q_val ≥ 2 * p_val^3 + 27
  subprob_use_hypothesis_h1_proof ⇐ show subprob_use_hypothesis_h1 by sorry

  -- AM-GM for p_val^3, p_val^3, 27.
  -- Need p_val^3 > 0. Since p_val = Sa > 0 (subprob_Sa_pos), p_val^3 > 0.
  subprob_p_val_cubed_pos :≡ p_val^3 > 0
  subprob_p_val_cubed_pos_proof ⇐ show subprob_p_val_cubed_pos by sorry

  -- (p_val^3 + p_val^3 + 27) / 3 ≥ (p_val^3 * p_val^3 * 27)^(1/3)
  -- RHS: (27 * p_val^6)^(1/3) = ( (3 * p_val^2)^3 )^(1/3) = 3 * p_val^2 (since p_val >= 0 implies p_val^2 >= 0).
  subprob_amgm_rhs_eval :≡ Real.rpow (p_val^3 * p_val^3 * 27) (1/3) = 3 * p_val^2
  subprob_amgm_rhs_eval_proof ⇐ show subprob_amgm_rhs_eval by sorry

  subprob_amgm_apply :≡ (p_val^3 + p_val^3 + 27) / 3 ≥ Real.rpow (p_val^3 * p_val^3 * 27) (1/3)
  subprob_amgm_apply_proof ⇐ show subprob_amgm_apply by sorry

  -- So (2 * p_val^3 + 27) / 3 ≥ 3 * p_val^2  =>  2 * p_val^3 + 27 ≥ 9 * p_val^2.
  subprob_amgm_implies_ineq :≡ 2 * p_val^3 + 27 ≥ 9 * p_val^2
  subprob_amgm_implies_ineq_proof ⇐ show subprob_amgm_implies_ineq by sorry

  -- Combine:
  -- 2 * p_val^3 + 9 * q_val ≥ 2 * p_val^3 + 27  (from subprob_use_hypothesis_h1)
  -- 2 * p_val^3 + 27 ≥ 9 * p_val^2             (from subprob_amgm_implies_ineq)
  -- Therefore, 2 * p_val^3 + 9 * q_val ≥ 9 * p_val^2, which is ineq_rearranged.
  subprob_ineq_rearranged_is_true :≡ ineq_rearranged
  subprob_ineq_rearranged_is_true_proof ⇐ show subprob_ineq_rearranged_is_true by sorry

  -- Step 6. (Conclusion)
  -- We have proved `ineq_rearranged`.
  -- By `subprob_ineq_rearranged_equiv`, `(2 * p_val^3 ≥ 9 * (p_val^2 - q_val))` is true.
  -- By `subprob_ineq_pq_clear_den`, `ineq_pq_form` is true.
  -- By `subprob_reduced_target_equiv_pq_form`, `reduced_target_ineq` is true. (i.e. Sa^3 / S_sum_a_ab ≥ 9/2)
  -- By `subprob_rhs_sq_eval` and `subprob_target_equiv_sq`, `target_ineq` is true. (i.e. Sa^(3/2) / S_sum_a_ab^(1/2) ≥ 3 / Real.sqrt 2)
  -- By `subprob_suffices_step`, `S1 ≥ 3 / Real.sqrt 2` is true.
  subprob_final_goal :≡ 3 / Real.sqrt 2 ≤ S1
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
variable (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : 3 ≤ a * b + b * c + c * a)
play
  ha_pos := h₀.1
  hb_pos := h₀.2.1
  hc_pos := h₀.2.2

  S1 := a / Real.sqrt (a+b) + b / Real.sqrt (b+c) + c / Real.sqrt (c+a)
  Sa := a+b+c
  S_sum_a_ab := a*(a+b) + b*(b+c) + c*(c+a)

  subprob_S1_pos :≡ S1 > 0
  subprob_S1_pos_proof ⇐ show subprob_S1_pos by
    -- The goal is to prove S1 > 0.
    -- S1 is defined as a sum of three terms: a/√(a+b), b/√(b+c), c/√(c+a).
    -- We are given that a, b, c are positive real numbers.
    -- The strategy is to show that each of these three terms is positive.
    -- The sum of positive terms is positive.

    -- Unfold the definition of S1 to expose its structure.
    rw [S1_def]

    -- First, let's prove that the term a / √(a + b) is positive.
    have h_term1_pos : a / √(a + b) > 0 := by
      -- To show a / √(a + b) > 0, we need to show a > 0 and √(a + b) > 0.
      -- a > 0 is given by ha_pos.
      -- To show √(a + b) > 0, we first need to show a + b > 0.
      have h_apb_pos : a + b > 0 := by
        -- Since a > 0 (ha_pos) and b > 0 (hb_pos), their sum a + b is positive.
        apply add_pos ha_pos hb_pos
      -- Now that a + b > 0, we can show √(a + b) > 0.
      have h_sqrt_apb_pos : √(a + b) > 0 := by
        -- Real.sqrt_pos.mpr states that if x > 0, then √x > 0.
        apply Real.sqrt_pos.mpr
        exact h_apb_pos
      -- Since a > 0 (ha_pos) and √(a + b) > 0 (h_sqrt_apb_pos), their quotient is positive.
      apply div_pos ha_pos h_sqrt_apb_pos

    -- Second, let's prove that the term b / √(b + c) is positive.
    have h_term2_pos : b / √(b + c) > 0 := by
      -- To show b / √(b + c) > 0, we need to show b > 0 and √(b + c) > 0.
      -- b > 0 is given by hb_pos.
      -- To show √(b + c) > 0, we first need to show b + c > 0.
      have h_bpc_pos : b + c > 0 := by
        -- Since b > 0 (hb_pos) and c > 0 (hc_pos), their sum b + c is positive.
        apply add_pos hb_pos hc_pos
      -- Now that b + c > 0, we can show √(b + c) > 0.
      have h_sqrt_bpc_pos : √(b + c) > 0 := by
        -- Using Real.sqrt_pos.mpr.
        apply Real.sqrt_pos.mpr
        exact h_bpc_pos
      -- Since b > 0 (hb_pos) and √(b + c) > 0 (h_sqrt_bpc_pos), their quotient is positive.
      apply div_pos hb_pos h_sqrt_bpc_pos

    -- Third, let's prove that the term c / √(c + a) is positive.
    have h_term3_pos : c / √(c + a) > 0 := by
      -- To show c / √(c + a) > 0, we need to show c > 0 and √(c + a) > 0.
      -- c > 0 is given by hc_pos.
      -- To show √(c + a) > 0, we first need to show c + a > 0.
      have h_cpa_pos : c + a > 0 := by
        -- Since c > 0 (hc_pos) and a > 0 (ha_pos), their sum c + a is positive.
        apply add_pos hc_pos ha_pos
      -- Now that c + a > 0, we can show √(c + a) > 0.
      have h_sqrt_cpa_pos : √(c + a) > 0 := by
        -- Using Real.sqrt_pos.mpr.
        apply Real.sqrt_pos.mpr
        exact h_cpa_pos
      -- Since c > 0 (hc_pos) and √(c + a) > 0 (h_sqrt_cpa_pos), their quotient is positive.
      apply div_pos hc_pos h_sqrt_cpa_pos

    -- Now we have proven that all three terms are positive:
    -- h_term1_pos: a / √(a + b) > 0
    -- h_term2_pos: b / √(b + c) > 0
    -- h_term3_pos: c / √(c + a) > 0
    -- The sum of positive real numbers is positive.
    -- S1 = (a / √(a + b) + b / √(b + c)) + c / √(c + a)
    -- We apply add_pos twice.
    apply add_pos
    -- The first part of the sum is (a / √(a + b) + b / √(b + c)). This must be positive.
    apply add_pos
    -- Apply positivity of term 1
    exact h_term1_pos
    -- Apply positivity of term 2
    exact h_term2_pos
    -- The second part of the sum is c / √(c + a). This must be positive.
    -- Apply positivity of term 3
    exact h_term3_pos
  subprob_Sa_pos :≡ Sa > 0
  subprob_Sa_pos_proof ⇐ show subprob_Sa_pos by

    -- The goal is to prove Sa > 0.
    -- We are given the definition of Sa: Sa_def: Sa = a + b + c.
    -- We are also given that a, b, and c are positive real numbers:
    -- ha_pos: 0 < a
    -- hb_pos: 0 < b
    -- hc_pos: 0 < c
    -- The other hypotheses (h₀, h₁, S1_def, S_sum_a_ab_def, subprob_S1_pos_proof)
    -- are not relevant for this specific goal.

    -- Step 1: Substitute the definition of Sa into the goal.
    -- The goal Sa > 0 becomes (a + b + c) > 0.
    rw [Sa_def]

    -- Step 2: Prove that a + b + c > 0.
    -- We know that a, b, and c are positive. The sum of three positive real numbers is positive.
    -- The original proof used 'add_pos_three', which is not a recognized identifier, causing an error.
    -- We replace its use with two applications of the standard Mathlib theorem `add_pos`.
    -- `add_pos` states: if `x > 0` and `y > 0`, then `x + y > 0`.
    -- The Lean parser typically handles `a + b + c` as `(a + b) + c`.
    -- Applying `add_pos` to the goal `0 < (a + b) + c` generates two subgoals:
    -- 1. `0 < a + b`
    -- 2. `0 < c`
    apply add_pos

    -- Step 2a: Prove the first subgoal `0 < a + b`.
    -- We apply `add_pos` again. This generates two further subgoals:
    -- 1a. `0 < a`
    -- 1b. `0 < b`
    . apply add_pos
      -- Step 2a.i: Prove `0 < a`.
      -- This is directly given by the hypothesis `ha_pos`.
      . exact ha_pos
      -- Step 2a.ii: Prove `0 < b`.
      -- This is directly given by the hypothesis `hb_pos`.
      . exact hb_pos

    -- Step 2b: Prove the second subgoal `0 < c`.
    -- This is directly given by the hypothesis `hc_pos`.
    . exact hc_pos

  subprob_S_sum_a_ab_pos :≡ S_sum_a_ab > 0
  subprob_S_sum_a_ab_pos_proof ⇐ show subprob_S_sum_a_ab_pos by
    -- The goal is to prove S_sum_a_ab > 0.
    -- We are given the definition of S_sum_a_ab:
    -- S_sum_a_ab_def: S_sum_a_ab = a * (a + b) + b * (b + c) + c * (c + a)
    -- We are also given that a, b, and c are positive real numbers:
    -- ha_pos: 0 < a
    -- hb_pos: 0 < b
    -- hc_pos: 0 < c
    -- Other hypotheses (h₀, h₁, S1, S1_def, Sa, Sa_def, subprob_S1_pos_proof, subprob_Sa_pos_proof)
    -- are not relevant for this specific subproblem, as per instructions to not be disturbed by irrelevant ones.

    -- Substitute the definition of S_sum_a_ab into the goal.
    rw [S_sum_a_ab_def]
    -- The goal becomes: a * (a + b) + b * (b + c) + c * (c + a) > 0

    -- We will prove this by showing that each term in the sum
    -- a * (a + b), b * (b + c), and c * (c + a) is positive,
    -- and the sum of positive numbers is positive.

    -- Step 1: Show that (a + b) is positive.
    have h_a_plus_b_pos : a + b > 0 := by
      -- Since a > 0 (ha_pos) and b > 0 (hb_pos), their sum (a + b) must be positive.
      apply add_pos
      exact ha_pos
      exact hb_pos

    -- Step 2: Show that (b + c) is positive.
    have h_b_plus_c_pos : b + c > 0 := by
      -- Since b > 0 (hb_pos) and c > 0 (hc_pos), their sum (b + c) must be positive.
      apply add_pos
      exact hb_pos
      exact hc_pos

    -- Step 3: Show that (c + a) is positive.
    have h_c_plus_a_pos : c + a > 0 := by
      -- Since c > 0 (hc_pos) and a > 0 (ha_pos), their sum (c + a) must be positive.
      apply add_pos
      exact hc_pos
      exact ha_pos

    -- Step 4: Show that the first term a * (a + b) is positive.
    have h_term1_pos : a * (a + b) > 0 := by
      -- Since a > 0 (ha_pos) and (a + b) > 0 (h_a_plus_b_pos),
      -- their product a * (a + b) must be positive.
      apply mul_pos
      exact ha_pos
      exact h_a_plus_b_pos

    -- Step 5: Show that the second term b * (b + c) is positive.
    have h_term2_pos : b * (b + c) > 0 := by
      -- Since b > 0 (hb_pos) and (b + c) > 0 (h_b_plus_c_pos),
      -- their product b * (b + c) must be positive.
      apply mul_pos
      exact hb_pos
      exact h_b_plus_c_pos

    -- Step 6: Show that the third term c * (c + a) is positive.
    have h_term3_pos : c * (c + a) > 0 := by
      -- Since c > 0 (hc_pos) and (c + a) > 0 (h_c_plus_a_pos),
      -- their product c * (c + a) must be positive.
      apply mul_pos
      exact hc_pos
      exact h_c_plus_a_pos

    -- Step 7: Show that the sum of the first two positive terms is positive.
    -- (a * (a + b)) + (b * (b + c)) > 0
    have h_sum_term1_term2_pos : a * (a + b) + b * (b + c) > 0 := by
      -- Since a * (a + b) > 0 (h_term1_pos) and b * (b + c) > 0 (h_term2_pos),
      -- their sum must be positive.
      apply add_pos
      exact h_term1_pos
      exact h_term2_pos

    -- Step 8: Show that the sum of all three terms is positive.
    -- This is (a * (a + b) + b * (b + c)) + c * (c + a).
    -- This corresponds to h_sum_term1_term2_pos + h_term3_pos.
    have h_final_sum_pos : (a * (a + b) + b * (b + c)) + c * (c + a) > 0 := by
      -- Since (a * (a + b) + b * (b + c)) > 0 (h_sum_term1_term2_pos)
      -- and c * (c + a) > 0 (h_term3_pos), their sum must be positive.
      apply add_pos
      exact h_sum_term1_term2_pos
      exact h_term3_pos

    -- The goal is now identical to h_final_sum_pos.
    exact h_final_sum_pos

  subprob_holder :≡ Real.rpow S1 (2/3) * Real.rpow S_sum_a_ab (1/3) ≥ Sa
  subprob_holder_proof ⇐ show subprob_holder by








    let u_fn : Fin 3 → ℝ := fun i => (![a, b, c]) i

    -- Define p and q for Holder's inequality
    let p₀ : ℝ := 3/2
    let q₀ : ℝ := 3

    have hp₀_gt_1 : 1 < p₀ := by norm_num
    have hq₀_gt_1 : 1 < q₀ := by norm_num
    have hp₀_inv_add_hq₀_inv_eq_1 : p₀⁻¹ + q₀⁻¹ = 1 := by
      field_simp
      norm_num

    -- Define a helper lemma that replaces the unknown 'Real.eq_of_log_eq_log_of_pos'
    -- This lemma states that if A > 0, B > 0, and log A = log B, then A = B.
    -- It is derived from Real.log_eq_log_iff.
    -- -- Corrected the type of h_log_eq to use Real.log explicitly to resolve ambiguity.
    have my_eq_of_log_eq_log_of_pos_for_apply {A B : ℝ} (hA_pos : 0 < A) (hB_pos : 0 < B) (h_log_eq : Real.log A = Real.log B) : A = B := by
      -- -- The theorem `Real.log_inj_iff` was reported as an unknown constant.
      -- -- We replace the call to `Real.log_inj_iff` with a proof based on `Real.log_le_log_iff` and `le_antisymm`.
      -- -- `Real.log_le_log_iff hX_pos hY_pos` provides `log X ≤ log Y ↔ X ≤ Y`.
      -- -- From `log A = log B`, we deduce `log A ≤ log B` and `log B ≤ log A`.
      have h_log_A_le_log_B : Real.log A ≤ Real.log B := Eq.le h_log_eq
      have h_log_B_le_log_A : Real.log B ≤ Real.log A := Eq.le h_log_eq.symm
      -- -- Applying `(Real.log_le_log_iff hA_pos hB_pos).mp` to `h_log_A_le_log_B` gives `A ≤ B`.
      have hA_le_B : A ≤ B := (Real.log_le_log_iff hA_pos hB_pos).mp h_log_A_le_log_B
      -- -- Applying `(Real.log_le_log_iff hB_pos hA_pos).mp` to `h_log_B_le_log_A` gives `B ≤ A`.
      have hB_le_A : B ≤ A := (Real.log_le_log_iff hB_pos hA_pos).mp h_log_B_le_log_A
      -- -- From `A ≤ B` and `B ≤ A`, `le_antisymm` gives `A = B`.
      exact le_antisymm hA_le_B hB_le_A

    -- Define a local lemma for (x^y)^z = x^(y*z) because Real.rpow_rpow is marked as unknown.
    -- This version requires x > 0, which is true in all contexts where it's used.
    have my_rpow_rpow {x : ℝ} (hx_pos : 0 < x) (y z : ℝ) : Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) := by
      -- Replace the unknown constant with our defined helper lemma.
      -- Applying this lemma will create three goals:
      -- 1. Prove that the left side of the equality is positive.
      -- 2. Prove that the right side of the equality is positive.
      -- 3. Prove that the logarithms of the two sides are equal.
      apply my_eq_of_log_eq_log_of_pos_for_apply
      · -- Prove (Real.rpow x y)^z > 0
        exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hx_pos y) z
      · -- Prove x^(y*z) > 0
        exact Real.rpow_pos_of_pos hx_pos (y * z)
      -- Prove log((Real.rpow x y)^z) = log(x^(y*z))
      -- -- The goal here is now Real.log (Real.rpow (Real.rpow x y) z) = Real.log (Real.rpow x (y * z))
      -- -- The existing rw rules use Real.log_rpow, so they should work correctly.
      -- -- Changed rw to erw because rw failed to find the pattern.
      -- -- erw is more powerful in matching up to definitional equality.
      -- -- The pattern involves `^` (HPow.hPow) from Real.log_rpow's definition,
      -- -- while the goal might be using Real.rpow directly.
      erw [Real.log_rpow (Real.rpow_pos_of_pos hx_pos y) z] -- Real.log((x^y)^z) = z * Real.log(x^y)
      rw [Real.log_rpow hx_pos y]                         -- z * Real.log(x^y) = z * (y * Real.log x)
      -- The `rw` tactic failed to find the pattern `Real.log (x ^ (y*z))` in the expression `Real.log (rpow x (y*z))`.
      -- This is likely due to `rw` not fully unfolding `HPow.hPow` (notation `^`) to `Real.rpow` or vice-versa.
      -- The `erw` tactic (equality rewrite) performs more aggressive unfolding up to definitional equality and can resolve this.
      -- We change `rw` to `erw` for this line. This is consistent with previous `erw` usage in this proof for similar reasons.
      erw [Real.log_rpow hx_pos (y*z)]                     -- Real.log(x^(y*z)) = (y*z) * Real.log x
      ring                                                -- z * y * Real.log x = y * z * Real.log x

    have hu_fn_pos : ∀ (i : Fin 3), 0 < u_fn i := by
      intro i
      fin_cases i
      . exact h₀.1 -- a > 0
      . exact h₀.2.1 -- b > 0
      . exact h₀.2.2 -- c > 0

    have hu_fn_sum_pos : ∀ (i : Fin 3), 0 < u_fn i + u_fn (i+1) := by
      intro i
      fin_cases i
      . simp [u_fn]; linarith [h₀.1, h₀.2.1] -- a+b > 0
      . simp [u_fn]; linarith [h₀.2.1, h₀.2.2] -- b+c > 0
      . simp [u_fn]; linarith [h₀.2.2, h₀.1] -- c+a > 0

    let base_U_fn : Fin 3 → ℝ := fun i => u_fn i / Real.sqrt (u_fn i + u_fn (i+1))
    let base_V_fn : Fin 3 → ℝ := fun i => u_fn i * (u_fn i + u_fn (i+1))

    have hbase_U_fn_pos : ∀ (i : Fin 3), 0 < base_U_fn i := by
      intro i
      simp [base_U_fn]
      apply div_pos (hu_fn_pos i) (Real.sqrt_pos.mpr (hu_fn_sum_pos i))

    have hbase_V_fn_pos : ∀ (i : Fin 3), 0 < base_V_fn i := by
      intro i
      simp [base_V_fn]
      apply mul_pos (hu_fn_pos i) (hu_fn_sum_pos i)

    let U_holder : Fin 3 → ℝ := fun i => Real.rpow (base_U_fn i) (2/3)
    let V_holder : Fin 3 → ℝ := fun i => Real.rpow (base_V_fn i) ((1 : ℝ) / (3 : ℝ))

    have hU_holder_pos : ∀ (i : Fin 3), 0 < U_holder i := by
      intro i; simp [U_holder]; apply Real.rpow_pos_of_pos (hbase_U_fn_pos i)

    have hV_holder_pos : ∀ (i : Fin 3), 0 < V_holder i := by
      intro i; simp [V_holder]; apply Real.rpow_pos_of_pos (hbase_V_fn_pos i)

    have h_conj_exp : Real.IsConjExponent p₀ q₀ :=
      Real.IsConjExponent.mk hp₀_gt_1 hp₀_inv_add_hq₀_inv_eq_1

    have holder_ineq : _ := Real.inner_le_Lp_mul_Lq_of_nonneg
      (Finset.univ : Finset (Fin 3))
      h_conj_exp
      (fun i _ => (hU_holder_pos i).le)
      (fun i _ => (hV_holder_pos i).le)

    have sum_UV_term : ∀ i, U_holder i * V_holder i = u_fn i := by
      intro i
      simp only [U_holder, V_holder, base_U_fn, base_V_fn, Real.sqrt_eq_rpow]
      have h_sum_pos := hu_fn_sum_pos i
      have h_fn_pos := hu_fn_pos i
      have h_u_fn_ge_0 : 0 ≤ u_fn i := (hu_fn_pos i).le
      have h_u_fn_sum_ge_0 : 0 ≤ u_fn i + u_fn (i + (1 : Fin (3 : ℕ))) := (hu_fn_sum_pos i).le

      have h_term_U_transformed : rpow (u_fn i / ((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ)/(2 : ℝ)))) ((2 : ℝ)/(3 : ℝ)) =
          rpow (u_fn i) ((2 : ℝ)/(3 : ℝ)) / rpow (((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ)/(2 : ℝ)))) ((2 : ℝ) / (3 : ℝ)) := by
        apply Real.div_rpow h_u_fn_ge_0 (Real.rpow_nonneg (h_u_fn_sum_ge_0) _) -- Corrected from Real.rpow_pos_of_pos to Real.rpow_nonneg for Real.div_rpow assumption

      rw [h_term_U_transformed]

      have h_V_factor_expanded :
          rpow (u_fn i * (u_fn i + u_fn (i + (1 : Fin (3 : ℕ))))) ((1 : ℝ) / (3 : ℝ)) =
          rpow (u_fn i) ((1 : ℝ) / (3 : ℝ)) * rpow (u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ((1 : ℝ) / (3 : ℝ)) := by
        -- The theorem Real.mul_rpow takes two hypotheses: 0 ≤ x and 0 ≤ y.
        -- The exponent is inferred from the goal.
        -- The previous error was due to passing the exponent as an argument.
        -- The corrected line uses `exact Real.mul_rpow hx hy`.
        exact Real.mul_rpow h_u_fn_ge_0 h_u_fn_sum_ge_0
      rw [h_V_factor_expanded]

      have h_inner_rpow_nonneg : 0 ≤ (u_fn i + u_fn (i + 1)) ^ ((1 : ℝ) / (2 : ℝ)) := Real.rpow_nonneg h_u_fn_sum_ge_0 ((1 : ℝ) / (2 : ℝ))
      have h_rpow_chain_rule_application :
          rpow ((u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) ^ ((1 : ℝ) / (2 : ℝ))) ((2 : ℝ) / (3 : ℝ)) =
          rpow (u_fn i + u_fn (i + (1 : Fin (3 : ℕ)))) (((1 : ℝ) / (2 : ℝ)) * ((2 : ℝ) / (3 : ℝ))) := by
        exact my_rpow_rpow (hu_fn_sum_pos i) ((1 : ℝ)/(2 : ℝ)) ((2 : ℝ)/(3 : ℝ))
      rw [h_rpow_chain_rule_application]
      have h_exponent_mult : ((1 : ℝ) / (2 : ℝ)) * ((2 : ℝ) / (3 : ℝ)) = (1 : ℝ) / (3 : ℝ) := by norm_num
      rw [h_exponent_mult]
      rw [mul_comm (rpow (u_fn i) (1/3)) (rpow (u_fn i + u_fn (i+1)) (1/3))]
      rw [←mul_assoc]
      have h_denom_term_ne_zero : rpow (u_fn i + u_fn (i+1)) (1/3) ≠ 0 :=
        (Real.rpow_pos_of_pos (hu_fn_sum_pos i) _).ne'
      rw [div_mul_cancel₀ _ h_denom_term_ne_zero]
      have h_lhs_step1 : rpow (u_fn i) ((2:ℝ)/(3:ℝ)) * rpow (u_fn i) ((1:ℝ)/(3:ℝ)) = rpow (u_fn i) (((2:ℝ)/(3:ℝ)) + ((1:ℝ)/(3:ℝ))) := by
        exact (Real.rpow_add (hu_fn_pos i) _ _).symm
      rw [h_lhs_step1]
      have h_exp_simplified : ((2:ℝ)/(3:ℝ)) + ((1:ℝ)/(3:ℝ)) = 1 := by
        norm_num
      rw [h_exp_simplified]
      apply Real.rpow_one

    have sum_UV_eq_Sa : Finset.sum Finset.univ (fun i => U_holder i * V_holder i) = Sa := by
      simp_rw [sum_UV_term]
      rw [Sa_def]
      rw [Fin.sum_univ_three u_fn]
      simp [u_fn]

    have sum_U_pow_p0_term : ∀ i, U_holder i ^ p₀ = base_U_fn i := by
      intro i
      simp only [U_holder, p₀]
      change Real.rpow (Real.rpow (base_U_fn i) (2/3)) (3/2) = base_U_fn i
      rw [my_rpow_rpow (hbase_U_fn_pos i) (2/3) (3/2)]
      have h_exponent_is_one : (2/3 : ℝ) * (3/2 : ℝ) = 1 := by norm_num
      rw [h_exponent_is_one]
      apply Real.rpow_one

    have sum_U_pow_p0_eq_S1 : Finset.sum Finset.univ (fun i => U_holder i ^ p₀) = S1 := by
      simp_rw [sum_U_pow_p0_term]
      rw [S1_def]
      rw [Fin.sum_univ_three base_U_fn]
      simp [base_U_fn, u_fn, Real.sqrt_eq_rpow]

    have sum_V_pow_q0_term : ∀ i, V_holder i ^ q₀ = base_V_fn i := by
      intro i
      simp only [V_holder, q₀]
      change Real.rpow (Real.rpow (base_V_fn i) (1/3)) 3 = base_V_fn i
      rw [my_rpow_rpow (hbase_V_fn_pos i) (1/3) 3]
      have h_exponent_is_one : (1/3 : ℝ) * (3 : ℝ) = 1 := by norm_num
      rw [h_exponent_is_one]
      apply Real.rpow_one

    have sum_V_pow_q0_eq_S_sum_a_ab : Finset.sum Finset.univ (fun i => V_holder i ^ q₀) = S_sum_a_ab := by
      simp_rw [sum_V_pow_q0_term]
      rw [S_sum_a_ab_def]
      rw [Fin.sum_univ_three base_V_fn]
      simp [base_V_fn, u_fn]

    have h_one_div_p₀ : 1/p₀ = 2/3 := by
      simp only [p₀, one_div_div]
    have h_one_div_q₀ : 1/q₀ = 1/3 := by
      simp only [q₀]

    -- The original line was:
    -- simp only [sum_UV_eq_Sa, sum_U_pow_p0_eq_S1, sum_V_pow_q0_eq_S_sum_a_ab, h_one_div_p₀, h_one_div_q₀] at holder_ineq
    -- This is replaced by a sequence of explicit rewrites at holder_ineq.
    -- This makes the transformation of holder_ineq more step-by-step and potentially more robust.
    rw [sum_UV_eq_Sa] at holder_ineq
    rw [sum_U_pow_p0_eq_S1] at holder_ineq
    rw [sum_V_pow_q0_eq_S_sum_a_ab] at holder_ineq
    rw [h_one_div_p₀] at holder_ineq
    rw [h_one_div_q₀] at holder_ineq

    -- After the rewrites, holder_ineq is:
    -- Sa ≤ S1 ^ (2/3) * S_sum_a_ab ^ (1/3)
    -- which is Sa ≤ Real.rpow S1 (2/3) * Real.rpow S_sum_a_ab (1/3)
    -- The goal is Real.rpow S1 (2/3) * Real.rpow S_sum_a_ab (1/3) ≥ Sa
    -- This is equivalent to holder_ineq because X ≥ Y is definitionally Y ≤ X in Lean.
    -- The `apply ge_iff_le.mpr` makes this equivalence explicit if needed, but `exact holder_ineq` should work directly.
    apply ge_iff_le.mpr
    exact holder_ineq

  subprob_isolate_S1 :≡ S1 ≥ Real.rpow Sa (3/2) / Real.rpow S_sum_a_ab (1/2)
  subprob_isolate_S1_proof ⇐ show subprob_isolate_S1 by



    -- The goal is S1 ≥ (Sa ^ (3/2)) / (S_sum_a_ab ^ (1/2)).
    -- This is equivalent to S1 * (S_sum_a_ab ^ (1/2)) ≥ Sa ^ (3/2), if S_sum_a_ab ^ (1/2) > 0.
    -- Or, (Sa ^ (3/2)) / (S_sum_a_ab ^ (1/2)) ≤ S1.
    -- This is equivalent to Sa ^ (3/2) ≤ S1 * (S_sum_a_ab ^ (1/2)), if S_sum_a_ab ^ (1/2) > 0.

    -- First, show that the denominator S_sum_a_ab ^ (1/2) is positive.
    have h_denom_pos : 0 < Real.rpow S_sum_a_ab (1 / 2) := by
      apply Real.rpow_pos_of_pos subprob_S_sum_a_ab_pos_proof -- (1/2) is any real number here

    -- Rewrite the goal using the equivalence (A / B ≤ C) ↔ (A ≤ C * B) for B > 0.
    -- ge_iff_le rewrites S1 ≥ X to X ≤ S1.
    rw [ge_iff_le, div_le_iff h_denom_pos]
    -- The goal is now: Real.rpow Sa (3 / 2) ≤ S1 * Real.rpow S_sum_a_ab (1 / 2)

    -- We are given subprob_holder_proof: rpow S1 (2/3) * rpow S_sum_a_ab (1/3) ≥ Sa.
    let LHS_holder := Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3)
    have h_holder_ineq : LHS_holder ≥ Sa := subprob_holder_proof -- This is Sa ≤ LHS_holder

    -- To manipulate this inequality by raising to a power, we need non-negativity of terms.
    have h_Sa_nn : 0 ≤ Sa := by
      exact le_of_lt subprob_Sa_pos_proof

    have h_S1_nn : 0 ≤ S1 := by -- Used for Real.rpow_nonneg, but Real.rpow_pos_of_pos can use S1 > 0.
      exact le_of_lt subprob_S1_pos_proof

    have h_S_sum_a_ab_nn : 0 ≤ S_sum_a_ab := by -- Used for Real.rpow_nonneg, but Real.rpow_pos_of_pos can use S_sum_a_ab > 0.
      exact le_of_lt subprob_S_sum_a_ab_pos_proof

    -- The terms in LHS_holder are non-negative because S1 and S_sum_a_ab are non-negative (actually positive).
    have h_rpow_S1_nn : 0 ≤ Real.rpow S1 (2 / 3) := by
      apply Real.rpow_nonneg h_S1_nn

    have h_rpow_S_sum_a_ab_nn : 0 ≤ Real.rpow S_sum_a_ab (1 / 3) := by
      apply Real.rpow_nonneg h_S_sum_a_ab_nn

    have h_LHS_holder_nn : 0 ≤ LHS_holder := by
      -- LHS_holder is Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3)
      -- Each factor is non-negative, so their product is non-negative.
      exact mul_nonneg h_rpow_S1_nn h_rpow_S_sum_a_ab_nn

    -- The exponent we will use is 3/2, which is non-negative.
    have h_exp_nn : 0 ≤ (3 / 2 : ℝ) := by
      norm_num

    -- Raise both sides of h_holder_ineq (Sa ≤ LHS_holder) to the power 3/2.
    -- Using Real.rpow_le_rpow: (hx : 0 ≤ x) (h_ineq_le : x ≤ y) (hz : 0 ≤ z) : x ^ z ≤ y ^ z.
    -- Here, x is Sa, y is LHS_holder. h_ineq_le is Sa ≤ LHS_holder.
    have h_raised_ineq : Real.rpow Sa (3 / 2) ≤ Real.rpow LHS_holder (3 / 2) := by
      apply Real.rpow_le_rpow h_Sa_nn h_holder_ineq h_exp_nn

    -- Simplify the right hand side: Real.rpow LHS_holder (3 / 2)
    have h_simplify_rhs : Real.rpow LHS_holder (3 / 2) = S1 * Real.rpow S_sum_a_ab (1 / 2) := by
      -- Unfold LHS_holder definition
      dsimp only [LHS_holder] -- LHS_holder is (Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3))

      -- Apply (x*y)^z = x^z * y^z.
      -- We introduce an intermediate hypothesis h_mul_rpow_step to apply Real.mul_rpow.
      -- This ensures that Real.rpow is used explicitly in the equality,
      -- avoiding potential confusion between Real.rpow and HPow.hPow notation (`^`) that might
      -- cause `rw` to fail if `^` is not definitionally Real.rpow in all contexts.
      have h_mul_rpow_step : Real.rpow (Real.rpow S1 (2 / 3) * Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) =
                               Real.rpow (Real.rpow S1 (2 / 3)) (3 / 2) * Real.rpow (Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) := by
        exact Real.mul_rpow h_rpow_S1_nn h_rpow_S_sum_a_ab_nn
      rw [h_mul_rpow_step]
      -- We now have (S1^(2/3))^(3/2) * (S_sum_a_ab^(1/3))^(3/2).

      -- Apply (x^a)^b = x^(a*b). Requires x ≥ 0 for the base of the rpow.
      have h_S1_rpow_rpow : Real.rpow (Real.rpow S1 (2 / 3)) (3 / 2) = Real.rpow S1 ((2 / 3 : ℝ) * (3 / 2 : ℝ)) := by
        let x := S1
        let y_exp := (2 / 3 : ℝ) -- renamed y to y_exp to avoid clash if Lean treats y in `Real.log_rpow {x} hx y` differently
        let z_exp := (3 / 2 : ℝ) -- renamed z to z_exp
        have hx_pos : 0 < x := subprob_S1_pos_proof
        have h_xy_pos : 0 < Real.rpow x y_exp := Real.rpow_pos_of_pos hx_pos y_exp
        have h_lhs_pos : 0 < Real.rpow (Real.rpow x y_exp) z_exp := Real.rpow_pos_of_pos h_xy_pos z_exp
        have h_rhs_pos : 0 < Real.rpow x (y_exp * z_exp) := Real.rpow_pos_of_pos hx_pos (y_exp * z_exp)
        suffices h_log_eq : Real.log (Real.rpow (Real.rpow x y_exp) z_exp) = Real.log (Real.rpow x (y_exp * z_exp)) by
          rw [(Real.exp_log h_lhs_pos).symm]
          rw [h_log_eq]
          rw [Real.exp_log h_rhs_pos]

        -- Proof for h_log_eq: log (LHS) = log (RHS)
        -- Using erw instead of rw as rw might not perform enough unfolding for the match.
        erw [@Real.log_rpow (Real.rpow x y_exp) h_xy_pos z_exp]
        erw [@Real.log_rpow x hx_pos y_exp]
        -- Corrected line: Changed rw to erw.
        -- rw failed because it could not strictly match the pattern of Real.log_rpow with the term in the goal.
        -- erw uses a more powerful matching algorithm that handles definitional equalities, allowing the rewrite to succeed.
        erw [@Real.log_rpow x hx_pos (y_exp*z_exp)]
        -- The theorem `mul_assoc a b c` is `(a * b) * c = a * (b * c)`.
        -- The current LHS is `z_exp * (y_exp * Real.log x)`. To change this to `(z_exp * y_exp) * Real.log x`,
        -- we need to apply `mul_assoc` in reverse.
        rw [← mul_assoc z_exp y_exp (Real.log x)]
        rw [mul_comm z_exp y_exp]

      -- Similarly for S_sum_a_ab. We have `h_S_sum_a_ab_nn : 0 ≤ S_sum_a_ab`.
      have h_S_sum_a_ab_rpow_rpow : Real.rpow (Real.rpow S_sum_a_ab (1 / 3)) (3 / 2) = Real.rpow S_sum_a_ab ((1 / 3 : ℝ) * (3 / 2 : ℝ)) := by
        let x := S_sum_a_ab
        let y_exp := (1 / 3 : ℝ) -- renamed y to y_exp
        let z_exp := (3 / 2 : ℝ) -- renamed z to z_exp
        have hx_pos : 0 < x := subprob_S_sum_a_ab_pos_proof
        have h_xy_pos : 0 < Real.rpow x y_exp := Real.rpow_pos_of_pos hx_pos y_exp
        have h_lhs_pos : 0 < Real.rpow (Real.rpow x y_exp) z_exp := Real.rpow_pos_of_pos h_xy_pos z_exp
        have h_rhs_pos : 0 < Real.rpow x (y_exp * z_exp) := Real.rpow_pos_of_pos hx_pos (y_exp * z_exp)
        suffices h_log_eq : Real.log (Real.rpow (Real.rpow x y_exp) z_exp) = Real.log (Real.rpow x (y_exp * z_exp)) by
          rw [(Real.exp_log h_lhs_pos).symm]
          rw [h_log_eq]
          rw [Real.exp_log h_rhs_pos]

        -- Proof for h_log_eq: log (LHS) = log (RHS)
        -- Corrected line: Using @ to make the 'base' argument of Real.log_rpow explicit.
        -- The original error was here. The base is (Real.rpow x y_exp), positivity proof is h_xy_pos, exponent is z_exp.
        -- Using erw instead of rw as rw might not perform enough unfolding for the match.
        erw [@Real.log_rpow (Real.rpow x y_exp) h_xy_pos z_exp]
        -- Assuming the above fixes the issue, subsequent lines might need similar treatment if they fail.
        -- For now, only the reported error line is changed as per instructions.
        -- If the next line fails, it would be `rw [Real.log_rpow hx_pos y_exp]`.
        -- The fix would be `rw [@Real.log_rpow x hx_pos y_exp]`.
        -- Changed `rw` to `erw`. `rw` may fail to match the pattern if the terms are not syntactically identical after limited unfolding.
        -- `erw` performs more aggressive unfolding (matching up to definitional equality), which is needed here, similar to the corresponding rewrite in the proof of `h_S1_rpow_rpow`.
        erw [@Real.log_rpow x hx_pos y_exp]
        -- Similarly for the next line.
        -- If it fails: `rw [Real.log_rpow hx_pos (y_exp*z_exp)]`
        -- Fix: `rw [@Real.log_rpow x hx_pos (y_exp*z_exp)]`
        -- Changed `rw` to `erw`. `rw` can fail to match if the expression in the goal (`Real.rpow ...`)
        -- and the expression in the theorem (`HPow.hPow ...`) are not syntactically identical,
        -- even if definitionally equal. `erw` uses matching up to definitional equality, which succeeds here.
        erw [@Real.log_rpow x hx_pos (y_exp*z_exp)]
        -- The theorem `mul_assoc a b c` is `(a * b) * c = a * (b * c)`.
        -- The goal's LHS is `z_exp * (y_exp * Real.log x)`, which is the RHS of `mul_assoc z_exp y_exp (Real.log x)`.
        -- To change `z_exp * (y_exp * Real.log x)` to `(z_exp * y_exp) * Real.log x`, we use `rw [←mul_assoc ...]`.
        rw [←mul_assoc z_exp y_exp (Real.log x)]
        rw [mul_comm z_exp y_exp]

      rw [h_S1_rpow_rpow, h_S_sum_a_ab_rpow_rpow]
      -- We now have S1^((2/3)*(3/2)) * S_sum_a_ab^((1/3)*(3/2)).

      -- Simplify the exponents.
      have exp1_val : (2 / 3 : ℝ) * (3 / 2 : ℝ) = 1 := by norm_num
      have exp2_val : (1 / 3 : ℝ) * (3 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [exp1_val, exp2_val]
      -- We now have S1^1 * S_sum_a_ab^(1/2).
      -- The goal is: Real.rpow S1 1 * Real.rpow S_sum_a_ab (1 / 2) = S1 * Real.rpow S_sum_a_ab (1 / 2)

      rw [show Real.rpow S1 (1 : ℝ) = S1 from Real.rpow_one S1]
      -- After this rewrite, the goal becomes `S1 * Real.rpow S_sum_a_ab (1 / 2) = S1 * Real.rpow S_sum_a_ab (1 / 2)`.
      -- This equality is true by reflexivity.
      -- rfl -- No need for rfl if the goal is already proved by rw.

    -- Substitute the simplified RHS back into h_raised_ineq.
    rw [h_simplify_rhs] at h_raised_ineq
    -- Now h_raised_ineq is: Real.rpow Sa (3 / 2) ≤ S1 * Real.rpow S_sum_a_ab (1 / 2).
    -- This is exactly our current goal.
    exact h_raised_ineq








  target_ineq_rhs := Real.rpow Sa (3/2) / Real.rpow S_sum_a_ab (1/2)
  target_ineq := target_ineq_rhs ≥ 3 / Real.sqrt 2
  subprob_suffices_step :≡ target_ineq → S1 ≥ 3 / Real.sqrt 2
  subprob_suffices_step_proof ⇐ show subprob_suffices_step by

    -- This proof aims to show that if `target_ineq` holds, then `S1 ≥ 3 / Real.sqrt 2`.
    -- The argument `htiq : target_ineq` is the hypothesis that `target_ineq` is true.
    intro htiq

    -- Step 1: From `htiq` (which is `target_ineq`) and its definition `target_ineq_def`,
    -- deduce that `target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2`.
    -- Let's call this inequality `ineq_rhs_ge_const`.
    have ineq_rhs_ge_const : target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2 := by
      -- We have `htiq : target_ineq`.
      -- We have `target_ineq_def : target_ineq = (target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2)`.
      -- We want to show `target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2`.
      -- We can rewrite `target_ineq` in `htiq` using `target_ineq_def`.
      rw [target_ineq_def] at htiq
      -- Now `htiq` is `target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2`.
      exact htiq

    -- Step 2: Show that `S1 ≥ target_ineq_rhs`.
    -- We have `subprob_isolate_S1_proof : S1 ≥ rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))`.
    -- We also have `target_ineq_rhs_def : target_ineq_rhs = rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))`.
    -- Let's call this inequality `S1_ge_ineq_rhs`.
    have S1_ge_ineq_rhs : S1 ≥ target_ineq_rhs := by
      -- We want to show `S1 ≥ target_ineq_rhs`.
      -- Substitute `target_ineq_rhs` in the goal with its definition `target_ineq_rhs_def`.
      rw [target_ineq_rhs_def]
      -- The goal becomes `S1 ≥ rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))`.
      -- This is exactly what `subprob_isolate_S1_proof` states.
      exact subprob_isolate_S1_proof

    -- Step 3: Combine the two inequalities by transitivity.
    -- We have `S1_ge_ineq_rhs : S1 ≥ target_ineq_rhs`.
    -- We have `ineq_rhs_ge_const : target_ineq_rhs ≥ (3 : ℝ) / Real.sqrt 2`.
    -- By transitivity of `≥` (`ge_trans`), we can conclude `S1 ≥ (3 : ℝ) / Real.sqrt 2`.
    exact ge_trans S1_ge_ineq_rhs ineq_rhs_ge_const

  subprob_sqrt2_pos :≡ Real.sqrt 2 > 0
  subprob_sqrt2_pos_proof ⇐ show subprob_sqrt2_pos by


    -- The goal is to prove Real.sqrt 2 > 0.
    -- This is equivalent to 0 < Real.sqrt 2.
    -- All the hypotheses provided (a, b, c, S1, Sa, etc.) are irrelevant to this specific goal.

    -- The theorem `Real.sqrt_pos` is an equivalence: `∀ {x : ℝ}, 0 < √x ↔ 0 < x`.
    -- The `apply` tactic cannot directly use an `iff` statement to prove one side of it without specifying the direction.
    -- We use `rw [Real.sqrt_pos]` to rewrite the goal `0 < √2` (which is `√2 > 0`) into its equivalent form `0 < 2`.

    -- The original `rw [Real.sqrt_pos]` failed because the syntactic form of the goal `√(2 : ℝ) > (0 : ℝ)`
    -- did not directly match the pattern `(0 : ℝ) < √?x` expected by `Real.sqrt_pos` (which states `(0 : ℝ) < √x ↔ (0 : ℝ) < x`).
    -- While `√(2 : ℝ) > (0 : ℝ)` is definitionally equivalent to `(0 : ℝ) < √(2 : ℝ)`, `rw` sometimes
    -- requires a more direct syntactic match, and the `>` operator might prevent this.
    -- To resolve this, we first use `rw [gt_iff_lt]` to change the goal `√(2 : ℝ) > (0 : ℝ)`
    -- into the syntactically explicit form `(0 : ℝ) < √(2 : ℝ)`.
    -- After this, `rw [Real.sqrt_pos]` can successfully match and rewrite the goal to `(0 : ℝ) < 2`.
    rw [gt_iff_lt, Real.sqrt_pos]

    -- The new goal is 0 < (2 : ℝ).
    -- This is a standard inequality, proven by the lemma zero_lt_two.
    exact zero_lt_two
  subprob_target_rhs_pos :≡ 3 / Real.sqrt 2 ≥ 0
  subprob_target_rhs_pos_proof ⇐ show subprob_target_rhs_pos by


    -- The goal is to prove that (3 / √2) ≥ 0.
    -- This can be proven if we show that the numerator (3) is non-negative
    -- and the denominator (√2) is positive.

    -- We use the theorem `div_nonneg {a b : α} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b`.
    -- Here, a = 3 and b = √2.
    apply div_nonneg
    · -- First subgoal: Prove 3 ≥ 0
      -- This is true by numerical evaluation.
      norm_num
    · -- Second subgoal: Prove √2 ≥ 0
      -- The tactic `apply div_nonneg` expects a proof for `0 ≤ √2`.
      -- We have `subprob_sqrt2_pos_proof : √(2 : ℝ) > (0 : ℝ)`.
      -- Since `x > 0` implies `x ≥ 0` (or `0 < x` implies `0 ≤ x`), we can use `le_of_lt`.
      exact le_of_lt subprob_sqrt2_pos_proof

  subprob_target_lhs_pos :≡ target_ineq_rhs ≥ 0
  subprob_target_lhs_pos_proof ⇐ show subprob_target_lhs_pos by
    -- The goal is target_ineq_rhs ≥ 0.
    -- We are given target_ineq_rhs_def: target_ineq_rhs = rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)).
    -- So we need to prove rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) ≥ 0.

    -- First, let's substitute the definition of target_ineq_rhs into the goal.
    rw [target_ineq_rhs_def]

    -- Let N = rpow Sa ((3 : ℝ) / (2 : ℝ)) (the numerator).
    -- Let D = rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) (the denominator).
    -- We need to show N / D ≥ 0.

    -- We are given subprob_Sa_pos_proof: Sa > 0.
    -- Since Sa > 0, rpow Sa (anything) > 0. More specifically, rpow Sa (3/2) > 0.
    have h_numerator_pos : rpow Sa ((3 : ℝ) / (2 : ℝ)) > 0 := by
      apply Real.rpow_pos_of_pos
      -- This requires proving Sa > 0, which is given by subprob_Sa_pos_proof.
      exact subprob_Sa_pos_proof

    -- We are given subprob_S_sum_a_ab_pos_proof: S_sum_a_ab > 0.
    -- Since S_sum_a_ab > 0, rpow S_sum_a_ab (anything) > 0. More specifically, rpow S_sum_a_ab (1/2) > 0.
    have h_denominator_pos : rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) > 0 := by
      apply Real.rpow_pos_of_pos
      -- This requires proving S_sum_a_ab > 0, which is given by subprob_S_sum_a_ab_pos_proof.
      exact subprob_S_sum_a_ab_pos_proof

    -- Since the numerator N > 0 and the denominator D > 0, their quotient N / D must also be > 0.
    have h_fraction_pos : rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) > 0 := by
      apply div_pos
      -- This requires proving N > 0 and D > 0.
      exact h_numerator_pos
      exact h_denominator_pos

    -- If a number is strictly greater than 0, it is also greater than or equal to 0.
    apply le_of_lt
    exact h_fraction_pos

  subprob_target_equiv_sq :≡ target_ineq ↔ (Sa^3 / S_sum_a_ab ≥ (3 / Real.sqrt 2)^2)
  subprob_target_equiv_sq_proof ⇐ show subprob_target_equiv_sq by

























































    -- The main goal is an equivalence:
    -- target_ineq ↔ (Sa ^ 3 / S_sum_a_ab ≥ (3 / Real.sqrt 2) ^ 2)

    -- Substitute the definitions of target_ineq and target_ineq_rhs
    -- target_ineq_def: target_ineq = (target_ineq_rhs ≥ (3 : ℝ) / √(2 : ℝ))
    -- target_ineq_rhs_def: target_ineq_rhs = rpow Sa ((3 : ℝ) / (2 : ℝ)) / rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))
    rw [target_ineq_def, target_ineq_rhs_def]
    -- The goal becomes:
    -- (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2) ≥ (3 : ℝ) / √(2 : ℝ)) ↔ (Sa ^ 3 / S_sum_a_ab ≥ (3 / Real.sqrt 2) ^ 2)

    -- Let A_val := (3 : ℝ) / √(2 : ℝ)
    -- Let B_val := rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)
    -- The LHS of the goal's equivalence is B_val ≥ A_val.
    -- We will use a theorem that for non-negative X, Y, (X ≤ Y ↔ X^2 ≤ Y^2).
    -- To make the LHS of the goal (B_val ≥ A_val) match the form X ≤ Y,
    -- we use `conv` to apply `ge_iff_le` specifically to the LHS of the main equivalence in the goal.
    conv =>
      lhs -- Focus on the LHS of the main iff: (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2) ≥ (3 : ℝ) / √(2 : ℝ))
      rw [ge_iff_le] -- Changes it to: ((3 : ℝ) / √(2 : ℝ) ≤ rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2))
    -- After conv, the goal is:
    -- ((3 : ℝ) / √(2 : ℝ) ≤ rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ↔ (Sa ^ 3 / S_sum_a_ab ≥ (3 / Real.sqrt 2) ^ 2)
    -- This is of the form (A_val ≤ B_val) ↔ (RHS_ineq_ge)

    have hX_nonneg : 0 ≤ rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2) := by {
      rw [←target_ineq_rhs_def]
      exact subprob_target_lhs_pos_proof
    }
    -- Now, the LHS of the goal `(A_val ≤ B_val)` matches the LHS of the rewrite rule derived from `pow_le_pow_iff_left`.
    -- The rewrite rule `(pow_le_pow_iff_left subprob_target_rhs_pos_proof hX_nonneg hn).symm` is:
    -- (A_val ≤ B_val) ↔ (A_val^2 ≤ B_val^2)
    -- Applying this rule transforms the goal (A_val ≤ B_val) ↔ (RHS_ineq_ge) into:
    -- (A_val^2 ≤ B_val^2) ↔ (RHS_ineq_ge)

    have h_sq_le_sq_symm : ((3 : ℝ) / √(2 : ℝ)) ≤ (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ↔
                           ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ) ≤ (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ^ (2 : ℕ) :=
      (pow_le_pow_iff_left subprob_target_rhs_pos_proof hX_nonneg (by {norm_num} : (2 : ℕ) ≠ (0 : ℕ))).symm
    rw [h_sq_le_sq_symm]
    -- The rewrite `rw [h_sq_le_sq_symm]` applies the proven equivalence.
    -- Let `A_val := (3 : ℝ) / √(2 : ℝ)` and `B_val := rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)`.
    -- The LHS of the goal was `A_val ≤ B_val`. After the rewrite, it becomes `A_val^2 ≤ B_val^2`.
    -- The goal is now an equivalence where the LHS inequality has both sides squared:
    -- `(A_val^2 ≤ B_val^2) ↔ (Sa ^ 3 / S_sum_a_ab ≥ A_val^2)`
    -- The next steps will simplify `B_val^2` to `Sa ^ 3 / S_sum_a_ab`.

    -- Simplify the term (rpow Sa (3 / 2) / rpow S_sum_a_ab (1 / 2)) ^ 2
    -- Use div_pow: (a / b) ^ n = a ^ n / b ^ n for n : ℕ. Here n = 2.
    -- ℝ is a DivisionRing, so div_pow applies.
    rw [div_pow (rpow Sa (3 / 2)) (rpow S_sum_a_ab (1 / 2)) 2]
    -- The LHS of the equivalence's LHS is now:
    -- (rpow Sa (3 / 2)) ^ 2 / (rpow S_sum_a_ab (1 / 2)) ^ 2

    -- Simplify the numerator: (rpow Sa (3 / 2)) ^ 2
    -- Use Real.rpow_mul for Sa as well. (x^y)^z = x^(y*z) -- This comment refers to the general idea, not the specific theorem Real.rpow_mul
    have hSa_nonneg : 0 ≤ Sa := le_of_lt subprob_Sa_pos_proof
    have h_num_simpl : (rpow Sa ((3 : ℝ) / (2 : ℝ))) ^ (2 : ℕ) = rpow Sa (((3 : ℝ) / (2 : ℝ)) * (2 : ℝ)) := by
      -- The original proof used `rw [Real.rpow_pow hSa_nonneg]`, but `Real.rpow_pow` is reported as an "unknown constant".
      -- We replace this with a proof strategy that relies on logarithms, using `Real.log_pow` (from hints) and `Real.log_rpow`.
      -- This requires proving that arguments to log are positive.
      have hSa_pos : Sa > 0 := subprob_Sa_pos_proof -- Given assumption for Sa.
      let p_exp := (3 : ℝ) / (2 : ℝ) -- Define p for clarity
      let n_exp := (2 : ℕ) -- Define n for clarity

      -- LHS of goal is (Sa ^ p_exp) ^ n_exp. RHS is Sa ^ (p_exp * (2:ℝ)).
      -- Prove terms that will be arguments to log are positive.
      have h_Sap_pos : Sa ^ p_exp > 0 := Real.rpow_pos_of_pos hSa_pos p_exp
      have h_LHS_val_pos : (Sa ^ p_exp) ^ n_exp > 0 := pow_pos h_Sap_pos n_exp -- `Sa ^ p_exp` is the base, `n_exp` is the Nat exponent
      -- The RHS of the main equality is Sa ^ (p_exp * (2:ℝ)). (2:ℝ) is the literal Real number 2.
      have h_RHS_val_pos : Sa ^ (p_exp * (2:ℝ)) > 0 := Real.rpow_pos_of_pos hSa_pos (p_exp * (2:ℝ))

      -- The theorem `Real.log_inj_iff` was reported as an unknown constant.
      -- We replace it with a proof based on `Real.log_le_log_iff` and `le_antisymm`.
      -- First, prove that the logarithms of both sides are equal.
      have h_log_eq : Real.log ((Sa ^ p_exp) ^ n_exp) = Real.log (Sa ^ (p_exp * (2:ℝ))) := by
        -- Goal is: log((Sa ^ p_exp) ^ n_exp) = log(Sa ^ (p_exp * (2:ℝ)))
        -- Simplify LHS: log((Sa ^ p_exp) ^ n_exp) = ↑n_exp * log(Sa ^ p_exp) using Real.log_pow.
        -- The argument to Real.log_pow should be the base of the power, which is (Sa ^ p_exp).
        -- h_Sap_pos is a proof that this base is positive, not the base itself.
        rw [Real.log_pow (Sa ^ p_exp) n_exp]
        -- LHS is now: ↑n_exp * log(Sa ^ p_exp)
        -- Simplify log(Sa ^ p_exp) = p_exp * log Sa using Real.log_rpow.
        rw [Real.log_rpow hSa_pos p_exp]
        -- LHS is now: ↑n_exp * (p_exp * log Sa)

        -- Simplify RHS: log(Sa ^ (p_exp * (2:ℝ))) = (p_exp * (2:ℝ)) * log Sa using Real.log_rpow.
        rw [Real.log_rpow hSa_pos (p_exp * (2:ℝ))]
        -- Goal is now: ↑n_exp * (p_exp * log Sa) = (p_exp * (2:ℝ)) * log Sa
        -- Substitute n_exp = 2 (Nat). ↑(2:ℕ) becomes (2:ℝ) after simp.
        simp -- Simplifies ↑(2 : ℕ) to (2 : ℝ) among other things.
        -- Goal becomes: (2 : ℝ) * (p_exp * log Sa) = (p_exp * (2 : ℝ)) * log Sa
        ring -- This equality holds by commutativity and associativity of multiplication.

      -- Now we have log LHS_val = log RHS_val (h_log_eq).
      -- We use `le_antisymm` to prove LHS_val = RHS_val.
      apply le_antisymm
      · -- Prove LHS_val ≤ RHS_val.
        -- The current goal is `(Sa ^ p_exp) ^ n_exp ≤ Sa ^ (p_exp * (2 : ℝ))`. Let this be `X ≤ Y`.
        -- We have `h_LHS_val_pos: X > 0` and `h_RHS_val_pos: Y > 0`.
        -- The theorem `Real.log_le_log_iff h_LHS_val_pos h_RHS_val_pos` states `(Real.log X ≤ Real.log Y) ↔ (X ≤ Y)`.
        -- The `.mp` part of this equivalence is `(Real.log X ≤ Real.log Y) → (X ≤ Y)`.
        -- When we `apply (...).mp` to the goal `X ≤ Y`, Lean replaces the goal with the premise `Real.log X ≤ Real.log Y`.
        -- The previous code used `.mpr`, which is `(X ≤ Y) → (Real.log X ≤ Real.log Y)`.
        -- `apply (...).mpr` to a goal `G` means `G` must unify with the conclusion of `.mpr` (which is `Real.log X ≤ Real.log Y`).
        -- The goal `X ≤ Y` does not unify with `Real.log X ≤ Real.log Y`, hence the error.
        apply (Real.log_le_log_iff h_LHS_val_pos h_RHS_val_pos).mp
        -- The goal is now `log LHS_val ≤ log RHS_val`. This follows from `h_log_eq`.
        exact h_log_eq.le
      · -- Prove RHS_val ≤ LHS_val.
        -- Similar to the above, the goal is `Sa ^ (p_exp * (2 : ℝ)) ≤ (Sa ^ p_exp) ^ n_exp`. Let this be `Y ≤ X`.
        -- We apply the `.mp` part of `Real.log_le_log_iff h_RHS_val_pos h_LHS_val_pos`, which is `(Real.log Y ≤ Real.log X) → (Y ≤ X)`.
        -- This changes the goal to `Real.log Y ≤ Real.log X`.
        apply (Real.log_le_log_iff h_RHS_val_pos h_LHS_val_pos).mp
        -- The goal is now `log RHS_val ≤ log LHS_val`. This follows from `h_log_eq.symm.le`.
        exact h_log_eq.symm.le
    rw [h_num_simpl] -- result: rpow Sa (((3 : ℝ) / (2 : ℝ)) * (2 : ℝ))

    -- Simplify the denominator: (rpow S_sum_a_ab (1 / 2)) ^ 2
    -- Use Real.rpow_mul for S_sum_a_ab as well.
    -- We have subprob_S_sum_a_ab_pos_proof: S_sum_a_ab > 0, which implies 0 ≤ S_sum_a_ab.
    have hS_sum_a_ab_nonneg : 0 ≤ S_sum_a_ab := le_of_lt subprob_S_sum_a_ab_pos_proof
    -- Similarly, for the denominator, prove the equality as `h_den_simpl` first.
    have h_den_simpl : (rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ))) ^ (2 : ℕ) = rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) := by
      -- The original definition of h_sqrt_id_local was `√X = X^(1/2)`.
      -- The tactic `rw [h_sqrt_id_local]` attempts to find the LHS of h_sqrt_id_local (`√X`) in the target.
      -- Since `√X` was not in the target `(X^(1/2))^2 = X^((1/2)*2)`, the rewrite failed.
      -- The comment in the original code indicated an intention to rewrite `X^(1/2)` to `√X` using `rw [h_sqrt_id_local]`.
      -- For `rw [h_sqrt_id_local]` to achieve this, `h_sqrt_id_local` must be defined as `X^(1/2) = √X`.
      -- We therefore change the definition of `h_sqrt_id_local` (its type and proof term) to match this intention.
      have h_sqrt_id_local : Real.rpow S_sum_a_ab ((1 : ℝ) / (2 : ℝ)) = Real.sqrt S_sum_a_ab :=
        (Real.sqrt_eq_rpow S_sum_a_ab).symm
      rw [h_sqrt_id_local]
      rw [Real.sq_sqrt hS_sum_a_ab_nonneg]
      have h_exp_eq_one : ((1 : ℝ) / (2 : ℝ)) * (2 : ℝ) = 1 := by norm_num
      rw [h_exp_eq_one]
      -- The goal is `S_sum_a_ab = rpow S_sum_a_ab (1 : ℝ)`.
      -- `Real.rpow_one S_sum_a_ab` is the theorem `rpow S_sum_a_ab (1 : ℝ) = S_sum_a_ab`.
      -- The symmetric version of this theorem, `(Real.rpow_one S_sum_a_ab).symm`, is
      -- `S_sum_a_ab = rpow S_sum_a_ab (1 : ℝ)`, which exactly matches the goal.
      exact (Real.rpow_one S_sum_a_ab).symm
    rw [h_den_simpl] -- result: rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ))
    -- The LHS of the equivalence's LHS is now:
    -- rpow Sa ((3 / 2) * 2) / rpow S_sum_a_ab ((1 / 2) * 2)

    -- Simplify the exponents
    have h_exp_numer : (3 / 2 : ℝ) * (2 : ℝ) = 3 := by norm_num
    rw [h_exp_numer] -- result: rpow Sa 3

    have h_exp_denom : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
    -- The following two lines `rw [h_exp_denom]` and `erw [Real.rpow_one S_sum_a_ab]` are replaced.
    -- rw [h_exp_denom]
    -- erw [Real.rpow_one S_sum_a_ab]

    -- The original erw [Real.rpow_one S_sum_a_ab] failed to find the pattern after rw [h_exp_denom].
    -- We combine these two steps into a new lemma h_simplify_denom_rpow that directly
    -- simplifies rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) to S_sum_a_ab.
    -- This makes the simplification more robust. The term (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) is currently
    -- the exponent of S_sum_a_ab in the goal.
    have h_simplify_denom_rpow : rpow S_sum_a_ab (((1 : ℝ) / (2 : ℝ)) * (2 : ℝ)) = S_sum_a_ab := by
      rw [h_exp_denom] -- This uses the h_exp_denom defined above to change the exponent to 1.
      exact Real.rpow_one S_sum_a_ab -- This states rpow S_sum_a_ab 1 = S_sum_a_ab.
    rw [h_simplify_denom_rpow] -- This applies the simplification to the main goal.
    -- The LHS of the equivalence's LHS is now:
    -- ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ) ≤ rpow Sa (3 : ℝ) / S_sum_a_ab

    -- Convert rpow terms to standard power or simplify
    -- rpow x (n : ℝ) where n is an integer (represented as real) should be x ^ n (integer power).
    -- For `rpow Sa 3`, which is `rpow Sa (3 : ℝ)`, we want to convert it to `Sa ^ (3 : ℕ)`.
    -- First, show (3 : ℝ) = (↑(3 : ℕ) : ℝ).
    have h_three_is_cast : (3 : ℝ) = (↑(3 : ℕ) : ℝ) := by simp
    rw [h_three_is_cast] -- Changes `rpow Sa (3 : ℝ)` to `rpow Sa (↑(3 : ℕ) : ℝ)`.
                         -- This also affects `(3:ℝ)` on the RHS of the goal, in `((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ)`.

    -- The `rw [Real.rpow_nat_cast]` tactic failed, possibly due to unification subtleties
    -- with the term `(↑(3 : ℕ) : ℝ)`.
    -- We make the rewrite more explicit by first proving the specific instance of
    -- Real.rpow_nat_cast that we need for `Sa` and `(3 : ℕ)`.
    have h_sa_rpow_eq_pow : rpow Sa (↑(3 : ℕ) : ℝ) = Sa ^ (3 : ℕ) := by
      -- This is a direct application of `Real.rpow_nat_cast Sa (3 : ℕ)`.
      -- `Sa` corresponds to `x` and `(3 : ℕ)` to `n` in the theorem `Real.rpow_nat_cast x n`.
      exact Real.rpow_nat_cast Sa (3 : ℕ)
    rw [h_sa_rpow_eq_pow]
    -- After this rewrite, the goal becomes:
    -- `(((↑(3 : ℕ)) : ℝ) / √(2 : ℝ)) ^ (2 : ℕ) ≤ Sa ^ (3 : ℕ) / S_sum_a_ab ↔ Sa ^ (3 : ℕ) / S_sum_a_ab ≥ (((↑(3 : ℕ)) : ℝ) / √(2 : ℝ)) ^ (2 : ℕ)`
    -- This is of the form (X ≤ Y) ↔ (Y ≥ X).
    -- Since `Y ≥ X` is definitionally equivalent to `X ≤ Y` (as per `ge_iff_le`),
    -- the goal is definitionally equivalent to (X ≤ Y) ↔ (X ≤ Y).
    -- The `rw` tactic automatically tries `rfl` after performing the rewrite.
    -- Since the goal is reflexively true after the substitution, `rw` closes the goal.
    -- Thus, the explicit `rfl` tactic on the next line is redundant and has been removed.

  subprob_rhs_sq_eval :≡ (3 / Real.sqrt 2)^2 = 9/2
  subprob_rhs_sq_eval_proof ⇐ show subprob_rhs_sq_eval by
    -- Proof Sketch:
    -- The goal is to prove (3 / √2) ^ 2 = 9 / 2.
    -- 1. Apply the power of a division rule: (x / y) ^ n = x ^ n / y ^ n.
    --    This transforms (3 / √2) ^ 2 to 3 ^ 2 / (√2) ^ 2.
    -- 2. Simplify (√2) ^ 2 to 2 using the rule (√x) ^ 2 = x for x ≥ 0.
    --    This requires proving that 2 ≥ 0, which is straightforward.
    --    The expression becomes 3 ^ 2 / 2.
    -- 3. Evaluate 3 ^ 2 to 9.
    --    The expression becomes 9 / 2.
    -- 4. The goal is now 9 / 2 = 9 / 2, which is true by reflexivity.
    -- Tactics `rw`, `norm_num` and `have` will be used.

    -- Apply the rule (x / y) ^ n = x ^ n / y ^ n. Here x = 3, y = √2, n = 2.
    rw [div_pow]
    -- The goal is now: 3 ^ 2 / (Real.sqrt 2) ^ 2 = 9 / 2.

    -- Simplify (Real.sqrt 2) ^ 2 to 2.
    -- This uses the theorem Real.sq_sqrt, which states (√x) ^ 2 = x if x ≥ 0.
    -- We need to show that 2 ≥ 0.
    have h_two_nonneg : (0 : ℝ) ≤ 2 := by
      norm_num -- This tactic proves numerical inequalities like 0 ≤ 2.
    -- Now apply Real.sq_sqrt using h_two_nonneg.
    rw [Real.sq_sqrt h_two_nonneg]
    -- The goal is now: 3 ^ 2 / 2 = 9 / 2.

    -- Evaluate the numerical expression 3 ^ 2 / 2.
    -- 3 ^ 2 = 9, so the left side is 9 / 2.
    -- The goal becomes 9 / 2 = 9 / 2.
    norm_num -- This tactic handles numerical computations and equalities.

  reduced_target_ineq := Sa^3 / S_sum_a_ab ≥ 9/2

  p_val := Sa -- p_val to avoid conflict if p is a Prop
  q_val := a*b + b*c + c*a

  subprob_S_sum_a_ab_rewrite_pq :≡ S_sum_a_ab = p_val^2 - q_val
  subprob_S_sum_a_ab_rewrite_pq_proof ⇐ show subprob_S_sum_a_ab_rewrite_pq by
    -- Substitute the definitions of S_sum_a_ab, p_val, and q_val
    rw [S_sum_a_ab_def]
    rw [p_val_def]
    rw [q_val_def]
    rw [Sa_def]
    -- We need to prove:
    -- a * (a + b) + b * (b + c) + c * (c + a) = (a + b + c) ^ 2 - (a * b + b * c + c * a)
    -- Expand both sides and simplify
    -- LHS: a * (a + b) + b * (b + c) + c * (c + a)
    --      = a^2 + ab + b^2 + bc + c^2 + ca
    -- RHS: (a + b + c) ^ 2 - (a * b + b * c + c * a)
    --      = (a^2 + b^2 + c^2 + 2ab + 2bc + 2ca) - (ab + bc + ca)
    --      = a^2 + b^2 + c^2 + ab + bc + ca
    -- Both sides are equal.
    -- The `ring` tactic can handle this.
    ring

  ineq_pq_form := p_val^3 / (p_val^2 - q_val) ≥ 9/2
  subprob_reduced_target_equiv_pq_form :≡ reduced_target_ineq ↔ ineq_pq_form
  subprob_reduced_target_equiv_pq_form_proof ⇐ show subprob_reduced_target_equiv_pq_form by

    -- Unfold definitions of reduced_target_ineq and ineq_pq_form
    rw [reduced_target_ineq_def]
    rw [ineq_pq_form_def]
    -- Goal: (Sa ^ (3 : ℕ) / S_sum_a_ab ≥ (9 : ℝ) / (2 : ℝ)) ↔ (p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ))

    -- Substitute p_val with Sa in the right hand side of the equivalence, using p_val_def
    rw [p_val_def]
    -- Goal: (Sa ^ (3 : ℕ) / S_sum_a_ab ≥ (9 : ℝ) / (2 : ℝ)) ↔ (Sa ^ (3 : ℕ) / (Sa ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ))

    -- Establish that S_sum_a_ab = Sa ^ (2 : ℕ) - q_val
    have h_S_sum_a_ab_eq_Sa_q_val : S_sum_a_ab = Sa ^ (2 : ℕ) - q_val := by
      -- Start from the given subprob_S_sum_a_ab_rewrite_pq_proof: S_sum_a_ab = p_val ^ (2 : ℕ) - q_val
      rw [subprob_S_sum_a_ab_rewrite_pq_proof]
      -- Goal of this `have` is now: p_val ^ (2 : ℕ) - q_val = Sa ^ (2 : ℕ) - q_val
      -- Substitute p_val with Sa using p_val_def
      rw [p_val_def]
      -- Goal of this `have` is now: Sa ^ (2 : ℕ) - q_val = Sa ^ (2 : ℕ) - q_val, which is true by reflexivity.

    -- Substitute S_sum_a_ab in the main goal using the equality h_S_sum_a_ab_eq_Sa_q_val
    rw [h_S_sum_a_ab_eq_Sa_q_val]
    -- Goal: (Sa ^ (3 : ℕ) / (Sa ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)) ↔ (Sa ^ (3 : ℕ) / (Sa ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ))
    -- This is of the form P ↔ P, which is true by Iff.rfl.
    -- The previous `rw` tactic already solved the goal by reducing it to `P ↔ P`
    -- and applying reflexivity. So `apply Iff.rfl` is redundant.


  subprob_ineq_pq_clear_den :≡ ineq_pq_form ↔ 2 * p_val^3 ≥ 9 * (p_val^2 - q_val)
  subprob_ineq_pq_clear_den_proof ⇐ show subprob_ineq_pq_clear_den by







    -- The goal is to prove the equivalence:
    -- (p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)) ↔ (2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val))
    -- where p_val ^ 3 means HPow.hPow p_val (3 : Nat), which is Real.pow p_val 3, same as p_val ^ (3 : ℕ).

    -- First, unfold the definition of ineq_pq_form
    rw [ineq_pq_form_def]

    -- Let D1 = p_val ^ (2 : ℕ) - q_val be the denominator on the left side of the inequality.
    -- Let D2 = (2 : ℝ) be the denominator on the right side of the inequality.
    -- We need to show D1 > 0 and D2 > 0.

    -- Prove D1 > 0 (denominator of LHS fraction)
    have h_denom_pos : p_val ^ (2 : ℕ) - q_val > 0 := by
      -- Substitute S_sum_a_ab for p_val ^ (2 : ℕ) - q_val using the provided hypothesis
      rw [← subprob_S_sum_a_ab_rewrite_pq_proof] -- Now goal is S_sum_a_ab > 0
      -- Use the provided hypothesis that S_sum_a_ab > 0
      exact subprob_S_sum_a_ab_pos_proof

    -- Prove D2 > 0 (denominator of RHS fraction)
    have h_two_pos : (0 : ℝ) < (2 : ℝ) := by
      norm_num -- Proves 0 < 2

    -- The inequality on the LHS of the `↔` is of the form `X₁/Y₁ ≥ X₂/Y₂`.
    -- We use `div_le_div_iff` which states `a/c ≤ b/d ↔ a*d ≤ b*c` given `0 < c` and `0 < d`.
    -- Our goal `(X₁/Y₁ ≥ X₂/Y₂) ↔ (X₁*Y₂ ≥ X₂*Y₁)` is equivalent to `(X₂/Y₂ ≤ X₁/Y₁) ↔ (X₂*Y₁ ≤ X₁*Y₂)`.
    -- Let `X₁ = p_val ^ (3 : ℕ)`, `Y₁ = p_val ^ (2 : ℕ) - q_val`.
    -- Let `X₂ = (9 : ℝ)`, `Y₂ = (2 : ℝ)`.
    -- For `div_le_div_iff hc hd : a/c ≤ b/d ↔ ...`:
    -- `a` corresponds to `X₂ = (9 : ℝ)`.
    -- `c` corresponds to `Y₂ = (2 : ℝ)`. `hc` is `h_two_pos`.
    -- `b` corresponds to `X₁ = p_val ^ (3 : ℕ)`.
    -- `d` corresponds to `Y₁ = p_val ^ (2 : ℕ) - q_val`. `hd` is `h_denom_pos`.
    -- So, `(X₂/Y₂ ≤ X₁/Y₁) ↔ (X₂*Y₁ ≤ X₁*Y₂)` is proven by `div_le_div_iff h_two_pos h_denom_pos`.

    have h_div_iff : (p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)) ↔
                     (p_val ^ (3 : ℕ) * (2 : ℝ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)) := by
      -- Apply `div_le_div_iff`. The unification process maps variables as described above.
      -- Note: `div_le_div_iff` expects `a/c ≤ b/d`. Our inequality is `LHS ≥ RHS`, which is `RHS ≤ LHS`.
      -- So, `a` will be `(9 : ℝ)`, `c` will be `(2 : ℝ)`, `b` will be `p_val ^ (3 : ℕ)`, and `d` will be `(p_val ^ (2 : ℕ) - q_val)`.
      apply div_le_div_iff
      -- The first goal is `0 < c`, where `c` is unified with `(2:ℝ)`. This is `h_two_pos`.
      . exact h_two_pos
      -- The second goal is `0 < d`, where `d` is unified with `(p_val ^ (2:ℕ) - q_val)`. This is `h_denom_pos`.
      . exact h_denom_pos

    -- Now we rewrite using this specific, proven equivalence.
    rw [h_div_iff]

    -- Now the goal is:
    -- (p_val ^ (3 : ℕ) * (2 : ℝ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)) ↔ (2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val))
    -- To make the expressions match, commute multiplication on the left side of the inequality on the left side of the equivalence.
    -- p_val ^ (3 : ℕ) * (2 : ℝ)  becomes (2 : ℝ) * p_val ^ (3 : ℕ)
    -- Note: p_val ^ 3 in the problem statement means p_val ^ (3 : ℕ).
    rw [mul_comm (p_val ^ (3 : ℕ)) (2 : ℝ)]

    -- Now the goal is of the form `P ↔ P` because `p_val ^ (k : ℕ)` and `p_val ^ k` (for literal `k`)
    -- are definitionally equal for `p_val : ℝ`.
    -- Specifically, the goal is:
    -- ((2 : ℝ) * p_val ^ (3 : ℕ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)) ↔ ((2 : ℝ) * p_val ^ 3 ≥ (9 : ℝ) * (p_val ^ 2 - q_val))
    -- The `rfl` tactic correctly closes this goal.
    -- The previous `rw` tactic simplified the goal to the form `P ↔ P` where both sides are syntactically identical (considering definitional equalities like `x ^ (n : ℕ)` vs `x ^ n`).
    -- Such goals are closed by reflexivity, which `rw` tries automatically. Thus, the `exact Iff.rfl` line was redundant and has been removed.


  ineq_rearranged := 2 * p_val^3 + 9 * q_val ≥ 9 * p_val^2
  subprob_ineq_rearranged_equiv :≡ (2 * p_val^3 ≥ 9 * (p_val^2 - q_val)) ↔ ineq_rearranged
  subprob_ineq_rearranged_equiv_proof ⇐ show subprob_ineq_rearranged_equiv by




    -- The goal is to prove the equivalence:
    -- (2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val)) ↔ ineq_rearranged
    -- where ineq_rearranged is defined as (2 * p_val ^ 3 + 9 * q_val ≥ 9 * p_val ^ 2).

    -- Substitute the definition of ineq_rearranged into the goal.
    rw [ineq_rearranged_def]
    -- The goal becomes:
    -- (2 * p_val ^ 3 ≥ 9 * (p_val ^ 2 - q_val)) ↔ (2 * p_val ^ (3 : ℕ) + 9 * q_val ≥ 9 * p_val ^ (2 : ℕ))

    -- We need to ensure that the powers and coefficients are treated consistently.
    -- `p_val : ℝ`.
    -- `p_val ^ 3` is notation for `HPow.hPow p_val 3`, where `3` is a `Nat` literal.
    -- `p_val ^ (3 : ℕ)` is `HPow.hPow p_val (3 : ℕ)`. These are definitionally equal.
    -- Similarly for `p_val ^ 2` and `p_val ^ (2 : ℕ)`.
    -- Numerals like `2` in `2 * p_val ^ 3` are interpreted as `(2 : ℝ)` by type inference.
    -- So, the expressions on both sides of the equivalence use the same underlying terms.

    -- Distribute the multiplication by 9 on the left-hand side of the equivalence.
    -- `9 * (p_val ^ 2 - q_val)` becomes `9 * p_val ^ 2 - 9 * q_val`.
    have h_distrib : 9 * (p_val ^ 2 - q_val) = 9 * p_val ^ 2 - 9 * q_val := by
      ring
    rw [h_distrib]
    -- The goal is now:
    -- (2 * p_val ^ 3 ≥ 9 * p_val ^ 2 - 9 * q_val) ↔ (2 * p_val ^ 3 + 9 * q_val ≥ 9 * p_val ^ 2)

    -- This equivalence is of the form (A ≥ B - C) ↔ (A + C ≥ B).
    -- The theorem `ge_sub_comm` (from Lean 3) is not found in Mathlib 4.
    -- The equivalent transformation in Mathlib 4 for `ℝ` (an `OrderedAddCommGroup`)
    -- is captured by `sub_le_iff_le_add`, which states `a - b ≤ c ↔ a ≤ c + b`.
    -- Our goal `(X ≥ Y - Z) ↔ (X + Z ≥ Y)` is equivalent to `(Y - Z ≤ X) ↔ (Y ≤ X + Z)`,
    -- which matches `sub_le_iff_le_add` by setting theorem's `a := Y`, `b := Z`, `c := X`.
    apply sub_le_iff_le_add


  subprob_9q_ge_27 :≡ 9 * q_val ≥ 27
  subprob_9q_ge_27_proof ⇐ show subprob_9q_ge_27 by

    -- The goal is to prove `9 * q_val ≥ 27`.
    -- We are given `q_val_def: q_val = a * b + b * c + c * a`.
    -- Substitute `q_val` in the goal using its definition.
    rw [q_val_def] -- Goal becomes `9 * (a * b + b * c + c * a) ≥ 27`.

    -- We want to show `9 * (a * b + b * c + c * a) ≥ 27`.
    -- This is equivalent to `9 * (a * b + b * c + c * a) ≥ 9 * 3`.
    -- First, state that `27` is indeed `9 * 3`.
    have h_27_eq_9_times_3 : (27 : ℝ) = 9 * 3 := by
      norm_num -- Proves `27 = 9 * 3`.

    -- Rewrite `27` in the goal using this equality.
    -- The original code had `rw [←h_27_eq_9_times_3]`.
    -- `h_27_eq_9_times_3` is `(27 : ℝ) = (9 : ℝ) * (3 : ℝ)`.
    -- `rw [←h]` means rewrite `RHS` to `LHS`. So `rw [←h_27_eq_9_times_3]` would try to rewrite `(9 : ℝ) * (3 : ℝ)` to `(27 : ℝ)`.
    -- This is not what is intended, and the pattern `(9 : ℝ) * (3 : ℝ)` is not in the goal `(9 : ℝ) * (a * b + b * c + c * a) ≥ (27 : ℝ)`.
    -- We want to rewrite `(27 : ℝ)` to `(9 : ℝ) * (3 : ℝ)`, which is a forward rewrite.
    -- So, we should use `rw [h_27_eq_9_times_3]`.
    rw [h_27_eq_9_times_3] -- Goal becomes `9 * (a * b + b * c + c * a) ≥ 9 * 3`.

    -- The goal is now `9 * (a * b + b * c + c * a) ≥ 9 * 3`.
    -- This is equivalent to `9 * 3 ≤ 9 * (a * b + b * c + c * a)`.
    -- We can use the theorem `mul_le_mul_left` which states for `0 < c`:
    -- `c * a ≤ c * b ↔ a ≤ b`.
    -- We will use the `.mpr` direction: `a ≤ b → c * a ≤ c * b`.
    -- Here, `c` is `9`, `a` (in the theorem) is `3`, and `b` (in the theorem) is `a * b + b * c + c * a`.
    -- So we need to show `0 < 9`.

    -- First, prove `0 < 9`.
    have nine_pos : (0 : ℝ) < 9 := by
      norm_num -- Proves `0 < 9`.

    -- Apply `(mul_le_mul_left nine_pos).mpr`.
    -- This changes the goal from `9 * 3 ≤ 9 * (a * b + b * c + c * a)`
    -- to `3 ≤ a * b + b * c + c * a`.
    apply (mul_le_mul_left nine_pos).mpr
    -- The new goal is `3 ≤ a * b + b * c + c * a`.

    -- This is exactly the hypothesis `h₁`.
    exact h₁

  subprob_use_hypothesis_h1 :≡ 2 * p_val^3 + 9 * q_val ≥ 2 * p_val^3 + 27
  subprob_use_hypothesis_h1_proof ⇐ show subprob_use_hypothesis_h1 by
    -- The goal is to prove `2 * p_val ^ (3 : ℕ) + 9 * q_val ≥ 2 * p_val ^ (3 : ℕ) + 27`.
    -- This inequality involves the term `2 * p_val ^ (3 : ℕ)` on both sides.
    -- Such terms can be cancelled in linear arithmetic.
    -- After cancellation, the inequality simplifies to `9 * q_val ≥ 27`.
    -- We are given the hypothesis `subprob_9q_ge_27_proof : (9 : ℝ) * q_val ≥ (27 : ℝ)`.
    -- This hypothesis directly matches the simplified inequality.
    -- The `linarith` tactic is designed to solve linear arithmetic problems.
    -- It can perform the necessary simplification (cancellation) and then use the provided hypothesis
    -- `subprob_9q_ge_27_proof` to close the goal.
    linarith [subprob_9q_ge_27_proof]

  subprob_p_val_cubed_pos :≡ p_val^3 > 0
  subprob_p_val_cubed_pos_proof ⇐ show subprob_p_val_cubed_pos by
    -- The goal is to prove p_val ^ 3 > 0.
    -- We are given p_val_def: p_val = Sa.
    -- We are also given subprob_Sa_pos_proof: Sa > 0.

    -- First, substitute p_val with Sa using p_val_def.
    rw [p_val_def] -- Goal becomes Sa ^ 3 > 0

    -- We need to show Sa ^ 3 > 0.
    -- We know Sa > 0 from subprob_Sa_pos_proof.
    -- If a real number x is positive, then x^n is positive for any natural number n.
    -- Here, Sa is a real number, and 3 is a natural number.
    -- We can use the theorem `pow_pos` which states: `∀ {x : ℝ} (h : 0 < x) (n : ℕ), 0 < x ^ n`.
    apply pow_pos
    -- This creates a new goal: 0 < Sa.
    -- This is exactly what subprob_Sa_pos_proof states.
    exact subprob_Sa_pos_proof

  subprob_amgm_rhs_eval :≡ Real.rpow (p_val^3 * p_val^3 * 27) (1/3) = 3 * p_val^2
  subprob_amgm_rhs_eval_proof ⇐ show subprob_amgm_rhs_eval by


















    -- Assumptions on p_val based on `subprob_p_val_cubed_pos_proof`.
    -- From `p_val ^ (3 : ℕ) > 0` and `3` being odd, we deduce `p_val > 0`.
    have h_p_val_pos : p_val > 0 := by
      apply (Odd.pow_pos_iff (by decide : Odd 3)).mp
      exact subprob_p_val_cubed_pos_proof
    have h_p_val_nonneg : p_val ≥ 0 := le_of_lt h_p_val_pos

    -- Rewrite the expression step-by-step.
    -- Step 1: Combine `p_val ^ 3 * p_val ^ 3` to `p_val ^ 6`.
    -- The notation `p_val ^ 3` means `p_val ^ (3 : ℕ)`, which is `pow p_val 3`.
    have h_pow_combo : p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) = p_val ^ (6 : ℕ) := by
      rw [← pow_add p_val 3 3] -- `x^a * x^b = x^(a+b)`
    rw [h_pow_combo] -- Goal: `Real.rpow (p_val ^ 6 * 27) (1 / 3) = 3 * p_val ^ 2`

    -- Step 2: Rewrite `27` as `(3 : ℝ) ^ 3`.
    have h_27_is_3_cubed : (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [h_27_is_3_cubed] -- Goal: `Real.rpow (p_val ^ 6 * (3 : ℝ) ^ 3) (1 / 3) = 3 * p_val ^ 2`

    -- Step 3: Apply `Real.mul_rpow` which states `(x * y) ^ z = x ^ z * y ^ z` if `x, y ≥ 0`.
    -- We need to show `p_val ^ 6 ≥ 0` and `(3 : ℝ) ^ 3 ≥ 0`.
    have h_pval6_nonneg : p_val ^ (6 : ℕ) ≥ 0 := by
      apply pow_nonneg h_p_val_nonneg -- `x ≥ 0 → x^n ≥ 0`
    have h_3_cubed_nonneg : (3 : ℝ) ^ (3 : ℕ) ≥ 0 := by
      apply pow_nonneg
      norm_num -- proves `3 ≥ 0`

    -- Define a helper lemma that states Real.mul_rpow with Real.rpow explicit
    have my_mul_rpow (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      Real.rpow (x * y) z = Real.rpow x z * Real.rpow y z := Real.mul_rpow hx hy

    -- Instantiate this lemma with the specific terms.
    -- `p_val ^ (6 : ℕ)` is `pow p_val 6`. `(3 : ℝ) ^ (3 : ℕ)` is `pow (3 : ℝ) 3`.
    have actual_lemma_to_apply := my_mul_rpow (p_val ^ (6 : ℕ)) ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) h_pval6_nonneg h_3_cubed_nonneg

    rw [actual_lemma_to_apply]
    -- Goal: `Real.rpow (p_val ^ 6) (1 / 3) * Real.rpow ((3 : ℝ) ^ 3) (1 / 3) = 3 * p_val ^ 2`

    -- Step 4: Simplify `Real.rpow (p_val ^ 6) (1 / 3)`.
    -- Use `Real.rpow_pow_nat (x : ℝ) (n : ℕ) (z : ℝ) (hx : 0 ≤ x ∨ Even n) → Real.rpow (x ^ n) z = Real.rpow x (↑n * z)`.
    -- Here `x` is `p_val`, `n` is `6`, `z` is `1/3`.
    -- The condition `0 ≤ x ∨ Even n` is satisfied by `Or.inl h_p_val_nonneg` (since `0 ≤ p_val`).
    have h_term1_simplify : Real.rpow (p_val ^ (6 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = p_val ^ (2 : ℕ) := by
      -- The `rw` tactic failed with "equality or iff proof expected" when directly using the instantiated `Real.rpow_pow_nat` theorem with named arguments.
      -- This error can occur if the rewrite system has difficulty elaborating the complex term `Real.rpow_pow_nat (...)` directly within the `rw [...]` syntax.
      -- To address this, we first explicitly prove the equality as a hypothesis `rpp_eq` using `have` command.
      -- Then, `rw [rpp_eq]` is used, which is a simpler form for the tactic to process.
      have rpp_eq : Real.rpow (p_val ^ (6 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = Real.rpow p_val (↑(6 : ℕ) * ((1 : ℝ) / (3 : ℝ))) := by
        -- The theorem `Real.pow_eq_rpow_natCast` is not a standard Mathlib theorem.
        -- The intended transformation is to rewrite `x ^ n` (type `Pow.pow x n`) to `Real.rpow x (n : ℝ)`.
        -- The standard theorem `Real.rpow_natCast x n` states `Real.rpow x (n : ℝ) = x ^ n`.
        -- Therefore, we use `rw [← Real.rpow_natCast p_val 6]` to rewrite `p_val ^ 6` in the goal.
        -- This changes `Real.rpow (p_val ^ 6) (1/3)` to `Real.rpow (Real.rpow p_val (↑6)) (1/3)`,
        -- which then allows `Real.rpow_mul` to be applied.
        rw [← Real.rpow_natCast p_val 6]
        exact Eq.symm (Real.rpow_mul h_p_val_nonneg (Nat.cast 6) ((1 : ℝ) / (3 : ℝ)))
      rw [rpp_eq]
      have h_exponent_val : (↑(6 : ℕ) : ℝ) * (1 / 3) = 2 := by norm_num
      rw [h_exponent_val]
      -- `Real.rpow x 2` should be `pow x 2` (i.e. `x ^ (2 : ℕ)`)
      -- `Real.rpow_natCast x n` (alias for `Real.rpow_ofNat`) states `Real.rpow x (Nat.cast n) = pow x n`.
      -- The `rw` tactic failed because `(2 : ℝ)` in the goal `Real.rpow p_val (2 : ℝ)` is not syntactically identical to `(↑(2 : ℕ) : ℝ)`
      -- which is the form in the theorem `Real.rpow_natCast p_val 2` (specifically, its LHS is `Real.rpow p_val (↑(2 : ℕ))`).
      -- While `(2 : ℝ)` and `(↑(2 : ℕ) : ℝ)` are definitionally equal, `rw` sometimes requires syntactic identity for patterns.
      -- Using `simp only [Real.rpow_natCast]` is more robust as `simp` can handle definitional equalities during matching.
      -- It successfully applies the theorem `Real.rpow_natCast x n : Real.rpow x (↑n) = x ^ n`
      -- by unifying `x` with `p_val` and `↑n` with `(2 : ℝ)` (implying `n=2`),
      -- rewriting the LHS of the goal to `p_val ^ 2`, which makes the goal `p_val ^ 2 = p_val ^ 2`. This is then closed by `rfl` (implicitly by `simp`).
      -- The line `simp only [Real.rpow_natCast]` made no progress because the goal `Real.rpow p_val (2 : ℝ) = p_val ^ (2 : ℕ)`
      -- is true by definitional equality. `Real.rpow_natCast` itself is an `rfl` theorem.
      -- `simp` does not report progress when applying an `rfl` theorem to a goal already true by `rfl`.
      -- The goal will be closed by an implicit `rfl` at the end of the `by` block.
      -- simp only [Real.rpow_natCast] -- This line is removed.
      -- -- The previous line `simp only [Real.rpow_natCast]` was removed, which caused this subproof to be incomplete.
      -- -- The goal `Real.rpow p_val (2 : ℝ) = p_val ^ (2 : ℕ)` is true by definitional equality (as `Real.rpow_ofNat p_val 2` is an `rfl` theorem).
      -- -- Adding `rfl.` explicitly closes this goal.
      -- The goal is `Real.rpow p_val (2 : ℝ) = p_val ^ (2 : ℕ)`.
      -- This equality is stated by the theorem `Real.rpow_natCast p_val 2`.
      -- `Real.rpow_natCast x n` is defined as `Real.rpow x (↑n) = x ^ n`.
      -- Since `(2 : ℝ)` is definitionally equal to `(↑(2 : ℕ) : ℝ)` (as `OfNat.ofNat 2` for reals is `Nat.cast 2`),
      -- the theorem `Real.rpow_natCast p_val 2` directly proves the goal.
      -- While `Real.rpow_natCast` itself is an `rfl` theorem, using it explicitly with `exact`
      -- can be more robust if a plain `rfl` fails due to subtleties in the definitional equality checker in a complex context.
      exact (Real.rpow_natCast p_val 2)
    rw [h_term1_simplify]
    -- Goal: `p_val ^ 2 * Real.rpow ((3 : ℝ) ^ 3) (1 / 3) = 3 * p_val ^ 2`

    -- Step 5: Simplify `Real.rpow ((3 : ℝ) ^ 3) (1 / 3)`.
    -- Use `Real.rpow_pow_nat` again. Here `x` is `3`, `n` is `3`, `z` is `1/3`.
    -- The condition `0 ≤ x ∨ Even n` is satisfied because `0 ≤ 3` (h_3_nonneg).
    have h_term2_simplify : Real.rpow ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = (3 : ℝ) := by
      have h_3_nonneg : (3 : ℝ) ≥ 0 := by norm_num
      -- Apply Real.rpow_pow_nat, similar to h_term1_simplify.
      -- x := (3 : ℝ), n := (3 : ℕ), z := (1 : ℝ) / (3 : ℝ).
      -- Condition (0 ≤ x ∨ Even n) is met by Or.inl h_3_nonneg.
      -- To address the "equality or iff proof expected" error, we first introduce the equality from Real.rpow_pow_nat as a hypothesis.
      have rpp_instance : Real.rpow ((3 : ℝ) ^ (3 : ℕ)) ((1 : ℝ) / (3 : ℝ)) = Real.rpow (3 : ℝ) (↑(3 : ℕ) * ((1 : ℝ) / (3 : ℝ))) := by
        -- The original `rw [Real.pow_eq_rpow_natCast (3 : ℝ) 3]` failed with "equality or iff proof expected". This error often indicates that the rewrite system had trouble elaborating the provided term into a simple equality `lhs = rhs` that `rw` can directly use, possibly due to complexities with literals or casts.
        -- Using `simp only [Real.pow_eq_rpow_natCast]` is a more robust approach. `simp` employs more powerful matching algorithms that can better handle definitional equalities and type coercions. It will search for occurrences of `x ^ n` (where `x` is a real number and `n` is a natural number) in the goal and replace them with `Real.rpow x (↑n)` according to the theorem `Real.pow_eq_rpow_natCast`.
        -- In this specific context, `(3 : ℝ) ^ (3 : ℕ)` on the left-hand side of the equality to be proven is transformed into `Real.rpow (3 : ℝ) (↑(3 : ℕ))`. The subsequent `exact Real.rpow_mul ...` then applies, as the goal's structure matches what `Real.rpow_mul` proves.
        -- The line `simp only [Real.pow_eq_rpow_natCast]` made no progress because `(3 : ℝ) ^ (3 : ℕ)` is definitionally `Real.rpow (3 : ℝ) (↑(3 : ℕ))`.
        -- So, the lemma `Real.pow_eq_rpow_natCast` is essentially `A = A` in this context, and `simp` does not apply it.
        -- The line is therefore redundant and can be removed.
        -- The term `Real.rpow_mul h_3_nonneg (Nat.cast 3) ((1 : ℝ) / (3 : ℝ))` proves `Real.rpow (3:ℝ) (↑3 * (1/3)) = Real.rpow (Real.rpow (3:ℝ) (↑3)) (1/3)`.
        -- The goal is `Real.rpow (Real.rpow (3:ℝ) (↑3)) (1/3) = Real.rpow (3:ℝ) (↑3 * (1/3))`.
        -- So we need to use `Eq.symm`.
        rw [← Real.rpow_natCast (3 : ℝ) 3]
        exact Eq.symm (Real.rpow_mul h_3_nonneg (Nat.cast 3) ((1 : ℝ) / (3 : ℝ)))
      rw [rpp_instance]
      -- Goal is now: Real.rpow (3 : ℝ) (↑(3 : ℕ) * (1 / 3)) = (3 : ℝ)
      -- Simplify the exponent.
      have h_exponent_val_3 : (↑(3 : ℕ) : ℝ) * ((1 : ℝ) / (3 : ℝ)) = (1 : ℝ) := by
        norm_num -- This proves (3 : ℝ) * (1/3) = 1
      rw [h_exponent_val_3]
      -- Goal is now: Real.rpow (3 : ℝ) 1 = (3 : ℝ)
      -- The original `rw [Real.rpow_one]` failed with a "did not find instance of the pattern" error.
      -- This suggests `rw` struggled to match `Real.rpow (3 : ℝ) (1 : ℝ)` in the goal with the pattern `?x ^ (1 : ℝ)` from `Real.rpow_one`.
      -- `apply Real.rpow_one` is a more direct way to use the theorem. It matches the conclusion of `Real.rpow_one` (which is `?x ^ (1 : ℝ) = ?x`)
      -- with the goal `Real.rpow (3 : ℝ) (1 : ℝ) = (3 : ℝ)`. Lean successfully unifies `?x` with `(3 : ℝ)` and proves the goal.
      apply Real.rpow_one
    rw [h_term2_simplify]
    -- Goal: `p_val ^ 2 * (3 : ℝ) = 3 * p_val ^ 2`

    -- Step 6: Commute multiplication.
    rw [mul_comm] -- `x * y = y * x`
    -- Goal: `(3 : ℝ) * p_val ^ 2 = (3 : ℝ) * p_val ^ 2`, which is true by `rfl`.





















  subprob_amgm_apply :≡ (p_val^3 + p_val^3 + 27) / 3 ≥ Real.rpow (p_val^3 * p_val^3 * 27) (1/3)
  subprob_amgm_apply_proof ⇐ show subprob_amgm_apply by








    -- The goal is to prove the AM-GM inequality for three terms:
    -- x₁ = p_val ^ 3 (which is p_val ^ (3 : ℕ) as p_val : ℝ)
    -- x₂ = p_val ^ 3 (similarly, p_val ^ (3 : ℕ))
    -- x₃ = 27
    -- The inequality is (x₁ + x₂ + x₃) / 3 ≥ (x₁ * x₂ * x₃)^(1/3).
    -- We will use the Mathlib theorem `Real.geom_mean_le_arith_mean3_weighted`.
    -- `Real.geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) : p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃`

    -- First, we need to show that the terms are non-negative.
    -- For p_val ^ 3 (which is p_val ^ (3 : ℕ)):
    have h_p_val_cubed_nonneg : 0 ≤ p_val ^ (3 : ℕ) := by
      -- We are given `subprob_p_val_cubed_pos_proof : p_val ^ (3 : ℕ) > 0`.
      -- If a number is strictly positive, it is also non-negative.
      -- `p_val ^ 3` in the goal is interpreted as `p_val ^ (3 : ℕ)`.
      exact le_of_lt subprob_p_val_cubed_pos_proof

    -- For 27:
    have h_27_nonneg : 0 ≤ (27 : ℝ) := by
      -- 27 is a positive constant, so it's non-negative.
      norm_num -- This tactic proves `0 ≤ 27`.
      -- Alternative: `apply le_of_lt`, `norm_num` (proves `0 < 27`).

    -- Now, apply the AM-GM inequality theorem.
    -- Let `term1 := p_val ^ 3`, `term2 := p_val ^ 3`, `term3 := (27 : ℝ)`.
    -- Note that `p_val ^ 3` is `p_val ^ (3 : ℕ)` since `p_val : ℝ`.
    -- We have `h_p_val_cubed_nonneg : 0 ≤ p_val ^ (3 : ℕ)`, and `h_27_nonneg : 0 ≤ (27 : ℝ)`.
    have am_gm_ineq : Real.rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * (27 : ℝ)) ((1 : ℝ) / (3 : ℝ))
                      ≤ (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) := by
      -- Define the terms and weights for the weighted AM-GM inequality.
      let p₁ := p_val ^ (3 : ℕ)
      let p₂ := p_val ^ (3 : ℕ)
      let p₃ := (27 : ℝ)
      let w : ℝ := (1:ℝ) / 3

      -- Prove necessary conditions for weights.
      have hw_nonneg : 0 ≤ w := by norm_num
      have hw_sum_eq_1 : w + w + w = 1 := by norm_num

      -- Apply Real.geom_mean_le_arith_mean3_weighted.
      -- This theorem states: p₁^w * p₂^w * p₃^w ≤ w*p₁ + w*p₂ + w*p₃
      -- (assuming w₁=w₂=w₃=w and appropriate non-negativity and sum conditions).
      have H := Real.geom_mean_le_arith_mean3_weighted
                  hw_nonneg hw_nonneg hw_nonneg  -- For 0 ≤ w₁, 0 ≤ w₂, 0 ≤ w₃
                  h_p_val_cubed_nonneg h_p_val_cubed_nonneg h_27_nonneg -- For 0 ≤ p₁, 0 ≤ p₂, 0 ≤ p₃
                  hw_sum_eq_1 -- For w₁ + w₂ + w₃ = 1

      -- H is p₁^w * p₂^w * p₃^w ≤ w*p₁ + w*p₂ + w*p₃
      -- We need to transform H into the form (p₁*p₂*p₃)^w ≤ (p₁+p₂+p₃)/3.

      -- Transform the LHS of H: p₁^w * p₂^w * p₃^w  to  (p₁*p₂*p₃)^w
      -- The expression p₁^w * p₂^w * p₃^w is parsed as (p₁^w * p₂^w) * p₃^w.
      -- First, group (p₁^w * p₂^w) into (p₁*p₂)^w using ←Real.mul_rpow.
      -- The non-negativity proofs for p₁ and p₂ are h_p_val_cubed_nonneg.
      rw [← Real.mul_rpow h_p_val_cubed_nonneg h_p_val_cubed_nonneg] at H
      -- Now the LHS of H is ((p_val ^ (3 : ℕ)) * (p_val ^ (3 : ℕ)))^w * (27 : ℝ)^w.
      -- Next, group this into (((p_val ^ (3 : ℕ)) * (p_val ^ (3 : ℕ))) * (27 : ℝ))^w.
      -- The non-negativity proof for ((p_val ^ (3 : ℕ)) * (p_val ^ (3 : ℕ))) is (mul_nonneg h_p_val_cubed_nonneg h_p_val_cubed_nonneg).
      -- The non-negativity proof for (27 : ℝ) is h_27_nonneg.
      rw [← Real.mul_rpow (mul_nonneg h_p_val_cubed_nonneg h_p_val_cubed_nonneg) h_27_nonneg] at H
      -- Now H is (p₁*p₂*p₃)^w ≤ w*p₁ + w*p₂ + w*p₃ (associativity of * makes ((p₁*p₂) * p₃) equal to (p₁*p₂*p₃)).

      -- Substitute w = 1/3 into H.
      -- `w` is already defined as `(1:ℝ)/3`. The variables `p₁, p₂, p₃` are also defined.
      -- So H is already in the form (p₁*p₂*p₃)^((1:ℝ)/(3:ℝ)) ≤ ((1:ℝ)/(3:ℝ))*p₁ + ((1:ℝ)/(3:ℝ))*p₂ + ((1:ℝ)/(3:ℝ))*p₃.
      -- The `simp only [w, Real.one_div] at H` in the original code might have been intended to ensure `w` is fully substituted
      -- or to normalize its form, but it should not be strictly necessary here if `w` is a `let` binding that has already been substituted.
      -- We will proceed assuming H is already in the desired form with (1:ℝ)/(3:ℝ).

      -- Transform the RHS of H: (1/3)*p₁ + (1/3)*p₂ + (1/3)*p₃  to  (p₁+p₂+p₃)/3
      -- The previous proof for this step had an issue. Using `ring` is more robust for this kind of algebraic identity.
      rw [show ((1:ℝ)/(3:ℝ))*p₁ + ((1:ℝ)/(3:ℝ))*p₂ + ((1:ℝ)/(3:ℝ))*p₃ = (p₁ + p₂ + p₃) / (3:ℝ) by ring] at H
      -- Now H is (p₁*p₂*p₃)^(1/3) ≤ (p₁+p₂+p₃)/3, which is the desired inequality.
      exact H

    -- `am_gm_ineq` is `Real.rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * 27) (1 / 3) ≤ (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + 27) / 3`.
    -- This is equivalent to the goal: `(p_val ^ 3 + p_val ^ 3 + 27) / 3 ≥ Real.rpow (p_val ^ 3 * p_val ^ 3 * 27) (1 / 3)`.
    -- `p_val ^ 3` in the goal is `p_val ^ (3 : ℕ)`.
    -- The `exact am_gm_ineq` will close the goal because `a ≤ b` is the same proposition as `b ≥ a`.
    exact am_gm_ineq

  subprob_amgm_implies_ineq :≡ 2 * p_val^3 + 27 ≥ 9 * p_val^2
  subprob_amgm_implies_ineq_proof ⇐ show subprob_amgm_implies_ineq by






    -- The goal is `2 * p_val ^ 3 + 27 ≥ 9 * p_val ^ 2`.
    -- Note that `p_val ^ 3` is `p_val ^ (3 : ℕ)` and `p_val ^ 2` is `p_val ^ (2 : ℕ)`.
    -- We are given:
    -- `subprob_amgm_apply_proof : (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * (27 : ℝ)) ((1 : ℝ) / (3 : ℝ))`
    -- `subprob_amgm_rhs_eval_proof : rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * (27 : ℝ)) ((1 : ℝ) / (3 : ℝ)) = (3 : ℝ) * p_val ^ (2 : ℕ)`

    -- Step 1: Combine the given AM-GM results to get a simpler inequality.
    -- The LHS of `subprob_amgm_apply_proof` can be simplified:
    -- `(p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) = (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ)`
    -- The RHS of `subprob_amgm_apply_proof` is given by `subprob_amgm_rhs_eval_proof`.
    -- So, `subprob_amgm_apply_proof` implies `(2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ (3 : ℝ) * p_val ^ (2 : ℕ)`.
    have h_amgm_combined : (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ (3 : ℝ) * p_val ^ (2 : ℕ) := by
      -- Create a helper for the LHS simplification to use with `rw`.
      have h_lhs_rewrite : (p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) = (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) := by
        ring
      -- Rewrite the goal using `←h_lhs_rewrite` and `←subprob_amgm_rhs_eval_proof`.
      -- `←h_lhs_rewrite` changes the LHS of the goal: `(2 * p_val³ + 27)/3` becomes `(p_val³ + p_val³ + 27)/3`.
      -- `←subprob_amgm_rhs_eval_proof` changes the RHS of the goal: `3 * p_val²` becomes `rpow (p_val³ * p_val³ * 27) (1/3)`.
      -- The goal then becomes `(p_val ^ (3 : ℕ) + p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) >= rpow (p_val ^ (3 : ℕ) * p_val ^ (3 : ℕ) * (27 : ℝ)) ((1 : ℝ) / (3 : ℝ))`,
      -- which is exactly `subprob_amgm_apply_proof`.
      rw [←h_lhs_rewrite, ←subprob_amgm_rhs_eval_proof]
      exact subprob_amgm_apply_proof

    -- Step 2: Multiply both sides of `h_amgm_combined` by 3.
    -- We have `(2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ (3 : ℝ) * p_val ^ (2 : ℕ)`.
    -- We need to show `2 * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ (9 : ℝ) * p_val ^ (2 : ℕ)`.
    -- Since `3 > 0`, we can multiply both sides by `3` preserving the inequality:
    -- `2 * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ ((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ)`.
    have h_three_pos : (0 : ℝ) < 3 := by norm_num

    have h_multiplied : 2 * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ ((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ) := by
      -- The previous line `rw [← le_div_iff_mul_le h_three_pos]` caused an error "tactic 'rewrite' failed, equality or iff proof expected".
      -- This indicates that `le_div_iff_mul_le h_three_pos` was not recognized as a valid `iff` statement for rewriting.
      -- The theorem `le_div_iff_mul_le` is generic (for `Group α`). For `ℝ` (a `LinearOrderedField`),
      -- the specific theorem is `le_div_iff` from `Mathlib.Algebra.Order.Field.Defs`.
      -- This theorem is `∀ {K} [LinearOrderedField K] {a b c : K} (hc : 0 < c), a ≤ b / c ↔ a * c ≤ b`.
      -- Let `Y = (3 : ℝ) * p_val ^ (2 : ℕ)`, `X = (2 * p_val ^ (3 : ℕ) + (27 : ℝ))`, `C = (3 : ℝ)`.
      -- The goal is `X ≥ Y * C`, which is `Y * C ≤ X`.
      -- `h_amgm_combined` is `X / C ≥ Y`, which is `Y ≤ X / C`.
      -- `h_three_pos` is `0 < C`.
      -- `(le_div_iff h_three_pos)` provides `Y ≤ X / C ↔ Y * C ≤ X`.
      -- We apply the forward direction (`.mp`) of this `iff`: `(Y ≤ X / C) → (Y * C ≤ X)`.
      -- This changes the goal `Y * C ≤ X` to `Y ≤ X / C`.
      apply (le_div_iff h_three_pos).mp
      -- The new goal is `(3 : ℝ) * p_val ^ (2 : ℕ) ≤ (2 * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ)`.
      -- `h_amgm_combined` is `((2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ)) / (3 : ℝ) ≥ (3 : ℝ) * p_val ^ (2 : ℕ)`,
      -- which is definitionally equivalent to the new goal.
      exact h_amgm_combined

    -- Step 3: Simplify the right-hand side of `h_multiplied`.
    -- `((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ) = (9 : ℝ) * p_val ^ (2 : ℕ)`.
    have h_rhs_simplified : ((3 : ℝ) * p_val ^ (2 : ℕ)) * (3 : ℝ) = (9 : ℝ) * p_val ^ (2 : ℕ) := by
      ring
    rw [h_rhs_simplified] at h_multiplied

    -- `h_multiplied` is now `2 * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ (9 : ℝ) * p_val ^ (2 : ℕ)`, which is the goal.
    exact h_multiplied

  subprob_ineq_rearranged_is_true :≡ ineq_rearranged
  subprob_ineq_rearranged_is_true_proof ⇐ show subprob_ineq_rearranged_is_true by
    -- The goal is to prove ineq_rearranged.
    -- By definition, ineq_rearranged is:
    -- (2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (9 : ℝ) * p_val ^ (2 : ℕ)
    rw [ineq_rearranged_def]

    -- We are given subprob_use_hypothesis_h1_proof:
    -- (2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ)
    -- Let's denote the left side of our goal as LHS and the right side of this hypothesis as MID.
    -- So, LHS ≥ MID.
    have h_lhs_ge_mid : (2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ) := by
      exact subprob_use_hypothesis_h1_proof

    -- We are also given subprob_amgm_implies_ineq_proof:
    -- (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ (9 : ℝ) * p_val ^ (2 : ℕ)
    -- This is MID ≥ RHS, where RHS is the right side of our goal.
    have h_mid_ge_rhs : (2 : ℝ) * p_val ^ (3 : ℕ) + (27 : ℝ) ≥ (9 : ℝ) * p_val ^ (2 : ℕ) := by
      exact subprob_amgm_implies_ineq_proof

    -- By transitivity of the "greater than or equal to" relation (≥):
    -- If LHS ≥ MID and MID ≥ RHS, then LHS ≥ RHS.
    -- This is precisely what we want to prove.
    exact ge_trans h_lhs_ge_mid h_mid_ge_rhs

  subprob_final_goal :≡ 3 / Real.sqrt 2 ≤ S1
  subprob_final_goal_proof ⇐ show subprob_final_goal by

    -- The main goal is `3 / Real.sqrt 2 ≤ S1`.
    -- This is equivalent to `S1 ≥ 3 / Real.sqrt 2`.
    -- We are given `subprob_suffices_step_proof: target_ineq → S1 ≥ (3 : ℝ) / √(2 : ℝ)`.
    -- Thus, if we prove `target_ineq`, the main goal follows.
    apply subprob_suffices_step_proof

    -- Current goal: `target_ineq`.
    -- We are given `subprob_target_equiv_sq_proof: target_ineq ↔ Sa ^ (3 : ℕ) / S_sum_a_ab ≥ ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ)`.
    -- To prove `target_ineq` (LHS of iff), we can prove the RHS and use the `.mpr` direction of the equivalence.
    apply subprob_target_equiv_sq_proof.mpr

    -- Current goal: `Sa ^ (3 : ℕ) / S_sum_a_ab ≥ ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ)`.
    -- We have `subprob_rhs_sq_eval_proof: ((3 : ℝ) / √(2 : ℝ)) ^ (2 : ℕ) = (9 : ℝ) / (2 : ℝ)`.
    -- We rewrite the RHS of the goal using this proof.
    rw [subprob_rhs_sq_eval_proof]

    -- Current goal: `Sa ^ (3 : ℕ) / S_sum_a_ab ≥ (9 : ℝ) / (2 : ℝ)`.
    -- This is, by definition `reduced_target_ineq_def`, the proposition `reduced_target_ineq`.
    -- `rw [subprob_reduced_target_equiv_pq_form_proof]` would fail here because the goal is not syntactically `reduced_target_ineq`.
    -- We first rewrite the goal to be `reduced_target_ineq` using its definition `reduced_target_ineq_def`.
    rw [← reduced_target_ineq_def]
    -- Now the goal is syntactically `reduced_target_ineq`.
    -- We are given `subprob_reduced_target_equiv_pq_form_proof: reduced_target_ineq ↔ ineq_pq_form`.
    -- `rw [subprob_reduced_target_equiv_pq_form_proof]` changes the goal from `reduced_target_ineq` to `ineq_pq_form`.
    rw [subprob_reduced_target_equiv_pq_form_proof]

    -- Current goal: `ineq_pq_form`.
    -- (Defined as `p_val ^ (3 : ℕ) / (p_val ^ (2 : ℕ) - q_val) ≥ (9 : ℝ) / (2 : ℝ)`)
    -- We are given `subprob_ineq_pq_clear_den_proof: ineq_pq_form ↔ (2 : ℝ) * p_val ^ (3 : ℕ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)`.
    -- Since the current goal is `ineq_pq_form` (LHS of iff),
    -- `rw [subprob_ineq_pq_clear_den_proof]` changes the goal to the RHS of the equivalence.
    rw [subprob_ineq_pq_clear_den_proof]

    -- Current goal: `(2 : ℝ) * p_val ^ (3 : ℕ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val)`.
    -- We are given `subprob_ineq_rearranged_equiv_proof: (2 : ℝ) * p_val ^ (3 : ℕ) ≥ (9 : ℝ) * (p_val ^ (2 : ℕ) - q_val) ↔ ineq_rearranged`.
    -- Since the current goal is the LHS of this equivalence,
    -- `rw [subprob_ineq_rearranged_equiv_proof]` changes the goal to `ineq_rearranged`.
    rw [subprob_ineq_rearranged_equiv_proof]

    -- Current goal: `ineq_rearranged`.
    -- (Defined as `(2 : ℝ) * p_val ^ (3 : ℕ) + (9 : ℝ) * q_val ≥ (9 : ℝ) * p_val ^ (2 : ℕ)`)
    -- We are given `subprob_ineq_rearranged_is_true_proof`, which is a proof of `ineq_rearranged`.
    exact subprob_ineq_rearranged_is_true_proof

-/
