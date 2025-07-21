import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem amc12a_2020_p15
  (a b : ℂ)
  (h₀ : a^3 - 8 = 0)
  (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0) :
  Complex.abs (a - b) ≤ 2 * Real.sqrt 21 := by
  letI target_bound_val := (2 : ℝ) * Real.sqrt (21 : ℝ)
  retro' target_bound_val_def : target_bound_val = (2 : ℝ) * √(21 : ℝ) := by funext; rfl
  letI D_max_sq_val := (84 : ℝ)
  have subprob_target_bound_ge_0_proof : target_bound_val ≥ (0 : ℝ) := by
    mkOpaque
    have h₀ : (0 : ℝ) ≤ √(21 : ℝ) := Real.sqrt_nonneg _
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  retro' D_max_sq_val_def : D_max_sq_val = (84 : ℝ) := by funext; rfl
  have subprob_target_bound_sq_is_84_proof : target_bound_val ^ 2 = D_max_sq_val := by
    mkOpaque
    rw [target_bound_val_def, D_max_sq_val_def]
    ring_nf <;> norm_num <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  have subprob_target_equiv_normSq_proof : (Complex.abs (a - b) ≤ target_bound_val) ↔ (Complex.normSq (a - b) ≤ D_max_sq_val) := by
    mkOpaque
    rw [Complex.abs]
    dsimp
    rw [Real.sqrt_le_iff]
    simp [subprob_target_bound_ge_0_proof]
    rw [← subprob_target_bound_sq_is_84_proof]
  letI sqrt3_real := Real.sqrt (3 : ℝ)
  letI sqrt2_real := Real.sqrt (2 : ℝ)
  letI a_1_val := Complex.mk (2 : ℝ) (0 : ℝ)
  retro' a_1_val_def : a_1_val = { re := (2 : ℝ), im := (0 : ℝ) : ℂ } := by funext; rfl
  letI a_2_val := Complex.mk (-1 : ℝ) sqrt3_real
  retro' a_2_val_def : a_2_val = { re := -(1 : ℝ), im := sqrt3_real : ℂ } := by funext; rfl
  letI a_3_val := Complex.mk (-1 : ℝ) (-sqrt3_real)
  retro' a_3_val_def : a_3_val = { re := -(1 : ℝ), im := -sqrt3_real : ℂ } := by funext; rfl
  letI b_1_val := Complex.mk (8 : ℝ) (0 : ℝ)
  retro' b_1_val_def : b_1_val = { re := (8 : ℝ), im := (0 : ℝ) : ℂ } := by funext; rfl
  letI b_2_val := Complex.mk ((2 : ℝ) * sqrt2_real) (0 : ℝ)
  retro' b_2_val_def : b_2_val = { re := (2 : ℝ) * sqrt2_real, im := (0 : ℝ) : ℂ } := by funext; rfl
  letI b_3_val := Complex.mk (-(2 : ℝ) * sqrt2_real) (0 : ℝ)
  retro' b_3_val_def : b_3_val = { re := -(2 : ℝ) * sqrt2_real, im := (0 : ℝ) : ℂ } := by funext; rfl
  retro' sqrt3_real_def : sqrt3_real = √(3 : ℝ) := by funext; rfl
  retro' sqrt2_real_def : sqrt2_real = √(2 : ℝ) := by funext; rfl
  have subprob_A_poly_factor_proof : ∀ (z : ℂ), z ^ 3 - (8 : ℂ) = (z - a_1_val) * (z ^ 2 + (2 : ℂ) * z + (4 : ℂ)) := by
    mkOpaque
    intro z
    ring_nf <;> simp_all [Complex.ext_iff, pow_two, pow_three, mul_add, mul_comm, mul_left_comm] <;> norm_num <;> linarith [sqrt3_real_def, sqrt2_real_def, a_1_val_def, a_2_val_def, a_3_val_def, b_1_val_def, b_2_val_def, b_3_val_def, D_max_sq_val_def, target_bound_val_def]
  have subprob_A_quadratic_roots_iff_proof : ∀ (z : ℂ), z ^ 2 + (2 : ℂ) * z + (4 : ℂ) = 0 ↔ (z = a_2_val ∨ z = a_3_val) := by
    mkOpaque
    intro z
    have h_sum : a_2_val + a_3_val = (-2 : ℂ) := by
      rw [a_2_val_def, a_3_val_def]
      rw [Complex.ext_iff]
      rw [sqrt3_real_def]
      simp
      norm_num
    have h_prod : a_2_val * a_3_val = (4 : ℂ) := by
      rw [a_2_val_def, a_3_val_def]
      rw [Complex.ext_iff]
      constructor
      . rw [Complex.mul_re]
        rw [sqrt3_real_def]
        simp only [neg_mul_neg, one_mul, mul_neg, neg_neg]
        have h_sqrt3_sq : √(3 : ℝ) * √(3 : ℝ) = 3 := Real.mul_self_sqrt (by norm_num : 0 ≤ (3 : ℝ))
        rw [h_sqrt3_sq]
        norm_num
      . rw [Complex.mul_im]
        rw [sqrt3_real_def]
        simp only [neg_mul_neg, one_mul, mul_neg]
        simp
    have identity : z ^ 2 + (2 : ℂ) * z + (4 : ℂ) = (z - a_2_val) * (z - a_3_val) := by
      have identity_expanded : (z - a_2_val) * (z - a_3_val) = z ^ 2 - (a_2_val + a_3_val) * z + a_2_val * a_3_val := by ring
      rw [identity_expanded]
      rw [h_sum, h_prod]
      ring
    rw [identity]
    apply Iff.intro
    . intro h_prod_zero
      have h_sub_zero_or_sub_zero : z - a_2_val = (0 : ℂ) ∨ z - a_3_val = (0 : ℂ) := _root_.mul_eq_zero.mp h_prod_zero
      rw [sub_eq_zero, sub_eq_zero] at h_sub_zero_or_sub_zero
      exact h_sub_zero_or_sub_zero
    . intro h_or_eq
      rcases h_or_eq with h_eq_a2 | h_eq_a3
      . rw [h_eq_a2]
        rw [sub_self]
        rw [zero_mul]
      . rw [h_eq_a3]
        rw [sub_self]
        rw [mul_zero]
  have subprob_roots_A_iff_proof : ∀ (z : ℂ), z ^ 3 - (8 : ℂ) = 0 ↔ (z = a_1_val ∨ z = a_2_val ∨ z = a_3_val) := by
    mkOpaque
    intro z
    rw [subprob_A_poly_factor_proof]
    rw [show (z - a_1_val) * (z ^ (2 : ℕ) + (2 : ℂ) * z + (4 : ℂ)) = (0 : ℂ) ↔ (z - a_1_val = 0 ∨ z ^ (2 : ℕ) + (2 : ℂ) * z + (4 : ℂ) = (0 : ℂ)) from mul_eq_zero]
    rw [sub_eq_zero]
    rw [subprob_A_quadratic_roots_iff_proof]
  have subprob_B_poly_factor_proof : ∀ (z : ℂ), z ^ 3 - (8 : ℂ) * z ^ 2 - (8 : ℂ) * z + (64 : ℂ) = (z - b_1_val) * (z ^ 2 - (8 : ℂ)) := by
    mkOpaque
    intro z
    ring_nf <;> simp_all [Complex.ext_iff, pow_two, pow_three] <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_B_quadratic_roots_iff_proof : ∀ (z : ℂ), z ^ 2 - (8 : ℂ) = 0 ↔ (z = b_2_val ∨ z = b_3_val) := by
    mkOpaque
    intro z
    have hr_sq : (Complex.ofReal ((2 : ℝ) * sqrt2_real)) ^ 2 = (8 : ℂ) := by
      have h_rewrite_step : (Complex.ofReal ((2 : ℝ) * sqrt2_real)) ^ (2 : ℕ) = Complex.ofReal (((2 : ℝ) * sqrt2_real) ^ (2 : ℕ)) := Eq.symm (Complex.ofReal_pow ((2 : ℝ) * sqrt2_real) (2 : ℕ))
      rw [h_rewrite_step]
      have h_R_val_sq_real : ((2 : ℝ) * sqrt2_real) ^ 2 = 8 := by
        rw [sqrt2_real_def]
        rw [mul_pow]
        have h2sq : (2 : ℝ) ^ 2 = 4 := by norm_num
        rw [h2sq]
        have hsqrt2sq : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
        rw [hsqrt2sq]
        norm_num
      rw [h_R_val_sq_real]
      rfl
    rw [← hr_sq]
    rw [sq_sub_sq z (Complex.ofReal ((2 : ℝ) * sqrt2_real))]
    rw [_root_.mul_eq_zero]
    rw [sub_eq_zero]
    rw [add_eq_zero_iff_eq_neg]
    have hb2_eq : b_2_val = Complex.ofReal ((2 : ℝ) * sqrt2_real) := by
      rw [b_2_val_def]
      rfl
    rw [hb2_eq]
    have hb3_eq : b_3_val = Complex.ofReal (-((2 : ℝ) * sqrt2_real)) := by
      rw [b_3_val_def]
      apply Complex.ext
      . simp
      . rfl
    rw [hb3_eq]
    have h_neg_of_real_eq : -Complex.ofReal ((2 : ℝ) * sqrt2_real) = Complex.ofReal (-((2 : ℝ) * sqrt2_real)) := (Complex.ofReal_neg ((2 : ℝ) * sqrt2_real)).symm
    rw [← h_neg_of_real_eq]
    apply or_comm
  have subprob_roots_B_iff_proof : ∀ (z : ℂ), z ^ 3 - (8 : ℂ) * z ^ 2 - (8 : ℂ) * z + (64 : ℂ) = 0 ↔ (z = b_1_val ∨ z = b_2_val ∨ z = b_3_val) := by
    mkOpaque
    intro z
    rw [subprob_B_poly_factor_proof z]
    rw [_root_.mul_eq_zero]
    rw [sub_eq_zero]
    rw [subprob_B_quadratic_roots_iff_proof z]
  letI hA_cases := (subprob_roots_A_iff_proof a).mp h₀
  letI hB_cases := (subprob_roots_B_iff_proof b).mp h₁
  letI diff_1_1 := a_1_val - b_1_val
  retro' diff_1_1_def : diff_1_1 = a_1_val - b_1_val := by funext; rfl
  have subprob_diff_1_1_calc_mk_proof : diff_1_1 = Complex.mk ((2 : ℝ) - (8 : ℝ)) ((0 : ℝ) - (0 : ℝ)) := by
    mkOpaque
    rw [diff_1_1_def, a_1_val_def, b_1_val_def]
    simp [Complex.ext_iff, sub_eq_add_neg] <;> norm_num
  have subprob_diff_1_1_res_mk_proof : diff_1_1 = Complex.mk (-6 : ℝ) (0 : ℝ) := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc] <;> norm_num <;> linarith
  have subprob_normSq_1_1_calc_proof : Complex.normSq diff_1_1 = (-6 : ℝ) ^ 2 + (0 : ℝ) ^ 2 := by
    mkOpaque
    simp [Complex.normSq, subprob_diff_1_1_res_mk_proof, pow_two] <;> norm_num
  have subprob_normSq_1_1_is_36_proof : Complex.normSq diff_1_1 = (36 : ℝ) := by
    mkOpaque
    rw [subprob_normSq_1_1_calc_proof]
    norm_num
  have subprob_36_le_84_proof : (36 : ℝ) ≤ D_max_sq_val := by
    mkOpaque
    rw [D_max_sq_val_def]
    norm_num <;> linarith
  have subprob_normSq_1_1_le_Dmax_proof : Complex.normSq diff_1_1 ≤ D_max_sq_val := by
    mkOpaque
    have h₀ : Complex.normSq diff_1_1 = 36 := by rw [subprob_normSq_1_1_is_36_proof]
    linarith [subprob_36_le_84_proof]
  letI diff_1_2 := a_1_val - b_2_val
  retro' diff_1_2_def : diff_1_2 = a_1_val - b_2_val := by funext; rfl
  letI val_normSq_1_2 := (12 : ℝ) - (8 : ℝ) * sqrt2_real
  letI real_part_1_2 := (2 : ℝ) - (2 : ℝ) * sqrt2_real
  retro' real_part_1_2_def : real_part_1_2 = (2 : ℝ) - (2 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_diff_1_2_calc_mk_proof : diff_1_2 = Complex.mk real_part_1_2 ((0 : ℝ) - (0 : ℝ)) := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, mul_comm] <;> norm_num <;> linarith [sqrt2_real_def]
  have subprob_normSq_1_2_calc_proof : Complex.normSq diff_1_2 = real_part_1_2 ^ 2 + (0 : ℝ) ^ 2 := by
    mkOpaque
    simp [Complex.normSq, subprob_diff_1_2_calc_mk_proof, real_part_1_2_def] <;> ring <;> norm_num <;> linarith [sqrt2_real_def]
  retro' val_normSq_1_2_def : val_normSq_1_2 = (12 : ℝ) - (8 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_real_part_1_2_sq_eval_proof : real_part_1_2 ^ 2 = val_normSq_1_2 := by
    mkOpaque
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_zero, add_zero, zero_add, sub_zero, sub_neg_eq_add, add_assoc]
    norm_num
    ring <;> simp [sqrt2_real_def] <;> norm_num <;> ring
  have subprob_normSq_1_2_is_val_proof : Complex.normSq diff_1_2 = val_normSq_1_2 := by
    mkOpaque
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, neg_add_rev, mul_neg, mul_one, neg_neg, neg_zero, add_zero, zero_add, mul_zero, zero_mul, sub_zero, add_comm, add_left_comm, add_assoc]
    norm_num <;> linarith [sqrt2_real_def]
  have subprob_val_normSq_1_2_le_Dmax_proof : val_normSq_1_2 ≤ D_max_sq_val := by
    mkOpaque
    norm_num
    ring_nf
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  have subprob_normSq_1_2_le_Dmax_proof : Complex.normSq diff_1_2 ≤ D_max_sq_val := by
    mkOpaque
    rw [subprob_normSq_1_2_is_val_proof]
    exact subprob_val_normSq_1_2_le_Dmax_proof
  letI diff_1_3 := a_1_val - b_3_val
  retro' diff_1_3_def : diff_1_3 = a_1_val - b_3_val := by funext; rfl
  letI val_normSq_1_3 := (12 : ℝ) + (8 : ℝ) * sqrt2_real
  letI real_part_1_3 := (2 : ℝ) - (-(2 : ℝ) * sqrt2_real)
  retro' real_part_1_3_def : real_part_1_3 = (2 : ℝ) - -(2 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_diff_1_3_calc_mk_proof : diff_1_3 = Complex.mk real_part_1_3 ((0 : ℝ) - (0 : ℝ)) := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, mul_comm] <;> norm_num <;> linarith [sqrt2_real_def]
  have subprob_normSq_1_3_calc_proof : Complex.normSq diff_1_3 = real_part_1_3 ^ 2 + (0 : ℝ) ^ 2 := by
    mkOpaque
    simp [Complex.normSq, subprob_diff_1_3_calc_mk_proof, real_part_1_3_def, pow_two] <;> norm_num <;> ring
  retro' val_normSq_1_3_def : val_normSq_1_3 = (12 : ℝ) + (8 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_real_part_1_3_sq_eval_proof : real_part_1_3 ^ 2 = val_normSq_1_3 := by
    mkOpaque
    simp only [real_part_1_3_def, sqrt2_real_def, sub_eq_add_neg, neg_mul, neg_neg]
    norm_num <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_normSq_1_3_is_val_proof : Complex.normSq diff_1_3 = val_normSq_1_3 := by
    mkOpaque
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
    norm_num <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_val_normSq_1_3_le_Dmax_proof : val_normSq_1_3 ≤ D_max_sq_val := by
    mkOpaque
    simp_all only [Complex.normSq, Complex.re, Complex.im, Complex.ofReal_im, Complex.ofReal_re, Complex.ext_iff, eq_self_iff_true, and_true]
    norm_num
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_normSq_1_3_le_Dmax_proof : Complex.normSq diff_1_3 ≤ D_max_sq_val := by
    mkOpaque
    have h₀ : Complex.normSq diff_1_3 = val_normSq_1_3 := by rw [subprob_normSq_1_3_is_val_proof]
    rw [h₀]
    exact subprob_val_normSq_1_3_le_Dmax_proof
  letI diff_2_1 := a_2_val - b_1_val
  retro' diff_2_1_def : diff_2_1 = a_2_val - b_1_val := by funext; rfl
  letI real_part_2_1 := (-1 : ℝ) - (8 : ℝ)
  letI imag_part_2_1 := sqrt3_real - (0 : ℝ)
  retro' real_part_2_1_def : real_part_2_1 = -(1 : ℝ) - (8 : ℝ) := by funext; rfl
  retro' imag_part_2_1_def : imag_part_2_1 = sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_2_1_calc_mk_proof : diff_2_1 = Complex.mk real_part_2_1 imag_part_2_1 := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc] <;> norm_num <;> linarith [sqrt3_real_def]
  have subprob_normSq_2_1_calc_proof : Complex.normSq diff_2_1 = real_part_2_1 ^ 2 + imag_part_2_1 ^ 2 := by
    mkOpaque
    simp_all [Complex.normSq, Complex.ext_iff, pow_two, mul_neg, mul_one, sub_neg_eq_add, add_assoc] <;> norm_num <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  letI val_normSq_2_1 := (81 : ℝ) + (3 : ℝ)
  retro' val_normSq_2_1_def : val_normSq_2_1 = (81 : ℝ) + (3 : ℝ) := by funext; rfl
  have subprob_parts_2_1_sq_eval_proof : real_part_2_1 ^ 2 + imag_part_2_1 ^ 2 = val_normSq_2_1 := by
    mkOpaque
    rw [real_part_2_1_def, imag_part_2_1_def]
    norm_num [sqrt3_real_def, val_normSq_2_1_def] <;> ring <;> norm_num <;> linarith
  have subprob_normSq_2_1_is_84_proof : Complex.normSq diff_2_1 = (84 : ℝ) := by
    mkOpaque
    have h₀ : real_part_2_1 = -9 := by
      rw [real_part_2_1_def]
      norm_num
    have h₁ : imag_part_2_1 = sqrt3_real := by
      rw [imag_part_2_1_def]
      norm_num
    rw [subprob_normSq_2_1_calc_proof, h₀, h₁]
    norm_num [sqrt3_real_def, val_normSq_2_1_def]
  have subprob_normSq_2_1_le_Dmax_proof : Complex.normSq diff_2_1 ≤ D_max_sq_val := by
    mkOpaque
    have h : Complex.normSq diff_2_1 = 84 := subprob_normSq_2_1_is_84_proof
    rw [D_max_sq_val_def]
    linarith
  letI diff_2_2 := a_2_val - b_2_val
  retro' diff_2_2_def : diff_2_2 = a_2_val - b_2_val := by funext; rfl
  letI val_normSq_2_2 := (12 : ℝ) + (4 : ℝ) * sqrt2_real
  letI real_part_2_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  retro' real_part_2_2_def : real_part_2_2 = -(1 : ℝ) - (2 : ℝ) * sqrt2_real := by funext; rfl
  letI imag_part_2_2 := sqrt3_real - (0 : ℝ)
  retro' imag_part_2_2_def : imag_part_2_2 = sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_2_2_calc_mk_proof : diff_2_2 = Complex.mk real_part_2_2 imag_part_2_2 := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> norm_num <;> linarith [sqrt2_real_def, sqrt3_real_def]
  have subprob_normSq_2_2_calc_proof : Complex.normSq diff_2_2 = real_part_2_2 ^ 2 + imag_part_2_2 ^ 2 := by
    mkOpaque
    simp [Complex.normSq, subprob_diff_2_2_calc_mk_proof, real_part_2_2_def, imag_part_2_2_def] <;> norm_num <;> ring
  retro' val_normSq_2_2_def : val_normSq_2_2 = (12 : ℝ) + (4 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_parts_2_2_sq_eval_proof : real_part_2_2 ^ 2 + imag_part_2_2 ^ 2 = val_normSq_2_2 := by
    mkOpaque
    rw [real_part_2_2_def, imag_part_2_2_def]
    ring_nf <;> simp [sqrt2_real_def, sqrt3_real_def] <;> norm_num <;> linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  have subprob_normSq_2_2_is_val_proof : Complex.normSq diff_2_2 = val_normSq_2_2 := by
    mkOpaque
    simp only [real_part_2_2_def, imag_part_2_2_def, val_normSq_2_2_def] at *
    norm_num <;> ring <;> simp_all <;> norm_num <;> linarith
  have subprob_val_normSq_2_2_le_Dmax_proof : val_normSq_2_2 ≤ D_max_sq_val := by
    mkOpaque
    rw [val_normSq_2_2_def]
    norm_num
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_normSq_2_2_le_Dmax_proof : Complex.normSq diff_2_2 ≤ D_max_sq_val := by
    mkOpaque
    have h₀ : val_normSq_2_2 ≤ D_max_sq_val := subprob_val_normSq_2_2_le_Dmax_proof
    have h₁ : Complex.normSq diff_2_2 = val_normSq_2_2 := subprob_normSq_2_2_is_val_proof
    rw [h₁]
    exact h₀
  letI diff_2_3 := a_2_val - b_3_val
  retro' diff_2_3_def : diff_2_3 = a_2_val - b_3_val := by funext; rfl
  letI real_part_2_3 := (-1 : ℝ) - (-(2 : ℝ) * sqrt2_real)
  letI imag_part_2_3 := sqrt3_real - (0 : ℝ)
  retro' real_part_2_3_def : real_part_2_3 = -(1 : ℝ) - -(2 : ℝ) * sqrt2_real := by funext; rfl
  retro' imag_part_2_3_def : imag_part_2_3 = sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_2_3_calc_mk_proof : diff_2_3 = Complex.mk real_part_2_3 imag_part_2_3 := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> norm_num <;> ring <;> field_simp [sqrt2_real_def, sqrt3_real_def] <;> norm_num <;> ring
  have subprob_normSq_2_3_calc_proof : Complex.normSq diff_2_3 = real_part_2_3 ^ 2 + imag_part_2_3 ^ 2 := by
    mkOpaque
    simp [Complex.normSq, real_part_2_3_def, imag_part_2_3_def, subprob_diff_2_3_calc_mk_proof] <;> norm_num <;> ring <;> norm_num <;> ring <;> norm_num
  letI val_normSq_2_3 := (12 : ℝ) - (4 : ℝ) * sqrt2_real
  retro' val_normSq_2_3_def : val_normSq_2_3 = (12 : ℝ) - (4 : ℝ) * sqrt2_real := by funext; rfl
  have subprob_parts_2_3_sq_eval_proof : real_part_2_3 ^ 2 + imag_part_2_3 ^ 2 = val_normSq_2_3 := by
    mkOpaque
    simp_all only [sub_eq_add_neg, add_assoc, add_left_comm, add_right_comm]
    norm_num
    ring <;> linarith [sqrt2_real_def, sqrt3_real_def]
  have subprob_val_normSq_2_3_le_Dmax_proof : val_normSq_2_3 ≤ D_max_sq_val := by
    mkOpaque
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_neg_one, mul_one, mul_zero, add_zero, zero_add, sub_zero, sub_neg_eq_add, add_assoc]
    norm_num
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have subprob_normSq_2_3_le_Dmax_proof : Complex.normSq diff_2_3 ≤ D_max_sq_val := by
    mkOpaque
    have h := subprob_val_normSq_2_3_le_Dmax_proof
    simp [val_normSq_2_3_def] at h ⊢
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  letI diff_3_1 := a_3_val - b_1_val
  retro' diff_3_1_def : diff_3_1 = a_3_val - b_1_val := by funext; rfl
  letI real_part_3_1 := (-1 : ℝ) - (8 : ℝ)
  letI imag_part_3_1 := (-sqrt3_real) - (0 : ℝ)
  retro' real_part_3_1_def : real_part_3_1 = -(1 : ℝ) - (8 : ℝ) := by funext; rfl
  retro' imag_part_3_1_def : imag_part_3_1 = -sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_3_1_calc_mk_proof : diff_3_1 = Complex.mk real_part_3_1 imag_part_3_1 := by
    mkOpaque
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> norm_num <;> linarith [sqrt3_real_def, sqrt2_real_def]
  have subprob_normSq_3_1_calc_proof : Complex.normSq diff_3_1 = real_part_3_1 ^ 2 + imag_part_3_1 ^ 2 := by
    mkOpaque
    simp_all [Complex.normSq, Complex.ext_iff, pow_two] <;> norm_num <;> linarith [sqrt3_real_def, sqrt2_real_def]
  letI val_normSq_3_1 := (81 : ℝ) + (3 : ℝ)
  retro' val_normSq_3_1_def : val_normSq_3_1 = (81 : ℝ) + (3 : ℝ) := by funext; rfl
  have subprob_parts_3_1_sq_eval_proof : real_part_3_1 ^ 2 + imag_part_3_1 ^ 2 = val_normSq_3_1 := by
    mkOpaque
    rw [real_part_3_1_def, imag_part_3_1_def]
    norm_num [sqrt3_real_def, val_normSq_3_1_def] <;> linarith
  have subprob_normSq_3_1_is_84_proof : Complex.normSq diff_3_1 = (84 : ℝ) := by
    mkOpaque
    rw [subprob_diff_3_1_calc_mk_proof]
    simp [real_part_3_1_def, imag_part_3_1_def, sqrt3_real_def]
    norm_num <;> linarith
  have subprob_normSq_3_1_le_Dmax_proof : Complex.normSq diff_3_1 ≤ D_max_sq_val := by
    mkOpaque
    have h1 : Complex.normSq diff_3_1 = 84 := subprob_normSq_3_1_is_84_proof
    linarith [D_max_sq_val_def]
  letI diff_3_2 := a_3_val - b_2_val
  retro' diff_3_2_def : diff_3_2 = a_3_val - b_2_val := by funext; rfl
  letI real_part_3_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  letI imag_part_3_2 := (-sqrt3_real) - (0 : ℝ)
  retro' real_part_3_2_def : real_part_3_2 = -(1 : ℝ) - (2 : ℝ) * sqrt2_real := by funext; rfl
  retro' imag_part_3_2_def : imag_part_3_2 = -sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_3_2_calc_mk_proof : diff_3_2 = Complex.mk real_part_3_2 imag_part_3_2 := by
    mkOpaque
    rw [diff_3_2_def, a_3_val_def, b_2_val_def]
    simp [Complex.ext_iff, real_part_3_2_def, imag_part_3_2_def] <;> norm_num <;> simp_all
  have subprob_normSq_3_2_calc_proof : Complex.normSq diff_3_2 = real_part_3_2 ^ 2 + imag_part_3_2 ^ 2 := by
    mkOpaque
    rw [subprob_diff_3_2_calc_mk_proof]
    simp [Complex.normSq] <;> norm_num <;> linarith [sqrt2_real_def, sqrt3_real_def]
  have subprob_parts_3_2_sq_eval_proof : real_part_3_2 ^ 2 + imag_part_3_2 ^ 2 = val_normSq_2_2 := by
    mkOpaque
    simp_all only [Complex.normSq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    norm_num
    ring <;> simp [sqrt2_real_def, sqrt3_real_def] <;> norm_num <;> ring
  have subprob_normSq_3_2_is_val_proof : Complex.normSq diff_3_2 = val_normSq_2_2 := by
    mkOpaque
    simp [real_part_3_2_def, imag_part_3_2_def, val_normSq_2_2_def]
    norm_num
    ring <;> norm_num <;> linarith [sqrt2_real_def, sqrt3_real_def]
  have subprob_normSq_3_2_le_Dmax_proof : Complex.normSq diff_3_2 ≤ D_max_sq_val := by
    mkOpaque
    have h₀ : Complex.normSq diff_3_2 = val_normSq_2_2 := subprob_normSq_3_2_is_val_proof
    have h₁ : val_normSq_2_2 ≤ D_max_sq_val := subprob_val_normSq_2_2_le_Dmax_proof
    linarith
  letI diff_3_3 := a_3_val - b_3_val
  retro' diff_3_3_def : diff_3_3 = a_3_val - b_3_val := by funext; rfl
  letI real_part_3_3 := (-1 : ℝ) - (-(2 : ℝ) * sqrt2_real)
  letI imag_part_3_3 := (-sqrt3_real) - (0 : ℝ)
  retro' real_part_3_3_def : real_part_3_3 = -(1 : ℝ) - -(2 : ℝ) * sqrt2_real := by funext; rfl
  retro' imag_part_3_3_def : imag_part_3_3 = -sqrt3_real - (0 : ℝ) := by funext; rfl
  have subprob_diff_3_3_calc_mk_proof : diff_3_3 = Complex.mk real_part_3_3 imag_part_3_3 := by
    mkOpaque
    rw [diff_3_3_def, a_3_val_def, b_3_val_def]
    simp [Complex.ext_iff, real_part_3_3_def, imag_part_3_3_def, sub_eq_add_neg, mul_neg, mul_comm] <;> norm_num <;> ring
  have subprob_normSq_3_3_calc_proof : Complex.normSq diff_3_3 = real_part_3_3 ^ 2 + imag_part_3_3 ^ 2 := by
    mkOpaque
    simp [Complex.normSq, subprob_diff_3_3_calc_mk_proof, real_part_3_3_def, imag_part_3_3_def]
    norm_num
    ring <;> simp [sqrt2_real_def, sqrt3_real_def] <;> norm_num <;> ring
  have subprob_parts_3_3_sq_eval_proof : real_part_3_3 ^ 2 + imag_part_3_3 ^ 2 = val_normSq_2_3 := by
    mkOpaque
    simp_all only [sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_add, mul_sub, mul_comm]
    norm_num <;> ring <;> norm_num <;> ring
  have subprob_normSq_3_3_is_val_proof : Complex.normSq diff_3_3 = val_normSq_2_3 := by
    mkOpaque
    simp_all [Complex.normSq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;> norm_num <;> linarith [sqrt2_real_def, sqrt3_real_def]
  have subprob_normSq_3_3_le_Dmax_proof : Complex.normSq diff_3_3 ≤ D_max_sq_val := by
    mkOpaque
    have h₀ : val_normSq_2_3 ≤ D_max_sq_val := subprob_val_normSq_2_3_le_Dmax_proof
    have h₁ : Complex.normSq diff_3_3 = val_normSq_2_3 := subprob_normSq_3_3_is_val_proof
    linarith [h₀, h₁]
  have subprob_main_goal_normSq_le_84_proof : Complex.normSq (a - b) ≤ D_max_sq_val := by
    mkOpaque
    rcases hA_cases with rfl | rfl | rfl
    . rcases hB_cases with rfl | rfl | rfl
      . rw [← diff_1_1_def]
        exact subprob_normSq_1_1_le_Dmax_proof
      . rw [← diff_1_2_def]
        exact subprob_normSq_1_2_le_Dmax_proof
      . rw [← diff_1_3_def]
        exact subprob_normSq_1_3_le_Dmax_proof
    . rcases hB_cases with rfl | rfl | rfl
      . rw [← diff_2_1_def]
        exact subprob_normSq_2_1_le_Dmax_proof
      . rw [← diff_2_2_def]
        exact subprob_normSq_2_2_le_Dmax_proof
      . rw [← diff_2_3_def]
        exact subprob_normSq_2_3_le_Dmax_proof
    . rcases hB_cases with rfl | rfl | rfl
      . rw [← diff_3_1_def]
        exact subprob_normSq_3_1_le_Dmax_proof
      . rw [← diff_3_2_def]
        exact subprob_normSq_3_2_le_Dmax_proof
      . rw [← diff_3_3_def]
        exact subprob_normSq_3_3_le_Dmax_proof
  have subprob_final_goal_proof : Complex.abs (a - b) ≤ target_bound_val := by
    mkOpaque
    rw [subprob_target_equiv_normSq_proof]
    exact subprob_main_goal_normSq_le_84_proof
  exact
    show Complex.abs (a - b) ≤ (2 : ℝ) * √(21 : ℝ) by
      mkOpaque
      have h₀ : Complex.abs (a - b) ≤ target_bound_val := subprob_final_goal_proof
      rw [target_bound_val_def] at h₀
      have h₁ : Complex.abs (a - b) ≤ 2 * √(21 : ℝ) := h₀
      exact h₁

#print axioms amc12a_2020_p15

/- Sketch
variable (a b : ℂ) (h₀ : a^3 - 8 = 0) (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0)
play
  -- Define constants and specific root values
  sqrt3_real := Real.sqrt (3 : ℝ)
  sqrt2_real := Real.sqrt (2 : ℝ)

  a_1_val := Complex.mk (2 : ℝ) (0 : ℝ)
  a_2_val := Complex.mk (-1 : ℝ) sqrt3_real
  a_3_val := Complex.mk (-1 : ℝ) (-sqrt3_real)

  b_1_val := Complex.mk (8 : ℝ) (0 : ℝ)
  b_2_val := Complex.mk ((2 : ℝ) * sqrt2_real) (0 : ℝ)
  b_3_val := Complex.mk (- (2 : ℝ) * sqrt2_real) (0 : ℝ)

  D_max_sq_val := (84 : ℝ)
  target_bound_val := (2 : ℝ) * Real.sqrt (21 : ℝ)

  -- Step 1: Characterize roots of z^3 - 8 = 0
  subprob_A_poly_factor :≡ ∀ (z : ℂ), z^3 - (8:ℂ) = (z - a_1_val) * (z^2 + (2:ℂ)*z + (4:ℂ))
  subprob_A_poly_factor_proof ⇐ show subprob_A_poly_factor by sorry
  subprob_A_quadratic_roots_iff :≡ ∀ (z : ℂ), z^2 + (2:ℂ)*z + (4:ℂ) = 0 ↔ (z = a_2_val ∨ z = a_3_val)
  subprob_A_quadratic_roots_iff_proof ⇐ show subprob_A_quadratic_roots_iff by sorry
  subprob_roots_A_iff :≡ ∀ (z : ℂ), z^3 - (8:ℂ) = 0 ↔ (z = a_1_val ∨ z = a_2_val ∨ z = a_3_val)
  subprob_roots_A_iff_proof ⇐ show subprob_roots_A_iff by sorry

  -- Step 2: Characterize roots of z^3 - 8z^2 - 8z + 64 = 0
  subprob_B_poly_factor :≡ ∀ (z : ℂ), z^3 - (8:ℂ) * z^2 - (8:ℂ) * z + (64:ℂ) = (z - b_1_val) * (z^2 - (8:ℂ))
  subprob_B_poly_factor_proof ⇐ show subprob_B_poly_factor by sorry
  subprob_B_quadratic_roots_iff :≡ ∀ (z : ℂ), z^2 - (8:ℂ) = 0 ↔ (z = b_2_val ∨ z = b_3_val)
  subprob_B_quadratic_roots_iff_proof ⇐ show subprob_B_quadratic_roots_iff by sorry
  subprob_roots_B_iff :≡ ∀ (z : ℂ), z^3 - (8:ℂ) * z^2 - (8:ℂ) * z + (64:ℂ) = 0 ↔ (z = b_1_val ∨ z = b_2_val ∨ z = b_3_val)
  subprob_roots_B_iff_proof ⇐ show subprob_roots_B_iff by sorry

  -- Step 3: Equivalence of goal with normSq
  subprob_target_bound_ge_0 :≡ target_bound_val ≥ (0 : ℝ)
  subprob_target_bound_ge_0_proof ⇐ show subprob_target_bound_ge_0 by sorry
  subprob_target_bound_sq_is_84 :≡ target_bound_val^2 = D_max_sq_val
  subprob_target_bound_sq_is_84_proof ⇐ show subprob_target_bound_sq_is_84 by sorry
  subprob_target_equiv_normSq :≡ (Complex.abs (a - b) ≤ target_bound_val) ↔ (Complex.normSq (a - b) ≤ D_max_sq_val)
  subprob_target_equiv_normSq_proof ⇐ show subprob_target_equiv_normSq by sorry

  -- From h₀ and h₁, a and b must be one of these roots
  hA_cases := (subprob_roots_A_iff_proof a).mp h₀
  hB_cases := (subprob_roots_B_iff_proof b).mp h₁

  -- Step 4: Calculate Complex.normSq (a_k - b_j) for all 9 pairs and show they are ≤ D_max_sq_val

  -- Pair (a_1_val, b_1_val)
  diff_1_1 := a_1_val - b_1_val
  subprob_diff_1_1_calc_mk :≡ diff_1_1 = Complex.mk ((2:ℝ) - (8:ℝ)) ((0:ℝ) - (0:ℝ))
  subprob_diff_1_1_calc_mk_proof ⇐ show subprob_diff_1_1_calc_mk by sorry
  subprob_diff_1_1_res_mk :≡ diff_1_1 = Complex.mk (-6:ℝ) (0:ℝ)
  subprob_diff_1_1_res_mk_proof ⇐ show subprob_diff_1_1_res_mk by sorry
  subprob_normSq_1_1_calc :≡ Complex.normSq diff_1_1 = (-6:ℝ)^2 + (0:ℝ)^2
  subprob_normSq_1_1_calc_proof ⇐ show subprob_normSq_1_1_calc by sorry
  subprob_normSq_1_1_is_36 :≡ Complex.normSq diff_1_1 = (36:ℝ)
  subprob_normSq_1_1_is_36_proof ⇐ show subprob_normSq_1_1_is_36 by sorry
  subprob_36_le_84 :≡ (36 : ℝ) ≤ D_max_sq_val
  subprob_36_le_84_proof ⇐ show subprob_36_le_84 by sorry
  subprob_normSq_1_1_le_Dmax :≡ Complex.normSq diff_1_1 ≤ D_max_sq_val
  subprob_normSq_1_1_le_Dmax_proof ⇐ show subprob_normSq_1_1_le_Dmax by sorry

  -- Pair (a_1_val, b_2_val)
  diff_1_2 := a_1_val - b_2_val
  real_part_1_2 := (2 : ℝ) - (2 : ℝ) * sqrt2_real
  subprob_diff_1_2_calc_mk :≡ diff_1_2 = Complex.mk real_part_1_2 ((0:ℝ) - (0:ℝ))
  subprob_diff_1_2_calc_mk_proof ⇐ show subprob_diff_1_2_calc_mk by sorry
  subprob_normSq_1_2_calc :≡ Complex.normSq diff_1_2 = real_part_1_2^2 + (0:ℝ)^2
  subprob_normSq_1_2_calc_proof ⇐ show subprob_normSq_1_2_calc by sorry
  val_normSq_1_2 := (12 : ℝ) - (8 : ℝ) * sqrt2_real
  subprob_real_part_1_2_sq_eval :≡ real_part_1_2^2 = val_normSq_1_2
  subprob_real_part_1_2_sq_eval_proof ⇐ show subprob_real_part_1_2_sq_eval by sorry
  subprob_normSq_1_2_is_val :≡ Complex.normSq diff_1_2 = val_normSq_1_2
  subprob_normSq_1_2_is_val_proof ⇐ show subprob_normSq_1_2_is_val by sorry
  subprob_val_normSq_1_2_le_Dmax :≡ val_normSq_1_2 ≤ D_max_sq_val
  subprob_val_normSq_1_2_le_Dmax_proof ⇐ show subprob_val_normSq_1_2_le_Dmax by sorry
  subprob_normSq_1_2_le_Dmax :≡ Complex.normSq diff_1_2 ≤ D_max_sq_val
  subprob_normSq_1_2_le_Dmax_proof ⇐ show subprob_normSq_1_2_le_Dmax by sorry

  -- Pair (a_1_val, b_3_val)
  diff_1_3 := a_1_val - b_3_val
  real_part_1_3 := (2 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  subprob_diff_1_3_calc_mk :≡ diff_1_3 = Complex.mk real_part_1_3 ((0:ℝ) - (0:ℝ))
  subprob_diff_1_3_calc_mk_proof ⇐ show subprob_diff_1_3_calc_mk by sorry
  subprob_normSq_1_3_calc :≡ Complex.normSq diff_1_3 = real_part_1_3^2 + (0:ℝ)^2
  subprob_normSq_1_3_calc_proof ⇐ show subprob_normSq_1_3_calc by sorry
  val_normSq_1_3 := (12 : ℝ) + (8 : ℝ) * sqrt2_real
  subprob_real_part_1_3_sq_eval :≡ real_part_1_3^2 = val_normSq_1_3
  subprob_real_part_1_3_sq_eval_proof ⇐ show subprob_real_part_1_3_sq_eval by sorry
  subprob_normSq_1_3_is_val :≡ Complex.normSq diff_1_3 = val_normSq_1_3
  subprob_normSq_1_3_is_val_proof ⇐ show subprob_normSq_1_3_is_val by sorry
  subprob_val_normSq_1_3_le_Dmax :≡ val_normSq_1_3 ≤ D_max_sq_val
  subprob_val_normSq_1_3_le_Dmax_proof ⇐ show subprob_val_normSq_1_3_le_Dmax by sorry
  subprob_normSq_1_3_le_Dmax :≡ Complex.normSq diff_1_3 ≤ D_max_sq_val
  subprob_normSq_1_3_le_Dmax_proof ⇐ show subprob_normSq_1_3_le_Dmax by sorry

  -- Pair (a_2_val, b_1_val)
  diff_2_1 := a_2_val - b_1_val
  real_part_2_1 := (-1 : ℝ) - (8 : ℝ)
  imag_part_2_1 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_1_calc_mk :≡ diff_2_1 = Complex.mk real_part_2_1 imag_part_2_1
  subprob_diff_2_1_calc_mk_proof ⇐ show subprob_diff_2_1_calc_mk by sorry
  subprob_normSq_2_1_calc :≡ Complex.normSq diff_2_1 = real_part_2_1^2 + imag_part_2_1^2
  subprob_normSq_2_1_calc_proof ⇐ show subprob_normSq_2_1_calc by sorry
  val_normSq_2_1 := (81 : ℝ) + (3 : ℝ)
  subprob_parts_2_1_sq_eval :≡ real_part_2_1^2 + imag_part_2_1^2 = val_normSq_2_1
  subprob_parts_2_1_sq_eval_proof ⇐ show subprob_parts_2_1_sq_eval by sorry
  subprob_normSq_2_1_is_84 :≡ Complex.normSq diff_2_1 = (84:ℝ)
  subprob_normSq_2_1_is_84_proof ⇐ show subprob_normSq_2_1_is_84 by sorry
  subprob_normSq_2_1_le_Dmax :≡ Complex.normSq diff_2_1 ≤ D_max_sq_val
  subprob_normSq_2_1_le_Dmax_proof ⇐ show subprob_normSq_2_1_le_Dmax by sorry

  -- Pair (a_2_val, b_2_val)
  diff_2_2 := a_2_val - b_2_val
  real_part_2_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  imag_part_2_2 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_2_calc_mk :≡ diff_2_2 = Complex.mk real_part_2_2 imag_part_2_2
  subprob_diff_2_2_calc_mk_proof ⇐ show subprob_diff_2_2_calc_mk by sorry
  subprob_normSq_2_2_calc :≡ Complex.normSq diff_2_2 = real_part_2_2^2 + imag_part_2_2^2
  subprob_normSq_2_2_calc_proof ⇐ show subprob_normSq_2_2_calc by sorry
  val_normSq_2_2 := (12 : ℝ) + (4 : ℝ) * sqrt2_real
  subprob_parts_2_2_sq_eval :≡ real_part_2_2^2 + imag_part_2_2^2 = val_normSq_2_2
  subprob_parts_2_2_sq_eval_proof ⇐ show subprob_parts_2_2_sq_eval by sorry
  subprob_normSq_2_2_is_val :≡ Complex.normSq diff_2_2 = val_normSq_2_2
  subprob_normSq_2_2_is_val_proof ⇐ show subprob_normSq_2_2_is_val by sorry
  subprob_val_normSq_2_2_le_Dmax :≡ val_normSq_2_2 ≤ D_max_sq_val
  subprob_val_normSq_2_2_le_Dmax_proof ⇐ show subprob_val_normSq_2_2_le_Dmax by sorry
  subprob_normSq_2_2_le_Dmax :≡ Complex.normSq diff_2_2 ≤ D_max_sq_val
  subprob_normSq_2_2_le_Dmax_proof ⇐ show subprob_normSq_2_2_le_Dmax by sorry

  -- Pair (a_2_val, b_3_val)
  diff_2_3 := a_2_val - b_3_val
  real_part_2_3 := (-1 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  imag_part_2_3 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_3_calc_mk :≡ diff_2_3 = Complex.mk real_part_2_3 imag_part_2_3
  subprob_diff_2_3_calc_mk_proof ⇐ show subprob_diff_2_3_calc_mk by sorry
  subprob_normSq_2_3_calc :≡ Complex.normSq diff_2_3 = real_part_2_3^2 + imag_part_2_3^2
  subprob_normSq_2_3_calc_proof ⇐ show subprob_normSq_2_3_calc by sorry
  val_normSq_2_3 := (12 : ℝ) - (4 : ℝ) * sqrt2_real
  subprob_parts_2_3_sq_eval :≡ real_part_2_3^2 + imag_part_2_3^2 = val_normSq_2_3
  subprob_parts_2_3_sq_eval_proof ⇐ show subprob_parts_2_3_sq_eval by sorry
  subprob_normSq_2_3_is_val :≡ Complex.normSq diff_2_3 = val_normSq_2_3
  subprob_normSq_2_3_is_val_proof ⇐ show subprob_normSq_2_3_is_val by sorry
  subprob_val_normSq_2_3_le_Dmax :≡ val_normSq_2_3 ≤ D_max_sq_val
  subprob_val_normSq_2_3_le_Dmax_proof ⇐ show subprob_val_normSq_2_3_le_Dmax by sorry
  subprob_normSq_2_3_le_Dmax :≡ Complex.normSq diff_2_3 ≤ D_max_sq_val
  subprob_normSq_2_3_le_Dmax_proof ⇐ show subprob_normSq_2_3_le_Dmax by sorry

  -- Pair (a_3_val, b_1_val)
  diff_3_1 := a_3_val - b_1_val
  real_part_3_1 := (-1 : ℝ) - (8 : ℝ)
  imag_part_3_1 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_1_calc_mk :≡ diff_3_1 = Complex.mk real_part_3_1 imag_part_3_1
  subprob_diff_3_1_calc_mk_proof ⇐ show subprob_diff_3_1_calc_mk by sorry
  subprob_normSq_3_1_calc :≡ Complex.normSq diff_3_1 = real_part_3_1^2 + imag_part_3_1^2
  subprob_normSq_3_1_calc_proof ⇐ show subprob_normSq_3_1_calc by sorry
  val_normSq_3_1 := (81 : ℝ) + (3 : ℝ)
  subprob_parts_3_1_sq_eval :≡ real_part_3_1^2 + imag_part_3_1^2 = val_normSq_3_1
  subprob_parts_3_1_sq_eval_proof ⇐ show subprob_parts_3_1_sq_eval by sorry
  subprob_normSq_3_1_is_84 :≡ Complex.normSq diff_3_1 = (84:ℝ)
  subprob_normSq_3_1_is_84_proof ⇐ show subprob_normSq_3_1_is_84 by sorry
  subprob_normSq_3_1_le_Dmax :≡ Complex.normSq diff_3_1 ≤ D_max_sq_val
  subprob_normSq_3_1_le_Dmax_proof ⇐ show subprob_normSq_3_1_le_Dmax by sorry

  -- Pair (a_3_val, b_2_val)
  diff_3_2 := a_3_val - b_2_val
  real_part_3_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  imag_part_3_2 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_2_calc_mk :≡ diff_3_2 = Complex.mk real_part_3_2 imag_part_3_2
  subprob_diff_3_2_calc_mk_proof ⇐ show subprob_diff_3_2_calc_mk by sorry
  subprob_normSq_3_2_calc :≡ Complex.normSq diff_3_2 = real_part_3_2^2 + imag_part_3_2^2
  subprob_normSq_3_2_calc_proof ⇐ show subprob_normSq_3_2_calc by sorry
  subprob_parts_3_2_sq_eval :≡ real_part_3_2^2 + imag_part_3_2^2 = val_normSq_2_2
  subprob_parts_3_2_sq_eval_proof ⇐ show subprob_parts_3_2_sq_eval by sorry
  subprob_normSq_3_2_is_val :≡ Complex.normSq diff_3_2 = val_normSq_2_2
  subprob_normSq_3_2_is_val_proof ⇐ show subprob_normSq_3_2_is_val by sorry
  subprob_normSq_3_2_le_Dmax :≡ Complex.normSq diff_3_2 ≤ D_max_sq_val
  subprob_normSq_3_2_le_Dmax_proof ⇐ show subprob_normSq_3_2_le_Dmax by sorry

  -- Pair (a_3_val, b_3_val)
  diff_3_3 := a_3_val - b_3_val
  real_part_3_3 := (-1 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  imag_part_3_3 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_3_calc_mk :≡ diff_3_3 = Complex.mk real_part_3_3 imag_part_3_3
  subprob_diff_3_3_calc_mk_proof ⇐ show subprob_diff_3_3_calc_mk by sorry
  subprob_normSq_3_3_calc :≡ Complex.normSq diff_3_3 = real_part_3_3^2 + imag_part_3_3^2
  subprob_normSq_3_3_calc_proof ⇐ show subprob_normSq_3_3_calc by sorry
  subprob_parts_3_3_sq_eval :≡ real_part_3_3^2 + imag_part_3_3^2 = val_normSq_2_3
  subprob_parts_3_3_sq_eval_proof ⇐ show subprob_parts_3_3_sq_eval by sorry
  subprob_normSq_3_3_is_val :≡ Complex.normSq diff_3_3 = val_normSq_2_3
  subprob_normSq_3_3_is_val_proof ⇐ show subprob_normSq_3_3_is_val by sorry
  subprob_normSq_3_3_le_Dmax :≡ Complex.normSq diff_3_3 ≤ D_max_sq_val
  subprob_normSq_3_3_le_Dmax_proof ⇐ show subprob_normSq_3_3_le_Dmax by sorry

  -- Step 5: Main proof by cases using hA_cases and hB_cases
  subprob_main_goal_normSq_le_84 :≡ Complex.normSq (a - b) ≤ D_max_sq_val
  subprob_main_goal_normSq_le_84_proof ⇐ show subprob_main_goal_normSq_le_84 by sorry

  -- Final step: Conclude original goal using equivalence
  subprob_final_goal :≡ Complex.abs (a - b) ≤ target_bound_val
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketch with proof
variable (a: ℂ) (b: ℂ) (h₀: a ^ (3 : ℕ) - (8 : ℂ) = (0 : ℂ)) (h₁: b ^ (3 : ℕ) - (8 : ℂ) * b ^ (2 : ℕ) - (8 : ℂ) * b + (64 : ℂ) = (0 : ℂ))
play
  sqrt3_real := Real.sqrt (3 : ℝ)
  sqrt2_real := Real.sqrt (2 : ℝ)
  a_1_val := Complex.mk (2 : ℝ) (0 : ℝ)
  a_2_val := Complex.mk (-1 : ℝ) sqrt3_real
  a_3_val := Complex.mk (-1 : ℝ) (-sqrt3_real)
  b_1_val := Complex.mk (8 : ℝ) (0 : ℝ)
  b_2_val := Complex.mk ((2 : ℝ) * sqrt2_real) (0 : ℝ)
  b_3_val := Complex.mk (- (2 : ℝ) * sqrt2_real) (0 : ℝ)
  D_max_sq_val := (84 : ℝ)
  target_bound_val := (2 : ℝ) * Real.sqrt (21 : ℝ)
  subprob_A_poly_factor :≡ ∀ (z : ℂ), z^3 - (8:ℂ) = (z - a_1_val) * (z^2 + (2:ℂ)*z + (4:ℂ))
  subprob_A_poly_factor_proof ⇐ show subprob_A_poly_factor by
    intro z
    ring_nf
    <;> simp_all [Complex.ext_iff, pow_two, pow_three, mul_add, mul_comm, mul_left_comm]
    <;> norm_num
    <;> linarith [sqrt3_real_def, sqrt2_real_def, a_1_val_def, a_2_val_def, a_3_val_def, b_1_val_def, b_2_val_def, b_3_val_def, D_max_sq_val_def, target_bound_val_def]
  subprob_A_quadratic_roots_iff :≡ ∀ (z : ℂ), z^2 + (2:ℂ)*z + (4:ℂ) = 0 ↔ (z = a_2_val ∨ z = a_3_val)
  subprob_A_quadratic_roots_iff_proof ⇐ show subprob_A_quadratic_roots_iff by
    intro z
    have h_sum : a_2_val + a_3_val = (-2 : ℂ) := by
      rw [a_2_val_def, a_3_val_def]
      rw [Complex.ext_iff]
      rw [sqrt3_real_def]
      simp
      norm_num
    have h_prod : a_2_val * a_3_val = (4 : ℂ) := by
      rw [a_2_val_def, a_3_val_def]
      rw [Complex.ext_iff]
      constructor
      .
        rw [Complex.mul_re]
        rw [sqrt3_real_def]
        simp only [neg_mul_neg, one_mul, mul_neg, neg_neg]
        have h_sqrt3_sq : √(3 : ℝ) * √(3 : ℝ) = 3 := Real.mul_self_sqrt (by norm_num : 0 ≤ (3 : ℝ))
        rw [h_sqrt3_sq]
        norm_num
      .
        rw [Complex.mul_im]
        rw [sqrt3_real_def]
        simp only [neg_mul_neg, one_mul, mul_neg]
        simp
    have identity : z ^ 2 + (2 : ℂ) * z + (4 : ℂ) = (z - a_2_val) * (z - a_3_val) := by
      have identity_expanded : (z - a_2_val) * (z - a_3_val) = z ^ 2 - (a_2_val + a_3_val) * z + a_2_val * a_3_val := by ring
      rw [identity_expanded]
      rw [h_sum, h_prod]
      ring
    rw [identity]
    apply Iff.intro
    .
      intro h_prod_zero
      have h_sub_zero_or_sub_zero : z - a_2_val = (0 : ℂ) ∨ z - a_3_val = (0 : ℂ) := _root_.mul_eq_zero.mp h_prod_zero
      rw [sub_eq_zero, sub_eq_zero] at h_sub_zero_or_sub_zero
      exact h_sub_zero_or_sub_zero
    .
      intro h_or_eq
      rcases h_or_eq with h_eq_a2 | h_eq_a3
      .
        rw [h_eq_a2]
        rw [sub_self]
        rw [zero_mul]
      .
        rw [h_eq_a3]
        rw [sub_self]
        rw [mul_zero]
  subprob_roots_A_iff :≡ ∀ (z : ℂ), z^3 - (8:ℂ) = 0 ↔ (z = a_1_val ∨ z = a_2_val ∨ z = a_3_val)
  subprob_roots_A_iff_proof ⇐ show subprob_roots_A_iff by
    intro z
    rw [subprob_A_poly_factor_proof]
    rw [show (z - a_1_val) * (z ^ (2 : ℕ) + (2 : ℂ) * z + (4 : ℂ)) = (0 : ℂ) ↔ (z - a_1_val = 0 ∨ z ^ (2 : ℕ) + (2 : ℂ) * z + (4 : ℂ) = (0 : ℂ)) from mul_eq_zero]
    rw [sub_eq_zero]
    rw [subprob_A_quadratic_roots_iff_proof]
  subprob_B_poly_factor :≡ ∀ (z : ℂ), z^3 - (8:ℂ) * z^2 - (8:ℂ) * z + (64:ℂ) = (z - b_1_val) * (z^2 - (8:ℂ))
  subprob_B_poly_factor_proof ⇐ show subprob_B_poly_factor by
    intro z
    ring_nf
    <;> simp_all [Complex.ext_iff, pow_two, pow_three]
    <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_B_quadratic_roots_iff :≡ ∀ (z : ℂ), z^2 - (8:ℂ) = 0 ↔ (z = b_2_val ∨ z = b_3_val)
  subprob_B_quadratic_roots_iff_proof ⇐ show subprob_B_quadratic_roots_iff by
    intro z
    have hr_sq : (Complex.ofReal ((2 : ℝ) * sqrt2_real)) ^ 2 = (8 : ℂ) := by
      have h_rewrite_step : (Complex.ofReal ((2 : ℝ) * sqrt2_real)) ^ (2 : ℕ) = Complex.ofReal (((2 : ℝ) * sqrt2_real) ^ (2 : ℕ)) := Eq.symm (Complex.ofReal_pow ((2 : ℝ) * sqrt2_real) (2 : ℕ))
      rw [h_rewrite_step]
      have h_R_val_sq_real : ((2 : ℝ) * sqrt2_real) ^ 2 = 8 := by
        rw [sqrt2_real_def]
        rw [mul_pow]
        have h2sq : (2 : ℝ) ^ 2 = 4 := by norm_num
        rw [h2sq]
        have hsqrt2sq : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
        rw [hsqrt2sq]
        norm_num
      rw [h_R_val_sq_real]
      rfl
    rw [← hr_sq]
    rw [sq_sub_sq z (Complex.ofReal ((2 : ℝ) * sqrt2_real))]
    rw [_root_.mul_eq_zero]
    rw [sub_eq_zero]
    rw [add_eq_zero_iff_eq_neg]
    have hb2_eq : b_2_val = Complex.ofReal ((2 : ℝ) * sqrt2_real) := by
      rw [b_2_val_def]
      rfl
    rw [hb2_eq]
    have hb3_eq : b_3_val = Complex.ofReal (-((2 : ℝ) * sqrt2_real)) := by
      rw [b_3_val_def]
      apply Complex.ext
      .
        simp
      .
        rfl
    rw [hb3_eq]
    have h_neg_of_real_eq : -Complex.ofReal ((2 : ℝ) * sqrt2_real) = Complex.ofReal (-((2 : ℝ) * sqrt2_real)) :=
      (Complex.ofReal_neg ((2 : ℝ) * sqrt2_real)).symm
    rw [← h_neg_of_real_eq]
    apply or_comm
  subprob_roots_B_iff :≡ ∀ (z : ℂ), z^3 - (8:ℂ) * z^2 - (8:ℂ) * z + (64:ℂ) = 0 ↔ (z = b_1_val ∨ z = b_2_val ∨ z = b_3_val)
  subprob_roots_B_iff_proof ⇐ show subprob_roots_B_iff by
    intro z
    rw [subprob_B_poly_factor_proof z]
    rw [_root_.mul_eq_zero]
    rw [sub_eq_zero]
    rw [subprob_B_quadratic_roots_iff_proof z]
  subprob_target_bound_ge_0 :≡ target_bound_val ≥ (0 : ℝ)
  subprob_target_bound_ge_0_proof ⇐ show subprob_target_bound_ge_0 by
    have h₀ : (0 : ℝ) ≤ √(21 : ℝ) := Real.sqrt_nonneg _
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  subprob_target_bound_sq_is_84 :≡ target_bound_val^2 = D_max_sq_val
  subprob_target_bound_sq_is_84_proof ⇐ show subprob_target_bound_sq_is_84 by
    rw [target_bound_val_def, D_max_sq_val_def]
    ring_nf
    <;> norm_num
    <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  subprob_target_equiv_normSq :≡ (Complex.abs (a - b) ≤ target_bound_val) ↔ (Complex.normSq (a - b) ≤ D_max_sq_val)
  subprob_target_equiv_normSq_proof ⇐ show subprob_target_equiv_normSq by
    rw [Complex.abs]
    dsimp
    rw [Real.sqrt_le_iff]
    simp [subprob_target_bound_ge_0_proof]
    rw [← subprob_target_bound_sq_is_84_proof]
  hA_cases := (subprob_roots_A_iff_proof a).mp h₀
  hB_cases := (subprob_roots_B_iff_proof b).mp h₁
  diff_1_1 := a_1_val - b_1_val
  subprob_diff_1_1_calc_mk :≡ diff_1_1 = Complex.mk ((2:ℝ) - (8:ℝ)) ((0:ℝ) - (0:ℝ))
  subprob_diff_1_1_calc_mk_proof ⇐ show subprob_diff_1_1_calc_mk by
    rw [diff_1_1_def, a_1_val_def, b_1_val_def]
    simp [Complex.ext_iff, sub_eq_add_neg]
    <;> norm_num
  subprob_diff_1_1_res_mk :≡ diff_1_1 = Complex.mk (-6:ℝ) (0:ℝ)
  subprob_diff_1_1_res_mk_proof ⇐ show subprob_diff_1_1_res_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc]
    <;> norm_num
    <;> linarith
  subprob_normSq_1_1_calc :≡ Complex.normSq diff_1_1 = (-6:ℝ)^2 + (0:ℝ)^2
  subprob_normSq_1_1_calc_proof ⇐ show subprob_normSq_1_1_calc by
    simp [Complex.normSq, subprob_diff_1_1_res_mk_proof, pow_two]
    <;> norm_num
  subprob_normSq_1_1_is_36 :≡ Complex.normSq diff_1_1 = (36:ℝ)
  subprob_normSq_1_1_is_36_proof ⇐ show subprob_normSq_1_1_is_36 by
    rw [subprob_normSq_1_1_calc_proof]
    norm_num
  subprob_36_le_84 :≡ (36 : ℝ) ≤ D_max_sq_val
  subprob_36_le_84_proof ⇐ show subprob_36_le_84 by
    rw [D_max_sq_val_def]
    norm_num
    <;> linarith
  subprob_normSq_1_1_le_Dmax :≡ Complex.normSq diff_1_1 ≤ D_max_sq_val
  subprob_normSq_1_1_le_Dmax_proof ⇐ show subprob_normSq_1_1_le_Dmax by
    have h₀ : Complex.normSq diff_1_1 = 36 := by
      rw [subprob_normSq_1_1_is_36_proof]
    linarith [subprob_36_le_84_proof]
  diff_1_2 := a_1_val - b_2_val
  real_part_1_2 := (2 : ℝ) - (2 : ℝ) * sqrt2_real
  subprob_diff_1_2_calc_mk :≡ diff_1_2 = Complex.mk real_part_1_2 ((0:ℝ) - (0:ℝ))
  subprob_diff_1_2_calc_mk_proof ⇐ show subprob_diff_1_2_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, mul_comm]
    <;> norm_num
    <;> linarith [sqrt2_real_def]
  subprob_normSq_1_2_calc :≡ Complex.normSq diff_1_2 = real_part_1_2^2 + (0:ℝ)^2
  subprob_normSq_1_2_calc_proof ⇐ show subprob_normSq_1_2_calc by
    simp [Complex.normSq, subprob_diff_1_2_calc_mk_proof, real_part_1_2_def]
    <;> ring
    <;> norm_num
    <;> linarith [sqrt2_real_def]
  val_normSq_1_2 := (12 : ℝ) - (8 : ℝ) * sqrt2_real
  subprob_real_part_1_2_sq_eval :≡ real_part_1_2^2 = val_normSq_1_2
  subprob_real_part_1_2_sq_eval_proof ⇐ show subprob_real_part_1_2_sq_eval by
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_zero, add_zero, zero_add, sub_zero, sub_neg_eq_add, add_assoc]
    norm_num
    ring
    <;> simp [sqrt2_real_def]
    <;> norm_num
    <;> ring
  subprob_normSq_1_2_is_val :≡ Complex.normSq diff_1_2 = val_normSq_1_2
  subprob_normSq_1_2_is_val_proof ⇐ show subprob_normSq_1_2_is_val by
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, neg_add_rev, mul_neg, mul_one, neg_neg, neg_zero, add_zero, zero_add, mul_zero, zero_mul, sub_zero, add_comm, add_left_comm, add_assoc]
    norm_num
    <;> linarith [sqrt2_real_def]
  subprob_val_normSq_1_2_le_Dmax :≡ val_normSq_1_2 ≤ D_max_sq_val
  subprob_val_normSq_1_2_le_Dmax_proof ⇐ show subprob_val_normSq_1_2_le_Dmax by
    norm_num
    ring_nf
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  subprob_normSq_1_2_le_Dmax :≡ Complex.normSq diff_1_2 ≤ D_max_sq_val
  subprob_normSq_1_2_le_Dmax_proof ⇐ show subprob_normSq_1_2_le_Dmax by
    rw [subprob_normSq_1_2_is_val_proof]
    exact subprob_val_normSq_1_2_le_Dmax_proof
  diff_1_3 := a_1_val - b_3_val
  real_part_1_3 := (2 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  subprob_diff_1_3_calc_mk :≡ diff_1_3 = Complex.mk real_part_1_3 ((0:ℝ) - (0:ℝ))
  subprob_diff_1_3_calc_mk_proof ⇐ show subprob_diff_1_3_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, mul_comm]
    <;> norm_num
    <;> linarith [sqrt2_real_def]
  subprob_normSq_1_3_calc :≡ Complex.normSq diff_1_3 = real_part_1_3^2 + (0:ℝ)^2
  subprob_normSq_1_3_calc_proof ⇐ show subprob_normSq_1_3_calc by
    simp [Complex.normSq, subprob_diff_1_3_calc_mk_proof, real_part_1_3_def, pow_two]
    <;> norm_num
    <;> ring
  val_normSq_1_3 := (12 : ℝ) + (8 : ℝ) * sqrt2_real
  subprob_real_part_1_3_sq_eval :≡ real_part_1_3^2 = val_normSq_1_3
  subprob_real_part_1_3_sq_eval_proof ⇐ show subprob_real_part_1_3_sq_eval by
    simp only [real_part_1_3_def, sqrt2_real_def, sub_eq_add_neg, neg_mul, neg_neg]
    norm_num
    <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_normSq_1_3_is_val :≡ Complex.normSq diff_1_3 = val_normSq_1_3
  subprob_normSq_1_3_is_val_proof ⇐ show subprob_normSq_1_3_is_val by
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
    norm_num
    <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_val_normSq_1_3_le_Dmax :≡ val_normSq_1_3 ≤ D_max_sq_val
  subprob_val_normSq_1_3_le_Dmax_proof ⇐ show subprob_val_normSq_1_3_le_Dmax by
    simp_all only [Complex.normSq, Complex.re, Complex.im, Complex.ofReal_im, Complex.ofReal_re, Complex.ext_iff, eq_self_iff_true, and_true]
    norm_num
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_normSq_1_3_le_Dmax :≡ Complex.normSq diff_1_3 ≤ D_max_sq_val
  subprob_normSq_1_3_le_Dmax_proof ⇐ show subprob_normSq_1_3_le_Dmax by
    have h₀ : Complex.normSq diff_1_3 = val_normSq_1_3 := by
      rw [subprob_normSq_1_3_is_val_proof]
    rw [h₀]
    exact subprob_val_normSq_1_3_le_Dmax_proof
  diff_2_1 := a_2_val - b_1_val
  real_part_2_1 := (-1 : ℝ) - (8 : ℝ)
  imag_part_2_1 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_1_calc_mk :≡ diff_2_1 = Complex.mk real_part_2_1 imag_part_2_1
  subprob_diff_2_1_calc_mk_proof ⇐ show subprob_diff_2_1_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc]
    <;> norm_num
    <;> linarith [sqrt3_real_def]
  subprob_normSq_2_1_calc :≡ Complex.normSq diff_2_1 = real_part_2_1^2 + imag_part_2_1^2
  subprob_normSq_2_1_calc_proof ⇐ show subprob_normSq_2_1_calc by
    simp_all [Complex.normSq, Complex.ext_iff, pow_two, mul_neg, mul_one, sub_neg_eq_add, add_assoc]
    <;> norm_num
    <;> linarith [sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  val_normSq_2_1 := (81 : ℝ) + (3 : ℝ)
  subprob_parts_2_1_sq_eval :≡ real_part_2_1^2 + imag_part_2_1^2 = val_normSq_2_1
  subprob_parts_2_1_sq_eval_proof ⇐ show subprob_parts_2_1_sq_eval by
    rw [real_part_2_1_def, imag_part_2_1_def]
    norm_num [sqrt3_real_def, val_normSq_2_1_def]
    <;> ring
    <;> norm_num
    <;> linarith
  subprob_normSq_2_1_is_84 :≡ Complex.normSq diff_2_1 = (84:ℝ)
  subprob_normSq_2_1_is_84_proof ⇐ show subprob_normSq_2_1_is_84 by
    have h₀ : real_part_2_1 = -9 := by
      rw [real_part_2_1_def]
      norm_num
    have h₁ : imag_part_2_1 = sqrt3_real := by
      rw [imag_part_2_1_def]
      norm_num
    rw [subprob_normSq_2_1_calc_proof, h₀, h₁]
    norm_num [sqrt3_real_def, val_normSq_2_1_def]
  subprob_normSq_2_1_le_Dmax :≡ Complex.normSq diff_2_1 ≤ D_max_sq_val
  subprob_normSq_2_1_le_Dmax_proof ⇐ show subprob_normSq_2_1_le_Dmax by
    have h : Complex.normSq diff_2_1 = 84 := subprob_normSq_2_1_is_84_proof
    rw [D_max_sq_val_def]
    linarith
  diff_2_2 := a_2_val - b_2_val
  real_part_2_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  imag_part_2_2 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_2_calc_mk :≡ diff_2_2 = Complex.mk real_part_2_2 imag_part_2_2
  subprob_diff_2_2_calc_mk_proof ⇐ show subprob_diff_2_2_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    <;> norm_num
    <;> linarith [sqrt2_real_def, sqrt3_real_def]
  subprob_normSq_2_2_calc :≡ Complex.normSq diff_2_2 = real_part_2_2^2 + imag_part_2_2^2
  subprob_normSq_2_2_calc_proof ⇐ show subprob_normSq_2_2_calc by
    simp [Complex.normSq, subprob_diff_2_2_calc_mk_proof, real_part_2_2_def, imag_part_2_2_def]
    <;> norm_num
    <;> ring
  val_normSq_2_2 := (12 : ℝ) + (4 : ℝ) * sqrt2_real
  subprob_parts_2_2_sq_eval :≡ real_part_2_2^2 + imag_part_2_2^2 = val_normSq_2_2
  subprob_parts_2_2_sq_eval_proof ⇐ show subprob_parts_2_2_sq_eval by
    rw [real_part_2_2_def, imag_part_2_2_def]
    ring_nf
    <;> simp [sqrt2_real_def, sqrt3_real_def]
    <;> norm_num
    <;> linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3]
  subprob_normSq_2_2_is_val :≡ Complex.normSq diff_2_2 = val_normSq_2_2
  subprob_normSq_2_2_is_val_proof ⇐ show subprob_normSq_2_2_is_val by
    simp only [real_part_2_2_def, imag_part_2_2_def, val_normSq_2_2_def] at *
    norm_num
    <;> ring
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_val_normSq_2_2_le_Dmax :≡ val_normSq_2_2 ≤ D_max_sq_val
  subprob_val_normSq_2_2_le_Dmax_proof ⇐ show subprob_val_normSq_2_2_le_Dmax by
    rw [val_normSq_2_2_def]
    norm_num
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_normSq_2_2_le_Dmax :≡ Complex.normSq diff_2_2 ≤ D_max_sq_val
  subprob_normSq_2_2_le_Dmax_proof ⇐ show subprob_normSq_2_2_le_Dmax by
    have h₀ : val_normSq_2_2 ≤ D_max_sq_val := subprob_val_normSq_2_2_le_Dmax_proof
    have h₁ : Complex.normSq diff_2_2 = val_normSq_2_2 := subprob_normSq_2_2_is_val_proof
    rw [h₁]
    exact h₀
  diff_2_3 := a_2_val - b_3_val
  real_part_2_3 := (-1 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  imag_part_2_3 := sqrt3_real - (0 : ℝ)
  subprob_diff_2_3_calc_mk :≡ diff_2_3 = Complex.mk real_part_2_3 imag_part_2_3
  subprob_diff_2_3_calc_mk_proof ⇐ show subprob_diff_2_3_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    <;> norm_num
    <;> ring
    <;> field_simp [sqrt2_real_def, sqrt3_real_def]
    <;> norm_num
    <;> ring
  subprob_normSq_2_3_calc :≡ Complex.normSq diff_2_3 = real_part_2_3^2 + imag_part_2_3^2
  subprob_normSq_2_3_calc_proof ⇐ show subprob_normSq_2_3_calc by
    simp [Complex.normSq, real_part_2_3_def, imag_part_2_3_def, subprob_diff_2_3_calc_mk_proof]
    <;> norm_num
    <;> ring
    <;> norm_num
    <;> ring
    <;> norm_num
  val_normSq_2_3 := (12 : ℝ) - (4 : ℝ) * sqrt2_real
  subprob_parts_2_3_sq_eval :≡ real_part_2_3^2 + imag_part_2_3^2 = val_normSq_2_3
  subprob_parts_2_3_sq_eval_proof ⇐ show subprob_parts_2_3_sq_eval by
    simp_all only [sub_eq_add_neg, add_assoc, add_left_comm, add_right_comm]
    norm_num
    ring
    <;> linarith [sqrt2_real_def, sqrt3_real_def]
  subprob_normSq_2_3_is_val :≡ Complex.normSq diff_2_3 = val_normSq_2_3
  subprob_normSq_2_3_is_val_proof ⇐ show subprob_normSq_2_3_is_val by
    simp_all [Complex.normSq, subprob_diff_2_3_calc_mk_proof, subprob_normSq_2_3_calc_proof,
      subprob_parts_2_3_sq_eval_proof, val_normSq_2_3_def]
    <;> ring
  subprob_val_normSq_2_3_le_Dmax :≡ val_normSq_2_3 ≤ D_max_sq_val
  subprob_val_normSq_2_3_le_Dmax_proof ⇐ show subprob_val_normSq_2_3_le_Dmax by
    simp_all only [Complex.normSq, Complex.re, Complex.im, sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_neg_one, mul_one, mul_zero, add_zero, zero_add, sub_zero, sub_neg_eq_add, add_assoc]
    norm_num
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  subprob_normSq_2_3_le_Dmax :≡ Complex.normSq diff_2_3 ≤ D_max_sq_val
  subprob_normSq_2_3_le_Dmax_proof ⇐ show subprob_normSq_2_3_le_Dmax by
    have h := subprob_val_normSq_2_3_le_Dmax_proof
    simp [val_normSq_2_3_def] at h ⊢
    linarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  diff_3_1 := a_3_val - b_1_val
  real_part_3_1 := (-1 : ℝ) - (8 : ℝ)
  imag_part_3_1 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_1_calc_mk :≡ diff_3_1 = Complex.mk real_part_3_1 imag_part_3_1
  subprob_diff_3_1_calc_mk_proof ⇐ show subprob_diff_3_1_calc_mk by
    simp_all [Complex.ext_iff, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    <;> norm_num
    <;> linarith [sqrt3_real_def, sqrt2_real_def]
  subprob_normSq_3_1_calc :≡ Complex.normSq diff_3_1 = real_part_3_1^2 + imag_part_3_1^2
  subprob_normSq_3_1_calc_proof ⇐ show subprob_normSq_3_1_calc by
    simp_all [Complex.normSq, Complex.ext_iff, pow_two]
    <;> norm_num
    <;> linarith [sqrt3_real_def, sqrt2_real_def]
  val_normSq_3_1 := (81 : ℝ) + (3 : ℝ)
  subprob_parts_3_1_sq_eval :≡ real_part_3_1^2 + imag_part_3_1^2 = val_normSq_3_1
  subprob_parts_3_1_sq_eval_proof ⇐ show subprob_parts_3_1_sq_eval by
    rw [real_part_3_1_def, imag_part_3_1_def]
    norm_num [sqrt3_real_def, val_normSq_3_1_def]
    <;> linarith
  subprob_normSq_3_1_is_84 :≡ Complex.normSq diff_3_1 = (84:ℝ)
  subprob_normSq_3_1_is_84_proof ⇐ show subprob_normSq_3_1_is_84 by
    rw [subprob_diff_3_1_calc_mk_proof]
    simp [real_part_3_1_def, imag_part_3_1_def, sqrt3_real_def]
    norm_num
    <;> linarith
  subprob_normSq_3_1_le_Dmax :≡ Complex.normSq diff_3_1 ≤ D_max_sq_val
  subprob_normSq_3_1_le_Dmax_proof ⇐ show subprob_normSq_3_1_le_Dmax by
    have h1 : Complex.normSq diff_3_1 = 84 := subprob_normSq_3_1_is_84_proof
    linarith [D_max_sq_val_def]
  diff_3_2 := a_3_val - b_2_val
  real_part_3_2 := (-1 : ℝ) - ((2 : ℝ) * sqrt2_real)
  imag_part_3_2 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_2_calc_mk :≡ diff_3_2 = Complex.mk real_part_3_2 imag_part_3_2
  subprob_diff_3_2_calc_mk_proof ⇐ show subprob_diff_3_2_calc_mk by
    rw [diff_3_2_def, a_3_val_def, b_2_val_def]
    simp [Complex.ext_iff, real_part_3_2_def, imag_part_3_2_def]
    <;> norm_num
    <;> simp_all
  subprob_normSq_3_2_calc :≡ Complex.normSq diff_3_2 = real_part_3_2^2 + imag_part_3_2^2
  subprob_normSq_3_2_calc_proof ⇐ show subprob_normSq_3_2_calc by
    rw [subprob_diff_3_2_calc_mk_proof]
    simp [Complex.normSq]
    <;> norm_num
    <;> linarith [sqrt2_real_def, sqrt3_real_def]
  subprob_parts_3_2_sq_eval :≡ real_part_3_2^2 + imag_part_3_2^2 = val_normSq_2_2
  subprob_parts_3_2_sq_eval_proof ⇐ show subprob_parts_3_2_sq_eval by
    simp_all only [Complex.normSq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    norm_num
    ring
    <;> simp [sqrt2_real_def, sqrt3_real_def]
    <;> norm_num
    <;> ring
  subprob_normSq_3_2_is_val :≡ Complex.normSq diff_3_2 = val_normSq_2_2
  subprob_normSq_3_2_is_val_proof ⇐ show subprob_normSq_3_2_is_val by
    simp [real_part_3_2_def, imag_part_3_2_def, val_normSq_2_2_def]
    norm_num
    ring
    <;> norm_num
    <;> linarith [sqrt2_real_def, sqrt3_real_def]
  subprob_normSq_3_2_le_Dmax :≡ Complex.normSq diff_3_2 ≤ D_max_sq_val
  subprob_normSq_3_2_le_Dmax_proof ⇐ show subprob_normSq_3_2_le_Dmax by
    have h₀ : Complex.normSq diff_3_2 = val_normSq_2_2 := subprob_normSq_3_2_is_val_proof
    have h₁ : val_normSq_2_2 ≤ D_max_sq_val := subprob_val_normSq_2_2_le_Dmax_proof
    linarith
  diff_3_3 := a_3_val - b_3_val
  real_part_3_3 := (-1 : ℝ) - (- (2 : ℝ) * sqrt2_real)
  imag_part_3_3 := (-sqrt3_real) - (0 : ℝ)
  subprob_diff_3_3_calc_mk :≡ diff_3_3 = Complex.mk real_part_3_3 imag_part_3_3
  subprob_diff_3_3_calc_mk_proof ⇐ show subprob_diff_3_3_calc_mk by
    rw [diff_3_3_def, a_3_val_def, b_3_val_def]
    simp [Complex.ext_iff, real_part_3_3_def, imag_part_3_3_def, sub_eq_add_neg, mul_neg, mul_comm]
    <;> norm_num
    <;> ring
  subprob_normSq_3_3_calc :≡ Complex.normSq diff_3_3 = real_part_3_3^2 + imag_part_3_3^2
  subprob_normSq_3_3_calc_proof ⇐ show subprob_normSq_3_3_calc by
    simp [Complex.normSq, subprob_diff_3_3_calc_mk_proof, real_part_3_3_def, imag_part_3_3_def]
    norm_num
    ring
    <;> simp [sqrt2_real_def, sqrt3_real_def]
    <;> norm_num
    <;> ring
  subprob_parts_3_3_sq_eval :≡ real_part_3_3^2 + imag_part_3_3^2 = val_normSq_2_3
  subprob_parts_3_3_sq_eval_proof ⇐ show subprob_parts_3_3_sq_eval by
    simp_all only [sub_eq_add_neg, neg_mul, neg_neg, mul_neg, mul_one, mul_add, mul_sub, mul_comm]
    norm_num
    <;> ring
    <;> norm_num
    <;> ring
  subprob_normSq_3_3_is_val :≡ Complex.normSq diff_3_3 = val_normSq_2_3
  subprob_normSq_3_3_is_val_proof ⇐ show subprob_normSq_3_3_is_val by
    simp_all [Complex.normSq, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    <;> norm_num
    <;> linarith [sqrt2_real_def, sqrt3_real_def]
  subprob_normSq_3_3_le_Dmax :≡ Complex.normSq diff_3_3 ≤ D_max_sq_val
  subprob_normSq_3_3_le_Dmax_proof ⇐ show subprob_normSq_3_3_le_Dmax by
    have h₀ : val_normSq_2_3 ≤ D_max_sq_val := subprob_val_normSq_2_3_le_Dmax_proof
    have h₁ : Complex.normSq diff_3_3 = val_normSq_2_3 := subprob_normSq_3_3_is_val_proof
    linarith [h₀, h₁]
  subprob_main_goal_normSq_le_84 :≡ Complex.normSq (a - b) ≤ D_max_sq_val
  subprob_main_goal_normSq_le_84_proof ⇐ show subprob_main_goal_normSq_le_84 by
    rcases hA_cases with rfl | rfl | rfl
    .
      rcases hB_cases with rfl | rfl | rfl
      .
        rw [← diff_1_1_def]
        exact subprob_normSq_1_1_le_Dmax_proof
      .
        rw [← diff_1_2_def]
        exact subprob_normSq_1_2_le_Dmax_proof
      .
        rw [← diff_1_3_def]
        exact subprob_normSq_1_3_le_Dmax_proof
    .
      rcases hB_cases with rfl | rfl | rfl
      .
        rw [← diff_2_1_def]
        exact subprob_normSq_2_1_le_Dmax_proof
      .
        rw [← diff_2_2_def]
        exact subprob_normSq_2_2_le_Dmax_proof
      .
        rw [← diff_2_3_def]
        exact subprob_normSq_2_3_le_Dmax_proof
    .
      rcases hB_cases with rfl | rfl | rfl
      .
        rw [← diff_3_1_def]
        exact subprob_normSq_3_1_le_Dmax_proof
      .
        rw [← diff_3_2_def]
        exact subprob_normSq_3_2_le_Dmax_proof
      .
        rw [← diff_3_3_def]
        exact subprob_normSq_3_3_le_Dmax_proof
  subprob_final_goal :≡ Complex.abs (a - b) ≤ target_bound_val
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    rw [subprob_target_equiv_normSq_proof]
    exact subprob_main_goal_normSq_le_84_proof
  original_target :≡ Complex.abs (a - b) ≤ (2 : ℝ) * √(21 : ℝ)
  original_target_proof ⇐ show original_target by
    have h₀ : Complex.abs (a - b) ≤ target_bound_val := subprob_final_goal_proof
    rw [target_bound_val_def] at h₀
    have h₁ : Complex.abs (a - b) ≤ 2 * √(21 : ℝ) := h₀
    exact h₁
-/
