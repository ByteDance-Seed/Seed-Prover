import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem imo_1992_p1 (p q r : ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r) (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ p * q * r - 1) : (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) := by
  elim_exists ⟨n, hn_def⟩ := h₁
  have subprob_p_minus_1_pos_proof : p - 1 > 0 := by
    mkOpaque
    rcases h₀ with ⟨h_p_gt_1, h_p_lt_q, h_q_lt_r⟩
    rw [gt_iff_lt]
    rw [Int.sub_pos]
    exact h_p_gt_1
  have subprob_q_minus_1_pos_proof : q - 1 > 0 := by
    mkOpaque
    rw [gt_iff_lt, Int.sub_pos]
    have h_1_lt_p : 1 < p := by
      rw [← Int.sub_pos]
      exact subprob_p_minus_1_pos_proof
    rcases h₀ with ⟨_, ⟨h_p_lt_q, _⟩⟩
    apply lt_trans h_1_lt_p
    exact h_p_lt_q
  have subprob_r_minus_1_pos_proof : r - 1 > 0 := by
    mkOpaque
    rcases h₀ with ⟨h_1_lt_p, h_pq_and_qr⟩
    rcases h_pq_and_qr with ⟨h_p_lt_q, h_q_lt_r⟩
    have h_1_lt_q : (1 : ℤ) < q := by apply lt_trans h_1_lt_p h_p_lt_q
    have h_1_lt_r : (1 : ℤ) < r := by apply lt_trans h_1_lt_q h_q_lt_r
    apply sub_pos_of_lt h_1_lt_r
  letI denominator_val :=
    (p - 1) * (q - 1) *
      (r - 1)
  retro' denominator_val_def : denominator_val = (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) := by funext; rfl
  have subprob_denominator_pos_proof : denominator_val > 0 := by
    mkOpaque
    rw [denominator_val_def]
    have h_first_two_factors_pos : (p - (1 : ℤ)) * (q - (1 : ℤ)) > 0 := by
      apply mul_pos
      exact subprob_p_minus_1_pos_proof
      exact subprob_q_minus_1_pos_proof
    apply mul_pos
    exact h_first_two_factors_pos
    exact subprob_r_minus_1_pos_proof
  letI numerator_val :=
    p * q * r -
      1
  retro' numerator_val_def : numerator_val = p * q * r - (1 : ℤ) := by funext; rfl
  have subprob_numerator_pos_proof : numerator_val > 0 := by
    mkOpaque
    rw [numerator_val_def]
    rw [hn_def]
    rw [← denominator_val_def]
    apply (Int.mul_pos subprob_denominator_pos_proof)
    have h_expansion : p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) + (p - 1) * (q - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1) + (p - 1) + (q - 1) + (r - 1) := by ring
    let sop : ℤ := (p - 1) * (q - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1) + (p - 1) + (q - 1) + (r - 1)
    have h_num_eq_den_plus_sop : p * q * r - 1 = denominator_val + sop := by
      rw [denominator_val_def]
      conv_rhs =>
        dsimp only [sop]
        simp only [← Int.add_assoc]
      exact h_expansion
    have h_sop_eq_den_mul_n_minus_1 : sop = denominator_val * (n - 1) := by
      have h_prqr_eq_den_mul_n : p * q * r - 1 = denominator_val * n := by rw [hn_def, denominator_val_def]
      have h_intermediate_eq : denominator_val + sop = denominator_val * n := by rw [← h_num_eq_den_plus_sop, h_prqr_eq_den_mul_n]
      linarith [h_intermediate_eq]
    have hp1_ge_1 : p - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_p_minus_1_pos_proof
    have hq1_ge_1 : q - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_q_minus_1_pos_proof
    have hr1_ge_1 : r - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_r_minus_1_pos_proof
    have hpq_ge_1 : (p - 1) * (q - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hp1_ge_1 hq1_ge_1
    have hpr_ge_1 : (p - 1) * (r - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hp1_ge_1 hr1_ge_1
    have hqr_ge_1 : (q - 1) * (r - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hq1_ge_1 hr1_ge_1
    have h_sop_ge_6 : sop ≥ 6 := by linarith [hp1_ge_1, hq1_ge_1, hr1_ge_1, hpq_ge_1, hpr_ge_1, hqr_ge_1]
    have h_sop_pos : sop > 0 := by linarith [h_sop_ge_6]
    rw [h_sop_eq_den_mul_n_minus_1] at h_sop_pos
    have h_n_minus_1_pos : n - 1 > 0 := (mul_pos_iff_of_pos_left subprob_denominator_pos_proof).mp h_sop_pos
    have h_n_minus_1_ge_1 : n - 1 ≥ 1 := Int.pos_iff_one_le.mp h_n_minus_1_pos
    linarith [h_n_minus_1_ge_1]
  have subprob_n_pos_proof : n ≥ 1 := by
    mkOpaque
    have h_relation : numerator_val = denominator_val * n := by simp [numerator_val_def, denominator_val_def, hn_def]
    have h_prod_pos : denominator_val * n > 0 := by
      rw [← h_relation]
      exact subprob_numerator_pos_proof
    have n_pos : n > 0 := by
      apply (mul_pos_iff_of_pos_left subprob_denominator_pos_proof).mp
      exact h_prod_pos
    apply (Int.pos_iff_one_le).mp
    exact n_pos
  have subprob_n_lt_prod_fractions_real_proof : (n : ℝ) < ((p : ℝ) / ((p : ℝ) - 1)) * ((q : ℝ) / ((q : ℝ) - 1)) * ((r : ℝ) / ((r : ℝ) - 1)) := by
    mkOpaque
    let pr := (p : ℝ)
    let qr := (q : ℝ)
    let rr := (r : ℝ)
    let nr := (n : ℝ)
    have h_pr_minus_1_pos : pr - 1 > 0 := by
      rw [← Int.cast_one, ← Int.cast_sub p 1, gt_iff_lt, Int.cast_pos]
      exact subprob_p_minus_1_pos_proof
    have h_qr_minus_1_pos : qr - 1 > 0 := by
      rw [← Int.cast_one, ← Int.cast_sub q 1, gt_iff_lt, Int.cast_pos]
      exact subprob_q_minus_1_pos_proof
    have h_rr_minus_1_pos : rr - 1 > 0 := by
      rw [← Int.cast_one, ← Int.cast_sub r 1, gt_iff_lt, Int.cast_pos]
      exact subprob_r_minus_1_pos_proof
    have h_pr_minus_1_ne_zero : pr - 1 ≠ 0 := by exact ne_of_gt h_pr_minus_1_pos
    have h_qr_minus_1_ne_zero : qr - 1 ≠ 0 := by exact ne_of_gt h_qr_minus_1_pos
    have h_rr_minus_1_ne_zero : rr - 1 ≠ 0 := by exact ne_of_gt h_rr_minus_1_pos
    have h_rhs_expr : ((p : ℝ) / ((p : ℝ) - 1)) * ((q : ℝ) / ((q : ℝ) - 1)) * ((r : ℝ) / ((r : ℝ) - 1)) = (pr * qr * rr) / ((pr - 1) * (qr - 1) * (rr - 1)) := by field_simp [h_pr_minus_1_ne_zero, h_qr_minus_1_ne_zero, h_rr_minus_1_ne_zero]
    rw [h_rhs_expr]
    have hn_def_real : (pr * qr * rr - 1) = ((pr - 1) * (qr - 1) * (rr - 1)) * nr := by
      simp only [pr, qr, rr, nr]
      norm_cast
    let den_real := (pr - 1) * (qr - 1) * (rr - 1)
    have h_den_real_pos : den_real > 0 := by exact mul_pos (mul_pos h_pr_minus_1_pos h_qr_minus_1_pos) h_rr_minus_1_pos
    have h_den_real_ne_zero : den_real ≠ 0 := by exact ne_of_gt h_den_real_pos
    have h_nr_expr : nr = (pr * qr * rr - 1) / den_real := by
      apply (eq_div_iff h_den_real_ne_zero).mpr
      rw [hn_def_real]
      apply mul_comm
    change nr < pr * qr * rr / ((pr - (1 : ℝ)) * (qr - (1 : ℝ)) * (rr - (1 : ℝ)))
    rw [h_nr_expr]
    apply (div_lt_div_right h_den_real_pos).mpr
    exact sub_one_lt (pr * qr * rr)
  letI f := fun (x : ℝ) => x / (x - 1)
  retro' f_def : f = fun (x : ℝ) => x / (x - (1 : ℝ)) := by funext; rfl
  retro' f_def' : ∀ (x : ℝ), f x = x / (x - (1 : ℝ)) := by intros; rfl
  have subprob_f_decreasing_proof : ∀ (x₁ x₂ : ℝ), 1 < x₁ → x₁ < x₂ → f x₂ < f x₁ := by
    mkOpaque
    intros x₁ x₂ h_x1_gt_1 h_x1_lt_x2
    rw [f_def' x₂, f_def' x₁]
    have hx1m1_pos : x₁ - 1 > 0 := by linarith [h_x1_gt_1]
    have hx2m1_pos : x₂ - 1 > 0 := by linarith [h_x1_gt_1, h_x1_lt_x2]
    apply (div_lt_div_iff hx2m1_pos hx1m1_pos).mpr
    simp only [mul_sub, mul_one]
    rw [mul_comm x₂ x₁]
    apply (sub_lt_sub_iff_left (x₁ * x₂)).mpr
    exact h_x1_lt_x2
  have subprob_p_frac_le_5_4_proof : p ≥ (5 : ℤ) → (↑(p) : ℝ) / ((↑(p) : ℝ) - (1 : ℝ)) ≤ (5 : ℝ) / (4 : ℝ) := by
    intro h_p_ge_5
    exact
      show (p : ℝ) / ((p : ℝ) - 1) ≤ (5 : ℝ) / (4 : ℝ) by
        mkOpaque
        rw [← f_def' (p : ℝ)]
        have h_f_5_eval : f (5 : ℝ) = (5 : ℝ) / (4 : ℝ) := by
          rw [f_def']
          have h_denom_5 : (5 : ℝ) - (1 : ℝ) = (4 : ℝ) := by norm_num
          rw [h_denom_5]
        rw [← h_f_5_eval]
        have h_p_ge_5_real : (p : ℝ) ≥ (5 : ℝ) := by norm_cast
        rcases h_p_ge_5_real.eq_or_gt with h_p_eq_5 | h_p_gt_5
        . rw [h_p_eq_5]
        . have h_1_lt_5 : (1 : ℝ) < (5 : ℝ) := by norm_num
          have h_f_strict_ineq : f (p : ℝ) < f (5 : ℝ) := subprob_f_decreasing_proof (5 : ℝ) (p : ℝ) h_1_lt_5 h_p_gt_5
          exact le_of_lt h_f_strict_ineq
  have subprob_q_ge_6_proof : p ≥ (5 : ℤ) → q ≥ (6 : ℤ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    exact
      show q ≥ 6 by
        mkOpaque
        linarith [h₀.2.1, h_p_ge_5]
  have subprob_q_frac_le_6_5_proof : p ≥ (5 : ℤ) → (↑(q) : ℝ) / ((↑(q) : ℝ) - (1 : ℝ)) ≤ (6 : ℝ) / (5 : ℝ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    retro' subprob_q_ge_6_proof := subprob_q_ge_6_proof h_p_ge_5
    exact
      show (q : ℝ) / ((q : ℝ) - 1) ≤ (6 : ℝ) / (5 : ℝ) by
        mkOpaque
        rw [← f_def' (q : ℝ)]
        have h_f6_eval : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by
          rw [f_def' (6 : ℝ)]
          norm_num
        rw [← h_f6_eval]
        have h_one_lt_six : (1 : ℝ) < (6 : ℝ) := by norm_num
        have h_one_lt_q_int : (1 : ℤ) < q := by apply lt_trans h₀.1 h₀.2.1
        have h_one_lt_q_real : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h_one_lt_q_int
        rcases(LE.le.eq_or_gt subprob_q_ge_6_proof) with h_q_eq_6_int | h_q_gt_6_int
        . rw [h_q_eq_6_int]
          apply le_refl
        . have h_6_lt_q_real : (6 : ℝ) < (q : ℝ) := by exact_mod_cast h_q_gt_6_int
          have h_f_q_lt_f_6 : f (q : ℝ) < f (6 : ℝ) := by
            apply subprob_f_decreasing_proof (6 : ℝ) (q : ℝ)
            . exact h_one_lt_six
            . exact h_6_lt_q_real
          apply le_of_lt
          exact h_f_q_lt_f_6
  have subprob_r_ge_7_proof : p ≥ (5 : ℤ) → r ≥ (7 : ℤ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    retro' subprob_q_ge_6_proof := subprob_q_ge_6_proof h_p_ge_5
    retro' subprob_q_frac_le_6_5_proof := subprob_q_frac_le_6_5_proof h_p_ge_5
    exact
      show
        r ≥ 7
        by
        mkOpaque
        have h_q_lt_r : q < r := h₀.2.2
        have h_q_plus_1_le_r : q + 1 ≤ r := by exact h_q_lt_r
        have h_q_ge_6 : q ≥ (6 : ℤ) := subprob_q_ge_6_proof
        have h_seven_le_q_plus_1 : (7 : ℤ) ≤ q + 1 :=
          by
          have h_six_plus_one_le_q_plus_one : (6 : ℤ) + 1 ≤ q + 1 := by
            apply Int.add_le_add_right
            exact h_q_ge_6
          have h_seven_eq_six_plus_one : (7 : ℤ) = (6 : ℤ) + 1 := by norm_num
          rw [h_seven_eq_six_plus_one]
          exact h_six_plus_one_le_q_plus_one
        apply le_trans
        · exact h_seven_le_q_plus_1
        · exact h_q_plus_1_le_r
  have subprob_r_frac_le_7_6_proof : p ≥ (5 : ℤ) → (↑(r) : ℝ) / ((↑(r) : ℝ) - (1 : ℝ)) ≤ (7 : ℝ) / (6 : ℝ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    retro' subprob_q_ge_6_proof := subprob_q_ge_6_proof h_p_ge_5
    retro' subprob_q_frac_le_6_5_proof := subprob_q_frac_le_6_5_proof h_p_ge_5
    retro' subprob_r_ge_7_proof := subprob_r_ge_7_proof h_p_ge_5
    exact
      show (r : ℝ) / ((r : ℝ) - 1) ≤ (7 : ℝ) / (6 : ℝ) by
        mkOpaque
        have h_lhs_eq_f_r : (r : ℝ) / ((r : ℝ) - 1) = f (r : ℝ) := by rw [f_def' (r : ℝ)]
        have h_rhs_eq_f_7 : (7 : ℝ) / (6 : ℝ) = f (7 : ℝ) := by
          rw [f_def' (7 : ℝ)]
          have h_denom_7 : (7 : ℝ) - 1 = (6 : ℝ) := by norm_num
          rw [h_denom_7]
        rw [h_lhs_eq_f_r, h_rhs_eq_f_7]
        have hr_ge_7_real : (r : ℝ) ≥ (7 : ℝ) := by exact Int.cast_le.mpr subprob_r_ge_7_proof
        rcases hr_ge_7_real.eq_or_gt with hr_eq_7 | hr_gt_7
        . rw [hr_eq_7]
        . have h_7_gt_1 : (1 : ℝ) < (7 : ℝ) := by norm_num
          have f_r_lt_f_7 : f (r : ℝ) < f (7 : ℝ) := by apply subprob_f_decreasing_proof (7 : ℝ) (r : ℝ) h_7_gt_1 hr_gt_7
          apply le_of_lt
          exact f_r_lt_f_7
  have subprob_n_lt_7_4_real_proof : p ≥ (5 : ℤ) → (↑(n) : ℝ) < (7 : ℝ) / (4 : ℝ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    retro' subprob_q_ge_6_proof := subprob_q_ge_6_proof h_p_ge_5
    retro' subprob_q_frac_le_6_5_proof := subprob_q_frac_le_6_5_proof h_p_ge_5
    retro' subprob_r_ge_7_proof := subprob_r_ge_7_proof h_p_ge_5
    retro' subprob_r_frac_le_7_6_proof := subprob_r_frac_le_7_6_proof h_p_ge_5
    exact
      show (n : ℝ) < (7 : ℝ) / (4 : ℝ) by
        mkOpaque
        have p_minus_1_real_pos : (↑p : ℝ) - 1 > 0 := by
          rw [← Int.cast_one, ← Int.cast_sub, gt_iff_lt, Int.cast_pos]
          exact subprob_p_minus_1_pos_proof
        have q_minus_1_real_pos : (↑q : ℝ) - 1 > 0 := by
          rw [← Int.cast_one, ← Int.cast_sub, gt_iff_lt, Int.cast_pos]
          exact subprob_q_minus_1_pos_proof
        have r_minus_1_real_pos : (↑r : ℝ) - 1 > 0 := by
          rw [← Int.cast_one, ← Int.cast_sub, gt_iff_lt, Int.cast_pos]
          exact subprob_r_minus_1_pos_proof
        have p_gt_1 : p > 1 := h₀.1
        have p_real_pos : (↑p : ℝ) > 0 := by
          apply Int.cast_pos.mpr
          linarith [p_gt_1]
        have q_gt_p : p < q := h₀.2.1
        have q_real_pos : (↑q : ℝ) > 0 := by
          apply Int.cast_pos.mpr
          have q_gt_1 : q > 1 := by linarith [p_gt_1, q_gt_p]
          linarith [q_gt_1]
        have r_gt_q : q < r := h₀.2.2
        have r_real_pos : (↑r : ℝ) > 0 := by
          apply Int.cast_pos.mpr
          have q_gt_1 : q > 1 := by linarith [p_gt_1, q_gt_p]
          have r_gt_1 : r > 1 := by linarith [q_gt_1, r_gt_q]
          linarith [r_gt_1]
        have val_p_frac_pos : (↑p : ℝ) / (↑p - 1) > 0 := div_pos p_real_pos p_minus_1_real_pos
        have val_q_frac_pos : (↑q : ℝ) / (↑q - 1) > 0 := div_pos q_real_pos q_minus_1_real_pos
        have val_r_frac_pos : (↑r : ℝ) / (↑r - 1) > 0 := div_pos r_real_pos r_minus_1_real_pos
        have five_fourths_pos : (5 : ℝ) / 4 > 0 := by norm_num
        have six_fifths_pos : (6 : ℝ) / 5 > 0 := by norm_num
        have h_prod_pq_le : (↑p : ℝ) / (↑p - 1) * ((↑q : ℝ) / (↑q - 1)) ≤ (5 / 4 : ℝ) * (6 / 5 : ℝ) := by
          apply mul_le_mul
          · exact subprob_p_frac_le_5_4_proof
          · exact subprob_q_frac_le_6_5_proof
          · exact le_of_lt val_q_frac_pos
          · exact le_of_lt five_fourths_pos
        have five_fourths_mul_six_fifths_pos : (5 / 4 : ℝ) * (6 / 5 : ℝ) > 0 := by apply mul_pos five_fourths_pos six_fifths_pos
        have h_prod_pqr_le : ((↑p : ℝ) / (↑p - 1)) * ((↑q : ℝ) / (↑q - 1)) * ((↑r : ℝ) / (↑r - 1)) ≤ ((5 : ℝ) / 4) * ((6 : ℝ) / 5) * ((7 : ℝ) / 6) := by
          apply mul_le_mul
          · exact h_prod_pq_le
          · exact subprob_r_frac_le_7_6_proof
          · exact le_of_lt val_r_frac_pos
          · exact le_of_lt five_fourths_mul_six_fifths_pos
        have h_rhs_value : ((5 : ℝ) / 4) * ((6 : ℝ) / 5) * ((7 : ℝ) / 6) = (7 : ℝ) / 4 := by norm_num
        rw [h_rhs_value] at h_prod_pqr_le
        exact lt_of_lt_of_le subprob_n_lt_prod_fractions_real_proof h_prod_pqr_le
  have subprob_n_eq_1_if_p_ge_5_proof : p ≥ (5 : ℤ) → n = (1 : ℤ) := by
    intro h_p_ge_5
    retro' subprob_p_frac_le_5_4_proof := subprob_p_frac_le_5_4_proof h_p_ge_5
    retro' subprob_q_ge_6_proof := subprob_q_ge_6_proof h_p_ge_5
    retro' subprob_q_frac_le_6_5_proof := subprob_q_frac_le_6_5_proof h_p_ge_5
    retro' subprob_r_ge_7_proof := subprob_r_ge_7_proof h_p_ge_5
    retro' subprob_r_frac_le_7_6_proof := subprob_r_frac_le_7_6_proof h_p_ge_5
    retro' subprob_n_lt_7_4_real_proof := subprob_n_lt_7_4_real_proof h_p_ge_5
    exact
      show n = 1 by
        mkOpaque
        have h_n_lt_2_real : (n : ℝ) < 2 := by linarith [subprob_n_lt_7_4_real_proof]
        have h_n_lt_2 : n < 2 := by exact Int.cast_lt.mp h_n_lt_2_real
        have h_n_eq_1 : n = 1 := by linarith [subprob_n_pos_proof, h_n_lt_2]
        exact h_n_eq_1
  have subprob_n1_equation_proof : n = (1 : ℤ) → p * q * r - (1 : ℤ) = (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) := by
    intro h_n_eq_1
    exact
      show p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) by
        mkOpaque
        rw [hn_def]
        rw [h_n_eq_1]
        ring
  have subprob_n1_expanded_proof : n = (1 : ℤ) → (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) = p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ) := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    exact
      show (p - 1) * (q - 1) * (r - 1) = p * q * r - (p * q + p * r + q * r) + (p + q + r) - 1 by
        mkOpaque
        ring
  have subprob_n1_simplified_proof : n = (1 : ℤ) → p * q + p * r + q * r = p + q + r := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    exact
      show p * q + p * r + q * r = p + q + r by
        mkOpaque
        have h_combined : p * q * r - (1 : ℤ) = p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ) := by exact Eq.trans subprob_n1_equation_proof subprob_n1_expanded_proof
        have h_eq_zero : (p * q * r - (1 : ℤ)) - (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ)) = 0 := by
          rw [h_combined]
          exact sub_self (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ))
        have h_simplified_lhs : (p * q * r - (1 : ℤ)) - (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ)) = (p * q + p * r + q * r) - (p + q + r) := by ring
        rw [h_simplified_lhs] at h_eq_zero
        exact eq_of_sub_eq_zero h_eq_zero
  have subprob_p_lt_pq_proof : n = (1 : ℤ) → p < p * q := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    retro' subprob_n1_simplified_proof := subprob_n1_simplified_proof h_n_eq_1
    exact
      show p < p * q by
        mkOpaque
        have h_1_lt_p : (1 : ℤ) < p := h₀.1
        have h_p_pos : 0 < p := lt_trans (by norm_num : (0 : ℤ) < 1) h_1_lt_p
        rw [← Int.mul_one p]
        have h_p_mul_1_pos : p * (1 : ℤ) > 0 := mul_pos h_p_pos (zero_lt_one : (0 : ℤ) < 1)
        rw [← mul_one (p * (1 : ℤ))]
        rw [mul_assoc (p * (1 : ℤ)) (1 : ℤ) q]
        rw [mul_lt_mul_iff_of_pos_left h_p_mul_1_pos]
        simp only [one_mul]
        have h_p_lt_q : p < q := h₀.2.1
        have h_1_lt_q : 1 < q := lt_trans h_1_lt_p h_p_lt_q
        exact h_1_lt_q
  have subprob_q_lt_qr_proof : n = (1 : ℤ) → q < q * r := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    retro' subprob_n1_simplified_proof := subprob_n1_simplified_proof h_n_eq_1
    retro' subprob_p_lt_pq_proof := subprob_p_lt_pq_proof h_n_eq_1
    exact
      show q < q * r by
        mkOpaque
        rcases h₀ with ⟨h_1_lt_p, h_p_lt_q, h_q_lt_r⟩
        have h_1_lt_q : (1 : ℤ) < q := by apply lt_trans h_1_lt_p h_p_lt_q
        have h_q_pos : (0 : ℤ) < q := by linarith [h_1_lt_q]
        rw [← mul_one q]
        rw [mul_assoc q (1 : ℤ) r]
        rw [mul_lt_mul_iff_of_pos_left h_q_pos]
        simp only [one_mul]
        have h_1_lt_r : (1 : ℤ) < r := by apply lt_trans h_1_lt_q h_q_lt_r
        exact h_1_lt_r
  have subprob_r_lt_rp_proof : n = (1 : ℤ) → r < r * p := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    retro' subprob_n1_simplified_proof := subprob_n1_simplified_proof h_n_eq_1
    retro' subprob_p_lt_pq_proof := subprob_p_lt_pq_proof h_n_eq_1
    retro' subprob_q_lt_qr_proof := subprob_q_lt_qr_proof h_n_eq_1
    exact
      show r < r * p by
        mkOpaque
        rcases h₀ with ⟨h_p_gt_1, h_p_lt_q, h_q_lt_r⟩
        have h_r_pos : 0 < r := by linarith [h_p_gt_1, h_p_lt_q, h_q_lt_r]
        rw [mul_comm r p]
        apply (lt_mul_iff_one_lt_left h_r_pos).mpr
        exact h_p_gt_1
  have subprob_sum_lt_sum_prod_proof : n = (1 : ℤ) → p + q + r < p * q + p * r + q * r := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    retro' subprob_n1_simplified_proof := subprob_n1_simplified_proof h_n_eq_1
    retro' subprob_p_lt_pq_proof := subprob_p_lt_pq_proof h_n_eq_1
    retro' subprob_q_lt_qr_proof := subprob_q_lt_qr_proof h_n_eq_1
    retro' subprob_r_lt_rp_proof := subprob_r_lt_rp_proof h_n_eq_1
    exact
      show p + q + r < p * q + p * r + q * r by
        mkOpaque
        have h_p_lt_pq : p < p * q := subprob_p_lt_pq_proof
        have h_q_lt_qr : q < q * r := subprob_q_lt_qr_proof
        have h_r_lt_rp_orig : r < r * p := subprob_r_lt_rp_proof
        have h_r_lt_pr : r < p * r := by
          rw [mul_comm p r]
          exact h_r_lt_rp_orig
        have h_p_plus_q_lt_pq_plus_qr : p + q < p * q + q * r := by
          apply @_root_.add_lt_add
          exact h_p_lt_pq
          exact h_q_lt_qr
        have h_sum_unordered_rhs : p + q + r < p * q + q * r + p * r := by
          apply @_root_.add_lt_add
          exact h_p_plus_q_lt_pq_plus_qr
          exact h_r_lt_pr
        have h_rhs_reorder_eq : p * q + q * r + p * r = p * q + p * r + q * r := by
          rw [add_assoc (p * q) (q * r) (p * r)]
          rw [add_comm (q * r) (p * r)]
          rw [← add_assoc (p * q) (p * r) (q * r)]
        rw [h_rhs_reorder_eq] at h_sum_unordered_rhs
        exact h_sum_unordered_rhs
  have subprob_n1_impossible_proof : n = (1 : ℤ) → False := by
    intro h_n_eq_1
    retro' subprob_n1_equation_proof := subprob_n1_equation_proof h_n_eq_1
    retro' subprob_n1_expanded_proof := subprob_n1_expanded_proof h_n_eq_1
    retro' subprob_n1_simplified_proof := subprob_n1_simplified_proof h_n_eq_1
    retro' subprob_p_lt_pq_proof := subprob_p_lt_pq_proof h_n_eq_1
    retro' subprob_q_lt_qr_proof := subprob_q_lt_qr_proof h_n_eq_1
    retro' subprob_r_lt_rp_proof := subprob_r_lt_rp_proof h_n_eq_1
    retro' subprob_sum_lt_sum_prod_proof := subprob_sum_lt_sum_prod_proof h_n_eq_1
    exact
      show False by
        mkOpaque
        have h_eq : p * q + p * r + q * r = p + q + r := subprob_n1_simplified_proof
        have h_lt : p + q + r < p * q + p * r + q * r := subprob_sum_lt_sum_prod_proof
        have h_contradiction : p + q + r < p + q + r := by
          rw [h_eq] at h_lt
          exact h_lt
        exact lt_irrefl (p + q + r) h_contradiction
  have subprob_p_lt_5_proof : p < 5 := by
    mkOpaque
    by_contra h_not_p_lt_5
    have hp_ge_5 : p ≥ 5 := by
      apply Int.not_lt.mp
      exact h_not_p_lt_5
    have hn_eq_1 : n = 1 := by
      apply subprob_n_eq_1_if_p_ge_5_proof
      exact hp_ge_5
    have h_false : False := by
      apply subprob_n1_impossible_proof
      exact hn_eq_1
    exact h_false
  have subprob_p_cases_proof : p = 2 ∨ p = 3 ∨ p = 4 := by
    mkOpaque
    have h_p_ge_2 : (2 : ℤ) ≤ p := by exact Int.add_one_le_of_lt h₀.1
    have h_p_le_4 : p ≤ (4 : ℤ) := by exact Int.le_sub_one_of_lt subprob_p_lt_5_proof
    interval_cases p
    . left
      rfl
    . right
      left
      rfl
    . right
      right
      rfl
  have subprob_n2_equation_proof : n = (2 : ℤ) → p * q * r - (1 : ℤ) = (2 : ℤ) * (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) := by
    intro h_n_eq_2
    exact
      show p * q * r - 1 = 2 * (p - 1) * (q - 1) * (r - 1) by
        mkOpaque
        rw [hn_def]
        rw [h_n_eq_2]
        ring
  have subprob_pqr_minus_1_even_proof : n = (2 : ℤ) → (p * q * r - (1 : ℤ)) % (2 : ℤ) = (0 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    exact
      show (p * q * r - 1) % 2 = 0 by
        mkOpaque
        rw [subprob_n2_equation_proof]
        have h_assoc : (2 : ℤ) * (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) = (2 : ℤ) * ((p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ))) := by ring
        rw [h_assoc]
        rw [← denominator_val_def]
        rw [Int.mul_comm (2 : ℤ) denominator_val]
        exact Int.mul_emod_left denominator_val (2 : ℤ)
  have subprob_pqr_odd_proof : n = (2 : ℤ) → p * q * r % (2 : ℤ) = (1 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    exact
      show (p * q * r) % 2 = 1 by
        mkOpaque
        rw [← Int.one_emod_two]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        . exact subprob_pqr_minus_1_even_proof
  have subprob_p_q_r_all_odd_proof : n = (2 : ℤ) → p % (2 : ℤ) = (1 : ℤ) ∧ q % (2 : ℤ) = (1 : ℤ) ∧ r % (2 : ℤ) = (1 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    exact
      show p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1 by
        mkOpaque
        rw [← Int.odd_iff]
        rw [← Int.odd_iff]
        rw [← Int.odd_iff]
        rw [← Int.odd_iff] at subprob_pqr_odd_proof
        rw [Int.odd_mul] at subprob_pqr_odd_proof
        rcases subprob_pqr_odd_proof with ⟨hpq_odd, hr_odd⟩
        rw [Int.odd_mul] at hpq_odd
        rcases hpq_odd with ⟨hp_odd, hq_odd⟩
        exact ⟨hp_odd, hq_odd, hr_odd⟩
  have subprob_p_eq_3_for_n2_proof : n = (2 : ℤ) → p = (3 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    exact
      show p = 3 by
        mkOpaque
        rcases subprob_p_q_r_all_odd_proof with ⟨hp_odd, _, _⟩
        rcases subprob_p_cases_proof with hp_eq_2 | hp_eq_3 | hp_eq_4
        . rw [hp_eq_2] at hp_odd
          change (0 : ℤ) = 1 at hp_odd
          norm_num at hp_odd
        . exact hp_eq_3
        . rw [hp_eq_4] at hp_odd
          change (0 : ℤ) = 1 at hp_odd
          norm_num at hp_odd
  have subprob_n2_p3_equation_proof : n = (2 : ℤ) → p = (3 : ℤ) → (3 : ℤ) * q * r - (1 : ℤ) = (2 : ℤ) * ((3 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → (3 : ℤ) * q * r - (1 : ℤ) = (2 : ℤ) * ((3 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) by
        intro h_p_eq_3_n2
        exact
          show 3 * q * r - 1 = 2 * (3 - 1) * (q - 1) * (r - 1) by
            mkOpaque
            rw [← h_p_eq_3_n2]
            exact subprob_n2_equation_proof
  have subprob_n2_p3_simplified_proof : n = (2 : ℤ) → p = (3 : ℤ) → (3 : ℤ) * q * r - (1 : ℤ) = (4 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → (3 : ℤ) * q * r - (1 : ℤ) = (4 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        exact
          show 3 * q * r - 1 = 4 * (q - 1) * (r - 1) by
            mkOpaque
            rw [subprob_n2_p3_equation_proof]
            ring
  have subprob_n2_p3_expanded_proof : n = (2 : ℤ) → p = (3 : ℤ) → (4 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) = (4 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r + (4 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → (4 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) = (4 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r + (4 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        exact
          show 4 * (q - 1) * (r - 1) = 4 * q * r - 4 * q - 4 * r + 4 by
            mkOpaque
            have h_expand_factors : (q - 1) * (r - 1) = q * r - q - r + 1 := by ring
            rw [mul_assoc (4 : ℤ) (q - 1) (r - 1)]
            rw [h_expand_factors]
            ring
  have subprob_n2_p3_rearranged_proof : n = (2 : ℤ) → p = (3 : ℤ) → q * r - (4 : ℤ) * q - (4 : ℤ) * r + (5 : ℤ) = (0 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → q * r - (4 : ℤ) * q - (4 : ℤ) * r + (5 : ℤ) = (0 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_p_eq_3_n2
        exact
          show q * r - 4 * q - 4 * r + 5 = 0 by
            mkOpaque
            have h_combined : (3 : ℤ) * q * r - (1 : ℤ) = (4 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r + (4 : ℤ) := by
              rw [subprob_n2_p3_simplified_proof]
              exact subprob_n2_p3_expanded_proof
            linarith [h_combined]
  have subprob_n2_p3_factorized_proof : n = (2 : ℤ) → p = (3 : ℤ) → (q - (4 : ℤ)) * (r - (4 : ℤ)) = (11 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_n_eq_2
    retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → (q - (4 : ℤ)) * (r - (4 : ℤ)) = (11 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_p_eq_3_n2
        retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_p_eq_3_n2
        exact
          show (q - 4) * (r - 4) = 11 by
            mkOpaque
            rw [← sub_eq_zero]
            have h_lhs_simplified : (q - 4) * (r - 4) - 11 = q * r - (4 : ℤ) * q - (4 : ℤ) * r + (5 : ℤ) := by ring
            rw [h_lhs_simplified]
            exact subprob_n2_p3_rearranged_proof
  have subprob_q_minus_4_pos_proof : n = (2 : ℤ) → p = (3 : ℤ) → q - (4 : ℤ) > (0 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_n_eq_2
    retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_n_eq_2
    retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → q - (4 : ℤ) > (0 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_p_eq_3_n2
        retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_p_eq_3_n2
        retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_p_eq_3_n2
        exact
          show q - 4 > 0 by
            mkOpaque
            rcases h₀ with ⟨_, hpq, _⟩
            rw [h_p_eq_3_n2] at hpq
            have h_q_ge_4 : q ≥ 4 := by linarith [hpq]
            have h_q_minus_4_ge_0 : q - 4 ≥ 0 := by exact Int.sub_nonneg_of_le h_q_ge_4
            have h_prod_eq_11 : (q - 4) * (r - 4) = 11 := subprob_n2_p3_factorized_proof
            have h_q_minus_4_ne_0 : q - 4 ≠ 0 := by
              intro h_q_minus_4_eq_0
              have h_prod_rewritten : (0 : ℤ) * (r - 4) = 11 := by
                rw [← h_q_minus_4_eq_0]
                exact h_prod_eq_11
              simp at h_prod_rewritten
            exact lt_of_le_of_ne h_q_minus_4_ge_0 (Ne.symm h_q_minus_4_ne_0)
  have subprob_q_eq_5_r_eq_15_for_n2_p3_proof : n = (2 : ℤ) → p = (3 : ℤ) → q = (5 : ℤ) ∧ r = (15 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_n_eq_2
    retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_n_eq_2
    retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_n_eq_2
    retro' subprob_q_minus_4_pos_proof := subprob_q_minus_4_pos_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → q = (5 : ℤ) ∧ r = (15 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_p_eq_3_n2
        retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_p_eq_3_n2
        retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_p_eq_3_n2
        retro' subprob_q_minus_4_pos_proof := subprob_q_minus_4_pos_proof h_p_eq_3_n2
        exact
          show q = 5 ∧ r = 15 by
            mkOpaque
            let a := q - (4 : ℤ)
            let b := r - (4 : ℤ)
            have h_ab_eq_11 : a * b = (11 : ℤ) := subprob_n2_p3_factorized_proof
            have h_a_pos : a > (0 : ℤ) := subprob_q_minus_4_pos_proof
            have h_11_pos : (11 : ℤ) > 0 := by norm_num
            have h_ab_pos : a * b > 0 := by
              rw [h_ab_eq_11]
              exact h_11_pos
            have h_b_pos : b > (0 : ℤ) := by
              apply (mul_pos_iff_of_pos_left h_a_pos).mp
              exact h_ab_pos
            have h_a_ge_0 : a ≥ 0 := Int.le_of_lt h_a_pos
            have h_b_ge_0 : b ≥ 0 := Int.le_of_lt h_b_pos
            rcases Int.eq_ofNat_of_zero_le h_a_ge_0 with ⟨a_nat, ha_nat_eq_a⟩
            rcases Int.eq_ofNat_of_zero_le h_b_ge_0 with ⟨b_nat, hb_nat_eq_b⟩
            have h_prod_nat_cast_eq_11 : (↑a_nat : ℤ) * (↑b_nat : ℤ) = (11 : ℤ) := by
              rw [← ha_nat_eq_a, ← hb_nat_eq_b]
              exact h_ab_eq_11
            have h_prod_nat_cast_mul_eq_11 : ↑(a_nat * b_nat) = (11 : ℤ) := by
              rw [Nat.cast_mul]
              exact h_prod_nat_cast_eq_11
            have eleven_int_eq_coe_11_nat : (11 : ℤ) = ↑(11 : ℕ) := by rfl
            rw [eleven_int_eq_coe_11_nat] at h_prod_nat_cast_mul_eq_11
            have h_a_nat_mul_b_nat_eq_11 : a_nat * b_nat = 11 := by apply Nat.cast_inj.mp h_prod_nat_cast_mul_eq_11
            have h_11_prime_nat : Nat.Prime 11 := by decide
            have h_cases_nat : (a_nat = 1 ∧ b_nat = 11) ∨ (a_nat = 11 ∧ b_nat = 1) := by
              have hdvd_a : a_nat ∣ 11 := by exact ⟨b_nat, h_a_nat_mul_b_nat_eq_11.symm⟩
              have ha_cases : a_nat = 1 ∨ a_nat = 11 := Nat.Prime.eq_one_or_self_of_dvd h_11_prime_nat a_nat hdvd_a
              rcases ha_cases with ha_eq_1 | ha_eq_11
              . rw [ha_eq_1, one_mul] at h_a_nat_mul_b_nat_eq_11
                left
                exact ⟨ha_eq_1, h_a_nat_mul_b_nat_eq_11⟩
              . rw [ha_eq_11] at h_a_nat_mul_b_nat_eq_11
                have h_11_pos_nat : (11 : ℕ) > 0 := Nat.Prime.pos h_11_prime_nat
                have h_11_ne_zero : (11 : ℕ) ≠ 0 := Nat.ne_of_gt h_11_pos_nat
                have hb_eq_1 : b_nat = 11 / 11 := Nat.eq_div_of_mul_eq_right h_11_ne_zero h_a_nat_mul_b_nat_eq_11
                have h_div_self_11 : 11 / 11 = 1 := Nat.div_self h_11_pos_nat
                rw [h_div_self_11] at hb_eq_1
                right
                exact ⟨ha_eq_11, hb_eq_1⟩
            have h_q_lt_r : q < r := h₀.2.2
            have h_a_lt_b : a < b := by exact sub_lt_sub_right h_q_lt_r 4
            rw [ha_nat_eq_a, hb_nat_eq_b] at h_a_lt_b
            have h_a_nat_lt_b_nat : a_nat < b_nat := by
              apply Int.lt_of_ofNat_lt_ofNat
              exact h_a_lt_b
            have h_final_case : a_nat = 1 ∧ b_nat = 11 := by
              rcases h_cases_nat with ⟨hc1_left, hc1_right⟩ | ⟨hc2_left, hc2_right⟩
              . exact And.intro hc1_left hc1_right
              . exfalso
                have : (11 : ℕ) < (1 : ℕ) := by rwa [hc2_left, hc2_right] at h_a_nat_lt_b_nat
                norm_num at this
            apply And.intro
            . have h_a_nat_eq_1 : a_nat = 1 := h_final_case.1
              have h_a_eq_1 : a = (1 : ℤ) := by simp [h_a_nat_eq_1, ha_nat_eq_a]
              rw [show (5 : ℤ) = (1 : ℤ) + (4 : ℤ) by norm_num]
              rw [← sub_eq_iff_eq_add]
              exact h_a_eq_1
            . have h_b_nat_eq_11 : b_nat = 11 := h_final_case.2
              have h_b_eq_11 : b = (11 : ℤ) := by simp [h_b_nat_eq_11, hb_nat_eq_b]
              rw [show (15 : ℤ) = (11 : ℤ) + (4 : ℤ) by norm_num]
              rw [← sub_eq_iff_eq_add]
              exact h_b_eq_11
  have subprob_sol1_proof : n = (2 : ℤ) → p = (3 : ℤ) → p = (3 : ℤ) ∧ q = (5 : ℤ) ∧ r = (15 : ℤ) := by
    intro h_n_eq_2
    retro' subprob_n2_equation_proof := subprob_n2_equation_proof h_n_eq_2
    retro' subprob_pqr_minus_1_even_proof := subprob_pqr_minus_1_even_proof h_n_eq_2
    retro' subprob_pqr_odd_proof := subprob_pqr_odd_proof h_n_eq_2
    retro' subprob_p_q_r_all_odd_proof := subprob_p_q_r_all_odd_proof h_n_eq_2
    retro' subprob_p_eq_3_for_n2_proof := subprob_p_eq_3_for_n2_proof h_n_eq_2
    retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_n_eq_2
    retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_n_eq_2
    retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_n_eq_2
    retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_n_eq_2
    retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_n_eq_2
    retro' subprob_q_minus_4_pos_proof := subprob_q_minus_4_pos_proof h_n_eq_2
    retro' subprob_q_eq_5_r_eq_15_for_n2_p3_proof := subprob_q_eq_5_r_eq_15_for_n2_p3_proof h_n_eq_2
    exact
      show p = (3 : ℤ) → p = (3 : ℤ) ∧ q = (5 : ℤ) ∧ r = (15 : ℤ) by
        intro h_p_eq_3_n2
        retro' subprob_n2_p3_equation_proof := subprob_n2_p3_equation_proof h_p_eq_3_n2
        retro' subprob_n2_p3_simplified_proof := subprob_n2_p3_simplified_proof h_p_eq_3_n2
        retro' subprob_n2_p3_expanded_proof := subprob_n2_p3_expanded_proof h_p_eq_3_n2
        retro' subprob_n2_p3_rearranged_proof := subprob_n2_p3_rearranged_proof h_p_eq_3_n2
        retro' subprob_n2_p3_factorized_proof := subprob_n2_p3_factorized_proof h_p_eq_3_n2
        retro' subprob_q_minus_4_pos_proof := subprob_q_minus_4_pos_proof h_p_eq_3_n2
        retro' subprob_q_eq_5_r_eq_15_for_n2_p3_proof := subprob_q_eq_5_r_eq_15_for_n2_p3_proof h_p_eq_3_n2
        exact
          show p = 3 ∧ q = 5 ∧ r = 15 by
            mkOpaque
            apply And.intro
            . exact h_p_eq_3_n2
            . exact subprob_q_eq_5_r_eq_15_for_n2_p3_proof
  have subprob_n_ge_3_p2_eq_intermediate_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → (n - (2 : ℤ)) * q * r + (n + (1 : ℤ)) = n * (q + r) := by
    intro h_n_ge_3
    exact
      show p = (2 : ℤ) → (n - (2 : ℤ)) * q * r + (n + (1 : ℤ)) = n * (q + r) by
        intro h_p_eq_2_n_ge_3
        exact
          show (n - 2) * q * r + (n + 1) = n * (q + r) by
            mkOpaque
            have h_eq1 : (2 : ℤ) * q * r - (1 : ℤ) = ((2 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
              rw [← h_p_eq_2_n_ge_3]
              exact hn_def
            have h_eq2 : (2 : ℤ) * q * r - (1 : ℤ) = n * q * r - n * q - n * r + n := by
              rw [h_eq1]
              ring
            linarith [h_eq2]
  have subprob_n_lt_4_8_real_for_p2_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → (↑(n) : ℝ) < (24 : ℝ) / (5 : ℝ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → (↑(n) : ℝ) < (24 : ℝ) / (5 : ℝ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        exact
          show (n : ℝ) < (24 : ℝ) / (5 : ℝ) by
            mkOpaque
            have hp_val_eq_2 : (↑p : ℝ) = (2 : ℝ) := by
              rw [h_p_eq_2_n_ge_3]
              norm_cast
            have p_frac_val : (↑p : ℝ) / ((↑p : ℝ) - (1 : ℝ)) = (2 : ℝ) := by
              rw [hp_val_eq_2]
              have h_denom_ne_zero : (2 : ℝ) - (1 : ℝ) ≠ 0 := by norm_num
              field_simp [h_denom_ne_zero]
              norm_num
            have h_n_lt_2_fq_fr : (↑n : ℝ) < (2 : ℝ) * ((↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ))) * ((↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ))) := by
              apply lt_of_lt_of_eq subprob_n_lt_prod_fractions_real_proof
              rw [p_frac_val]
            rcases h₀ with ⟨_, h_p_lt_q, h_q_lt_r⟩
            have h_2_lt_q : (2 : ℤ) < q := by
              rw [h_p_eq_2_n_ge_3] at h_p_lt_q
              exact h_p_lt_q
            have h_q_ge_3 : q ≥ (3 : ℤ) := by linarith [h_2_lt_q]
            have h_r_ge_q_plus_1 : r ≥ q + (1 : ℤ) := by linarith [h_q_lt_r]
            have h_r_ge_4 : r ≥ (4 : ℤ) := by linarith [h_r_ge_q_plus_1, h_q_ge_3]
            let q_real := (↑q : ℝ)
            let r_real := (↑r : ℝ)
            have h_3_gt_1 : (3 : ℝ) > (1 : ℝ) := by norm_num
            have h_q_real_ge_3_real : q_real ≥ (3 : ℝ) := by
              dsimp [q_real]
              norm_cast
            have h_fq_le_f3 : q_real / (q_real - (1 : ℝ)) ≤ (3 : ℝ) / ((3 : ℝ) - (1 : ℝ)) := by
              have h_q_real_gt_1 : q_real > (1 : ℝ) := by norm_cast; linarith [h_q_ge_3]
              rw [← f_def' q_real, ← f_def' (3 : ℝ)]
              by_cases h_q_eq_3 : q_real = (3 : ℝ)
              . rw [h_q_eq_3]
              . have h_q_gt_3 : (3 : ℝ) < q_real := by exact lt_of_le_of_ne h_q_real_ge_3_real (Ne.symm h_q_eq_3)
                have res := subprob_f_decreasing_proof (3 : ℝ) q_real h_3_gt_1 h_q_gt_3
                exact le_of_lt res
            have val_f3_calc : (3 : ℝ) / ((3 : ℝ) - (1 : ℝ)) = (3 : ℝ) / (2 : ℝ) := by
              field_simp
              norm_num
            rw [val_f3_calc] at h_fq_le_f3
            have h_4_gt_1 : (4 : ℝ) > (1 : ℝ) := by norm_num
            have h_r_real_ge_4_real : r_real ≥ (4 : ℝ) := by
              dsimp [r_real]
              norm_cast
            have h_fr_le_f4 : r_real / (r_real - (1 : ℝ)) ≤ (4 : ℝ) / ((4 : ℝ) - (1 : ℝ)) := by
              have h_r_real_gt_1 : r_real > (1 : ℝ) := by norm_cast; linarith [h_r_ge_4]
              rw [← f_def' r_real, ← f_def' (4 : ℝ)]
              by_cases h_r_eq_4 : r_real = (4 : ℝ)
              . rw [h_r_eq_4]
              . have h_r_gt_4 : (4 : ℝ) < r_real := by exact lt_of_le_of_ne h_r_real_ge_4_real (Ne.symm h_r_eq_4)
                have res := subprob_f_decreasing_proof (4 : ℝ) r_real h_4_gt_1 h_r_gt_4
                exact le_of_lt res
            have val_f4_calc : (4 : ℝ) / ((4 : ℝ) - (1 : ℝ)) = (4 : ℝ) / (3 : ℝ) := by
              field_simp
              norm_num
            rw [val_f4_calc] at h_fr_le_f4
            have h_fq_pos : q_real / (q_real - (1 : ℝ)) > 0 := by
              have h_q_real_num_pos : q_real > 0 := by norm_cast; linarith [h_q_ge_3]
              have h_q_real_den_pos : q_real - (1 : ℝ) > 0 := by
                apply sub_pos.mpr
                norm_cast; linarith [h_q_ge_3]
              exact div_pos h_q_real_num_pos h_q_real_den_pos
            have h_fr_pos : r_real / (r_real - (1 : ℝ)) > 0 := by
              have h_r_real_num_pos : r_real > 0 := by norm_cast; linarith [h_r_ge_4]
              have h_r_real_den_pos : r_real - (1 : ℝ) > 0 := by
                apply sub_pos.mpr
                norm_cast; linarith [h_r_ge_4]
              exact div_pos h_r_real_num_pos h_r_real_den_pos
            have h_bound_intermediate : (2 : ℝ) * (q_real / (q_real - (1 : ℝ))) * (r_real / (r_real - (1 : ℝ))) ≤ (2 : ℝ) * ((3 : ℝ) / (2 : ℝ)) * ((4 : ℝ) / (3 : ℝ)) := by
              rw [mul_assoc (2 : ℝ) _ _, mul_assoc (2 : ℝ) _ _]
              apply mul_le_mul_of_nonneg_left
              . apply mul_le_mul
                . exact h_fq_le_f3
                . exact h_fr_le_f4
                . exact le_of_lt h_fr_pos
                . have three_half_pos : (3 : ℝ) / (2 : ℝ) ≥ 0 := by norm_num
                  exact three_half_pos
              . norm_num
            have h_prod_val : (2 : ℝ) * ((3 : ℝ) / (2 : ℝ)) * ((4 : ℝ) / (3 : ℝ)) = (4 : ℝ) := by field_simp
            have h_n_lt_4 : (↑n : ℝ) < (4 : ℝ) := by
              apply lt_of_lt_of_le h_n_lt_2_fq_fr
              rw [← h_prod_val]
              exact h_bound_intermediate
            have h_4_lt_24_5 : (4 : ℝ) < (24 : ℝ) / (5 : ℝ) := by norm_num
            exact lt_trans h_n_lt_4 h_4_lt_24_5
  have subprob_n_is_3_or_4_for_p2_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) ∨ n = (4 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) ∨ n = (4 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        exact
          show n = 3 ∨ n = 4 by
            mkOpaque
            have hn_lt_24_div_5_real : (↑n : ℝ) < (24 : ℝ) / (5 : ℝ) := subprob_n_lt_4_8_real_for_p2_proof
            have h_aux_frac_lt_5 : (24 : ℝ) / (5 : ℝ) < (5 : ℝ) := by
              have h_five_pos : (0 : ℝ) < 5 := by norm_num
              rw [div_lt_iff h_five_pos]
              norm_num
            have hn_real_lt_5 : (↑n : ℝ) < (5 : ℝ) := by apply lt_trans hn_lt_24_div_5_real h_aux_frac_lt_5
            have hn_int_lt_5 : n < 5 := by norm_cast at hn_real_lt_5
            have hn_le_4 : n ≤ 4 := by exact Order.le_of_lt_succ hn_int_lt_5
            have h_final_disj : n = 3 ∨ n = 4 := by omega
            exact h_final_disj
  have subprob_n3_p2_eq_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) → q * r + (4 : ℤ) = (3 : ℤ) * q + (3 : ℤ) * r := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) → q * r + (4 : ℤ) = (3 : ℤ) * q + (3 : ℤ) * r by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        exact
          show n = (3 : ℤ) → q * r + (4 : ℤ) = (3 : ℤ) * q + (3 : ℤ) * r by
            intro h_n_eq_3_p2
            exact
              show q * r + 4 = 3 * q + 3 * r by
                mkOpaque
                have h_eq_intermediate : (n - (2 : ℤ)) * q * r + (n + (1 : ℤ)) = n * (q + r) := by exact subprob_n_ge_3_p2_eq_intermediate_proof
                rw [h_n_eq_3_p2] at h_eq_intermediate
                norm_num at h_eq_intermediate
                rw [mul_add] at h_eq_intermediate
                exact h_eq_intermediate
  have subprob_n3_p2_factorized_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) → (q - (3 : ℤ)) * (r - (3 : ℤ)) = (5 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) → (q - (3 : ℤ)) * (r - (3 : ℤ)) = (5 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        exact
          show n = (3 : ℤ) → (q - (3 : ℤ)) * (r - (3 : ℤ)) = (5 : ℤ) by
            intro h_n_eq_3_p2
            retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_eq_3_p2
            exact
              show (q - 3) * (r - 3) = 5 by
                mkOpaque
                have h_lhs_expanded : (q - 3) * (r - 3) = q * r - 3 * q - 3 * r + 9 := by ring
                have h_rearranged_hyp : q * r - 3 * q - 3 * r = -4 := by linarith [subprob_n3_p2_eq_proof]
                rw [h_lhs_expanded]
                rw [h_rearranged_hyp]
                norm_num
  have subprob_q_minus_3_pos_p2_n3_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) → q - (3 : ℤ) > (0 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) → q - (3 : ℤ) > (0 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        exact
          show n = (3 : ℤ) → q - (3 : ℤ) > (0 : ℤ) by
            intro h_n_eq_3_p2
            retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_eq_3_p2
            retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_eq_3_p2
            exact
              show q - 3 > 0 by
                mkOpaque
                have h_p_lt_q : p < q := h₀.right.left
                have h_two_lt_q : (2 : ℤ) < q := by
                  rw [h_p_eq_2_n_ge_3] at h_p_lt_q
                  exact h_p_lt_q
                have h_q_minus_3_ge_0 : q - (3 : ℤ) ≥ (0 : ℤ) := by linarith [h_two_lt_q]
                have h_q_minus_3_ne_0 : q - (3 : ℤ) ≠ (0 : ℤ) := by
                  intro h_q_minus_3_eq_0
                  have h_prod_eq_5 : (q - (3 : ℤ)) * (r - (3 : ℤ)) = (5 : ℤ) := subprob_n3_p2_factorized_proof
                  rw [h_q_minus_3_eq_0] at h_prod_eq_5
                  simp only [zero_mul] at h_prod_eq_5
                  norm_num at h_prod_eq_5
                apply lt_of_le_of_ne h_q_minus_3_ge_0
                apply Ne.symm
                exact h_q_minus_3_ne_0
  have subprob_q_eq_4_r_eq_8_for_n3_p2_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) → q = (4 : ℤ) ∧ r = (8 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) → q = (4 : ℤ) ∧ r = (8 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_p_eq_2_n_ge_3
        exact
          show n = (3 : ℤ) → q = (4 : ℤ) ∧ r = (8 : ℤ) by
            intro h_n_eq_3_p2
            retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_eq_3_p2
            retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_eq_3_p2
            retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_eq_3_p2
            exact
              show q = 4 ∧ r = 8 by
                mkOpaque
                have hp_val : p = 2 := h_p_eq_2_n_ge_3
                have hq_lt_r : q < r := h₀.2.2
                have h_prod_eq_5 : (q - 3) * (r - 3) = 5 := subprob_n3_p2_factorized_proof
                have hA_pos : q - 3 > 0 := subprob_q_minus_3_pos_p2_n3_proof
                have hA_ge_1 : q - 3 ≥ 1 := by exact Int.pos_iff_one_le.mp hA_pos
                have hq_ge_4 : q ≥ 4 := by linarith
                have hr_ge_5 : r ≥ 5 := by linarith [hq_ge_4, hq_lt_r]
                have hB_pos : r - 3 > 0 := by linarith [hr_ge_5]
                let a_nat : ℕ := Int.toNat (q - 3)
                let b_nat : ℕ := Int.toNat (r - 3)
                have hA_nonneg : 0 ≤ q - 3 := Int.le_of_lt hA_pos
                have h_coe_a_nat : (↑a_nat : ℤ) = q - 3 := Int.toNat_of_nonneg hA_nonneg
                have hB_nonneg : 0 ≤ r - 3 := Int.le_of_lt hB_pos
                have h_coe_b_nat : (↑b_nat : ℤ) = r - 3 := Int.toNat_of_nonneg hB_nonneg
                have h_prod_nat_eq_5 : a_nat * b_nat = 5 := by
                  rw [← h_coe_a_nat, ← h_coe_b_nat] at h_prod_eq_5
                  rw [← Nat.cast_mul] at h_prod_eq_5
                  have h_5_is_coe : (5 : ℤ) = ↑(5 : ℕ) := by rfl
                  rw [h_5_is_coe] at h_prod_eq_5
                  apply Int.ofNat_injective
                  exact h_prod_eq_5
                have h_cases : (a_nat = 1 ∧ b_nat = 5) ∨ (a_nat = 5 ∧ b_nat = 1) := by
                  have ha_dvd_5 : a_nat ∣ 5 := dvd_of_mul_left_eq b_nat (Eq.trans (Nat.mul_comm b_nat a_nat) h_prod_nat_eq_5)
                  have ha_1_or_5 : a_nat = 1 ∨ a_nat = 5 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five a_nat ha_dvd_5
                  rcases ha_1_or_5 with ha1 | ha5
                  . rw [ha1, Nat.one_mul] at h_prod_nat_eq_5
                    left
                    exact And.intro ha1 h_prod_nat_eq_5
                  . rw [ha5] at h_prod_nat_eq_5
                    have h5_ne_zero : (5 : ℕ) ≠ 0 := Nat.prime_five.ne_zero
                    have h5_pos : 0 < (5 : ℕ) := Nat.pos_of_ne_zero h5_ne_zero
                    rw [Nat.mul_comm] at h_prod_nat_eq_5
                    have hb1 : b_nat = 1 := (Nat.mul_left_eq_self_iff h5_pos).mp h_prod_nat_eq_5
                    right
                    exact And.intro ha5 hb1
                rcases h_cases with ⟨ha_eq_1, hb_eq_5⟩ | ⟨ha_eq_5, hb_eq_1⟩
                . have hq_eq_4 : q = 4 :=
                    by
                    have h_q_minus_3_eq_1 : q - 3 = (1 : ℤ) := by
                      rw [← h_coe_a_nat]
                      rw [ha_eq_1]
                      norm_num
                    linarith [h_q_minus_3_eq_1]
                  have hr_eq_8 : r = 8 :=
                    by
                    have h_r_minus_3_eq_5 : r - 3 = (5 : ℤ) := by
                      rw [← h_coe_b_nat]
                      rw [hb_eq_5]
                      norm_num
                    linarith [h_r_minus_3_eq_5]
                  exact And.intro hq_eq_4 hr_eq_8
                . have hq_eq_8 : q = 8 :=
                    by
                    have h_q_minus_3_eq_5 : q - 3 = (5 : ℤ) := by
                      rw [← h_coe_a_nat]
                      rw [ha_eq_5]
                      norm_num
                    linarith [h_q_minus_3_eq_5]
                  have hr_eq_4 : r = 4 :=
                    by
                    have h_r_minus_3_eq_1 : r - 3 = (1 : ℤ) := by
                      rw [← h_coe_b_nat]
                      rw [hb_eq_1]
                      norm_num
                    linarith [h_r_minus_3_eq_1]
                  exfalso
                  linarith [hq_lt_r, hq_eq_8, hr_eq_4]
  have subprob_sol2_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (3 : ℤ) → p = (2 : ℤ) ∧ q = (4 : ℤ) ∧ r = (8 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (3 : ℤ) → p = (2 : ℤ) ∧ q = (4 : ℤ) ∧ r = (8 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_p_eq_2_n_ge_3
        retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_p_eq_2_n_ge_3
        exact
          show n = (3 : ℤ) → p = (2 : ℤ) ∧ q = (4 : ℤ) ∧ r = (8 : ℤ) by
            intro h_n_eq_3_p2
            retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_eq_3_p2
            retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_eq_3_p2
            retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_eq_3_p2
            retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_eq_3_p2
            exact
              show p = 2 ∧ q = 4 ∧ r = 8 by
                mkOpaque
                constructor
                . exact h_p_eq_2_n_ge_3
                . exact subprob_q_eq_4_r_eq_8_for_n3_p2_proof
  have subprob_n4_p2_eq_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (4 : ℤ) → (2 : ℤ) * q * r + (5 : ℤ) = (4 : ℤ) * q + (4 : ℤ) * r := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (4 : ℤ) → (2 : ℤ) * q * r + (5 : ℤ) = (4 : ℤ) * q + (4 : ℤ) * r by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_p_eq_2_n_ge_3
        retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_sol2_proof := subprob_sol2_proof h_p_eq_2_n_ge_3
        exact
          show n = (4 : ℤ) → (2 : ℤ) * q * r + (5 : ℤ) = (4 : ℤ) * q + (4 : ℤ) * r by
            intro h_n_eq_4_p2
            exact
              show 2 * q * r + 5 = 4 * q + 4 * r by
                mkOpaque
                have h_eq := subprob_n_ge_3_p2_eq_intermediate_proof
                rw [h_n_eq_4_p2] at h_eq
                norm_num at h_eq
                rw [Int.mul_add] at h_eq
                exact h_eq
  have subprob_n4_p2_rearranged_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (4 : ℤ) → (2 : ℤ) * (q * r - (2 : ℤ) * q - (2 : ℤ) * r) = -(5 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (4 : ℤ) → (2 : ℤ) * (q * r - (2 : ℤ) * q - (2 : ℤ) * r) = -(5 : ℤ) by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_p_eq_2_n_ge_3
        retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_sol2_proof := subprob_sol2_proof h_p_eq_2_n_ge_3
        retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_p_eq_2_n_ge_3
        exact
          show n = (4 : ℤ) → (2 : ℤ) * (q * r - (2 : ℤ) * q - (2 : ℤ) * r) = -(5 : ℤ) by
            intro h_n_eq_4_p2
            retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_eq_4_p2
            exact
              show 2 * (q * r - 2 * q - 2 * r) = -5 by
                mkOpaque
                have h_lhs_expanded : 2 * (q * r - 2 * q - 2 * r) = 2 * q * r - 4 * q - 4 * r := by ring
                rw [h_lhs_expanded]
                have h_transformed_given : (2 : ℤ) * q * r - ((4 : ℤ) * q + (4 : ℤ) * r) = -(5 : ℤ) := by
                  rw [← subprob_n4_p2_eq_proof]
                  rw [sub_add_eq_sub_sub]
                  rw [sub_self]
                  rw [zero_sub]
                have h_lhs_relation : (2 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r = (2 : ℤ) * q * r - ((4 : ℤ) * q + (4 : ℤ) * r) := by
                  apply Eq.symm
                  apply sub_add_eq_sub_sub
                rw [h_lhs_relation]
                exact h_transformed_given
  have subprob_n4_p2_impossible_proof : n ≥ (3 : ℤ) → p = (2 : ℤ) → n = (4 : ℤ) → False := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    exact
      show p = (2 : ℤ) → n = (4 : ℤ) → False by
        intro h_p_eq_2_n_ge_3
        retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_p_eq_2_n_ge_3
        retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_p_eq_2_n_ge_3
        retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_p_eq_2_n_ge_3
        retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_p_eq_2_n_ge_3
        retro' subprob_sol2_proof := subprob_sol2_proof h_p_eq_2_n_ge_3
        retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_p_eq_2_n_ge_3
        retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_p_eq_2_n_ge_3
        exact
          show n = (4 : ℤ) → False by
            intro h_n_eq_4_p2
            retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_eq_4_p2
            retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_eq_4_p2
            exact
              show False by
                mkOpaque
                have h_lhs_mod_2 : ((2 : ℤ) * (q * r - (2 : ℤ) * q - (2 : ℤ) * r)) % (2 : ℤ) = 0 := by simp
                have h_rhs_mod_2 : (-(5 : ℤ)) % (2 : ℤ) = 1 := by norm_num
                rw [subprob_n4_p2_rearranged_proof] at h_lhs_mod_2
                rw [h_rhs_mod_2] at h_lhs_mod_2
                norm_num at h_lhs_mod_2
  have subprob_n_ge_3_p3_eq_intermediate_proof : n ≥ (3 : ℤ) → p = (3 : ℤ) → ((2 : ℤ) * n - (3 : ℤ)) * q * r + ((2 : ℤ) * n + (1 : ℤ)) = (2 : ℤ) * n * (q + r) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    exact
      show p = (3 : ℤ) → ((2 : ℤ) * n - (3 : ℤ)) * q * r + ((2 : ℤ) * n + (1 : ℤ)) = (2 : ℤ) * n * (q + r) by
        intro h_p_eq_3_n_ge_3
        exact
          show (2 * n - 3) * q * r + (2 * n + 1) = 2 * n * (q + r) by
            mkOpaque
            have h_sub_p_eq_3 : (3 : ℤ) * q * r - (1 : ℤ) = ((3 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
              rw [h_p_eq_3_n_ge_3] at hn_def
              exact hn_def
            have h_simplified_const : (3 : ℤ) * q * r - (1 : ℤ) = (2 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
              rw [h_sub_p_eq_3]
              norm_num
            linarith [h_simplified_const]
  have subprob_n_lt_2_72_real_for_p3_proof : n ≥ (3 : ℤ) → p = (3 : ℤ) → (↑(n) : ℝ) < (30 : ℝ) / (11 : ℝ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    exact
      show p = (3 : ℤ) → (↑(n) : ℝ) < (30 : ℝ) / (11 : ℝ) by
        intro h_p_eq_3_n_ge_3
        retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_p_eq_3_n_ge_3
        exact
          show (n : ℝ) < (30 : ℝ) / (11 : ℝ) by
            mkOpaque
            have f_decreasing_le {x₁ x₂ : ℝ} (hx₁_gt_1 : 1 < x₁) (hx₁_le_x₂ : x₁ ≤ x₂) : f x₂ ≤ f x₁ := by
              rcases LE.le.eq_or_lt hx₁_le_x₂ with h_eq | h_lt
              . rw [h_eq]
              . have h_f_lt : f x₂ < f x₁ := subprob_f_decreasing_proof x₁ x₂ hx₁_gt_1 h_lt
                exact le_of_lt h_f_lt
            have hp_is_3 : p = (3 : ℤ) := h_p_eq_3_n_ge_3
            have fp_val_def : f (↑p : ℝ) = (↑p : ℝ) / ((↑p : ℝ) - (1 : ℝ)) := by rw [f_def]
            have fp_eval : f (↑p : ℝ) = (3 : ℝ) / (2 : ℝ) := by
              rw [fp_val_def, hp_is_3]
              simp only [Int.cast_ofNat, Int.cast_one]
              norm_num
            have h_3_lt_q : (3 : ℤ) < q := by
              rw [← hp_is_3]
              exact h₀.2.1
            have hq_ge_4 : q ≥ (4 : ℤ) := by linarith [h_3_lt_q]
            have hr_ge_5 : r ≥ (5 : ℤ) := by
              have h_q_lt_r : q < r := h₀.2.2
              linarith [h_3_lt_q, h_q_lt_r]
            have fq_val_def : f (↑q : ℝ) = (↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ)) := by rw [f_def]
            have fq_le_f4 : f (↑q : ℝ) ≤ f (4 : ℝ) := by
              apply f_decreasing_le
              . norm_num
              . exact Int.cast_le.mpr hq_ge_4
            have f4_eval : f (4 : ℝ) = (4 : ℝ) / (3 : ℝ) := by
              rw [f_def]
              norm_num
            rw [f4_eval] at fq_le_f4
            have fr_val_def : f (↑r : ℝ) = (↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ)) := by rw [f_def]
            have fr_le_f5 : f (↑r : ℝ) ≤ f (5 : ℝ) := by
              apply f_decreasing_le
              . norm_num
              . exact Int.cast_le.mpr hr_ge_5
            have f5_eval : f (5 : ℝ) = (5 : ℝ) / (4 : ℝ) := by
              rw [f_def]
              norm_num
            rw [f5_eval] at fr_le_f5
            have prod_f_le_upper_bound : f (↑p : ℝ) * f (↑q : ℝ) * f (↑r : ℝ) ≤ ((3 : ℝ) / (2 : ℝ) * (4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ)) := by
              rw [fp_eval]
              have fq_pos : 0 < f (↑q : ℝ) := by
                rw [fq_val_def]
                have q_cast_ge_4 : (↑q : ℝ) ≥ 4 := Int.cast_le.mpr hq_ge_4
                have q_cast_pos : 0 < (↑q : ℝ) := by linarith
                have q_minus_1_cast_pos : 0 < (↑q : ℝ) - (1 : ℝ) := by linarith
                exact div_pos q_cast_pos q_minus_1_cast_pos
              have fr_pos : 0 < f (↑r : ℝ) := by
                rw [fr_val_def]
                have r_cast_ge_5 : (↑r : ℝ) ≥ 5 := Int.cast_le.mpr hr_ge_5
                have r_cast_pos : 0 < (↑r : ℝ) := by linarith
                have r_minus_1_cast_pos : 0 < (↑r : ℝ) - (1 : ℝ) := by linarith
                exact div_pos r_cast_pos r_minus_1_cast_pos
              have temp1 : f (↑q : ℝ) * f (↑r : ℝ) ≤ (4 : ℝ) / (3 : ℝ) * f (↑r : ℝ) := by
                apply mul_le_mul_of_nonneg_right fq_le_f4
                exact le_of_lt fr_pos
              have temp2 : (4 : ℝ) / (3 : ℝ) * f (↑r : ℝ) ≤ (4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ) := by
                have h_multiplier_nonneg : 0 ≤ (4 : ℝ) / (3 : ℝ) := by norm_num
                rw [mul_div_assoc ((4 : ℝ) / (3 : ℝ)) (5 : ℝ) (4 : ℝ)]
                exact mul_le_mul_of_nonneg_left fr_le_f5 h_multiplier_nonneg
              have fq_fr_le_const : f (↑q : ℝ) * f (↑r : ℝ) ≤ (4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ) := le_trans temp1 temp2
              have h_3div2_pos : (0 : ℝ) < (3 : ℝ) / (2 : ℝ) := by norm_num
              rw [mul_assoc ((3 : ℝ) / (2 : ℝ)) (f (↑q : ℝ)) (f (↑r : ℝ))]
              have H_main_proof : (3 : ℝ) / (2 : ℝ) * (f (↑q : ℝ) * f (↑r : ℝ)) ≤ (3 : ℝ) / (2 : ℝ) * ((4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ)) := mul_le_mul_of_nonneg_left fq_fr_le_const (le_of_lt h_3div2_pos)
              have h_reassociate_rhs : (3 : ℝ) / (2 : ℝ) * ((4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ)) = ((3 : ℝ) / (2 : ℝ) * (4 : ℝ) / (3 : ℝ)) * (5 : ℝ) / (4 : ℝ) := by ring
              rw [h_reassociate_rhs] at H_main_proof
              exact H_main_proof
            have upper_bound_val_is_5_2 : ((3 : ℝ) / (2 : ℝ) * (4 : ℝ) / (3 : ℝ) * (5 : ℝ) / (4 : ℝ)) = (5 : ℝ) / (2 : ℝ) := by norm_num
            rw [upper_bound_val_is_5_2] at prod_f_le_upper_bound
            have n_lt_5_2 : (↑n : ℝ) < (5 : ℝ) / (2 : ℝ) := by
              rw [fp_val_def, fq_val_def, fr_val_def] at prod_f_le_upper_bound
              exact lt_of_lt_of_le subprob_n_lt_prod_fractions_real_proof prod_f_le_upper_bound
            have five_div_two_lt_thirty_div_eleven : (5 : ℝ) / (2 : ℝ) < (30 : ℝ) / (11 : ℝ) := by norm_num
            exact lt_trans n_lt_5_2 five_div_two_lt_thirty_div_eleven
  have subprob_n_ge_3_p3_impossible_proof : n ≥ (3 : ℤ) → p = (3 : ℤ) → False := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_n_ge_3
    exact
      show p = (3 : ℤ) → False by
        intro h_p_eq_3_n_ge_3
        retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_p_eq_3_n_ge_3
        retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_p_eq_3_n_ge_3
        exact
          show False by
            mkOpaque
            have hn_ge_3_real : (↑n : ℝ) ≥ (3 : ℝ) := by norm_cast
            have h_const_lt_3 : (30 : ℝ) / (11 : ℝ) < (3 : ℝ) := by
              have h_eleven_pos : (11 : ℝ) > 0 := by norm_num
              rw [div_lt_iff h_eleven_pos]
              norm_num
            have hn_lt_3_real : (↑n : ℝ) < (3 : ℝ) := by apply lt_trans subprob_n_lt_2_72_real_for_p3_proof h_const_lt_3
            have h_absurd : (3 : ℝ) < (3 : ℝ) := by apply lt_of_le_of_lt hn_ge_3_real hn_lt_3_real
            apply lt_irrefl (3 : ℝ) h_absurd
  have subprob_n_ge_3_p4_eq_intermediate_proof : n ≥ (3 : ℤ) → p = (4 : ℤ) → ((3 : ℤ) * n - (4 : ℤ)) * q * r + ((3 : ℤ) * n + (1 : ℤ)) = (3 : ℤ) * n * (q + r) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_impossible_proof := subprob_n_ge_3_p3_impossible_proof h_n_ge_3
    exact
      show p = (4 : ℤ) → ((3 : ℤ) * n - (4 : ℤ)) * q * r + ((3 : ℤ) * n + (1 : ℤ)) = (3 : ℤ) * n * (q + r) by
        intro h_p_eq_4_n_ge_3
        exact
          show (3 * n - 4) * q * r + (3 * n + 1) = 3 * n * (q + r) by
            mkOpaque
            have h_subst_p : (4 : ℤ) * q * r - 1 = ((4 : ℤ) - 1) * (q - 1) * (r - 1) * n := by
              rw [← h_p_eq_4_n_ge_3]
              exact hn_def
            norm_num at h_subst_p
            have h_rhs_expanded : 3 * (q - 1) * (r - 1) * n = 3 * n * q * r - 3 * n * q - 3 * n * r + 3 * n := by ring
            rw [h_rhs_expanded] at h_subst_p
            linarith [h_subst_p]
  have subprob_n_odd_q_r_even_for_p4_proof : n ≥ (3 : ℤ) → p = (4 : ℤ) → n % (2 : ℤ) = (1 : ℤ) ∧ q % (2 : ℤ) = (0 : ℤ) ∧ r % (2 : ℤ) = (0 : ℤ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_impossible_proof := subprob_n_ge_3_p3_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_n_ge_3
    exact
      show p = (4 : ℤ) → n % (2 : ℤ) = (1 : ℤ) ∧ q % (2 : ℤ) = (0 : ℤ) ∧ r % (2 : ℤ) = (0 : ℤ) by
        intro h_p_eq_4_n_ge_3
        retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_p_eq_4_n_ge_3
        exact
          show n % 2 = 1 ∧ q % 2 = 0 ∧ r % 2 = 0 by
            mkOpaque
            have hp_eq_4 : p = (4 : ℤ) := h_p_eq_4_n_ge_3
            have h_p_lt_q : p < q := h₀.2.1
            have h_q_lt_r : q < r := h₀.2.2
            have hq_gt_4 : (4 : ℤ) < q := by rw [hp_eq_4] at h_p_lt_q; exact h_p_lt_q
            have hq_ge_5 : q ≥ (5 : ℤ) := Int.add_one_le_of_lt hq_gt_4
            have hr_gt_q : q < r := h_q_lt_r
            have hr_ge_q_plus_1 : r ≥ q + 1 := Int.add_one_le_of_lt hr_gt_q
            have hr_ge_6 : r ≥ (6 : ℤ) := by linarith [hq_ge_5, hr_ge_q_plus_1]
            have hp_real_eq_4 : (↑p : ℝ) = (4 : ℝ) := by norm_cast
            have hq_real_ge_5 : (↑q : ℝ) ≥ (5 : ℝ) := by norm_cast
            have hr_real_ge_6 : (↑r : ℝ) ≥ (6 : ℝ) := by norm_cast
            let fp := (↑p : ℝ) / (↑p - (1 : ℝ))
            let fq := (↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ))
            let fr := (↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ))
            have fp_val : fp = (4 : ℝ) / (3 : ℝ) := by
              dsimp only [fp]
              rw [hp_real_eq_4]
              field_simp
              norm_num
            have f_strict_anti : StrictAntiOn f (Set.Ioi 1) := by
              intro x₁ hx₁ x₂ hx₂ hx₁_lt_x₂
              rw [f_def', f_def']
              exact (f_def' x₁) ▸ (f_def' x₂) ▸ (subprob_f_decreasing_proof x₁ x₂ hx₁ hx₁_lt_x₂)
            have f_antitone_on_Ioi1 : AntitoneOn f (Set.Ioi 1) := StrictAntiOn.antitoneOn f_strict_anti
            have five_gt_1 : (5 : ℝ) > 1 := by norm_num
            have q_gt_1_real : (↑q : ℝ) > 1 := by linarith [hq_real_ge_5]
            have six_gt_1 : (6 : ℝ) > 1 := by norm_num
            have r_gt_1_real : (↑r : ℝ) > 1 := by linarith [hr_real_ge_6]
            have five_mem_Ioi1 : (5 : ℝ) ∈ Set.Ioi 1 := five_gt_1
            have q_mem_Ioi1 : (↑q : ℝ) ∈ Set.Ioi 1 := q_gt_1_real
            have six_mem_Ioi1 : (6 : ℝ) ∈ Set.Ioi 1 := six_gt_1
            have r_mem_Ioi1 : (↑r : ℝ) ∈ Set.Ioi 1 := r_gt_1_real
            have fq_le_f5 : fq ≤ f (5 : ℝ) := by
              dsimp only [fq]
              exact (f_def' (↑q : ℝ)) ▸ (f_antitone_on_Ioi1 five_mem_Ioi1 q_mem_Ioi1 hq_real_ge_5)
            have f5_val : f (5 : ℝ) = (5 : ℝ) / (4 : ℝ) := by rw [f_def']; field_simp; norm_num
            rw [f5_val] at fq_le_f5
            have fr_le_f6 : fr ≤ f (6 : ℝ) := by
              dsimp only [fr]
              rw [← (f_def' (↑r : ℝ))]
              exact (f_antitone_on_Ioi1 six_mem_Ioi1 r_mem_Ioi1 hr_real_ge_6)
            have f6_val : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by rw [f_def']; field_simp; norm_num
            rw [f6_val] at fr_le_f6
            have fp_pos : 0 < fp := by rw [fp_val]; norm_num
            have fq_pos : 0 < fq := by apply div_pos (by linarith [hq_real_ge_5]) (by apply sub_pos_of_lt; linarith [hq_real_ge_5])
            have fr_pos : 0 < fr := by apply div_pos (by linarith [hr_real_ge_6]) (by apply sub_pos_of_lt; linarith [hr_real_ge_6])
            have five_fourths_pos : 0 < (5 : ℝ) / 4 := by norm_num
            have h_n_lt_prod := subprob_n_lt_prod_fractions_real_proof
            have fq_mul_fr_le : fq * fr ≤ ((5 : ℝ) / 4) * ((6 : ℝ) / 5) := by apply mul_le_mul fq_le_f5 fr_le_f6 (le_of_lt fr_pos) (le_of_lt five_fourths_pos)
            have prod_le_total_bound : fp * (fq * fr) ≤ fp * (((5 : ℝ) / 4) * ((6 : ℝ) / 5)) := by apply mul_le_mul_of_nonneg_left fq_mul_fr_le (le_of_lt fp_pos)
            have n_lt_bound_val : (↑n : ℝ) < fp * (((5 : ℝ) / 4) * ((6 : ℝ) / 5)) := by
              have h_temp := h_n_lt_prod
              rw [mul_assoc fp fq fr] at h_temp
              apply lt_of_lt_of_le h_temp prod_le_total_bound
            rw [fp_val] at n_lt_bound_val
            have bound_calc : (4 : ℝ) / 3 * (((5 : ℝ) / 4) * ((6 : ℝ) / 5)) = 2 := by
              field_simp
              norm_num
            rw [bound_calc] at n_lt_bound_val
            have n_lt_2_int : n < (2 : ℤ) := by
              apply (Int.cast_lt (R := ℝ)).mp
              rw [Int.cast_two]
              exact n_lt_bound_val
            have n_le_1 : n ≤ (1 : ℤ) := Order.le_pred_of_lt n_lt_2_int
            have contradiction : False := by linarith [n_le_1, h_n_ge_3]
            exact False.elim contradiction
  have subprob_n_lt_1_88_real_for_p4_proof : n ≥ (3 : ℤ) → p = (4 : ℤ) → (↑(n) : ℝ) < (32 : ℝ) / (17 : ℝ) := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_impossible_proof := subprob_n_ge_3_p3_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_odd_q_r_even_for_p4_proof := subprob_n_odd_q_r_even_for_p4_proof h_n_ge_3
    exact
      show p = (4 : ℤ) → (↑(n) : ℝ) < (32 : ℝ) / (17 : ℝ) by
        intro h_p_eq_4_n_ge_3
        retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_p_eq_4_n_ge_3
        retro' subprob_n_odd_q_r_even_for_p4_proof := subprob_n_odd_q_r_even_for_p4_proof h_p_eq_4_n_ge_3
        exact
          show (n : ℝ) < (32 : ℝ) / (17 : ℝ) by
            mkOpaque
            have h_n_lt_prod_frac : (↑n : ℝ) < (↑p : ℝ) / ((↑p : ℝ) - 1) * ((↑q : ℝ) / ((↑q : ℝ) - 1)) * ((↑r : ℝ) / ((↑r : ℝ) - 1)) := subprob_n_lt_prod_fractions_real_proof
            have h_n_lt_f_prod : (↑n : ℝ) < f (↑p : ℝ) * f (↑q : ℝ) * f (↑r : ℝ) := by rw [f_def' (↑p : ℝ), f_def' (↑q : ℝ), f_def' (↑r : ℝ)]; exact h_n_lt_prod_frac
            have hp_val_real : (↑p : ℝ) = (4 : ℝ) := by simp [h_p_eq_4_n_ge_3]
            rw [hp_val_real] at h_n_lt_f_prod
            have h_fp_eval : f (4 : ℝ) = (4 : ℝ) / (3 : ℝ) := by rw [f_def']; norm_num
            rw [h_fp_eval] at h_n_lt_f_prod
            have p_lt_q : p < q := h₀.2.1
            have q_lt_r : q < r := h₀.2.2
            have h_q_gt_4 : q > 4 := by rw [← h_p_eq_4_n_ge_3]; exact p_lt_q
            have h_q_even : q % 2 = 0 := subprob_n_odd_q_r_even_for_p4_proof.2.1
            have h_r_even : r % 2 = 0 := subprob_n_odd_q_r_even_for_p4_proof.2.2
            have h_q_ge_6 : q ≥ 6 := by
              apply Int.le_of_lt_add_one
              have q_ge_5 : q ≥ 5 := Int.add_one_le_of_lt h_q_gt_4
              have h_exists_k : (∃ k_val, q = 2 * k_val) := exists_eq_mul_right_of_dvd (Int.dvd_of_emod_eq_zero h_q_even)
              rcases h_exists_k with ⟨k, hk_q⟩
              rw [hk_q] at q_ge_5
              have k_ge_3 : k ≥ 3 := by linarith
              rw [hk_q]
              linarith
            have h_r_ge_8 : r ≥ 8 := by
              have r_ge_q_plus_1 : r ≥ q + 1 := Int.add_one_le_of_lt q_lt_r
              by_cases hr_eq_q_plus_1 : r = q + 1
              . rw [hr_eq_q_plus_1] at h_r_even
                have q_plus_1_is_odd : (q + 1) % 2 = 1 := by
                  rw [Int.add_emod]
                  simp [h_q_even, Int.one_emod_two]
                rw [q_plus_1_is_odd] at h_r_even
                norm_num at h_r_even
              . have r_gt_q_plus_1 : r > q + 1 := lt_of_le_of_ne' r_ge_q_plus_1 hr_eq_q_plus_1
                have r_ge_q_plus_2 : r ≥ q + 2 := (Int.add_assoc q 1 1) ▸ Int.add_one_le_of_lt r_gt_q_plus_1
                linarith [r_ge_q_plus_2, h_q_ge_6]
            have six_gt_1_real : (6 : ℝ) > 1 := by norm_num
            have q_ge_6_real : (↑q : ℝ) ≥ (6 : ℝ) := Int.cast_le.mpr h_q_ge_6
            have q_gt_1_real : (↑q : ℝ) > 1 := by linarith [q_ge_6_real, six_gt_1_real]
            have h_fq_le : f (↑q : ℝ) ≤ f (6 : ℝ) := by
              rcases eq_or_lt_of_le q_ge_6_real with h_q_eq_6 | h_q_gt_6
              · rw [h_q_eq_6]
              · exact (subprob_f_decreasing_proof (6 : ℝ) (↑q : ℝ) six_gt_1_real h_q_gt_6).le
            have h_f6_eval : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by rw [f_def']; norm_num
            rw [h_f6_eval] at h_fq_le
            have eight_gt_1_real : (8 : ℝ) > 1 := by norm_num
            have r_ge_8_real : (↑r : ℝ) ≥ (8 : ℝ) := Int.cast_le.mpr h_r_ge_8
            have r_gt_1_real : (↑r : ℝ) > 1 := by linarith [r_ge_8_real, eight_gt_1_real]
            have h_fr_le : f (↑r : ℝ) ≤ f (8 : ℝ) := by
              rcases eq_or_lt_of_le r_ge_8_real with h_r_eq_8 | h_r_gt_8
              · rw [h_r_eq_8]
              · exact (subprob_f_decreasing_proof (8 : ℝ) (↑r : ℝ) eight_gt_1_real h_r_gt_8).le
            have h_f8_eval : f (8 : ℝ) = (8 : ℝ) / (7 : ℝ) := by rw [f_def']; norm_num
            rw [h_f8_eval] at h_fr_le
            have h_n_lt_upper_bound : (↑n : ℝ) < (4 / 3 : ℝ) * (6 / 5 : ℝ) * (8 / 7 : ℝ) := by
              have f43_pos : (4 / 3 : ℝ) > 0 := by norm_num
              have fq_pos : f (↑q : ℝ) > 0 := by
                rw [f_def']
                apply div_pos <;> linarith [q_gt_1_real]
              have fr_pos : f (↑r : ℝ) > 0 := by
                rw [f_def']
                apply div_pos <;> linarith [r_gt_1_real]
              have h_aux1 : (4 / 3 : ℝ) * f (↑q : ℝ) * f (↑r : ℝ) ≤ (4 / 3 : ℝ) * (6 / 5 : ℝ) * f (↑r : ℝ) := by gcongr
              have h_aux2 : (4 / 3 : ℝ) * (6 / 5 : ℝ) * f (↑r : ℝ) ≤ (4 / 3 : ℝ) * (6 / 5 : ℝ) * (8 / 7 : ℝ) := by gcongr
              exact h_n_lt_f_prod.trans_le (h_aux1.trans h_aux2)
            have h_prod_val : (4 / 3 : ℝ) * (6 / 5 : ℝ) * (8 / 7 : ℝ) = (64 / 35 : ℝ) := by norm_num
            rw [h_prod_val] at h_n_lt_upper_bound
            have h_final_ineq : (64 / 35 : ℝ) < (32 / 17 : ℝ) := by norm_num
            exact h_n_lt_upper_bound.trans h_final_ineq
  have subprob_n_ge_3_p4_impossible_proof : n ≥ (3 : ℤ) → p = (4 : ℤ) → False := by
    intro h_n_ge_3
    retro' subprob_n_ge_3_p2_eq_intermediate_proof := subprob_n_ge_3_p2_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_4_8_real_for_p2_proof := subprob_n_lt_4_8_real_for_p2_proof h_n_ge_3
    retro' subprob_n_is_3_or_4_for_p2_proof := subprob_n_is_3_or_4_for_p2_proof h_n_ge_3
    retro' subprob_n3_p2_eq_proof := subprob_n3_p2_eq_proof h_n_ge_3
    retro' subprob_n3_p2_factorized_proof := subprob_n3_p2_factorized_proof h_n_ge_3
    retro' subprob_q_minus_3_pos_p2_n3_proof := subprob_q_minus_3_pos_p2_n3_proof h_n_ge_3
    retro' subprob_q_eq_4_r_eq_8_for_n3_p2_proof := subprob_q_eq_4_r_eq_8_for_n3_p2_proof h_n_ge_3
    retro' subprob_sol2_proof := subprob_sol2_proof h_n_ge_3
    retro' subprob_n4_p2_eq_proof := subprob_n4_p2_eq_proof h_n_ge_3
    retro' subprob_n4_p2_rearranged_proof := subprob_n4_p2_rearranged_proof h_n_ge_3
    retro' subprob_n4_p2_impossible_proof := subprob_n4_p2_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_eq_intermediate_proof := subprob_n_ge_3_p3_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_lt_2_72_real_for_p3_proof := subprob_n_lt_2_72_real_for_p3_proof h_n_ge_3
    retro' subprob_n_ge_3_p3_impossible_proof := subprob_n_ge_3_p3_impossible_proof h_n_ge_3
    retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_n_ge_3
    retro' subprob_n_odd_q_r_even_for_p4_proof := subprob_n_odd_q_r_even_for_p4_proof h_n_ge_3
    retro' subprob_n_lt_1_88_real_for_p4_proof := subprob_n_lt_1_88_real_for_p4_proof h_n_ge_3
    exact
      show p = (4 : ℤ) → False by
        intro h_p_eq_4_n_ge_3
        retro' subprob_n_ge_3_p4_eq_intermediate_proof := subprob_n_ge_3_p4_eq_intermediate_proof h_p_eq_4_n_ge_3
        retro' subprob_n_odd_q_r_even_for_p4_proof := subprob_n_odd_q_r_even_for_p4_proof h_p_eq_4_n_ge_3
        retro' subprob_n_lt_1_88_real_for_p4_proof := subprob_n_lt_1_88_real_for_p4_proof h_p_eq_4_n_ge_3
        exact
          show False by
            mkOpaque
            have h_n_ge_3_real : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h_n_ge_3
            have h_bound_val_lt_3 : (32 : ℝ) / (17 : ℝ) < (3 : ℝ) := by norm_num
            linarith [subprob_n_lt_1_88_real_for_p4_proof, h_n_ge_3_real, h_bound_val_lt_3]
  exact
    show (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15) by
      mkOpaque
      have hn_ge_1 : n ≥ (1 : ℤ) := subprob_n_pos_proof
      have h_n_cases : (1 : ℤ) = n ∨ (1 : ℤ) < n := eq_or_lt_of_le hn_ge_1
      rcases h_n_cases with hn_1_eq_n | hn_lt_1
      . exfalso
        exact subprob_n1_impossible_proof hn_1_eq_n.symm
      . have hn_ge_2 : n ≥ (2 : ℤ) := by linarith [hn_lt_1]
        have h_n_ge_2_cases : (2 : ℤ) = n ∨ (2 : ℤ) < n := eq_or_lt_of_le hn_ge_2
        rcases h_n_ge_2_cases with hn_eq_2 | hn_lt_2
        . have hp_eq_3_for_n2 : p = (3 : ℤ) := subprob_p_eq_3_for_n2_proof hn_eq_2.symm
          have h_sol1 := subprob_sol1_proof hn_eq_2.symm hp_eq_3_for_n2
          rcases h_sol1 with ⟨rfl, rfl, rfl⟩
          apply Or.inr
          rfl
        . have hn_ge_3 : n ≥ (3 : ℤ) := by linarith [hn_lt_2]
          rcases subprob_p_cases_proof with hp_eq_2 | hp_eq_3 | hp_eq_4
          . have hn_is_3_or_4 := subprob_n_is_3_or_4_for_p2_proof hn_ge_3 hp_eq_2
            rcases hn_is_3_or_4 with hn_eq_3 | hn_eq_4
            . have h_sol2 := subprob_sol2_proof hn_ge_3 hp_eq_2 hn_eq_3
              rcases h_sol2 with ⟨rfl, rfl, rfl⟩
              apply Or.inl
              rfl
            . exfalso
              exact subprob_n4_p2_impossible_proof hn_ge_3 hp_eq_2 hn_eq_4
          . exfalso
            exact subprob_n_ge_3_p3_impossible_proof hn_ge_3 hp_eq_3
          . exfalso
            exact subprob_n_ge_3_p4_impossible_proof hn_ge_3 hp_eq_4

#print axioms imo_1992_p1

/-Sketch
variable (p q r : ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r) (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ p * q * r - 1)
play

  -- From h₁, let n be the integer such that pqr - 1 = n * (p-1)(q-1)(r-1)
  -- h₁ is `∃ k : ℤ, p * q * r - 1 = k * (p - 1) * (q - 1) * (r - 1)`
  -- Extract n and the definitional property hn_def.
  ⟨n, hn_def⟩ := h₁

  -- Show p-1, q-1, r-1 are positive
  subprob_p_minus_1_pos :≡ p - 1 > 0
  subprob_p_minus_1_pos_proof ⇐ show subprob_p_minus_1_pos by sorry
  subprob_q_minus_1_pos :≡ q - 1 > 0
  subprob_q_minus_1_pos_proof ⇐ show subprob_q_minus_1_pos by sorry
  subprob_r_minus_1_pos :≡ r - 1 > 0
  subprob_r_minus_1_pos_proof ⇐ show subprob_r_minus_1_pos by sorry

  -- Show (p-1)(q-1)(r-1) > 0
  denominator_val := (p - 1) * (q - 1) * (r - 1) -- Renamed to avoid "pos" in name of a value
  subprob_denominator_pos :≡ denominator_val > 0
  subprob_denominator_pos_proof ⇐ show subprob_denominator_pos by sorry

  -- Show pqr - 1 > 0
  numerator_val := p * q * r - 1 -- Renamed to avoid "pos" in name of a value
  subprob_numerator_pos :≡ numerator_val > 0
  subprob_numerator_pos_proof ⇐ show subprob_numerator_pos by sorry

  -- Show n must be positive. hn_def is p * q * r - 1 = n * (p - 1) * (q - 1) * (r - 1)
  subprob_n_pos :≡ n ≥ 1
  subprob_n_pos_proof ⇐ show subprob_n_pos by sorry

  -- Step 1: Bound p. Show p < 5.
  -- n < (p/(p-1)) * (q/(q-1)) * (r/(r-1))
  subprob_n_lt_prod_fractions_real :≡ (n : ℝ) < ((p : ℝ) / ((p : ℝ) - 1)) * ((q : ℝ) / ((q : ℝ) - 1)) * ((r : ℝ) / ((r : ℝ) - 1))
  subprob_n_lt_prod_fractions_real_proof ⇐ show subprob_n_lt_prod_fractions_real by sorry

  -- Function f(x) = x/(x-1) is decreasing for x > 1.
  f := fun (x : ℝ) => x / (x - 1)
  subprob_f_decreasing :≡ ∀ (x₁ x₂ : ℝ), 1 < x₁ → x₁ < x₂ → f x₂ < f x₁
  subprob_f_decreasing_proof ⇐ show subprob_f_decreasing by sorry

  -- If p ≥ 5, then n < 7/4 = 1.75.
  suppose (h_p_ge_5 : p ≥ 5) then
    subprob_p_frac_le_5_4 :≡ (p : ℝ) / ((p : ℝ) - 1) ≤ (5 : ℝ) / (4 : ℝ)
    subprob_p_frac_le_5_4_proof ⇐ show subprob_p_frac_le_5_4 by sorry
    subprob_q_ge_6 :≡ q ≥ 6 -- Since p < q and p ≥ 5, q ≥ p+1 ≥ 6
    subprob_q_ge_6_proof ⇐ show subprob_q_ge_6 by sorry
    subprob_q_frac_le_6_5 :≡ (q : ℝ) / ((q : ℝ) - 1) ≤ (6 : ℝ) / (5 : ℝ)
    subprob_q_frac_le_6_5_proof ⇐ show subprob_q_frac_le_6_5 by sorry
    subprob_r_ge_7 :≡ r ≥ 7 -- Since q < r and q ≥ 6, r ≥ q+1 ≥ 7
    subprob_r_ge_7_proof ⇐ show subprob_r_ge_7 by sorry
    subprob_r_frac_le_7_6 :≡ (r : ℝ) / ((r : ℝ) - 1) ≤ (7 : ℝ) / (6 : ℝ)
    subprob_r_frac_le_7_6_proof ⇐ show subprob_r_frac_le_7_6 by sorry

    subprob_n_lt_7_4_real :≡ (n : ℝ) < (7 : ℝ) / (4 : ℝ)
    subprob_n_lt_7_4_real_proof ⇐ show subprob_n_lt_7_4_real by sorry
    subprob_n_eq_1_if_p_ge_5 :≡ n = 1 -- Since n ≥ 1 and (n:ℝ) < 1.75, n must be 1
    subprob_n_eq_1_if_p_ge_5_proof ⇐ show subprob_n_eq_1_if_p_ge_5 by sorry

  -- Step 2: Case n=1. Show it's impossible.
  suppose (h_n_eq_1 : n = 1) then
    subprob_n1_equation :≡ p * q * r - 1 = (p - 1) * (q - 1) * (r - 1) -- from hn_def and h_n_eq_1
    subprob_n1_equation_proof ⇐ show subprob_n1_equation by sorry
    subprob_n1_expanded :≡ (p - 1) * (q - 1) * (r - 1) = p*q*r - (p*q + p*r + q*r) + (p+q+r) - 1
    subprob_n1_expanded_proof ⇐ show subprob_n1_expanded by sorry
    subprob_n1_simplified :≡ p*q + p*r + q*r = p + q + r
    subprob_n1_simplified_proof ⇐ show subprob_n1_simplified by sorry

    -- Show p+q+r < pq+pr+qr for 1 < p < q < r.
    subprob_p_lt_pq :≡ p < p * q -- Since q > 1 (actually q ≥ p+1 ≥ 2)
    subprob_p_lt_pq_proof ⇐ show subprob_p_lt_pq by sorry
    subprob_q_lt_qr :≡ q < q * r -- Since r > 1 (actually r ≥ q+1 ≥ 3)
    subprob_q_lt_qr_proof ⇐ show subprob_q_lt_qr by sorry
    subprob_r_lt_rp :≡ r < r * p -- Since p > 1 (actually p ≥ 2)
    subprob_r_lt_rp_proof ⇐ show subprob_r_lt_rp by sorry
    subprob_sum_lt_sum_prod :≡ p + q + r < p*q + p*r + q*r
    subprob_sum_lt_sum_prod_proof ⇐ show subprob_sum_lt_sum_prod by sorry

    subprob_n1_impossible :≡ False -- Contradiction from subprob_n1_simplified and subprob_sum_lt_sum_prod
    subprob_n1_impossible_proof ⇐ show subprob_n1_impossible by sorry

  -- Conclude p < 5 from (p ≥ 5 → n=1) and (n=1 → False).
  subprob_p_lt_5 :≡ p < 5
  subprob_p_lt_5_proof ⇐ show subprob_p_lt_5 by sorry

  -- Since 1 < p (from h₀) and p < 5, p can be 2, 3, 4.
  subprob_p_cases :≡ p = 2 ∨ p = 3 ∨ p = 4
  subprob_p_cases_proof ⇐ show subprob_p_cases by sorry

  -- Step 3: Case n=2
  suppose (h_n_eq_2 : n = 2) then
    subprob_n2_equation :≡ p*q*r - 1 = 2 * (p-1)*(q-1)*(r-1)
    subprob_n2_equation_proof ⇐ show subprob_n2_equation by sorry
    subprob_pqr_minus_1_even :≡ (p*q*r - 1) % 2 = 0
    subprob_pqr_minus_1_even_proof ⇐ show subprob_pqr_minus_1_even by sorry
    subprob_pqr_odd :≡ (p*q*r) % 2 = 1
    subprob_pqr_odd_proof ⇐ show subprob_pqr_odd by sorry
    subprob_p_q_r_all_odd :≡ p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1
    subprob_p_q_r_all_odd_proof ⇐ show subprob_p_q_r_all_odd by sorry

    -- With p ∈ {2,3,4} and p is odd.
    subprob_p_eq_3_for_n2 :≡ p = 3
    subprob_p_eq_3_for_n2_proof ⇐ show subprob_p_eq_3_for_n2 by sorry

    suppose (h_p_eq_3_n2 : p = 3) then -- This hypothesis is derived from subprob_p_eq_3_for_n2
      subprob_n2_p3_equation :≡ 3*q*r - 1 = 2 * (3-1)*(q-1)*(r-1)
      subprob_n2_p3_equation_proof ⇐ show subprob_n2_p3_equation by sorry
      subprob_n2_p3_simplified :≡ 3*q*r - 1 = 4*(q-1)*(r-1)
      subprob_n2_p3_simplified_proof ⇐ show subprob_n2_p3_simplified by sorry
      subprob_n2_p3_expanded :≡ 4*(q-1)*(r-1) = 4*q*r - 4*q - 4*r + 4
      subprob_n2_p3_expanded_proof ⇐ show subprob_n2_p3_expanded by sorry
      subprob_n2_p3_rearranged :≡ q*r - 4*q - 4*r + 5 = 0
      subprob_n2_p3_rearranged_proof ⇐ show subprob_n2_p3_rearranged by sorry
      subprob_n2_p3_factorized :≡ (q-4)*(r-4) = 11
      subprob_n2_p3_factorized_proof ⇐ show subprob_n2_p3_factorized by sorry

      -- Since p=3 < q and q is odd, q ≥ 5. So q-4 ≥ 1.
      subprob_q_minus_4_pos :≡ q-4 > 0
      subprob_q_minus_4_pos_proof ⇐ show subprob_q_minus_4_pos by sorry

      -- Since 11 is prime, q-4=1 and r-4=11 (because q-4 < r-4 as q < r)
      subprob_q_eq_5_r_eq_15_for_n2_p3 :≡ q=5 ∧ r=15
      subprob_q_eq_5_r_eq_15_for_n2_p3_proof ⇐ show subprob_q_eq_5_r_eq_15_for_n2_p3 by sorry

      subprob_sol1 :≡ p = 3 ∧ q = 5 ∧ r = 15 -- Using p=3 from h_p_eq_3_n2
      subprob_sol1_proof ⇐ show subprob_sol1 by sorry

  -- Step 4: Case n ≥ 3
  suppose (h_n_ge_3 : n ≥ 3) then
    -- Subcase 4.1: p=2 and n ≥ 3
    suppose (h_p_eq_2_n_ge_3 : p = 2) then
      -- From hn_def: 2qr - 1 = n(2-1)(q-1)(r-1) = n(q-1)(r-1)
      -- (n-2)qr + (n+1) = n(q+r)
      subprob_n_ge_3_p2_eq_intermediate :≡ (n-2)*q*r + (n+1) = n*(q+r)
      subprob_n_ge_3_p2_eq_intermediate_proof ⇐ show subprob_n_ge_3_p2_eq_intermediate by sorry
      -- From inequality analysis: n-2 < n/r + n/q. With p=2 < q < r, q ≥ 3, r ≥ 4.
      -- n-2 < n/3 + n/4 = 7n/12  => 5n < 24 => n < 4.8
      subprob_n_lt_4_8_real_for_p2 :≡ (n:ℝ) < (24:ℝ)/(5:ℝ)
      subprob_n_lt_4_8_real_for_p2_proof ⇐ show subprob_n_lt_4_8_real_for_p2 by sorry
      -- Since n ≥ 3 is integer, n can be 3 or 4.
      subprob_n_is_3_or_4_for_p2 :≡ n = 3 ∨ n = 4
      subprob_n_is_3_or_4_for_p2_proof ⇐ show subprob_n_is_3_or_4_for_p2 by sorry

      suppose (h_n_eq_3_p2 : n = 3) then -- This is one case from subprob_n_is_3_or_4_for_p2
        -- (3-2)qr + (3+1) = 3(q+r) => qr + 4 = 3q+3r
        subprob_n3_p2_eq :≡ q*r + 4 = 3*q + 3*r
        subprob_n3_p2_eq_proof ⇐ show subprob_n3_p2_eq by sorry
        subprob_n3_p2_factorized :≡ (q-3)*(r-3) = 5
        subprob_n3_p2_factorized_proof ⇐ show subprob_n3_p2_factorized by sorry
        -- Since p=2 < q, q ≥ 3. If q=3, q-3=0, so 0=5 (impossible). So q-3 > 0.
        subprob_q_minus_3_pos_p2_n3 :≡ q-3 > 0
        subprob_q_minus_3_pos_p2_n3_proof ⇐ show subprob_q_minus_3_pos_p2_n3 by sorry
        -- Since 5 is prime, q-3=1 and r-3=5 (as q-3 < r-3)
        subprob_q_eq_4_r_eq_8_for_n3_p2 :≡ q=4 ∧ r=8
        subprob_q_eq_4_r_eq_8_for_n3_p2_proof ⇐ show subprob_q_eq_4_r_eq_8_for_n3_p2 by sorry
        subprob_sol2 :≡ p = 2 ∧ q = 4 ∧ r = 8 -- Using p=2 from h_p_eq_2_n_ge_3
        subprob_sol2_proof ⇐ show subprob_sol2 by sorry

      suppose (h_n_eq_4_p2 : n = 4) then -- This is other case from subprob_n_is_3_or_4_for_p2
        -- (4-2)qr + (4+1) = 4(q+r) => 2qr + 5 = 4q+4r
        subprob_n4_p2_eq :≡ 2*q*r + 5 = 4*q + 4*r
        subprob_n4_p2_eq_proof ⇐ show subprob_n4_p2_eq by sorry
        subprob_n4_p2_rearranged :≡ 2*(q*r - 2*q - 2*r) = -5
        subprob_n4_p2_rearranged_proof ⇐ show subprob_n4_p2_rearranged by sorry
        -- LHS is even, RHS is odd. Contradiction.
        subprob_n4_p2_impossible :≡ False
        subprob_n4_p2_impossible_proof ⇐ show subprob_n4_p2_impossible by sorry

    -- Subcase 4.2: p=3 and n ≥ 3
    suppose (h_p_eq_3_n_ge_3 : p = 3) then
      -- (2n-3)qr + (2n+1) = 2n(q+r)
      subprob_n_ge_3_p3_eq_intermediate :≡ (2*n-3)*q*r + (2*n+1) = 2*n*(q+r)
      subprob_n_ge_3_p3_eq_intermediate_proof ⇐ show subprob_n_ge_3_p3_eq_intermediate by sorry
      -- Inequality: 2n-3 < 2n/r + 2n/q. With p=3 < q < r, q ≥ 4, r ≥ 5.
      -- 2n-3 < 2n/4 + 2n/5 = 9n/10 => 11n < 30 => n < 30/11 ≈ 2.72
      subprob_n_lt_2_72_real_for_p3 :≡ (n:ℝ) < (30:ℝ)/(11:ℝ)
      subprob_n_lt_2_72_real_for_p3_proof ⇐ show subprob_n_lt_2_72_real_for_p3 by sorry
      -- This contradicts n ≥ 3.
      subprob_n_ge_3_p3_impossible :≡ False
      subprob_n_ge_3_p3_impossible_proof ⇐ show subprob_n_ge_3_p3_impossible by sorry

    -- Subcase 4.3: p=4 and n ≥ 3
    suppose (h_p_eq_4_n_ge_3 : p = 4) then
      -- (3n-4)qr + (3n+1) = 3n(q+r)
      subprob_n_ge_3_p4_eq_intermediate :≡ (3*n-4)*q*r + (3*n+1) = 3*n*(q+r)
      subprob_n_ge_3_p4_eq_intermediate_proof ⇐ show subprob_n_ge_3_p4_eq_intermediate by sorry
      -- Parity: 4qr-1 is odd. So 3n(4-1)(q-1)(r-1) = 3n*3*(q-1)(r-1) is odd.
      -- So 3n is odd, 3 is odd, q-1 is odd, r-1 is odd.
      -- n is odd. q is even. r is even.
      subprob_n_odd_q_r_even_for_p4 :≡ n % 2 = 1 ∧ q % 2 = 0 ∧ r % 2 = 0
      subprob_n_odd_q_r_even_for_p4_proof ⇐ show subprob_n_odd_q_r_even_for_p4 by sorry
      -- With p=4 < q < r, q,r even: q ≥ 6, r ≥ 8.
      -- Inequality: 3n-4 < 3n/r + 3n/q.
      -- 3n-4 < 3n/6 + 3n/8 = 7n/8 => 17n < 32 => n < 32/17 ≈ 1.88
      subprob_n_lt_1_88_real_for_p4 :≡ (n:ℝ) < (32:ℝ)/(17:ℝ)
      subprob_n_lt_1_88_real_for_p4_proof ⇐ show subprob_n_lt_1_88_real_for_p4 by sorry
      -- This contradicts n ≥ 3 (and n odd).
      subprob_n_ge_3_p4_impossible :≡ False
      subprob_n_ge_3_p4_impossible_proof ⇐ show subprob_n_ge_3_p4_impossible by sorry

  -- The final goal combines results from all cases.
  -- The notation (p, q, r) = (x, y, z) is assumed to be equivalent to p=x ∧ q=y ∧ r=z.
  subprob_final_goal :≡ (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15)
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
variable (p q r : ℤ) (h₀ : 1 < p ∧ p < q ∧ q < r) (h₁ : (p - 1) * (q - 1) * (r - 1) ∣ p * q * r - 1)
play

  ⟨n, hn_def⟩ := h₁

  subprob_p_minus_1_pos :≡ p - 1 > 0
  subprob_p_minus_1_pos_proof ⇐ show subprob_p_minus_1_pos by



    rcases h₀ with ⟨h_p_gt_1, h_p_lt_q, h_q_lt_r⟩


    rw [gt_iff_lt]
    rw [Int.sub_pos]

    exact h_p_gt_1




  subprob_q_minus_1_pos :≡ q - 1 > 0
  subprob_q_minus_1_pos_proof ⇐ show subprob_q_minus_1_pos by

    rw [gt_iff_lt, Int.sub_pos]

    have h_1_lt_p : 1 < p := by
      rw [←Int.sub_pos]
      exact subprob_p_minus_1_pos_proof

    rcases h₀ with ⟨_, ⟨h_p_lt_q, _⟩⟩

    apply lt_trans h_1_lt_p
    exact h_p_lt_q

  subprob_r_minus_1_pos :≡ r - 1 > 0
  subprob_r_minus_1_pos_proof ⇐ show subprob_r_minus_1_pos by


    rcases h₀ with ⟨h_1_lt_p, h_pq_and_qr⟩
    rcases h_pq_and_qr with ⟨h_p_lt_q, h_q_lt_r⟩

    have h_1_lt_q : (1 : ℤ) < q := by
      apply lt_trans h_1_lt_p h_p_lt_q

    have h_1_lt_r : (1 : ℤ) < r := by
      apply lt_trans h_1_lt_q h_q_lt_r

    apply sub_pos_of_lt h_1_lt_r


  denominator_val := (p - 1) * (q - 1) * (r - 1) -- Renamed to avoid "pos" in name of a value
  subprob_denominator_pos :≡ denominator_val > 0
  subprob_denominator_pos_proof ⇐ show subprob_denominator_pos by

    rw [denominator_val_def]


    have h_first_two_factors_pos : (p - (1 : ℤ)) * (q - (1 : ℤ)) > 0 := by
      apply mul_pos
      exact subprob_p_minus_1_pos_proof
      exact subprob_q_minus_1_pos_proof

    apply mul_pos
    exact h_first_two_factors_pos
    exact subprob_r_minus_1_pos_proof

  numerator_val := p * q * r - 1 -- Renamed to avoid "pos" in name of a value
  subprob_numerator_pos :≡ numerator_val > 0
  subprob_numerator_pos_proof ⇐ show subprob_numerator_pos by






    rw [numerator_val_def]
    rw [hn_def]
    rw [←denominator_val_def]

    apply (Int.mul_pos subprob_denominator_pos_proof)

    have h_expansion : p * q * r - 1 =
        (p - 1) * (q - 1) * (r - 1) +
        (p - 1) * (q - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1) +
        (p - 1) + (q - 1) + (r - 1) := by
      ring

    let sop : ℤ := (p - 1) * (q - 1) + (p - 1) * (r - 1) + (q - 1) * (r - 1) +
                   (p - 1) + (q - 1) + (r - 1)

    have h_num_eq_den_plus_sop : p * q * r - 1 = denominator_val + sop := by
      rw [denominator_val_def]
      conv_rhs =>
        dsimp only [sop]
        simp only [←Int.add_assoc]
      exact h_expansion

    have h_sop_eq_den_mul_n_minus_1 : sop = denominator_val * (n - 1) := by
      have h_prqr_eq_den_mul_n : p * q * r - 1 = denominator_val * n := by
        rw [hn_def, denominator_val_def]
      have h_intermediate_eq : denominator_val + sop = denominator_val * n := by
        rw [←h_num_eq_den_plus_sop, h_prqr_eq_den_mul_n]
      linarith [h_intermediate_eq]

    have hp1_ge_1 : p - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_p_minus_1_pos_proof
    have hq1_ge_1 : q - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_q_minus_1_pos_proof
    have hr1_ge_1 : r - 1 ≥ 1 := Int.pos_iff_one_le.mp subprob_r_minus_1_pos_proof

    have hpq_ge_1 : (p - 1) * (q - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hp1_ge_1 hq1_ge_1
    have hpr_ge_1 : (p - 1) * (r - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hp1_ge_1 hr1_ge_1
    have hqr_ge_1 : (q - 1) * (r - 1) ≥ 1 := one_le_mul_of_one_le_of_one_le hq1_ge_1 hr1_ge_1

    have h_sop_ge_6 : sop ≥ 6 := by
      linarith [hp1_ge_1, hq1_ge_1, hr1_ge_1, hpq_ge_1, hpr_ge_1, hqr_ge_1]

    have h_sop_pos : sop > 0 := by
      linarith [h_sop_ge_6]

    rw [h_sop_eq_den_mul_n_minus_1] at h_sop_pos
    have h_n_minus_1_pos : n - 1 > 0 :=
      (mul_pos_iff_of_pos_left subprob_denominator_pos_proof).mp h_sop_pos

    have h_n_minus_1_ge_1 : n - 1 ≥ 1 := Int.pos_iff_one_le.mp h_n_minus_1_pos
    linarith [h_n_minus_1_ge_1]

  subprob_n_pos :≡ n ≥ 1
  subprob_n_pos_proof ⇐ show subprob_n_pos by




    have h_relation : numerator_val = denominator_val * n := by
      simp [numerator_val_def, denominator_val_def, hn_def]

    have h_prod_pos : denominator_val * n > 0 := by
      rw [←h_relation]
      exact subprob_numerator_pos_proof

    have n_pos : n > 0 := by
      apply (mul_pos_iff_of_pos_left subprob_denominator_pos_proof).mp
      exact h_prod_pos

    apply (Int.pos_iff_one_le).mp
    exact n_pos


  subprob_n_lt_prod_fractions_real :≡ (n : ℝ) < ((p : ℝ) / ((p : ℝ) - 1)) * ((q : ℝ) / ((q : ℝ) - 1)) * ((r : ℝ) / ((r : ℝ) - 1))
  subprob_n_lt_prod_fractions_real_proof ⇐ show subprob_n_lt_prod_fractions_real by









    let pr := (p : ℝ)
    let qr := (q : ℝ)
    let rr := (r : ℝ)
    let nr := (n : ℝ)

    have h_pr_minus_1_pos : pr - 1 > 0 := by
      rw [←Int.cast_one, ←Int.cast_sub p 1, gt_iff_lt, Int.cast_pos]
      exact subprob_p_minus_1_pos_proof
    have h_qr_minus_1_pos : qr - 1 > 0 := by
      rw [←Int.cast_one, ←Int.cast_sub q 1, gt_iff_lt, Int.cast_pos]
      exact subprob_q_minus_1_pos_proof
    have h_rr_minus_1_pos : rr - 1 > 0 := by
      rw [←Int.cast_one, ←Int.cast_sub r 1, gt_iff_lt, Int.cast_pos]
      exact subprob_r_minus_1_pos_proof

    have h_pr_minus_1_ne_zero : pr - 1 ≠ 0 := by exact ne_of_gt h_pr_minus_1_pos
    have h_qr_minus_1_ne_zero : qr - 1 ≠ 0 := by exact ne_of_gt h_qr_minus_1_pos
    have h_rr_minus_1_ne_zero : rr - 1 ≠ 0 := by exact ne_of_gt h_rr_minus_1_pos

    have h_rhs_expr : ((p : ℝ) / ((p : ℝ) - 1)) * ((q : ℝ) / ((q : ℝ) - 1)) * ((r : ℝ) / ((r : ℝ) - 1)) =
                      (pr * qr * rr) / ((pr - 1) * (qr - 1) * (rr - 1)) := by
      field_simp [h_pr_minus_1_ne_zero, h_qr_minus_1_ne_zero, h_rr_minus_1_ne_zero]

    rw [h_rhs_expr]

    have hn_def_real : (pr * qr * rr - 1) = ((pr - 1) * (qr - 1) * (rr - 1)) * nr := by
      simp only [pr, qr, rr, nr]
      norm_cast

    let den_real := (pr - 1) * (qr - 1) * (rr - 1)

    have h_den_real_pos : den_real > 0 := by
      exact mul_pos (mul_pos h_pr_minus_1_pos h_qr_minus_1_pos) h_rr_minus_1_pos

    have h_den_real_ne_zero : den_real ≠ 0 := by exact ne_of_gt h_den_real_pos

    have h_nr_expr : nr = (pr * qr * rr - 1) / den_real := by
      apply (eq_div_iff h_den_real_ne_zero).mpr
      rw [hn_def_real]
      apply mul_comm

    change nr < pr * qr * rr / ((pr - (1 : ℝ)) * (qr - (1 : ℝ)) * (rr - (1 : ℝ)))
    rw [h_nr_expr]

    apply (div_lt_div_right h_den_real_pos).mpr

    exact sub_one_lt (pr * qr * rr)

  f := fun (x : ℝ) => x / (x - 1)
  subprob_f_decreasing :≡ ∀ (x₁ x₂ : ℝ), 1 < x₁ → x₁ < x₂ → f x₂ < f x₁
  subprob_f_decreasing_proof ⇐ show subprob_f_decreasing by

    intros x₁ x₂ h_x1_gt_1 h_x1_lt_x2

    rw [f_def' x₂, f_def' x₁]

    have hx1m1_pos : x₁ - 1 > 0 := by
      linarith [h_x1_gt_1]

    have hx2m1_pos : x₂ - 1 > 0 := by
      linarith [h_x1_gt_1, h_x1_lt_x2]

    apply (div_lt_div_iff hx2m1_pos hx1m1_pos).mpr

    simp only [mul_sub, mul_one]

    rw [mul_comm x₂ x₁]

    apply (sub_lt_sub_iff_left (x₁ * x₂)).mpr

    exact h_x1_lt_x2

  suppose (h_p_ge_5 : p ≥ 5) then
    subprob_p_frac_le_5_4 :≡ (p : ℝ) / ((p : ℝ) - 1) ≤ (5 : ℝ) / (4 : ℝ)
    subprob_p_frac_le_5_4_proof ⇐ show subprob_p_frac_le_5_4 by




      rw [← f_def' (p : ℝ)]

      have h_f_5_eval : f (5 : ℝ) = (5 : ℝ) / (4 : ℝ) := by
        rw [f_def']
        have h_denom_5 : (5 : ℝ) - (1 : ℝ) = (4 : ℝ) := by
          norm_num
        rw [h_denom_5]

      rw [←h_f_5_eval]

      have h_p_ge_5_real : (p : ℝ) ≥ (5 : ℝ) := by
        norm_cast

      rcases h_p_ge_5_real.eq_or_gt with h_p_eq_5 | h_p_gt_5
      .
        rw [h_p_eq_5]
      .
        have h_1_lt_5 : (1 : ℝ) < (5 : ℝ) := by
          norm_num

        have h_f_strict_ineq : f (p : ℝ) < f (5 : ℝ) :=
          subprob_f_decreasing_proof (5 : ℝ) (p : ℝ) h_1_lt_5 h_p_gt_5

        exact le_of_lt h_f_strict_ineq
    subprob_q_ge_6 :≡ q ≥ 6
    subprob_q_ge_6_proof ⇐ show subprob_q_ge_6 by
      linarith [h₀.2.1, h_p_ge_5]
    subprob_q_frac_le_6_5 :≡ (q : ℝ) / ((q : ℝ) - 1) ≤ (6 : ℝ) / (5 : ℝ)
    subprob_q_frac_le_6_5_proof ⇐ show subprob_q_frac_le_6_5 by



      rw [← f_def' (q : ℝ)]

      have h_f6_eval : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by
        rw [f_def' (6 : ℝ)]
        norm_num

      rw [← h_f6_eval]

      have h_one_lt_six : (1 : ℝ) < (6 : ℝ) := by
        norm_num

      have h_one_lt_q_int : (1 : ℤ) < q := by
        apply lt_trans h₀.1 h₀.2.1

      have h_one_lt_q_real : (1 : ℝ) < (q : ℝ) := by
        exact_mod_cast h_one_lt_q_int

      rcases (LE.le.eq_or_gt subprob_q_ge_6_proof) with h_q_eq_6_int | h_q_gt_6_int

      .
        rw [h_q_eq_6_int]
        apply le_refl

      .
        have h_6_lt_q_real : (6 : ℝ) < (q : ℝ) := by
          exact_mod_cast h_q_gt_6_int

        have h_f_q_lt_f_6 : f (q : ℝ) < f (6 : ℝ) := by
          apply subprob_f_decreasing_proof (6 : ℝ) (q : ℝ)
          . exact h_one_lt_six
          . exact h_6_lt_q_real

        apply le_of_lt
        exact h_f_q_lt_f_6
    subprob_r_ge_7 :≡ r ≥ 7 -- Since q < r and q ≥ 6, r ≥ q+1 ≥ 7
    subprob_r_ge_7_proof ⇐ show subprob_r_ge_7 by

      have h_q_lt_r : q < r := h₀.2.2
      have h_q_plus_1_le_r : q + 1 ≤ r := by
        exact h_q_lt_r

      have h_q_ge_6 : q ≥ (6 : ℤ) := subprob_q_ge_6_proof
      have h_seven_le_q_plus_1 : (7 : ℤ) ≤ q + 1 := by
        have h_six_plus_one_le_q_plus_one : (6 : ℤ) + 1 ≤ q + 1 := by
          apply Int.add_le_add_right
          exact h_q_ge_6
        have h_seven_eq_six_plus_one : (7 : ℤ) = (6 : ℤ) + 1 := by norm_num
        rw [h_seven_eq_six_plus_one]
        exact h_six_plus_one_le_q_plus_one

      apply le_trans
      · exact h_seven_le_q_plus_1
      · exact h_q_plus_1_le_r


    subprob_r_frac_le_7_6 :≡ (r : ℝ) / ((r : ℝ) - 1) ≤ (7 : ℝ) / (6 : ℝ)
    subprob_r_frac_le_7_6_proof ⇐ show subprob_r_frac_le_7_6 by

      have h_lhs_eq_f_r : (r : ℝ) / ((r : ℝ) - 1) = f (r : ℝ) := by
        rw [f_def' (r : ℝ)]
      have h_rhs_eq_f_7 : (7 : ℝ) / (6 : ℝ) = f (7 : ℝ) := by
        rw [f_def' (7 : ℝ)]
        have h_denom_7 : (7 : ℝ) - 1 = (6 : ℝ) := by norm_num
        rw [h_denom_7]

      rw [h_lhs_eq_f_r, h_rhs_eq_f_7]

      have hr_ge_7_real : (r : ℝ) ≥ (7 : ℝ) := by
        exact Int.cast_le.mpr subprob_r_ge_7_proof

      rcases hr_ge_7_real.eq_or_gt with hr_eq_7 | hr_gt_7
      .
        rw [hr_eq_7]
      .
        have h_7_gt_1 : (1 : ℝ) < (7 : ℝ) := by
          norm_num

        have f_r_lt_f_7 : f (r : ℝ) < f (7 : ℝ) := by
          apply subprob_f_decreasing_proof (7 : ℝ) (r : ℝ) h_7_gt_1 hr_gt_7

        apply le_of_lt
        exact f_r_lt_f_7


    subprob_n_lt_7_4_real :≡ (n : ℝ) < (7 : ℝ) / (4 : ℝ)
    subprob_n_lt_7_4_real_proof ⇐ show subprob_n_lt_7_4_real by


      have p_minus_1_real_pos : (↑p : ℝ) - 1 > 0 := by
        rw [←Int.cast_one, ←Int.cast_sub, gt_iff_lt, Int.cast_pos]
        exact subprob_p_minus_1_pos_proof

      have q_minus_1_real_pos : (↑q : ℝ) - 1 > 0 := by
        rw [←Int.cast_one, ←Int.cast_sub, gt_iff_lt, Int.cast_pos]
        exact subprob_q_minus_1_pos_proof

      have r_minus_1_real_pos : (↑r : ℝ) - 1 > 0 := by
        rw [←Int.cast_one, ←Int.cast_sub, gt_iff_lt, Int.cast_pos]
        exact subprob_r_minus_1_pos_proof

      have p_gt_1 : p > 1 := h₀.1
      have p_real_pos : (↑p : ℝ) > 0 := by
        apply Int.cast_pos.mpr
        linarith [p_gt_1]

      have q_gt_p : p < q := h₀.2.1
      have q_real_pos : (↑q : ℝ) > 0 := by
        apply Int.cast_pos.mpr
        have q_gt_1 : q > 1 := by linarith [p_gt_1, q_gt_p]
        linarith [q_gt_1]

      have r_gt_q : q < r := h₀.2.2
      have r_real_pos : (↑r : ℝ) > 0 := by
        apply Int.cast_pos.mpr
        have q_gt_1 : q > 1 := by linarith [p_gt_1, q_gt_p]
        have r_gt_1 : r > 1 := by linarith [q_gt_1, r_gt_q]
        linarith [r_gt_1]

      have val_p_frac_pos : (↑p : ℝ) / (↑p - 1) > 0 := div_pos p_real_pos p_minus_1_real_pos
      have val_q_frac_pos : (↑q : ℝ) / (↑q - 1) > 0 := div_pos q_real_pos q_minus_1_real_pos
      have val_r_frac_pos : (↑r : ℝ) / (↑r - 1) > 0 := div_pos r_real_pos r_minus_1_real_pos

      have five_fourths_pos : (5:ℝ)/4 > 0 := by norm_num
      have six_fifths_pos : (6:ℝ)/5 > 0 := by norm_num

      have h_prod_pq_le : (↑p : ℝ) / (↑p - 1) * ((↑q : ℝ) / (↑q - 1)) ≤ (5/4 : ℝ) * (6/5 : ℝ) := by
        apply mul_le_mul
        · exact subprob_p_frac_le_5_4_proof
        · exact subprob_q_frac_le_6_5_proof
        · exact le_of_lt val_q_frac_pos
        · exact le_of_lt five_fourths_pos

      have five_fourths_mul_six_fifths_pos : (5/4 : ℝ) * (6/5 : ℝ) > 0 := by
        apply mul_pos five_fourths_pos six_fifths_pos

      have h_prod_pqr_le : ((↑p : ℝ) / (↑p - 1)) * ((↑q : ℝ) / (↑q - 1)) * ((↑r : ℝ) / (↑r - 1)) ≤ ((5:ℝ)/4) * ((6:ℝ)/5) * ((7:ℝ)/6) := by
        apply mul_le_mul
        · exact h_prod_pq_le
        · exact subprob_r_frac_le_7_6_proof
        · exact le_of_lt val_r_frac_pos
        · exact le_of_lt five_fourths_mul_six_fifths_pos

      have h_rhs_value : ((5:ℝ)/4) * ((6:ℝ)/5) * ((7:ℝ)/6) = (7:ℝ)/4 := by
        norm_num

      rw [h_rhs_value] at h_prod_pqr_le
      exact lt_of_lt_of_le subprob_n_lt_prod_fractions_real_proof h_prod_pqr_le


    subprob_n_eq_1_if_p_ge_5 :≡ n = 1
    subprob_n_eq_1_if_p_ge_5_proof ⇐ show subprob_n_eq_1_if_p_ge_5 by
      have h_n_lt_2_real : (n : ℝ) < 2 := by linarith [subprob_n_lt_7_4_real_proof]
      have h_n_lt_2 : n < 2 := by
        exact Int.cast_lt.mp h_n_lt_2_real
      have h_n_eq_1 : n = 1 := by
        linarith [subprob_n_pos_proof, h_n_lt_2]
      exact h_n_eq_1

  suppose (h_n_eq_1 : n = 1) then
    subprob_n1_equation :≡ p * q * r - 1 = (p - 1) * (q - 1) * (r - 1)
    subprob_n1_equation_proof ⇐ show subprob_n1_equation by
      rw [hn_def]
      rw [h_n_eq_1]
      ring
    subprob_n1_expanded :≡ (p - 1) * (q - 1) * (r - 1) = p*q*r - (p*q + p*r + q*r) + (p+q+r) - 1
    subprob_n1_expanded_proof ⇐ show subprob_n1_expanded by

      ring
    subprob_n1_simplified :≡ p*q + p*r + q*r = p + q + r
    subprob_n1_simplified_proof ⇐ show subprob_n1_simplified by



      have h_combined : p * q * r - (1 : ℤ) = p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ) := by
        exact Eq.trans subprob_n1_equation_proof subprob_n1_expanded_proof

      have h_eq_zero : (p * q * r - (1 : ℤ)) - (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ)) = 0 := by
        rw [h_combined]
        exact sub_self (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ))

      have h_simplified_lhs : (p * q * r - (1 : ℤ)) - (p * q * r - (p * q + p * r + q * r) + (p + q + r) - (1 : ℤ)) = (p * q + p * r + q * r) - (p + q + r) := by
        ring

      rw [h_simplified_lhs] at h_eq_zero

      exact eq_of_sub_eq_zero h_eq_zero


    subprob_p_lt_pq :≡ p < p * q
    subprob_p_lt_pq_proof ⇐ show subprob_p_lt_pq by




      have h_1_lt_p : (1 : ℤ) < p := h₀.1
      have h_p_pos : 0 < p := lt_trans (by norm_num : (0 : ℤ) < 1) h_1_lt_p
      rw [← Int.mul_one p]
      have h_p_mul_1_pos : p * (1 : ℤ) > 0 := mul_pos h_p_pos (zero_lt_one : (0 : ℤ) < 1)
      rw [← mul_one (p * (1 : ℤ))]
      rw [mul_assoc (p * (1 : ℤ)) (1 : ℤ) q]
      rw [mul_lt_mul_iff_of_pos_left h_p_mul_1_pos]
      simp only [one_mul]
      have h_p_lt_q : p < q := h₀.2.1
      have h_1_lt_q : 1 < q := lt_trans h_1_lt_p h_p_lt_q
      exact h_1_lt_q
    subprob_q_lt_qr :≡ q < q * r
    subprob_q_lt_qr_proof ⇐ show subprob_q_lt_qr by











      rcases h₀ with ⟨h_1_lt_p, h_p_lt_q, h_q_lt_r⟩

      have h_1_lt_q : (1 : ℤ) < q := by
        apply lt_trans h_1_lt_p h_p_lt_q

      have h_q_pos : (0 : ℤ) < q := by
        linarith [h_1_lt_q]

      rw [← mul_one q]

      rw [mul_assoc q (1 : ℤ) r]
      rw [mul_lt_mul_iff_of_pos_left h_q_pos]
      simp only [one_mul]

      have h_1_lt_r : (1 : ℤ) < r := by
        apply lt_trans h_1_lt_q h_q_lt_r

      exact h_1_lt_r
    subprob_r_lt_rp :≡ r < r * p
    subprob_r_lt_rp_proof ⇐ show subprob_r_lt_rp by



      rcases h₀ with ⟨h_p_gt_1, h_p_lt_q, h_q_lt_r⟩

      have h_r_pos : 0 < r := by
        linarith [h_p_gt_1, h_p_lt_q, h_q_lt_r]

      rw [mul_comm r p]

      apply (lt_mul_iff_one_lt_left h_r_pos).mpr

      exact h_p_gt_1

    subprob_sum_lt_sum_prod :≡ p + q + r < p*q + p*r + q*r
    subprob_sum_lt_sum_prod_proof ⇐ show subprob_sum_lt_sum_prod by


      have h_p_lt_pq : p < p * q := subprob_p_lt_pq_proof

      have h_q_lt_qr : q < q * r := subprob_q_lt_qr_proof

      have h_r_lt_rp_orig : r < r * p := subprob_r_lt_rp_proof

      have h_r_lt_pr : r < p * r := by
        rw [mul_comm p r]
        exact h_r_lt_rp_orig

      have h_p_plus_q_lt_pq_plus_qr : p + q < p * q + q * r := by
        apply @_root_.add_lt_add
        exact h_p_lt_pq
        exact h_q_lt_qr

      have h_sum_unordered_rhs : p + q + r < p * q + q * r + p * r := by
        apply @_root_.add_lt_add
        exact h_p_plus_q_lt_pq_plus_qr
        exact h_r_lt_pr

      have h_rhs_reorder_eq : p * q + q * r + p * r = p * q + p * r + q * r := by
        rw [add_assoc (p*q) (q*r) (p*r)]
        rw [add_comm (q*r) (p*r)]
        rw [←add_assoc (p*q) (p*r) (q*r)]

      rw [h_rhs_reorder_eq] at h_sum_unordered_rhs

      exact h_sum_unordered_rhs


    subprob_n1_impossible :≡ False
    subprob_n1_impossible_proof ⇐ show subprob_n1_impossible by



      have h_eq : p * q + p * r + q * r = p + q + r := subprob_n1_simplified_proof
      have h_lt : p + q + r < p * q + p * r + q * r := subprob_sum_lt_sum_prod_proof

      have h_contradiction : p + q + r < p + q + r := by
        rw [h_eq] at h_lt
        exact h_lt

      exact lt_irrefl (p + q + r) h_contradiction


  subprob_p_lt_5 :≡ p < 5
  subprob_p_lt_5_proof ⇐ show subprob_p_lt_5 by


    by_contra h_not_p_lt_5

    have hp_ge_5 : p ≥ 5 := by
      apply Int.not_lt.mp
      exact h_not_p_lt_5

    have hn_eq_1 : n = 1 := by
      apply subprob_n_eq_1_if_p_ge_5_proof
      exact hp_ge_5

    have h_false : False := by
      apply subprob_n1_impossible_proof
      exact hn_eq_1

    exact h_false

  subprob_p_cases :≡ p = 2 ∨ p = 3 ∨ p = 4
  subprob_p_cases_proof ⇐ show subprob_p_cases by



    have h_p_ge_2 : (2 : ℤ) ≤ p := by
      exact Int.add_one_le_of_lt h₀.1

    have h_p_le_4 : p ≤ (4 : ℤ) := by
      exact Int.le_sub_one_of_lt subprob_p_lt_5_proof

    interval_cases p

    .
      left
      rfl

    .
      right
      left
      rfl

    .
      right
      right
      rfl


  suppose (h_n_eq_2 : n = 2) then
    subprob_n2_equation :≡ p*q*r - 1 = 2 * (p-1)*(q-1)*(r-1)
    subprob_n2_equation_proof ⇐ show subprob_n2_equation by


      rw [hn_def]

      rw [h_n_eq_2]

      ring
    subprob_pqr_minus_1_even :≡ (p*q*r - 1) % 2 = 0
    subprob_pqr_minus_1_even_proof ⇐ show subprob_pqr_minus_1_even by








      rw [subprob_n2_equation_proof]
      have h_assoc : (2 : ℤ) * (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) =
                       (2 : ℤ) * ( (p - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) ) := by ring
      rw [h_assoc]
      rw [← denominator_val_def]

      rw [Int.mul_comm (2 : ℤ) denominator_val]
      exact Int.mul_emod_left denominator_val (2 : ℤ)
    subprob_pqr_odd :≡ (p*q*r) % 2 = 1
    subprob_pqr_odd_proof ⇐ show subprob_pqr_odd by





      rw [← Int.one_emod_two]

      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      . exact subprob_pqr_minus_1_even_proof

    subprob_p_q_r_all_odd :≡ p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1
    subprob_p_q_r_all_odd_proof ⇐ show subprob_p_q_r_all_odd by








      rw [← Int.odd_iff]

      rw [← Int.odd_iff]
      rw [← Int.odd_iff]

      rw [← Int.odd_iff] at subprob_pqr_odd_proof

      rw [Int.odd_mul] at subprob_pqr_odd_proof

      rcases subprob_pqr_odd_proof with ⟨hpq_odd, hr_odd⟩

      rw [Int.odd_mul] at hpq_odd

      rcases hpq_odd with ⟨hp_odd, hq_odd⟩

      exact ⟨hp_odd, hq_odd, hr_odd⟩

    subprob_p_eq_3_for_n2 :≡ p = 3
    subprob_p_eq_3_for_n2_proof ⇐ show subprob_p_eq_3_for_n2 by



      rcases subprob_p_q_r_all_odd_proof with ⟨hp_odd, _ , _⟩
      rcases subprob_p_cases_proof with hp_eq_2 | hp_eq_3 | hp_eq_4
      .
        rw [hp_eq_2] at hp_odd
        change (0 : ℤ) = 1 at hp_odd
        norm_num at hp_odd
      .
        exact hp_eq_3
      .
        rw [hp_eq_4] at hp_odd
        change (0 : ℤ) = 1 at hp_odd
        norm_num at hp_odd



    suppose (h_p_eq_3_n2 : p = 3) then
      subprob_n2_p3_equation :≡ 3*q*r - 1 = 2 * (3-1)*(q-1)*(r-1)
      subprob_n2_p3_equation_proof ⇐ show subprob_n2_p3_equation by


        rw [←h_p_eq_3_n2]

        exact subprob_n2_equation_proof
      subprob_n2_p3_simplified :≡ 3*q*r - 1 = 4*(q-1)*(r-1)
      subprob_n2_p3_simplified_proof ⇐ show subprob_n2_p3_simplified by

        rw [subprob_n2_p3_equation_proof]

        ring
      subprob_n2_p3_expanded :≡ 4*(q-1)*(r-1) = 4*q*r - 4*q - 4*r + 4
      subprob_n2_p3_expanded_proof ⇐ show subprob_n2_p3_expanded by



        have h_expand_factors : (q - 1) * (r - 1) = q * r - q - r + 1 := by
          ring

        rw [mul_assoc (4 : ℤ) (q - 1) (r - 1)]

        rw [h_expand_factors]

        ring

      subprob_n2_p3_rearranged :≡ q*r - 4*q - 4*r + 5 = 0
      subprob_n2_p3_rearranged_proof ⇐ show subprob_n2_p3_rearranged by


        have h_combined : (3 : ℤ) * q * r - (1 : ℤ) = (4 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r + (4 : ℤ) := by
          rw [subprob_n2_p3_simplified_proof]
          exact subprob_n2_p3_expanded_proof

        linarith [h_combined]
      subprob_n2_p3_factorized :≡ (q-4)*(r-4) = 11
      subprob_n2_p3_factorized_proof ⇐ show subprob_n2_p3_factorized by

        rw [← sub_eq_zero]
        have h_lhs_simplified : (q - 4) * (r - 4) - 11 = q * r - (4 : ℤ) * q - (4 : ℤ) * r + (5 : ℤ) := by
          ring
        rw [h_lhs_simplified]
        exact subprob_n2_p3_rearranged_proof

      subprob_q_minus_4_pos :≡ q-4 > 0
      subprob_q_minus_4_pos_proof ⇐ show subprob_q_minus_4_pos by













        rcases h₀ with ⟨_, hpq, _⟩
        rw [h_p_eq_3_n2] at hpq

        have h_q_ge_4 : q ≥ 4 := by linarith [hpq]

        have h_q_minus_4_ge_0 : q - 4 ≥ 0 := by
          exact Int.sub_nonneg_of_le h_q_ge_4

        have h_prod_eq_11 : (q - 4) * (r - 4) = 11 := subprob_n2_p3_factorized_proof

        have h_q_minus_4_ne_0 : q - 4 ≠ 0 := by
          intro h_q_minus_4_eq_0
          have h_prod_rewritten : (0 : ℤ) * (r - 4) = 11 := by
            rw [←h_q_minus_4_eq_0]
            exact h_prod_eq_11
          simp at h_prod_rewritten

        exact lt_of_le_of_ne h_q_minus_4_ge_0 (Ne.symm h_q_minus_4_ne_0)


      subprob_q_eq_5_r_eq_15_for_n2_p3 :≡ q=5 ∧ r=15
      subprob_q_eq_5_r_eq_15_for_n2_p3_proof ⇐ show subprob_q_eq_5_r_eq_15_for_n2_p3 by


















        let a := q - (4 : ℤ)
        let b := r - (4 : ℤ)
        have h_ab_eq_11 : a * b = (11 : ℤ) := subprob_n2_p3_factorized_proof

        have h_a_pos : a > (0 : ℤ) := subprob_q_minus_4_pos_proof

        have h_11_pos : (11 : ℤ) > 0 := by norm_num
        have h_ab_pos : a * b > 0 := by
          rw [h_ab_eq_11]
          exact h_11_pos
        have h_b_pos : b > (0 : ℤ) := by
          apply (mul_pos_iff_of_pos_left h_a_pos).mp
          exact h_ab_pos

        have h_a_ge_0 : a ≥ 0 := Int.le_of_lt h_a_pos
        have h_b_ge_0 : b ≥ 0 := Int.le_of_lt h_b_pos

        rcases Int.eq_ofNat_of_zero_le h_a_ge_0 with ⟨a_nat, ha_nat_eq_a⟩
        rcases Int.eq_ofNat_of_zero_le h_b_ge_0 with ⟨b_nat, hb_nat_eq_b⟩

        have h_prod_nat_cast_eq_11 : (↑a_nat : ℤ) * (↑b_nat : ℤ) = (11 : ℤ) := by
          rw [← ha_nat_eq_a, ← hb_nat_eq_b]
          exact h_ab_eq_11

        have h_prod_nat_cast_mul_eq_11 : ↑(a_nat * b_nat) = (11 : ℤ) := by
          rw [Nat.cast_mul]
          exact h_prod_nat_cast_eq_11

        have eleven_int_eq_coe_11_nat : (11 : ℤ) = ↑(11 : ℕ) := by rfl
        rw [eleven_int_eq_coe_11_nat] at h_prod_nat_cast_mul_eq_11

        have h_a_nat_mul_b_nat_eq_11 : a_nat * b_nat = 11 := by
          apply Nat.cast_inj.mp h_prod_nat_cast_mul_eq_11

        have h_11_prime_nat : Nat.Prime 11 := by decide

        have h_cases_nat : (a_nat = 1 ∧ b_nat = 11) ∨ (a_nat = 11 ∧ b_nat = 1) := by
          have hdvd_a : a_nat ∣ 11 := by
            exact ⟨b_nat, h_a_nat_mul_b_nat_eq_11.symm⟩
          have ha_cases : a_nat = 1 ∨ a_nat = 11 := Nat.Prime.eq_one_or_self_of_dvd h_11_prime_nat a_nat hdvd_a
          rcases ha_cases with ha_eq_1 | ha_eq_11
          .
            rw [ha_eq_1, one_mul] at h_a_nat_mul_b_nat_eq_11
            left
            exact ⟨ha_eq_1, h_a_nat_mul_b_nat_eq_11⟩
          .
            rw [ha_eq_11] at h_a_nat_mul_b_nat_eq_11
            have h_11_pos_nat : (11 : ℕ) > 0 := Nat.Prime.pos h_11_prime_nat
            have h_11_ne_zero : (11 : ℕ) ≠ 0 := Nat.ne_of_gt h_11_pos_nat
            have hb_eq_1 : b_nat = 11 / 11 := Nat.eq_div_of_mul_eq_right h_11_ne_zero h_a_nat_mul_b_nat_eq_11
            have h_div_self_11 : 11 / 11 = 1 := Nat.div_self h_11_pos_nat
            rw [h_div_self_11] at hb_eq_1
            right
            exact ⟨ha_eq_11, hb_eq_1⟩

        have h_q_lt_r : q < r := h₀.2.2
        have h_a_lt_b : a < b := by
          exact sub_lt_sub_right h_q_lt_r 4

        rw [ha_nat_eq_a, hb_nat_eq_b] at h_a_lt_b
        have h_a_nat_lt_b_nat : a_nat < b_nat := by
          apply Int.lt_of_ofNat_lt_ofNat
          exact h_a_lt_b

        have h_final_case : a_nat = 1 ∧ b_nat = 11 := by
          rcases h_cases_nat with ⟨hc1_left, hc1_right⟩ | ⟨hc2_left, hc2_right⟩
          .
            exact And.intro hc1_left hc1_right
          .
            exfalso
            have : (11 : ℕ) < (1 : ℕ) := by rwa [hc2_left, hc2_right] at h_a_nat_lt_b_nat
            norm_num at this

        apply And.intro
        .
          have h_a_nat_eq_1 : a_nat = 1 := h_final_case.1
          have h_a_eq_1 : a = (1 : ℤ) := by simp [h_a_nat_eq_1, ha_nat_eq_a]
          rw [show (5 : ℤ) = (1 : ℤ) + (4 : ℤ) by norm_num]
          rw [←sub_eq_iff_eq_add]
          exact h_a_eq_1
        .
          have h_b_nat_eq_11 : b_nat = 11 := h_final_case.2
          have h_b_eq_11 : b = (11 : ℤ) := by simp [h_b_nat_eq_11, hb_nat_eq_b]
          rw [show (15 : ℤ) = (11 : ℤ) + (4 : ℤ) by norm_num]
          rw [←sub_eq_iff_eq_add]
          exact h_b_eq_11


      subprob_sol1 :≡ p = 3 ∧ q = 5 ∧ r = 15
      subprob_sol1_proof ⇐ show subprob_sol1 by
        apply And.intro
        . exact h_p_eq_3_n2
        . exact subprob_q_eq_5_r_eq_15_for_n2_p3_proof

  suppose (h_n_ge_3 : n ≥ 3) then
    suppose (h_p_eq_2_n_ge_3 : p = 2) then
      subprob_n_ge_3_p2_eq_intermediate :≡ (n-2)*q*r + (n+1) = n*(q+r)
      subprob_n_ge_3_p2_eq_intermediate_proof ⇐ show subprob_n_ge_3_p2_eq_intermediate by
        have h_eq1 : (2 : ℤ) * q * r - (1 : ℤ) = ((2 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
          rw [←h_p_eq_2_n_ge_3]
          exact hn_def

        have h_eq2 : (2 : ℤ) * q * r - (1 : ℤ) = n * q * r - n * q - n * r + n := by
          rw [h_eq1]
          ring

        linarith [h_eq2]
      subprob_n_lt_4_8_real_for_p2 :≡ (n:ℝ) < (24:ℝ)/(5:ℝ)
      subprob_n_lt_4_8_real_for_p2_proof ⇐ show subprob_n_lt_4_8_real_for_p2 by







        have hp_val_eq_2 : (↑p : ℝ) = (2 : ℝ) := by
          rw [h_p_eq_2_n_ge_3]
          norm_cast

        have p_frac_val : (↑p : ℝ) / ((↑p : ℝ) - (1 : ℝ)) = (2 : ℝ) := by
          rw [hp_val_eq_2]
          have h_denom_ne_zero : (2 : ℝ) - (1 : ℝ) ≠ 0 := by norm_num
          field_simp [h_denom_ne_zero]
          norm_num

        have h_n_lt_2_fq_fr : (↑n : ℝ) < (2 : ℝ) * ((↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ))) * ((↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ))) := by
          apply lt_of_lt_of_eq subprob_n_lt_prod_fractions_real_proof
          rw [p_frac_val]

        rcases h₀ with ⟨_, h_p_lt_q, h_q_lt_r⟩

        have h_2_lt_q : (2 : ℤ) < q := by
          rw [h_p_eq_2_n_ge_3] at h_p_lt_q
          exact h_p_lt_q

        have h_q_ge_3 : q ≥ (3 : ℤ) := by linarith [h_2_lt_q]

        have h_r_ge_q_plus_1 : r ≥ q + (1 : ℤ) := by linarith [h_q_lt_r]
        have h_r_ge_4 : r ≥ (4 : ℤ) := by linarith [h_r_ge_q_plus_1, h_q_ge_3]

        let q_real := (↑q : ℝ)
        let r_real := (↑r : ℝ)

        have h_3_gt_1 : (3 : ℝ) > (1 : ℝ) := by norm_num
        have h_q_real_ge_3_real : q_real ≥ (3 : ℝ) := by
          dsimp [q_real]
          norm_cast

        have h_fq_le_f3 : q_real / (q_real - (1 : ℝ)) ≤ (3 : ℝ) / ((3 : ℝ) - (1 : ℝ)) := by
          have h_q_real_gt_1 : q_real > (1 : ℝ) := by norm_cast; linarith [h_q_ge_3]
          rw [← f_def' q_real, ← f_def' (3 : ℝ)]
          by_cases h_q_eq_3 : q_real = (3 : ℝ)
          . rw [h_q_eq_3]
          . have h_q_gt_3 : (3 : ℝ) < q_real := by exact lt_of_le_of_ne h_q_real_ge_3_real (Ne.symm h_q_eq_3)
            have res := subprob_f_decreasing_proof (3 : ℝ) q_real h_3_gt_1 h_q_gt_3
            exact le_of_lt res

        have val_f3_calc : (3 : ℝ) / ((3 : ℝ) - (1 : ℝ)) = (3 : ℝ) / (2 : ℝ) := by
          field_simp
          norm_num

        rw [val_f3_calc] at h_fq_le_f3

        have h_4_gt_1 : (4 : ℝ) > (1 : ℝ) := by norm_num
        have h_r_real_ge_4_real : r_real ≥ (4 : ℝ) := by
          dsimp [r_real]
          norm_cast

        have h_fr_le_f4 : r_real / (r_real - (1 : ℝ)) ≤ (4 : ℝ) / ((4 : ℝ) - (1 : ℝ)) := by
          have h_r_real_gt_1 : r_real > (1 : ℝ) := by norm_cast; linarith [h_r_ge_4]
          rw [← f_def' r_real, ← f_def' (4 : ℝ)]
          by_cases h_r_eq_4 : r_real = (4 : ℝ)
          . rw [h_r_eq_4]
          . have h_r_gt_4 : (4 : ℝ) < r_real := by exact lt_of_le_of_ne h_r_real_ge_4_real (Ne.symm h_r_eq_4)
            have res := subprob_f_decreasing_proof (4 : ℝ) r_real h_4_gt_1 h_r_gt_4
            exact le_of_lt res

        have val_f4_calc : (4 : ℝ) / ((4 : ℝ) - (1 : ℝ)) = (4 : ℝ) / (3 : ℝ) := by
          field_simp
          norm_num

        rw [val_f4_calc] at h_fr_le_f4

        have h_fq_pos : q_real / (q_real - (1 : ℝ)) > 0 := by
          have h_q_real_num_pos : q_real > 0 := by norm_cast; linarith [h_q_ge_3]
          have h_q_real_den_pos : q_real - (1 : ℝ) > 0 := by
            apply sub_pos.mpr
            norm_cast; linarith [h_q_ge_3]
          exact div_pos h_q_real_num_pos h_q_real_den_pos

        have h_fr_pos : r_real / (r_real - (1 : ℝ)) > 0 := by
          have h_r_real_num_pos : r_real > 0 := by norm_cast; linarith [h_r_ge_4]
          have h_r_real_den_pos : r_real - (1 : ℝ) > 0 := by
            apply sub_pos.mpr
            norm_cast; linarith [h_r_ge_4]
          exact div_pos h_r_real_num_pos h_r_real_den_pos

        have h_bound_intermediate : (2 : ℝ) * (q_real / (q_real - (1 : ℝ))) * (r_real / (r_real - (1 : ℝ))) ≤ (2 : ℝ) * ((3:ℝ)/(2:ℝ)) * ((4:ℝ)/(3:ℝ)) := by
          rw [mul_assoc (2 : ℝ) _ _, mul_assoc (2 : ℝ) _ _]
          apply mul_le_mul_of_nonneg_left
          .
            apply mul_le_mul
            . exact h_fq_le_f3
            . exact h_fr_le_f4
            . exact le_of_lt h_fr_pos
            . have three_half_pos : (3 : ℝ) / (2 : ℝ) ≥ 0 := by norm_num
              exact three_half_pos
          .
            norm_num

        have h_prod_val : (2 : ℝ) * ((3 : ℝ) / (2 : ℝ)) * ((4 : ℝ) / (3 : ℝ)) = (4 : ℝ) := by
          field_simp

        have h_n_lt_4 : (↑n : ℝ) < (4 : ℝ) := by
          apply lt_of_lt_of_le h_n_lt_2_fq_fr
          rw [←h_prod_val]
          exact h_bound_intermediate

        have h_4_lt_24_5 : (4 : ℝ) < (24 : ℝ) / (5 : ℝ) := by
          norm_num

        exact lt_trans h_n_lt_4 h_4_lt_24_5

      subprob_n_is_3_or_4_for_p2 :≡ n = 3 ∨ n = 4
      subprob_n_is_3_or_4_for_p2_proof ⇐ show subprob_n_is_3_or_4_for_p2 by



        have hn_lt_24_div_5_real : (↑n : ℝ) < (24 : ℝ) / (5 : ℝ) := subprob_n_lt_4_8_real_for_p2_proof

        have h_aux_frac_lt_5 : (24 : ℝ) / (5 : ℝ) < (5 : ℝ) := by
          have h_five_pos : (0 : ℝ) < 5 := by norm_num
          rw [div_lt_iff h_five_pos]
          norm_num

        have hn_real_lt_5 : (↑n : ℝ) < (5 : ℝ) := by
          apply lt_trans hn_lt_24_div_5_real h_aux_frac_lt_5

        have hn_int_lt_5 : n < 5 := by
          norm_cast at hn_real_lt_5

        have hn_le_4 : n ≤ 4 := by
          exact Order.le_of_lt_succ hn_int_lt_5

        have h_final_disj : n = 3 ∨ n = 4 := by
          omega


        exact h_final_disj

      suppose (h_n_eq_3_p2 : n = 3) then
        subprob_n3_p2_eq :≡ q*r + 4 = 3*q + 3*r
        subprob_n3_p2_eq_proof ⇐ show subprob_n3_p2_eq by


          have h_eq_intermediate : (n - (2 : ℤ)) * q * r + (n + (1 : ℤ)) = n * (q + r) := by
            exact subprob_n_ge_3_p2_eq_intermediate_proof

          rw [h_n_eq_3_p2] at h_eq_intermediate

          norm_num at h_eq_intermediate

          rw [mul_add] at h_eq_intermediate

          exact h_eq_intermediate

        subprob_n3_p2_factorized :≡ (q-3)*(r-3) = 5
        subprob_n3_p2_factorized_proof ⇐ show subprob_n3_p2_factorized by

          have h_lhs_expanded : (q - 3) * (r - 3) = q * r - 3 * q - 3 * r + 9 := by
            ring

          have h_rearranged_hyp : q * r - 3 * q - 3 * r = -4 := by
            linarith [subprob_n3_p2_eq_proof]

          rw [h_lhs_expanded]

          rw [h_rearranged_hyp]

          norm_num
        subprob_q_minus_3_pos_p2_n3 :≡ q-3 > 0
        subprob_q_minus_3_pos_p2_n3_proof ⇐ show subprob_q_minus_3_pos_p2_n3 by

          have h_p_lt_q : p < q := h₀.right.left

          have h_two_lt_q : (2 : ℤ) < q := by
            rw [h_p_eq_2_n_ge_3] at h_p_lt_q
            exact h_p_lt_q

          have h_q_minus_3_ge_0 : q - (3 : ℤ) ≥ (0 : ℤ) := by
            linarith [h_two_lt_q]

          have h_q_minus_3_ne_0 : q - (3 : ℤ) ≠ (0 : ℤ) := by
            intro h_q_minus_3_eq_0
            have h_prod_eq_5 : (q - (3 : ℤ)) * (r - (3 : ℤ)) = (5 : ℤ) := subprob_n3_p2_factorized_proof
            rw [h_q_minus_3_eq_0] at h_prod_eq_5
            simp only [zero_mul] at h_prod_eq_5
            norm_num at h_prod_eq_5

          apply lt_of_le_of_ne h_q_minus_3_ge_0
          apply Ne.symm
          exact h_q_minus_3_ne_0

        subprob_q_eq_4_r_eq_8_for_n3_p2 :≡ q=4 ∧ r=8
        subprob_q_eq_4_r_eq_8_for_n3_p2_proof ⇐ show subprob_q_eq_4_r_eq_8_for_n3_p2 by


















          have hp_val : p = 2 := h_p_eq_2_n_ge_3

          have hq_lt_r : q < r := h₀.2.2

          have h_prod_eq_5 : (q - 3) * (r - 3) = 5 := subprob_n3_p2_factorized_proof

          have hA_pos : q - 3 > 0 := subprob_q_minus_3_pos_p2_n3_proof

          have hA_ge_1 : q - 3 ≥ 1 := by
            exact Int.pos_iff_one_le.mp hA_pos
          have hq_ge_4 : q ≥ 4 := by
            linarith

          have hr_ge_5 : r ≥ 5 := by
            linarith [hq_ge_4, hq_lt_r]

          have hB_pos : r - 3 > 0 := by linarith [hr_ge_5]

          let a_nat : ℕ := Int.toNat (q - 3)
          let b_nat : ℕ := Int.toNat (r - 3)

          have hA_nonneg : 0 ≤ q - 3 := Int.le_of_lt hA_pos
          have h_coe_a_nat : (↑a_nat : ℤ) = q - 3 := Int.toNat_of_nonneg hA_nonneg

          have hB_nonneg : 0 ≤ r - 3 := Int.le_of_lt hB_pos
          have h_coe_b_nat : (↑b_nat : ℤ) = r - 3 := Int.toNat_of_nonneg hB_nonneg

          have h_prod_nat_eq_5 : a_nat * b_nat = 5 := by
            rw [← h_coe_a_nat, ← h_coe_b_nat] at h_prod_eq_5
            rw [← Nat.cast_mul] at h_prod_eq_5
            have h_5_is_coe : (5 : ℤ) = ↑(5 : ℕ) := by rfl
            rw [h_5_is_coe] at h_prod_eq_5
            apply Int.ofNat_injective
            exact h_prod_eq_5

          have h_cases : (a_nat = 1 ∧ b_nat = 5) ∨ (a_nat = 5 ∧ b_nat = 1) := by
            have ha_dvd_5 : a_nat ∣ 5 := dvd_of_mul_left_eq b_nat (Eq.trans (Nat.mul_comm b_nat a_nat) h_prod_nat_eq_5)
            have ha_1_or_5 : a_nat = 1 ∨ a_nat = 5 := Nat.Prime.eq_one_or_self_of_dvd Nat.prime_five a_nat ha_dvd_5

            rcases ha_1_or_5 with ha1 | ha5
            .
              rw [ha1, Nat.one_mul] at h_prod_nat_eq_5
              left
              exact And.intro ha1 h_prod_nat_eq_5
            .
              rw [ha5] at h_prod_nat_eq_5
              have h5_ne_zero : (5 : ℕ) ≠ 0 := Nat.prime_five.ne_zero
              have h5_pos : 0 < (5 : ℕ) := Nat.pos_of_ne_zero h5_ne_zero
              rw [Nat.mul_comm] at h_prod_nat_eq_5
              have hb1 : b_nat = 1 := (Nat.mul_left_eq_self_iff h5_pos).mp h_prod_nat_eq_5
              right
              exact And.intro ha5 hb1

          rcases h_cases with ⟨ha_eq_1, hb_eq_5⟩ | ⟨ha_eq_5, hb_eq_1⟩
          .
            have hq_eq_4 : q = 4 := by
              have h_q_minus_3_eq_1 : q - 3 = (1 : ℤ) := by
                rw [←h_coe_a_nat]
                rw [ha_eq_1]
                norm_num
              linarith [h_q_minus_3_eq_1]
            have hr_eq_8 : r = 8 := by
              have h_r_minus_3_eq_5 : r - 3 = (5 : ℤ) := by
                rw [←h_coe_b_nat]
                rw [hb_eq_5]
                norm_num
              linarith [h_r_minus_3_eq_5]
            exact And.intro hq_eq_4 hr_eq_8
          .
            have hq_eq_8 : q = 8 := by
              have h_q_minus_3_eq_5 : q - 3 = (5 : ℤ) := by
                rw [←h_coe_a_nat]
                rw [ha_eq_5]
                norm_num
              linarith [h_q_minus_3_eq_5]
            have hr_eq_4 : r = 4 := by
              have h_r_minus_3_eq_1 : r - 3 = (1 : ℤ) := by
                rw [←h_coe_b_nat]
                rw [hb_eq_1]
                norm_num
              linarith [h_r_minus_3_eq_1]
            exfalso
            linarith [hq_lt_r, hq_eq_8, hr_eq_4]





        subprob_sol2 :≡ p = 2 ∧ q = 4 ∧ r = 8
        subprob_sol2_proof ⇐ show subprob_sol2 by
                  constructor
                  .
                    exact h_p_eq_2_n_ge_3
                  .
                    exact subprob_q_eq_4_r_eq_8_for_n3_p2_proof

      suppose (h_n_eq_4_p2 : n = 4) then
        subprob_n4_p2_eq :≡ 2*q*r + 5 = 4*q + 4*r
        subprob_n4_p2_eq_proof ⇐ show subprob_n4_p2_eq by

          have h_eq := subprob_n_ge_3_p2_eq_intermediate_proof

          rw [h_n_eq_4_p2] at h_eq

          norm_num at h_eq

          rw [Int.mul_add] at h_eq

          exact h_eq
        subprob_n4_p2_rearranged :≡ 2*(q*r - 2*q - 2*r) = -5
        subprob_n4_p2_rearranged_proof ⇐ show subprob_n4_p2_rearranged by






          have h_lhs_expanded : 2 * (q * r - 2 * q - 2 * r) = 2 * q * r - 4 * q - 4 * r := by
            ring

          rw [h_lhs_expanded]

          have h_transformed_given : (2 : ℤ) * q * r - ((4 : ℤ) * q + (4 : ℤ) * r) = -(5 : ℤ) := by
            rw [← subprob_n4_p2_eq_proof]
            rw [sub_add_eq_sub_sub]
            rw [sub_self]
            rw [zero_sub]

          have h_lhs_relation : (2 : ℤ) * q * r - (4 : ℤ) * q - (4 : ℤ) * r = (2 : ℤ) * q * r - ((4 : ℤ) * q + (4 : ℤ) * r) := by
            apply Eq.symm
            apply sub_add_eq_sub_sub

          rw [h_lhs_relation]
          exact h_transformed_given




        subprob_n4_p2_impossible :≡ False
        subprob_n4_p2_impossible_proof ⇐ show subprob_n4_p2_impossible by

          have h_lhs_mod_2 : ((2 : ℤ) * (q * r - (2 : ℤ) * q - (2 : ℤ) * r)) % (2 : ℤ) = 0 := by
            simp

          have h_rhs_mod_2 : (-(5 : ℤ)) % (2 : ℤ) = 1 := by
            norm_num

          rw [subprob_n4_p2_rearranged_proof] at h_lhs_mod_2
          rw [h_rhs_mod_2] at h_lhs_mod_2
          norm_num at h_lhs_mod_2

    suppose (h_p_eq_3_n_ge_3 : p = 3) then
      subprob_n_ge_3_p3_eq_intermediate :≡ (2*n-3)*q*r + (2*n+1) = 2*n*(q+r)
      subprob_n_ge_3_p3_eq_intermediate_proof ⇐ show subprob_n_ge_3_p3_eq_intermediate by

        have h_sub_p_eq_3 : (3 : ℤ) * q * r - (1 : ℤ) = ((3 : ℤ) - (1 : ℤ)) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
          rw [h_p_eq_3_n_ge_3] at hn_def
          exact hn_def

        have h_simplified_const : (3 : ℤ) * q * r - (1 : ℤ) = (2 : ℤ) * (q - (1 : ℤ)) * (r - (1 : ℤ)) * n := by
          rw [h_sub_p_eq_3]
          norm_num

        linarith [h_simplified_const]
      subprob_n_lt_2_72_real_for_p3 :≡ (n:ℝ) < (30:ℝ)/(11:ℝ)
      subprob_n_lt_2_72_real_for_p3_proof ⇐ show subprob_n_lt_2_72_real_for_p3 by
















        have f_decreasing_le {x₁ x₂ : ℝ} (hx₁_gt_1 : 1 < x₁) (hx₁_le_x₂ : x₁ ≤ x₂) : f x₂ ≤ f x₁ := by
          rcases LE.le.eq_or_lt hx₁_le_x₂ with h_eq | h_lt
          . rw [h_eq]
          . have h_f_lt : f x₂ < f x₁ := subprob_f_decreasing_proof x₁ x₂ hx₁_gt_1 h_lt
            exact le_of_lt h_f_lt

        have hp_is_3 : p = (3:ℤ) := h_p_eq_3_n_ge_3

        have fp_val_def : f (↑p : ℝ) = (↑p : ℝ) / ((↑p : ℝ) - (1 : ℝ)) := by
          rw [f_def]
        have fp_eval : f (↑p : ℝ) = (3:ℝ) / (2:ℝ) := by
          rw [fp_val_def, hp_is_3]
          simp only [Int.cast_ofNat, Int.cast_one]
          norm_num

        have h_3_lt_q : (3:ℤ) < q := by
          rw [←hp_is_3]
          exact h₀.2.1
        have hq_ge_4 : q ≥ (4:ℤ) := by
          linarith [h_3_lt_q]
        have hr_ge_5 : r ≥ (5:ℤ) := by
          have h_q_lt_r : q < r := h₀.2.2
          linarith [h_3_lt_q, h_q_lt_r]

        have fq_val_def : f (↑q : ℝ) = (↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ)) := by rw [f_def]
        have fq_le_f4 : f (↑q:ℝ) ≤ f (4:ℝ) := by
          apply f_decreasing_le
          . norm_num
          . exact Int.cast_le.mpr hq_ge_4
        have f4_eval : f (4:ℝ) = (4:ℝ) / (3:ℝ) := by
          rw [f_def]
          norm_num
        rw [f4_eval] at fq_le_f4

        have fr_val_def : f (↑r : ℝ) = (↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ)) := by rw [f_def]
        have fr_le_f5 : f (↑r:ℝ) ≤ f (5:ℝ) := by
          apply f_decreasing_le
          . norm_num
          . exact Int.cast_le.mpr hr_ge_5
        have f5_eval : f (5:ℝ) = (5:ℝ) / (4:ℝ) := by
          rw [f_def]
          norm_num
        rw [f5_eval] at fr_le_f5

        have prod_f_le_upper_bound : f (↑p:ℝ) * f (↑q:ℝ) * f (↑r:ℝ) ≤ ( (3:ℝ)/(2:ℝ) * (4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ) ) := by
          rw [fp_eval]
          have fq_pos : 0 < f (↑q:ℝ) := by
            rw [fq_val_def]
            have q_cast_ge_4 : (↑q : ℝ) ≥ 4 := Int.cast_le.mpr hq_ge_4
            have q_cast_pos : 0 < (↑q : ℝ) := by linarith
            have q_minus_1_cast_pos : 0 < (↑q : ℝ) - (1:ℝ) := by linarith
            exact div_pos q_cast_pos q_minus_1_cast_pos
          have fr_pos : 0 < f (↑r:ℝ) := by
            rw [fr_val_def]
            have r_cast_ge_5 : (↑r : ℝ) ≥ 5 := Int.cast_le.mpr hr_ge_5
            have r_cast_pos : 0 < (↑r : ℝ) := by linarith
            have r_minus_1_cast_pos : 0 < (↑r : ℝ) - (1:ℝ) := by linarith
            exact div_pos r_cast_pos r_minus_1_cast_pos

          have temp1 : f (↑q:ℝ) * f (↑r:ℝ) ≤ (4:ℝ)/(3:ℝ) * f (↑r:ℝ) := by
            apply mul_le_mul_of_nonneg_right fq_le_f4
            exact le_of_lt fr_pos
          have temp2 : (4:ℝ)/(3:ℝ) * f (↑r:ℝ) ≤ (4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ) := by
            have h_multiplier_nonneg : 0 ≤ (4:ℝ)/(3:ℝ) := by
              norm_num
            rw [mul_div_assoc ((4:ℝ)/(3:ℝ)) (5:ℝ) (4:ℝ)]
            exact mul_le_mul_of_nonneg_left fr_le_f5 h_multiplier_nonneg
          have fq_fr_le_const : f (↑q:ℝ) * f (↑r:ℝ) ≤ (4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ) := le_trans temp1 temp2

          have h_3div2_pos : (0:ℝ) < (3:ℝ)/(2:ℝ) := by norm_num

          rw [mul_assoc ((3:ℝ)/(2:ℝ)) (f (↑q:ℝ)) (f (↑r:ℝ))]

          have H_main_proof : (3:ℝ)/(2:ℝ) * (f (↑q:ℝ) * f (↑r:ℝ)) ≤ (3:ℝ)/(2:ℝ) * ((4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ)) :=
            mul_le_mul_of_nonneg_left fq_fr_le_const (le_of_lt h_3div2_pos)

          have h_reassociate_rhs : (3:ℝ)/(2:ℝ) * ((4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ)) =
                                   ((3:ℝ)/(2:ℝ) * (4:ℝ)/(3:ℝ)) * (5:ℝ)/(4:ℝ) := by
            ring
          rw [h_reassociate_rhs] at H_main_proof
          exact H_main_proof

        have upper_bound_val_is_5_2 : ( (3:ℝ)/(2:ℝ) * (4:ℝ)/(3:ℝ) * (5:ℝ)/(4:ℝ) ) = (5:ℝ)/(2:ℝ) := by
          norm_num

        rw [upper_bound_val_is_5_2] at prod_f_le_upper_bound
        have n_lt_5_2 : (↑n : ℝ) < (5:ℝ)/(2:ℝ) := by
          rw [fp_val_def, fq_val_def, fr_val_def] at prod_f_le_upper_bound
          exact lt_of_lt_of_le subprob_n_lt_prod_fractions_real_proof prod_f_le_upper_bound

        have five_div_two_lt_thirty_div_eleven : (5:ℝ)/(2:ℝ) < (30:ℝ)/(11:ℝ) := by
          norm_num

        exact lt_trans n_lt_5_2 five_div_two_lt_thirty_div_eleven

      subprob_n_ge_3_p3_impossible :≡ False
      subprob_n_ge_3_p3_impossible_proof ⇐ show subprob_n_ge_3_p3_impossible by


        have hn_ge_3_real : (↑n : ℝ) ≥ (3 : ℝ) := by
          norm_cast

        have h_const_lt_3 : (30 : ℝ) / (11 : ℝ) < (3 : ℝ) := by
          have h_eleven_pos : (11 : ℝ) > 0 := by
            norm_num
          rw [div_lt_iff h_eleven_pos]
          norm_num

        have hn_lt_3_real : (↑n : ℝ) < (3 : ℝ) := by
          apply lt_trans subprob_n_lt_2_72_real_for_p3_proof h_const_lt_3

        have h_absurd : (3 : ℝ) < (3 : ℝ) := by
          apply lt_of_le_of_lt hn_ge_3_real hn_lt_3_real

        apply lt_irrefl (3 : ℝ) h_absurd


    suppose (h_p_eq_4_n_ge_3 : p = 4) then
      subprob_n_ge_3_p4_eq_intermediate :≡ (3*n-4)*q*r + (3*n+1) = 3*n*(q+r)
      subprob_n_ge_3_p4_eq_intermediate_proof ⇐ show subprob_n_ge_3_p4_eq_intermediate by

        have h_subst_p : (4 : ℤ) * q * r - 1 = ((4 : ℤ) - 1) * (q - 1) * (r - 1) * n := by
          rw [← h_p_eq_4_n_ge_3]
          exact hn_def

        norm_num at h_subst_p

        have h_rhs_expanded : 3 * (q - 1) * (r - 1) * n = 3 * n * q * r - 3 * n * q - 3 * n * r + 3 * n := by
          ring

        rw [h_rhs_expanded] at h_subst_p


        linarith [h_subst_p]
      subprob_n_odd_q_r_even_for_p4 :≡ n % 2 = 1 ∧ q % 2 = 0 ∧ r % 2 = 0
      subprob_n_odd_q_r_even_for_p4_proof ⇐ show subprob_n_odd_q_r_even_for_p4 by



        have hp_eq_4 : p = (4 : ℤ) := h_p_eq_4_n_ge_3

        have h_p_lt_q : p < q := h₀.2.1
        have h_q_lt_r : q < r := h₀.2.2

        have hq_gt_4 : (4 : ℤ) < q := by rw [hp_eq_4] at h_p_lt_q; exact h_p_lt_q
        have hq_ge_5 : q ≥ (5 : ℤ) := Int.add_one_le_of_lt hq_gt_4

        have hr_gt_q : q < r := h_q_lt_r
        have hr_ge_q_plus_1 : r ≥ q + 1 := Int.add_one_le_of_lt hr_gt_q
        have hr_ge_6 : r ≥ (6 : ℤ) := by linarith [hq_ge_5, hr_ge_q_plus_1]

        have hp_real_eq_4 : (↑p : ℝ) = (4 : ℝ) := by norm_cast
        have hq_real_ge_5 : (↑q : ℝ) ≥ (5 : ℝ) := by norm_cast
        have hr_real_ge_6 : (↑r : ℝ) ≥ (6 : ℝ) := by norm_cast

        let fp := (↑p : ℝ) / (↑p - (1 : ℝ))
        let fq := (↑q : ℝ) / ((↑q : ℝ) - (1 : ℝ))
        let fr := (↑r : ℝ) / ((↑r : ℝ) - (1 : ℝ))

        have fp_val : fp = (4 : ℝ) / (3 : ℝ) := by
          dsimp only [fp]
          rw [hp_real_eq_4]
          field_simp
          norm_num

        have f_strict_anti : StrictAntiOn f (Set.Ioi 1) := by
          intro x₁ hx₁ x₂ hx₂ hx₁_lt_x₂
          rw [f_def', f_def']
          exact (f_def' x₁) ▸ (f_def' x₂) ▸ (subprob_f_decreasing_proof x₁ x₂ hx₁ hx₁_lt_x₂)

        have f_antitone_on_Ioi1 : AntitoneOn f (Set.Ioi 1) := StrictAntiOn.antitoneOn f_strict_anti

        have five_gt_1 : (5 : ℝ) > 1 := by norm_num
        have q_gt_1_real : (↑q : ℝ) > 1 := by linarith [hq_real_ge_5]
        have six_gt_1 : (6 : ℝ) > 1 := by norm_num
        have r_gt_1_real : (↑r : ℝ) > 1 := by linarith [hr_real_ge_6]

        have five_mem_Ioi1 : (5 : ℝ) ∈ Set.Ioi 1 := five_gt_1
        have q_mem_Ioi1 : (↑q : ℝ) ∈ Set.Ioi 1 := q_gt_1_real
        have six_mem_Ioi1 : (6 : ℝ) ∈ Set.Ioi 1 := six_gt_1
        have r_mem_Ioi1 : (↑r : ℝ) ∈ Set.Ioi 1 := r_gt_1_real

        have fq_le_f5 : fq ≤ f (5 : ℝ) := by
          dsimp only [fq]
          exact (f_def' (↑q : ℝ)) ▸ (f_antitone_on_Ioi1 five_mem_Ioi1 q_mem_Ioi1 hq_real_ge_5)
        have f5_val : f (5 : ℝ) = (5 : ℝ) / (4 : ℝ) := by rw [f_def']; field_simp; norm_num
        rw [f5_val] at fq_le_f5

        have fr_le_f6 : fr ≤ f (6 : ℝ) := by
          dsimp only [fr]
          rw [← (f_def' (↑r : ℝ))]
          exact (f_antitone_on_Ioi1 six_mem_Ioi1 r_mem_Ioi1 hr_real_ge_6)
        have f6_val : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by rw [f_def']; field_simp; norm_num
        rw [f6_val] at fr_le_f6

        have fp_pos : 0 < fp := by rw [fp_val]; norm_num
        have fq_pos : 0 < fq := by
          apply div_pos (by linarith [hq_real_ge_5]) (by apply sub_pos_of_lt; linarith [hq_real_ge_5])
        have fr_pos : 0 < fr := by
          apply div_pos (by linarith [hr_real_ge_6]) (by apply sub_pos_of_lt; linarith [hr_real_ge_6])

        have five_fourths_pos : 0 < (5:ℝ)/4 := by norm_num

        have h_n_lt_prod := subprob_n_lt_prod_fractions_real_proof

        have fq_mul_fr_le : fq * fr ≤ ((5:ℝ)/4) * ((6:ℝ)/5) := by
          apply mul_le_mul fq_le_f5 fr_le_f6 (le_of_lt fr_pos) (le_of_lt five_fourths_pos)

        have prod_le_total_bound : fp * (fq * fr) ≤ fp * (((5:ℝ)/4) * ((6:ℝ)/5)) := by
          apply mul_le_mul_of_nonneg_left fq_mul_fr_le (le_of_lt fp_pos)


        have n_lt_bound_val : (↑n : ℝ) < fp * (((5:ℝ)/4) * ((6:ℝ)/5)) := by
          have h_temp := h_n_lt_prod
          rw [mul_assoc fp fq fr] at h_temp
          apply lt_of_lt_of_le h_temp prod_le_total_bound

        rw [fp_val] at n_lt_bound_val

        have bound_calc : (4:ℝ)/3 * (((5:ℝ)/4) * ((6:ℝ)/5)) = 2 := by
          field_simp
          norm_num

        rw [bound_calc] at n_lt_bound_val

        have n_lt_2_int : n < (2 : ℤ) := by
          apply (Int.cast_lt (R := ℝ)).mp
          rw [Int.cast_two]
          exact n_lt_bound_val

        have n_le_1 : n ≤ (1 : ℤ) := Order.le_pred_of_lt n_lt_2_int

        have contradiction : False := by
          linarith [n_le_1, h_n_ge_3]

        exact False.elim contradiction


      subprob_n_lt_1_88_real_for_p4 :≡ (n:ℝ) < (32:ℝ)/(17:ℝ)
      subprob_n_lt_1_88_real_for_p4_proof ⇐ show subprob_n_lt_1_88_real_for_p4 by










        have h_n_lt_prod_frac : (↑n : ℝ) < (↑p : ℝ) / ((↑p : ℝ) - 1) * ((↑q : ℝ) / ((↑q : ℝ) - 1)) * ((↑r : ℝ) / ((↑r : ℝ) - 1)) :=
          subprob_n_lt_prod_fractions_real_proof

        have h_n_lt_f_prod : (↑n : ℝ) < f (↑p : ℝ) * f (↑q : ℝ) * f (↑r : ℝ) := by
          rw [f_def' (↑p : ℝ), f_def' (↑q : ℝ), f_def' (↑r : ℝ)]; exact h_n_lt_prod_frac

        have hp_val_real : (↑p : ℝ) = (4 : ℝ) := by simp [h_p_eq_4_n_ge_3]
        rw [hp_val_real] at h_n_lt_f_prod
        have h_fp_eval : f (4 : ℝ) = (4 : ℝ) / (3 : ℝ) := by
          rw [f_def']; norm_num
        rw [h_fp_eval] at h_n_lt_f_prod

        have p_lt_q : p < q := h₀.2.1
        have q_lt_r : q < r := h₀.2.2

        have h_q_gt_4 : q > 4 := by rw [← h_p_eq_4_n_ge_3]; exact p_lt_q

        have h_q_even : q % 2 = 0 := subprob_n_odd_q_r_even_for_p4_proof.2.1
        have h_r_even : r % 2 = 0 := subprob_n_odd_q_r_even_for_p4_proof.2.2

        have h_q_ge_6 : q ≥ 6 := by
          apply Int.le_of_lt_add_one
          have q_ge_5 : q ≥ 5 := Int.add_one_le_of_lt h_q_gt_4
          have h_exists_k : (∃ k_val, q = 2 * k_val) := exists_eq_mul_right_of_dvd (Int.dvd_of_emod_eq_zero h_q_even)
          rcases h_exists_k with ⟨k, hk_q⟩
          rw [hk_q] at q_ge_5
          have k_ge_3 : k ≥ 3 := by linarith
          rw [hk_q]
          linarith

        have h_r_ge_8 : r ≥ 8 := by
          have r_ge_q_plus_1 : r ≥ q + 1 := Int.add_one_le_of_lt q_lt_r
          by_cases hr_eq_q_plus_1 : r = q + 1
          . rw [hr_eq_q_plus_1] at h_r_even
            have q_plus_1_is_odd : (q + 1) % 2 = 1 := by
              rw [Int.add_emod]
              simp [h_q_even, Int.one_emod_two]
            rw [q_plus_1_is_odd] at h_r_even
            norm_num at h_r_even
          .
            have r_gt_q_plus_1 : r > q + 1 := lt_of_le_of_ne' r_ge_q_plus_1 hr_eq_q_plus_1
            have r_ge_q_plus_2 : r ≥ q + 2 := (Int.add_assoc q 1 1) ▸ Int.add_one_le_of_lt r_gt_q_plus_1
            linarith [r_ge_q_plus_2, h_q_ge_6]

        have six_gt_1_real : (6 : ℝ) > 1 := by norm_num
        have q_ge_6_real : (↑q : ℝ) ≥ (6 : ℝ) := Int.cast_le.mpr h_q_ge_6
        have q_gt_1_real : (↑q : ℝ) > 1 := by linarith [q_ge_6_real, six_gt_1_real]

        have h_fq_le : f (↑q : ℝ) ≤ f (6 : ℝ) := by
          rcases eq_or_lt_of_le q_ge_6_real with h_q_eq_6 | h_q_gt_6
          · rw [h_q_eq_6]
          · exact (subprob_f_decreasing_proof (6 : ℝ) (↑q : ℝ) six_gt_1_real h_q_gt_6).le

        have h_f6_eval : f (6 : ℝ) = (6 : ℝ) / (5 : ℝ) := by
          rw [f_def']; norm_num
        rw [h_f6_eval] at h_fq_le

        have eight_gt_1_real : (8 : ℝ) > 1 := by norm_num
        have r_ge_8_real : (↑r : ℝ) ≥ (8 : ℝ) := Int.cast_le.mpr h_r_ge_8
        have r_gt_1_real : (↑r : ℝ) > 1 := by linarith [r_ge_8_real, eight_gt_1_real]

        have h_fr_le : f (↑r : ℝ) ≤ f (8 : ℝ) := by
          rcases eq_or_lt_of_le r_ge_8_real with h_r_eq_8 | h_r_gt_8
          · rw [h_r_eq_8]
          · exact (subprob_f_decreasing_proof (8 : ℝ) (↑r : ℝ) eight_gt_1_real h_r_gt_8).le

        have h_f8_eval : f (8 : ℝ) = (8 : ℝ) / (7 : ℝ) := by
          rw [f_def']; norm_num
        rw [h_f8_eval] at h_fr_le

        have h_n_lt_upper_bound : (↑n : ℝ) < (4/3 : ℝ) * (6/5 : ℝ) * (8/7 : ℝ) := by
          have f43_pos : (4/3 : ℝ) > 0 := by norm_num
          have fq_pos : f (↑q:ℝ) > 0 := by
            rw [f_def']
            apply div_pos <;> linarith [q_gt_1_real]
          have fr_pos : f (↑r:ℝ) > 0 := by
            rw [f_def']
            apply div_pos <;> linarith [r_gt_1_real]

          have h_aux1 : (4 / 3 : ℝ) * f (↑q : ℝ) * f (↑r : ℝ) ≤ (4 / 3 : ℝ) * (6 / 5 : ℝ) * f (↑r : ℝ) := by
            gcongr
          have h_aux2 : (4 / 3 : ℝ) * (6 / 5 : ℝ) * f (↑r : ℝ) ≤ (4 / 3 : ℝ) * (6 / 5 : ℝ) * (8 / 7 : ℝ) := by
            gcongr
          exact h_n_lt_f_prod.trans_le (h_aux1.trans h_aux2)

        have h_prod_val : (4/3 : ℝ) * (6/5 : ℝ) * (8/7 : ℝ) = (64/35 : ℝ) := by norm_num
        rw [h_prod_val] at h_n_lt_upper_bound

        have h_final_ineq : (64/35 : ℝ) < (32/17 : ℝ) := by
          norm_num

        exact h_n_lt_upper_bound.trans h_final_ineq




      subprob_n_ge_3_p4_impossible :≡ False
      subprob_n_ge_3_p4_impossible_proof ⇐ show subprob_n_ge_3_p4_impossible by

        have h_n_ge_3_real : (n : ℝ) ≥ (3 : ℝ) := by
          exact_mod_cast h_n_ge_3

        have h_bound_val_lt_3 : (32 : ℝ) / (17 : ℝ) < (3 : ℝ) := by
          norm_num

        linarith [subprob_n_lt_1_88_real_for_p4_proof, h_n_ge_3_real, h_bound_val_lt_3]

  subprob_final_goal :≡ (p, q, r) = (2, 4, 8) ∨ (p, q, r) = (3, 5, 15)
  subprob_final_goal_proof ⇐ show subprob_final_goal by





    have hn_ge_1 : n ≥ (1 : ℤ) := subprob_n_pos_proof

    have h_n_cases : (1 : ℤ) = n ∨ (1 : ℤ) < n := eq_or_lt_of_le hn_ge_1
    rcases h_n_cases with hn_1_eq_n | hn_lt_1
    .
      exfalso
      exact subprob_n1_impossible_proof hn_1_eq_n.symm
    .
      have hn_ge_2 : n ≥ (2 : ℤ) := by linarith [hn_lt_1]

      have h_n_ge_2_cases : (2 : ℤ) = n ∨ (2 : ℤ) < n := eq_or_lt_of_le hn_ge_2
      rcases h_n_ge_2_cases with hn_eq_2 | hn_lt_2
      .
        have hp_eq_3_for_n2 : p = (3 : ℤ) := subprob_p_eq_3_for_n2_proof hn_eq_2.symm
        have h_sol1 := subprob_sol1_proof hn_eq_2.symm hp_eq_3_for_n2
        rcases h_sol1 with ⟨rfl, rfl, rfl⟩
        apply Or.inr
        rfl
      .
        have hn_ge_3 : n ≥ (3 : ℤ) := by linarith [hn_lt_2]

        rcases subprob_p_cases_proof with hp_eq_2 | hp_eq_3 | hp_eq_4
        .
          have hn_is_3_or_4 := subprob_n_is_3_or_4_for_p2_proof hn_ge_3 hp_eq_2
          rcases hn_is_3_or_4 with hn_eq_3 | hn_eq_4
          .
            have h_sol2 := subprob_sol2_proof hn_ge_3 hp_eq_2 hn_eq_3
            rcases h_sol2 with ⟨rfl, rfl, rfl⟩
            apply Or.inl
            rfl
          .
            exfalso
            exact subprob_n4_p2_impossible_proof hn_ge_3 hp_eq_2 hn_eq_4
        .
          exfalso
          exact subprob_n_ge_3_p3_impossible_proof hn_ge_3 hp_eq_3
        .
          exfalso
          exact subprob_n_ge_3_p4_impossible_proof hn_ge_3 hp_eq_4
-/
