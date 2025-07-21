import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2020_p25 (a : ℚ) (S : Finset ℝ) (h₀ : ∀ (x : ℝ), x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2) (h₁ : ∑ k in S, k = 420) : (↑(Rat.den a) : ℤ) + Rat.num a = (929 : ℤ) := by
  letI a_real := ↑a
  retro' a_real_def : a_real = a := by funext; rfl
  have subprob_a_num_pos_assumption_proof : a.num > 0 := by
    mkOpaque
    have ha_ne_zero : a ≠ 0 := by
      intro ha_eq_zero
      let M := {x : ℝ | (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑(0 : ℚ) : ℝ) * x ^ (2 : ℕ)}
      have M_infinite : M.Infinite :=
        by
        have M_contains_all_integers : Set.range (Int.cast : ℤ → ℝ) ⊆ M := by
          intro x hx_in_range
          simp only [Set.mem_range] at hx_in_range
          rcases hx_in_range with ⟨n, rfl⟩
          simp only [M, Set.mem_setOf_eq, Int.floor_intCast, sub_self, mul_zero, Rat.cast_zero, zero_mul]
        apply Set.Infinite.mono M_contains_all_integers
        apply (Set.infinite_range_iff Int.cast_injective).mpr
        exact Int.infinite
      have S_toSet_eq_M : (S : Set ℝ) = M := by
        ext x
        specialize h₀ x
        rw [ha_eq_zero] at h₀
        simp only [Rat.cast_zero, zero_mul] at h₀
        simp only [Finset.mem_coe, M, Set.mem_setOf_eq, Rat.cast_zero, zero_mul]
        exact h₀
      rw [← S_toSet_eq_M] at M_infinite
      apply M_infinite
      exact Finset.finite_toSet S
    have ha_not_neg : ¬(a < 0) := by
      intro ha_neg
      have all_elements_le_zero : ∀ x ∈ S, x ≤ 0 := by
        intro x hxS
        by_cases hx_eq_zero : x = 0
        . rw [hx_eq_zero]
        . have h_prop := (h₀ x).mp hxS
          have ax2_neg_cond : ↑a * x ^ 2 < 0 := by
            refine mul_neg_of_neg_of_pos ?_ (sq_pos_of_ne_zero hx_eq_zero)
            exact_mod_cast ha_neg
          have floor_times_raw_fract_neg : ↑(⌊x⌋) * (x - ↑(⌊x⌋)) < 0 := by
            rw [h_prop]
            exact ax2_neg_cond
          have floor_mul_fract_neg : (↑(⌊x⌋) : ℝ) * Int.fract x < 0 := by
            rw [eq_sub_of_add_eq (Int.fract_add_floor x)]
            exact floor_times_raw_fract_neg
          have fract_x_pos : Int.fract x > 0 := by
            apply lt_of_le_of_ne (Int.fract_nonneg x)
            intro h_fract_eq_zero
            have h_lhs_eq_zero : (↑(⌊x⌋) : ℝ) * Int.fract x = (↑(⌊x⌋) : ℝ) * 0 := by rw [h_fract_eq_zero]
            have h_rhs_is_zero : (↑(⌊x⌋) : ℝ) * 0 = 0 := by simp only [mul_zero]
            have h_zero_lt_zero : (0 : ℝ) < 0 := (h_lhs_eq_zero.trans h_rhs_is_zero) ▸ floor_mul_fract_neg
            linarith [h_zero_lt_zero]
          have h_floor_real_neg : ↑(⌊x⌋) < 0 := by
            rcases mul_neg_iff.mp floor_mul_fract_neg with (⟨h_floor_lt_0, _⟩ | ⟨actual_floor_neg, h_fract_lt_0⟩)
            . exfalso; linarith [fract_x_pos]
            . exact (Int.cast_lt_zero.mp actual_floor_neg)
          have h_floor_int_neg : ⌊x⌋ < 0 := Int.cast_lt_zero.mp h_floor_real_neg
          have h_floor_le_minus_one : ⌊x⌋ ≤ -1 := Int.le_sub_one_of_lt h_floor_int_neg
          apply le_of_lt
          have h_step1 : x = (↑(⌊x⌋) : ℝ) + Int.fract x := by rw [Int.floor_add_fract x]
          have h_step2 : (↑(⌊x⌋) : ℝ) + Int.fract x < (↑(⌊x⌋) : ℝ) + 1 := by
            apply (Real.add_lt_add_iff_left ((↑(⌊x⌋)) : ℝ)).mpr
            exact Int.fract_lt_one x
          have h_step3 : (↑(⌊x⌋) : ℝ) + 1 ≤ (↑(-1 : ℤ) : ℝ) + 1 := by simp only [add_le_add_iff_right, Int.cast_le]; exact h_floor_le_minus_one
          have h_step4 : (↑(-1 : ℤ) : ℝ) + 1 = 0 := by simp
          rw [h_step1]
          linarith [h_step2, h_step3, h_step4]
      have sum_S_le_zero : ∑ k ∈ S, k ≤ 0 := Finset.sum_nonpos all_elements_le_zero
      rw [h₁] at sum_S_le_zero
      linarith
    rcases lt_trichotomy a (0 : ℚ) with h_lt | h_eq | h_gt
    . contradiction
    . exact (ha_ne_zero h_eq).elim
    . exact Rat.num_pos_iff_pos.mpr h_gt
  have subprob_a_den_pos_assumption_proof : a.den > 0 := by
    mkOpaque
    apply Rat.den_pos
  have subprob_a_real_pos_proof : a_real > (0 : ℝ) := by
    mkOpaque
    rw [a_real_def]
    apply Rat.cast_pos.mpr
    rw [← Rat.num_pos]
    exact subprob_a_num_pos_assumption_proof
  have subprob_zero_in_S_proof : (0 : ℝ) ∈ S := by
    mkOpaque
    rw [h₀]
    have lhs_eq_zero : (↑(⌊(0 : ℝ)⌋) : ℝ) * (0 - ↑(⌊(0 : ℝ)⌋)) = 0 := by simp only [Int.floor_zero, Int.cast_zero, sub_self, mul_zero]
    have rhs_eq_zero : (↑(a) : ℝ) * (0 : ℝ) ^ (2 : ℕ) = 0 :=
      by
      have h_zero_pow_two : (0 : ℝ) ^ (2 : ℕ) = 0 := by
        apply zero_pow
        norm_num
      simp only [h_zero_pow_two, mul_zero]
    rw [lhs_eq_zero, rhs_eq_zero]
  letI w_int_x : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℤ := by
    intro x hxS hxne0
    exact ⌊x⌋
  retro' w_int_x_def : w_int_x = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) => ⌊x⌋ := by funext; rfl
  retro' w_int_x_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), w_int_x x hxS hxne0 = ⌊x⌋ := by intros; rfl
  letI f_real_x : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℝ := by
    intro x hxS hxne0
    exact x - ↑(⌊x⌋)
  retro' f_real_x_def : f_real_x = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) => x - (↑(⌊x⌋) : ℝ) := by funext; rfl
  retro' f_real_x_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), f_real_x x hxS hxne0 = x - (↑(⌊x⌋) : ℝ) := by intros; rfl
  letI w_real_x : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℤ := by
    intro x hxS hxne0
    exact ↑(⌊x⌋)
  retro' w_real_x_def : w_real_x = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) => ⌊x⌋ := by funext; rfl
  retro' w_real_x_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), w_real_x x hxS hxne0 = ⌊x⌋ := by intros; rfl
  have subprob_wf_eq_ax2_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), (↑(w_real_x x hxS hxne0) : ℝ) * f_real_x x hxS hxne0 = (↑(a_real) : ℝ) * x ^ (2 : ℕ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    exact
      show w_real_x * f_real_x = a_real * x ^ 2 by
        mkOpaque
        have h_equality_from_h0 : (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑a : ℝ) * x ^ 2 := by
          apply (h₀ x).mp
          exact hxS
        rw [w_real_x_def]
        rw [f_real_x_def]
        rw [a_real_def]
        exact h_equality_from_h0
  have subprob_ax2_pos_proof : ∀ (x : ℝ), x ∈ S → x ≠ (0 : ℝ) → (↑(a_real) : ℝ) * x ^ (2 : ℕ) > (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    exact
      show a_real * x ^ 2 > (0 : ℝ) by
        mkOpaque
        have h_x_sq_pos : x ^ (2 : ℕ) > 0 := by
          apply sq_pos_of_ne_zero
          exact hxne0
        apply mul_pos
        . exact subprob_a_real_pos_proof
        . exact h_x_sq_pos
  have subprob_wf_pos_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), (↑(w_real_x x hxS hxne0) : ℝ) * f_real_x x hxS hxne0 > (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    exact
      show w_real_x * f_real_x > (0 : ℝ) by
        mkOpaque
        rw [subprob_wf_eq_ax2_proof]
        exact subprob_ax2_pos_proof
  have subprob_f_real_x_bounds_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), (0 : ℝ) ≤ f_real_x x hxS hxne0 ∧ f_real_x x hxS hxne0 < (1 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    exact
      show (0 : ℝ) ≤ f_real_x ∧ f_real_x < (1 : ℝ) by
        mkOpaque
        rw [f_real_x_def]
        change (0 : ℝ) ≤ Int.fract x ∧ Int.fract x < (1 : ℝ)
        apply And.intro
        . apply Int.fract_nonneg
        . apply Int.fract_lt_one
  have subprob_f_real_x_ne_zero_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), f_real_x x hxS hxne0 ≠ (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    exact
      show f_real_x ≠ (0 : ℝ) by
        mkOpaque
        intro h_f_real_x_eq_zero
        have h_prod_gt_zero : (↑w_real_x : ℝ) * f_real_x > (0 : ℝ) := subprob_wf_pos_proof
        rw [h_f_real_x_eq_zero] at h_prod_gt_zero
        simp only [mul_zero] at h_prod_gt_zero
        exact lt_irrefl (0 : ℝ) h_prod_gt_zero
  have subprob_f_real_x_pos_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), f_real_x x hxS hxne0 > (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    exact
      show f_real_x > (0 : ℝ) by
        mkOpaque
        apply lt_of_le_of_ne'
        · exact subprob_f_real_x_bounds_proof.left
        · exact subprob_f_real_x_ne_zero_proof
  have subprob_w_real_x_pos_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), (↑(w_real_x x hxS hxne0) : ℝ) > (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    exact
      show w_real_x > (0 : ℝ) by
        mkOpaque
        have h_main_ineq : (↑w_real_x : ℝ) * f_real_x > (0 : ℝ) * f_real_x := by
          rw [zero_mul f_real_x]
          exact subprob_wf_pos_proof
        exact (mul_lt_mul_iff_of_pos_right subprob_f_real_x_pos_proof).mp h_main_ineq
  have subprob_w_int_x_ge_1_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), w_int_x x hxS hxne0 ≥ (1 : ℤ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    exact
      show w_int_x ≥ 1 by
        mkOpaque
        have h_w_eq : w_real_x = w_int_x := by
          rw [w_real_x_def]
          rw [w_int_x_def]
        have h_w_int_x_cast_pos : (↑(w_int_x) : ℝ) > (0 : ℝ) := by
          rw [← h_w_eq]
          exact subprob_w_real_x_pos_proof
        have h_w_int_x_pos : 0 < w_int_x := Int.cast_pos.mp h_w_int_x_cast_pos
        apply (Int.pos_iff_one_le).mp
        exact h_w_int_x_pos
  have subprob_quadratic_in_f_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), (↑(a_real) : ℝ) * f_real_x x hxS hxne0 ^ (2 : ℕ) + ((2 : ℝ) * (↑(a_real) : ℝ) - (1 : ℝ)) * (↑(w_real_x x hxS hxne0) : ℝ) * f_real_x x hxS hxne0 + (↑(a_real) : ℝ) * (↑(w_real_x x hxS hxne0) : ℝ) ^ (2 : ℕ) = (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    retro' with [w_int_x] subprob_w_int_x_ge_1_proof := subprob_w_int_x_ge_1_proof x hxS hxne0
    exact
      show a_real * f_real_x ^ 2 + ((2 : ℝ) * a_real - (1 : ℝ)) * w_real_x * f_real_x + a_real * w_real_x ^ 2 = (0 : ℝ) by
        mkOpaque
        have h_f_real_x_is_sub : f_real_x = x - ↑w_real_x := by rw [f_real_x_def, w_real_x_def]
        have h_sum_eq_x : f_real_x + (↑w_real_x : ℝ) = x := by rw [h_f_real_x_is_sub, sub_add_cancel]
        have h_lhs_transformed : (↑a_real : ℝ) * f_real_x ^ 2 + ((2 : ℝ) * ↑a_real - (1 : ℝ)) * (↑w_real_x : ℝ) * f_real_x + (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ 2 = (↑a_real : ℝ) * (f_real_x + ↑w_real_x) ^ 2 - (↑w_real_x : ℝ) * f_real_x := by ring
        rw [h_lhs_transformed]
        rw [h_sum_eq_x]
        rw [subprob_wf_eq_ax2_proof]
        simp
  letI discriminant_val : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℝ := by
    intro x hxS hxne0
    retro w_real_x := w_real_x x hxS hxne0
    exact w_real_x ^ 2 * ((1 : ℝ) - (4 : ℝ) * a_real)
  retro' discriminant_val_def : discriminant_val = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) => (↑(w_real_x x hxS hxne0) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by funext; rfl
  retro' discriminant_val_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), discriminant_val x hxS hxne0 = (↑(w_real_x x hxS hxne0) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by intros; rfl
  have subprob_discriminant_val_nonneg_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), discriminant_val x hxS hxne0 ≥ (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    retro' with [w_int_x] subprob_w_int_x_ge_1_proof := subprob_w_int_x_ge_1_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_quadratic_in_f_proof := subprob_quadratic_in_f_proof x hxS hxne0
    retro discriminant_val := discriminant_val x hxS hxne0
    retro' discriminant_val_def : discriminant_val = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by simp [discriminant_val, discriminant_val_def]
    exact
      show discriminant_val ≥ (0 : ℝ) by
        mkOpaque
        let A_coeff := (↑a_real : ℝ)
        let B_coeff := ((2 : ℝ) * (↑a_real : ℝ) - (1 : ℝ)) * (↑w_real_x : ℝ)
        let C_coeff := (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ (2 : ℕ)
        have h_quadratic_eq : A_coeff * f_real_x ^ (2 : ℕ) + B_coeff * f_real_x + C_coeff = 0 := by exact subprob_quadratic_in_f_proof
        have hA_ne_zero : A_coeff ≠ 0 := by linarith [subprob_a_real_pos_proof]
        have h_disc_ge_zero : B_coeff ^ 2 - 4 * A_coeff * C_coeff ≥ 0 :=
          by
          have h_quadratic_eq_for_thm : A_coeff * f_real_x * f_real_x + B_coeff * f_real_x + C_coeff = 0 := by
            rw [mul_assoc]
            rw [← pow_two f_real_x]
            exact h_quadratic_eq
          have h_disc_is_sq : discrim A_coeff B_coeff C_coeff = ((2 : ℝ) * A_coeff * f_real_x + B_coeff) ^ (2 : ℕ) := discrim_eq_sq_of_quadratic_eq_zero h_quadratic_eq_for_thm
          change (discrim A_coeff B_coeff C_coeff ≥ (0 : ℝ))
          rw [h_disc_is_sq]
          apply sq_nonneg ((2 : ℝ) * A_coeff * f_real_x + B_coeff)
        have h_calc_discr : B_coeff ^ 2 - 4 * A_coeff * C_coeff = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by
          simp only [A_coeff, B_coeff, C_coeff]
          ring
        rw [h_calc_discr] at h_disc_ge_zero
        rw [discriminant_val_def]
        exact h_disc_ge_zero
  have subprob_a_real_le_one_quarter_proof : ∀ (x : ℝ), x ∈ S → x ≠ (0 : ℝ) → (↑(a_real) : ℝ) ≤ (1 : ℝ) / (4 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    retro' with [w_int_x] subprob_w_int_x_ge_1_proof := subprob_w_int_x_ge_1_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_quadratic_in_f_proof := subprob_quadratic_in_f_proof x hxS hxne0
    retro discriminant_val := discriminant_val x hxS hxne0
    retro' discriminant_val_def : discriminant_val = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by simp [discriminant_val, discriminant_val_def]
    retro' with [discriminant_val] subprob_discriminant_val_nonneg_proof := subprob_discriminant_val_nonneg_proof x hxS hxne0
    exact
      show a_real ≤ (1 : ℝ) / (4 : ℝ) by
        mkOpaque
        have h_disc_formula_nonneg : (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) ≥ (0 : ℝ) := by
          rw [← discriminant_val_def]
          exact subprob_discriminant_val_nonneg_proof
        have h_w_real_x_sq_pos : (↑(w_real_x) : ℝ) ^ (2 : ℕ) > (0 : ℝ) := by exact pow_pos subprob_w_real_x_pos_proof (2 : ℕ)
        have h_factor_nonneg : (1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ) ≥ (0 : ℝ) := by
          exact
            nonneg_of_mul_nonneg_left
              (by {rw [mul_comm]; exact h_disc_formula_nonneg
              })
              h_w_real_x_sq_pos
        have h_one_ge_four_a : (1 : ℝ) ≥ (4 : ℝ) * (↑(a_real) : ℝ) := by exact sub_nonneg.mp h_factor_nonneg
        have four_pos : (4 : ℝ) > 0 := by norm_num
        have h_a_mul_four_le_one : (↑(a_real) : ℝ) * (4 : ℝ) ≤ (1 : ℝ) := by
          rw [mul_comm]
          exact h_one_ge_four_a
        rw [(le_div_iff' four_pos)]
        rw [mul_comm]
        exact h_a_mul_four_le_one
  letI k_expr_fn_of_a : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℝ → ℝ := by
    intro x hxS hxne0
    exact fun (cur_a_real : ℝ) => (((1 : ℝ) - (2 : ℝ) * cur_a_real) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real)
  retro' k_expr_fn_of_a_def : k_expr_fn_of_a = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) (cur_a_real : ℝ) => ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := by funext; rfl
  retro' k_expr_fn_of_a_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), ∀ (cur_a_real : ℝ), k_expr_fn_of_a x hxS hxne0 cur_a_real = ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := by intros; rfl
  letI k_val_for_x : (x : ℝ) → x ∈ S → x ≠ (0 : ℝ) → ℝ := by
    intro x hxS hxne0
    retro k_expr_fn_of_a := k_expr_fn_of_a x hxS hxne0
    exact k_expr_fn_of_a a_real
  retro' k_val_for_x_def : k_val_for_x = fun (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ (0 : ℝ)) => k_expr_fn_of_a x hxS hxne0 (↑(a_real) : ℝ) := by funext; rfl
  retro' k_val_for_x_def' : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), k_val_for_x x hxS hxne0 = k_expr_fn_of_a x hxS hxne0 (↑(a_real) : ℝ) := by intros; rfl
  have subprob_f_eq_w_k_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), f_real_x x hxS hxne0 = (↑(w_real_x x hxS hxne0) : ℝ) * k_val_for_x x hxS hxne0 := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    retro' with [w_int_x] subprob_w_int_x_ge_1_proof := subprob_w_int_x_ge_1_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_quadratic_in_f_proof := subprob_quadratic_in_f_proof x hxS hxne0
    retro discriminant_val := discriminant_val x hxS hxne0
    retro' discriminant_val_def : discriminant_val = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by simp [discriminant_val, discriminant_val_def]
    retro' with [discriminant_val] subprob_discriminant_val_nonneg_proof := subprob_discriminant_val_nonneg_proof x hxS hxne0
    retro' subprob_a_real_le_one_quarter_proof := subprob_a_real_le_one_quarter_proof x hxS hxne0
    retro k_expr_fn_of_a := k_expr_fn_of_a x hxS hxne0
    retro' k_expr_fn_of_a_def : k_expr_fn_of_a = fun (cur_a_real : ℝ) => ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := by simp [k_expr_fn_of_a, k_expr_fn_of_a_def]
    retro' k_expr_fn_of_a_def' : ∀ (cur_a_real : ℝ), k_expr_fn_of_a cur_a_real = ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := k_expr_fn_of_a_def' x hxS hxne0
    retro k_val_for_x := k_val_for_x x hxS hxne0
    retro' k_val_for_x_def : k_val_for_x = k_expr_fn_of_a (↑(a_real) : ℝ) := by simp [k_val_for_x, k_val_for_x_def]
    exact
      show f_real_x = w_real_x * k_val_for_x by
        mkOpaque
        let A_coeff := (↑a_real : ℝ)
        let B_coeff := ((2 : ℝ) * (↑a_real : ℝ) - (1 : ℝ)) * (↑w_real_x : ℝ)
        let C_coeff := (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ (2 : ℕ)
        have h_quadratic_eq : A_coeff * f_real_x * f_real_x + B_coeff * f_real_x + C_coeff = 0 := by
          rw [mul_assoc A_coeff f_real_x f_real_x]
          rw [← pow_two f_real_x]
          simp [A_coeff, B_coeff, C_coeff, subprob_quadratic_in_f_proof]
        have hA_coeff_ne_zero : A_coeff ≠ 0 := by linarith [subprob_a_real_pos_proof]
        have h_discrim_formula_eq_discriminant_val : B_coeff ^ 2 - 4 * A_coeff * C_coeff = discriminant_val := by
          simp only [A_coeff, B_coeff, C_coeff, discriminant_val_def]
          ring
        have h_discrim_eq_sqrt_sq : discrim A_coeff B_coeff C_coeff = (Real.sqrt discriminant_val) * (Real.sqrt discriminant_val) := by
          rw [discrim]
          rw [h_discrim_formula_eq_discriminant_val]
          exact (Real.mul_self_sqrt subprob_discriminant_val_nonneg_proof).symm
        have h_solutions := (quadratic_eq_zero_iff hA_coeff_ne_zero h_discrim_eq_sqrt_sq f_real_x).mp h_quadratic_eq
        have h_sqrt_discriminant_val_expr : Real.sqrt discriminant_val = (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ)) := by
          rw [discriminant_val_def]
          have hw_real_x_nonneg : (↑w_real_x : ℝ) ≥ 0 := by linarith [subprob_w_real_x_pos_proof]
          have h_term_nonneg : (1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ) ≥ 0 := by
            have h := subprob_a_real_le_one_quarter_proof
            linarith
          have h_sqrt_mul_eq : Real.sqrt ((↑w_real_x : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * ↑a_real)) = Real.sqrt ((↑w_real_x : ℝ) ^ (2 : ℕ)) * Real.sqrt ((1 : ℝ) - (4 : ℝ) * ↑a_real) := by
            apply Real.sqrt_mul
            exact sq_nonneg (↑w_real_x : ℝ)
          rw [h_sqrt_mul_eq]
          rw [Real.sqrt_sq_eq_abs]
          rw [_root_.abs_of_nonneg hw_real_x_nonneg]
        rw [h_sqrt_discriminant_val_expr] at h_solutions
        let sol1 := (-B_coeff + (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * A_coeff)
        let sol2 := (-B_coeff - (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * A_coeff)
        have h_sol2_eq_target : sol2 = (↑w_real_x : ℝ) * k_val_for_x := by
          simp only [sol2, B_coeff, A_coeff, k_val_for_x_def, k_expr_fn_of_a_def]
          have h_denom_ne_zero : (2 : ℝ) * (↑a_real : ℝ) ≠ 0 := by
            have h_denom_pos : (2 : ℝ) * (↑a_real : ℝ) > 0 := mul_pos (by norm_num) subprob_a_real_pos_proof
            exact ne_of_gt h_denom_pos
          field_simp [h_denom_ne_zero]
          ring
        have h_a_real_lt_one_quarter : (↑a_real : ℝ) < 1 / 4 := by
          apply lt_of_le_of_ne subprob_a_real_le_one_quarter_proof
          intro h_a_real_eq_one_quarter
          have h_discriminant_zero : discriminant_val = 0 := by
            rw [discriminant_val_def, h_a_real_eq_one_quarter]
            norm_num
          have h_sqrt_discriminant_zero : Real.sqrt discriminant_val = 0 := by
            rw [h_discriminant_zero]
            simp
          have h_f_real_x_is_unique_sol : f_real_x = -B_coeff / (2 * A_coeff) :=
            by
            have h_sqrt_term_zero_if_a_eq_one_quarter : Real.sqrt (1 - 4 * (↑a_real : ℝ)) = 0 := by
              rw [h_a_real_eq_one_quarter]
              norm_num
            rw [h_sqrt_term_zero_if_a_eq_one_quarter] at h_solutions
            simp only [mul_zero, add_zero, sub_zero, or_self] at h_solutions
            exact h_solutions
          have h_f_real_x_val_if_a_eq_one_quarter : f_real_x = (↑w_real_x : ℝ) := by
            rw [h_f_real_x_is_unique_sol]
            simp only [B_coeff, A_coeff, h_a_real_eq_one_quarter]
            field_simp [show (2 : ℝ) * (1 / 4 : ℝ) ≠ 0 by norm_num]
            ring
          have h_f_lt_1 := subprob_f_real_x_bounds_proof.2
          rw [h_f_real_x_val_if_a_eq_one_quarter] at h_f_lt_1
          have h_w_int_eq_w_real : w_int_x = w_real_x := by rw [w_int_x_def, w_real_x_def]
          have h_w_real_x_ge_1 : (↑w_real_x : ℝ) ≥ 1 := by
            rw [← h_w_int_eq_w_real]
            rw [ge_iff_le]
            rw [← Int.cast_one]
            exact (Int.cast_le (R := ℝ)).mpr subprob_w_int_x_ge_1_proof
          linarith [h_f_lt_1, h_w_real_x_ge_1]
        have h_sqrt_term_pos : 1 - 4 * (↑a_real : ℝ) > 0 := by linarith [h_a_real_lt_one_quarter]
        have h_Real_sqrt_pos : Real.sqrt (1 - 4 * (↑a_real : ℝ)) > 0 := Real.sqrt_pos_of_pos h_sqrt_term_pos
        have h_sol1_form : sol1 = (↑w_real_x : ℝ) * (((1 - 2 * (↑a_real : ℝ)) + Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * (↑a_real : ℝ))) := by
          simp only [sol1, B_coeff, A_coeff]
          field_simp [_root_.ne_of_gt subprob_a_real_pos_proof]
          ring
        have h_k_plus_val_gt_1 : ((1 - 2 * (↑a_real : ℝ)) + Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * (↑a_real : ℝ)) > 1 := by
          have h_2a_pos : 2 * (↑a_real : ℝ) > 0 := by exact mul_pos (by norm_num) subprob_a_real_pos_proof
          apply (lt_div_iff' h_2a_pos).mpr
          rw [mul_one]
          have h_intermediate_goal : 1 + Real.sqrt (1 - 4 * (↑a_real : ℝ)) > 4 * (↑a_real : ℝ) := by
            set y_val := Real.sqrt (1 - 4 * (↑a_real : ℝ)) with hy_val_def
            have h_identity_for_4a : 4 * (↑a_real : ℝ) = 1 - y_val ^ 2 := by
              rw [eq_comm]
              simp only [hy_val_def]
              rw [Real.sq_sqrt (le_of_lt h_sqrt_term_pos)]
              ring
            rw [h_identity_for_4a]
            have h_y_val_plus_y_val_sq_pos : y_val + y_val ^ 2 > 0 :=
              by
              have hy_val_pos : y_val > 0 := by
                rw [hy_val_def]
                exact h_Real_sqrt_pos
              have h_one_plus_y_val_pos : 1 + y_val > 0 := by linarith [hy_val_pos]
              have H_factor : y_val + y_val ^ 2 = y_val * (1 + y_val) := by ring
              rw [H_factor]
              exact mul_pos hy_val_pos h_one_plus_y_val_pos
            linarith [h_y_val_plus_y_val_sq_pos]
          linarith [h_intermediate_goal]
        have h_w_real_x_ge_1 : (↑w_real_x : ℝ) ≥ 1 := by
          have h_w_int_eq_w_real : w_int_x = w_real_x := by rw [w_int_x_def, w_real_x_def]
          rw [← h_w_int_eq_w_real]
          rw [ge_iff_le]
          rw [← Int.cast_one]
          exact (Int.cast_le (R := ℝ)).mpr subprob_w_int_x_ge_1_proof
        have h_sol1_gt_1 : sol1 > 1 := by
          rw [h_sol1_form]
          apply one_lt_mul_of_le_of_lt h_w_real_x_ge_1 h_k_plus_val_gt_1
        have h_f_real_x_lt_1 : f_real_x < 1 := subprob_f_real_x_bounds_proof.2
        rcases h_solutions with h_f_eq_sol1 | h_f_eq_sol2
        . exfalso
          linarith [h_f_eq_sol1, h_sol1_gt_1, h_f_real_x_lt_1]
        . rw [h_f_eq_sol2]
          exact h_sol2_eq_target
  have subprob_k_val_for_x_pos_proof : ∀ (x : ℝ), ∀ (hxS : x ∈ S), ∀ (hxne0 : x ≠ (0 : ℝ)), k_val_for_x x hxS hxne0 > (0 : ℝ) := by
    intro x hxS hxne0
    retro w_int_x := w_int_x x hxS hxne0
    retro' w_int_x_def : w_int_x = ⌊x⌋ := by simp [w_int_x, w_int_x_def]
    retro f_real_x := f_real_x x hxS hxne0
    retro' f_real_x_def : f_real_x = x - (↑(⌊x⌋) : ℝ) := by simp [f_real_x, f_real_x_def]
    retro w_real_x := w_real_x x hxS hxne0
    retro' w_real_x_def : w_real_x = ⌊x⌋ := by simp [w_real_x, w_real_x_def]
    retro' with [w_real_x, f_real_x] subprob_wf_eq_ax2_proof := subprob_wf_eq_ax2_proof x hxS hxne0
    retro' subprob_ax2_pos_proof := subprob_ax2_pos_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_wf_pos_proof := subprob_wf_pos_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_bounds_proof := subprob_f_real_x_bounds_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_ne_zero_proof := subprob_f_real_x_ne_zero_proof x hxS hxne0
    retro' with [f_real_x] subprob_f_real_x_pos_proof := subprob_f_real_x_pos_proof x hxS hxne0
    retro' with [w_real_x] subprob_w_real_x_pos_proof := subprob_w_real_x_pos_proof x hxS hxne0
    retro' with [w_int_x] subprob_w_int_x_ge_1_proof := subprob_w_int_x_ge_1_proof x hxS hxne0
    retro' with [w_real_x, f_real_x] subprob_quadratic_in_f_proof := subprob_quadratic_in_f_proof x hxS hxne0
    retro discriminant_val := discriminant_val x hxS hxne0
    retro' discriminant_val_def : discriminant_val = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by simp [discriminant_val, discriminant_val_def]
    retro' with [discriminant_val] subprob_discriminant_val_nonneg_proof := subprob_discriminant_val_nonneg_proof x hxS hxne0
    retro' subprob_a_real_le_one_quarter_proof := subprob_a_real_le_one_quarter_proof x hxS hxne0
    retro k_expr_fn_of_a := k_expr_fn_of_a x hxS hxne0
    retro' k_expr_fn_of_a_def : k_expr_fn_of_a = fun (cur_a_real : ℝ) => ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := by simp [k_expr_fn_of_a, k_expr_fn_of_a_def]
    retro' k_expr_fn_of_a_def' : ∀ (cur_a_real : ℝ), k_expr_fn_of_a cur_a_real = ((1 : ℝ) - (2 : ℝ) * cur_a_real - √((1 : ℝ) - (4 : ℝ) * cur_a_real)) / ((2 : ℝ) * cur_a_real) := k_expr_fn_of_a_def' x hxS hxne0
    retro k_val_for_x := k_val_for_x x hxS hxne0
    retro' k_val_for_x_def : k_val_for_x = k_expr_fn_of_a (↑(a_real) : ℝ) := by simp [k_val_for_x, k_val_for_x_def]
    retro' with [k_val_for_x, w_real_x, f_real_x] subprob_f_eq_w_k_proof := subprob_f_eq_w_k_proof x hxS hxne0
    exact
      show k_val_for_x > (0 : ℝ) by
        mkOpaque
        let h_f_pos := subprob_f_real_x_pos_proof
        let h_w_pos := subprob_w_real_x_pos_proof
        let h_eq := subprob_f_eq_w_k_proof
        have h_prod_pos : (↑w_real_x : ℝ) * k_val_for_x > 0 := by
          rw [← h_eq]
          exact h_f_pos
        exact (mul_pos_iff_of_pos_left h_w_pos).mp h_prod_pos
  letI k_actual := (((1 : ℝ) - (2 : ℝ) * a_real) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * a_real)) / ((2 : ℝ) * a_real)
  retro' k_actual_def : k_actual = ((1 : ℝ) - (2 : ℝ) * (↑(a_real) : ℝ) - √((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ))) / ((2 : ℝ) * (↑(a_real) : ℝ)) := by funext; rfl
  have subprob_k_actual_pos_proof : k_actual > (0 : ℝ) := by
    mkOpaque
    have h_exists_nonzero_in_S : ∃ x, x ∈ S ∧ x ≠ 0 := by
      by_contra! h_all_elements_in_S_are_zero
      have h_sum_is_zero : ∑ k in S, k = (0 : ℝ) := by
        apply Finset.sum_eq_zero
        exact h_all_elements_in_S_are_zero
      have h_420_eq_0 : (420 : ℝ) = (0 : ℝ) := by
        rw [← h₁]
        exact h_sum_is_zero
      norm_num at h_420_eq_0
    rcases h_exists_nonzero_in_S with ⟨x₀, hx₀S, hx₀ne0⟩
    rw [k_actual_def]
    rw [← k_expr_fn_of_a_def' x₀ hx₀S hx₀ne0 (↑a_real)]
    rw [← k_val_for_x_def' x₀ hx₀S hx₀ne0]
    exact subprob_k_val_for_x_pos_proof x₀ hx₀S hx₀ne0
  letI W_actual := Nat.ceil ((1 : ℝ) / k_actual) - 1
  retro' W_actual_def : W_actual = ⌈(1 : ℝ) / k_actual⌉₊ - (1 : ℕ) := by funext; rfl
  have subprob_S_elements_form_proof : S = Finset.image (fun (w_nat : ℕ) => (↑w_nat : ℝ) * ((1 : ℝ) + k_actual)) (Finset.Icc 1 W_actual) ∪ {(0 : ℝ)} := by
    mkOpaque
    let T := Finset.image (fun (w_nat : ℕ) => (↑w_nat : ℝ) * ((1 : ℝ) + k_actual)) (Finset.Icc 1 W_actual) ∪ {(0 : ℝ)}
    apply Finset.ext_iff.mpr
    intro x
    constructor
    . intro hxS
      by_cases hx_eq_zero : x = 0
      . rw [hx_eq_zero]
        apply Finset.mem_union_right
        apply Finset.mem_singleton_self
      . apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        let w_int := w_int_x x hxS hx_eq_zero
        have hw_int_def : w_int = ⌊x⌋ := by simp [w_int, w_int_x_def]
        have hw_int_ge_1 : w_int ≥ 1 := subprob_w_int_x_ge_1_proof x hxS hx_eq_zero
        let w_nat := Int.toNat w_int
        have hw_nat_ge_1 : w_nat ≥ 1 := by
          apply Nat.one_le_iff_ne_zero.mpr
          change (Int.toNat w_int) ≠ 0
          change ¬(Int.toNat w_int = 0)
          rw [Int.toNat_eq_zero]
          rw [not_le]
          linarith [hw_int_ge_1]
        have cast_w_nat_eq_w_int : (↑w_nat : ℤ) = w_int := by exact (Int.toNat_of_nonneg (Int.le_trans (by norm_num) hw_int_ge_1))
        have cast_w_nat_eq_w_int_real : (↑w_nat : ℝ) = (↑w_int : ℝ) := by norm_cast
        let f_x := f_real_x x hxS hx_eq_zero
        have hf_x_def : f_x = x - ↑⌊x⌋ := by simp [f_x, f_real_x_def]
        rw [← hw_int_def] at hf_x_def
        rw [← cast_w_nat_eq_w_int_real] at hf_x_def
        have hw_real_x_def : w_real_x x hxS hx_eq_zero = ⌊x⌋ := by rw [w_real_x_def]
        rw [← hw_int_def] at hw_real_x_def
        have hf_eq_wk : f_x = (↑w_int : ℝ) * k_val_for_x x hxS hx_eq_zero := by simp [f_x, subprob_f_eq_w_k_proof x hxS hx_eq_zero, hw_real_x_def]
        rw [k_val_for_x_def'] at hf_eq_wk
        rw [k_expr_fn_of_a_def'] at hf_eq_wk
        rw [← k_actual_def] at hf_eq_wk
        rw [← cast_w_nat_eq_w_int_real] at hf_eq_wk
        have hx_expr : x = (↑w_nat : ℝ) * (1 + k_actual) := by
          have h_x_eq_fx_plus_wnat : x = f_x + (↑w_nat : ℝ) := by exact eq_add_of_sub_eq (Eq.symm hf_x_def)
          rw [h_x_eq_fx_plus_wnat]
          rw [hf_eq_wk]
          ring
        use w_nat
        constructor
        . rw [Finset.mem_Icc]
          apply And.intro
          . exact hw_nat_ge_1
          . rw [W_actual_def]
            have hM_ge_1 : 1 ≤ ⌈(1 : ℝ) / k_actual⌉₊ := by
              apply Nat.one_le_of_lt
              apply Nat.ceil_pos.mpr
              apply one_div_pos.mpr
              exact subprob_k_actual_pos_proof
            rw [Nat.le_sub_iff_add_le hM_ge_1]
            rw [Nat.succ_le_iff]
            have h_inv_k_pos : (1 : ℝ) / k_actual > 0 := one_div_pos.mpr subprob_k_actual_pos_proof
            apply (Nat.lt_ceil).mpr
            rw [lt_div_iff' subprob_k_actual_pos_proof]
            rw [mul_comm]
            rw [← hf_eq_wk]
            exact (subprob_f_real_x_bounds_proof x hxS hx_eq_zero).right
        . exact (Eq.symm hx_expr)
    . intro hyT
      rw [Finset.mem_union] at hyT
      cases hyT
      . rename_i hy_in_image
        rw [Finset.mem_image] at hy_in_image
        rcases hy_in_image with ⟨w_nat, hw_nat_interval, hy_expr⟩
        apply (h₀ x).mpr
        rw [← a_real_def]
        have hy_expanded : x = (↑w_nat : ℝ) + (↑w_nat : ℝ) * k_actual := by
          rw [← hy_expr]
          ring
        have h_w_nat_ge_1 : w_nat ≥ 1 := (Finset.mem_Icc.mp hw_nat_interval).left
        have h_w_nat_le_W : w_nat ≤ W_actual := (Finset.mem_Icc.mp hw_nat_interval).right
        have w_k_pos : (↑w_nat : ℝ) * k_actual > 0 := by
          apply mul_pos
          . apply Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_w_nat_ge_1)
          . exact subprob_k_actual_pos_proof
        have w_k_lt_1 : (↑w_nat : ℝ) * k_actual < 1 := by
          rw [W_actual_def] at h_w_nat_le_W
          have h_ceil_ge_one : 1 ≤ ⌈1 / k_actual⌉₊ := by
            apply Nat.one_le_of_lt
            apply Nat.ceil_pos.mpr
            apply one_div_pos.mpr
            exact subprob_k_actual_pos_proof
          have h_lt_ceil : w_nat < ⌈1 / k_actual⌉₊ := by
            rw [Nat.le_sub_iff_add_le h_ceil_ge_one] at h_w_nat_le_W
            rw [Nat.succ_le_iff] at h_w_nat_le_W
            exact h_w_nat_le_W
          have cast_w_nat_lt_inv_k : (↑w_nat : ℝ) < 1 / k_actual := by
            apply Nat.lt_ceil.mp
            exact h_lt_ceil
          rw [mul_comm]
          rw [← lt_div_iff' subprob_k_actual_pos_proof]
          exact cast_w_nat_lt_inv_k
        have h_floor_y : ⌊x⌋ = (w_nat : ℤ) := by
          rw [hy_expanded]
          apply Int.floor_eq_iff.mpr
          constructor
          . rw [Int.cast_natCast]
            rw [le_add_iff_nonneg_right]
            exact le_of_lt w_k_pos
          . rw [Int.cast_natCast w_nat]
            rw [Real.add_lt_add_iff_left (↑w_nat : ℝ)]
            exact w_k_lt_1
        have lhs_eq : (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑w_nat : ℝ) ^ 2 * k_actual := by
          rw [h_floor_y, hy_expanded]
          simp only [Int.cast_natCast]
          ring
        rw [lhs_eq]
        have rhs_eq : (↑a_real : ℝ) * x ^ 2 = (↑a_real : ℝ) * (↑w_nat : ℝ) ^ 2 * (1 + k_actual) ^ 2 := by
          rw [← hy_expr]
          ring
        rw [rhs_eq]
        have w_nat_sq_pos : (↑w_nat : ℝ) ^ 2 > 0 := by apply sq_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_w_nat_ge_1))
        rw [mul_comm (↑a_real : ℝ) ((↑w_nat : ℝ) ^ 2)]
        rw [mul_assoc ((↑w_nat : ℝ) ^ 2) (↑a_real : ℝ) (((1 : ℝ) + k_actual) ^ (2 : ℕ))]
        rw [mul_right_inj' (ne_of_gt w_nat_sq_pos)]
        have h_k_equation : (↑a_real : ℝ) * k_actual ^ 2 + (2 * (↑a_real : ℝ) - 1) * k_actual + (↑a_real : ℝ) = 0 := by
          let A := (↑a_real : ℝ)
          have hA_pos : A > 0 := subprob_a_real_pos_proof
          have hA_ne_zero : A ≠ 0 := ne_of_gt hA_pos
          have h_sum_ne_zero : ∑ k in S, k ≠ 0 := by {rw [h₁]; norm_num
          }
          have exists_nonzero_elem : ∃ x_elem ∈ S, x_elem ≠ 0 := by {contrapose! h_sum_ne_zero; exact Finset.sum_eq_zero h_sum_ne_zero;
          }
          rcases exists_nonzero_elem with ⟨x_specific, hx_specific_S, hx_specific_ne0⟩
          have discriminant_prop := subprob_discriminant_val_nonneg_proof x_specific hx_specific_S hx_specific_ne0
          rw [discriminant_val_def'] at discriminant_prop
          have w_val_specific_pos : (↑(w_real_x x_specific hx_specific_S hx_specific_ne0) : ℝ) > 0 := subprob_w_real_x_pos_proof x_specific hx_specific_S hx_specific_ne0
          have w_sq_pos_specific : (↑(w_real_x x_specific hx_specific_S hx_specific_ne0) : ℝ) ^ 2 > 0 := pow_pos w_val_specific_pos 2
          have h_sqrt_term_nonneg : (1 : ℝ) - (4 : ℝ) * A ≥ 0 := nonneg_of_mul_nonneg_right discriminant_prop w_sq_pos_specific
          have h_k_eq_root : k_actual = ((1 - 2 * A - Real.sqrt (1 - 4 * A)) / (2 * A)) := k_actual_def
          rw [h_k_eq_root]
          field_simp [hA_ne_zero]
          ring_nf
          simp only [pow_two]
          have h_sqrt_term_target_nonneg : (1 : ℝ) - A * (4 : ℝ) ≥ 0 := by
            rw [mul_comm A (4 : ℝ)]
            exact h_sqrt_term_nonneg
          rw [Real.mul_self_sqrt h_sqrt_term_target_nonneg]
          ring
        rw [add_eq_zero_iff_eq_neg] at h_k_equation
        have h_target_rewrite : (↑a_real : ℝ) * (1 + k_actual) ^ 2 = (↑a_real : ℝ) + k_actual + ((↑a_real : ℝ) * k_actual ^ 2 + (2 * (↑a_real : ℝ) - 1) * k_actual) := by ring
        rw [h_target_rewrite]
        rw [h_k_equation]
        ring
      . rename_i hy_is_zero
        have hx_eq_zero_val : x = (0 : ℝ) := Finset.mem_singleton.mp hy_is_zero
        rw [hx_eq_zero_val]
        exact subprob_zero_in_S_proof
  have subprob_sum_eq_420_expanded_proof : (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ) * ((1 : ℝ) + k_actual)) = (420 : ℝ) := by
    mkOpaque
    let g := fun (w_nat : ℕ) => (↑w_nat : ℝ) * (1 + k_actual)
    let S' := Finset.image g (Finset.Icc 1 W_actual)
    have h_zero_not_in_S' : (0 : ℝ) ∉ S' := by
      rw [Finset.mem_image]
      rintro ⟨w_nat, hw_nat_mem_Icc, h_g_w_nat_eq_zero⟩
      have h_w_nat_ge_one : 1 ≤ w_nat := by
        rw [Finset.mem_Icc] at hw_nat_mem_Icc
        exact hw_nat_mem_Icc.left
      have h_w_nat_cast_pos : (↑w_nat : ℝ) > 0 := by
        simp only [Nat.cast_pos]
        exact lt_of_lt_of_le Nat.zero_lt_one h_w_nat_ge_one
      have h_one_plus_k_actual_pos : (1 : ℝ) + k_actual > 0 := by linarith [subprob_k_actual_pos_proof]
      have h_g_w_nat_pos : g w_nat > 0 := by
        simp only [g]
        exact mul_pos h_w_nat_cast_pos h_one_plus_k_actual_pos
      linarith [h_g_w_nat_pos, h_g_w_nat_eq_zero]
    have h_S'_disjoint_singleton_zero : Disjoint S' {(0 : ℝ)} := by
      apply Finset.disjoint_singleton_right.mpr
      exact h_zero_not_in_S'
    have h_sum_S_expanded : ∑ k ∈ S, k = (∑ k ∈ S', k) + (∑ k ∈ {(0 : ℝ)}, k) := by
      rw [subprob_S_elements_form_proof]
      exact Finset.sum_union h_S'_disjoint_singleton_zero
    have h_sum_singleton_zero : ∑ k ∈ {(0 : ℝ)}, k = (0 : ℝ) := by simp
    let sum_S := ∑ k ∈ S, k
    let sum_S' := ∑ k ∈ S', k
    have h_sum_S_eq_sum_S' : sum_S = sum_S' := by
      simp only [sum_S]
      rw [h_sum_S_expanded]
      rw [h_sum_singleton_zero]
      rw [add_zero]
    have h_sum_S'_eq_420 : (∑ k ∈ S', k) = (420 : ℝ) := by
      change sum_S' = (420 : ℝ)
      rw [← h_sum_S_eq_sum_S']
      exact h₁
    have h_g_inj_on_Icc : Set.InjOn g (Finset.Icc 1 W_actual : Set ℕ) := by
      intro w₁ hw₁_mem_Icc w₂ hw₂_mem_Icc h_g_w₁_eq_g_w₂
      simp only [g] at h_g_w₁_eq_g_w₂
      have h_one_plus_k_actual_pos : (1 : ℝ) + k_actual > 0 := by linarith [subprob_k_actual_pos_proof]
      have h_one_plus_k_actual_ne_zero : (1 : ℝ) + k_actual ≠ 0 := by linarith [h_one_plus_k_actual_pos]
      have h_cast_w₁_eq_cast_w₂ : (↑w₁ : ℝ) = (↑w₂ : ℝ) := by exact (mul_left_inj' h_one_plus_k_actual_ne_zero).mp h_g_w₁_eq_g_w₂
      exact Nat.cast_inj.mp h_cast_w₁_eq_cast_w₂
    have h_sum_S'_eq_sum_g_over_Icc : ∑ k ∈ S', k = ∑ w_nat ∈ Finset.Icc 1 W_actual, g w_nat := by
      simp only [S']
      exact Finset.sum_image h_g_inj_on_Icc
    rw [h_sum_S'_eq_sum_g_over_Icc] at h_sum_S'_eq_420
    exact h_sum_S'_eq_420
  have subprob_sum_rewritten_proof : ((1 : ℝ) + k_actual) * (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (420 : ℝ) := by
    mkOpaque
    rw [mul_comm]
    rw [Finset.sum_mul]
    exact subprob_sum_eq_420_expanded_proof
  have subprob_sum_arith_series_proof : (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ) := by
    mkOpaque
    rw [← Nat.cast_sum (Finset.Icc 1 W_actual) (fun x => x)]
    have h_nat_sum_formula : (∑ x ∈ Finset.Icc (1 : ℕ) W_actual, x) = W_actual * (W_actual + 1) / 2 := by
      change (∑ x ∈ Finset.Ico 1 (W_actual + 1), x) = W_actual * (W_actual + 1) / 2
      rw [Finset.sum_Ico_eq_sum_range (fun i : ℕ => i) 1 (W_actual + 1)]
      simp only [Nat.add_one_sub_one]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [add_comm]
      rw [Nat.mul_comm W_actual (W_actual + 1)]
      have h_rhs_is_sum_range_succ : (W_actual + 1) * W_actual / 2 = ∑ i in Finset.range (W_actual + 1), i := by
        rw [Finset.sum_range_id (W_actual + 1)]
        rw [Nat.add_one_sub_one W_actual]
      rw [h_rhs_is_sum_range_succ]
      exact (Finset.sum_range_succ id W_actual).symm
    rw [h_nat_sum_formula]
    have h_rhs_transformed : (↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (↑(2 : ℕ) : ℝ) := by
      have h1 : (↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ) = (↑W_actual : ℝ) * (↑W_actual + (1 : ℝ)) / (2 : ℝ) := by simp only [Nat.cast_one]
      have h2 : (↑W_actual : ℝ) * (↑W_actual + (1 : ℝ)) / (2 : ℝ) = (↑W_actual : ℝ) * (↑(W_actual + 1) : ℝ) / (2 : ℝ) := by rw [← Nat.cast_add_one W_actual]
      have h3 : (↑W_actual : ℝ) * (↑(W_actual + 1) : ℝ) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (2 : ℝ) := by rw [← Nat.cast_mul W_actual (W_actual + 1)]
      have h4 : (↑(W_actual * (W_actual + 1)) : ℝ) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (↑(2 : ℕ) : ℝ) := by rw [← Nat.cast_two]
      rw [h1, h2, h3, h4]
    rw [h_rhs_transformed]
    have h_dvd : 2 ∣ W_actual * (W_actual + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self W_actual)
    rw [Nat.cast_div h_dvd (by simp : (↑(2 : ℕ) : ℝ) ≠ (0 : ℝ))]
  have subprob_main_eq_W_k_proof : ((1 : ℝ) + k_actual) * ((↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ)) = (420 : ℝ) := by
    mkOpaque
    rw [← subprob_sum_arith_series_proof]
    exact subprob_sum_rewritten_proof
  have subprob_W_actual_ge_1_proof : W_actual ≥ 1 := by
    mkOpaque
    apply Nat.one_le_iff_ne_zero.mpr
    by_contra h_W_actual_is_zero
    have h_S_def : S = Finset.image (fun (w_nat : ℕ) => (↑(w_nat) : ℝ) * ((1 : ℝ) + k_actual)) (Finset.Icc (1 : ℕ) W_actual) ∪ ({(0 : ℝ)} : Finset ℝ) := subprob_S_elements_form_proof
    rw [h_W_actual_is_zero] at h_S_def
    have h_Icc_empty : Finset.Icc (1 : ℕ) 0 = ∅ := by
      apply Finset.Icc_eq_empty
      apply Nat.not_le_of_gt
      exact Nat.zero_lt_one
    rw [h_Icc_empty] at h_S_def
    rw [Finset.image_empty] at h_S_def
    rw [Finset.empty_union] at h_S_def
    have h_sum_S_val : ∑ k ∈ S, k = (420 : ℝ) := h₁
    rw [h_S_def] at h_sum_S_val
    simp only [Finset.sum_singleton] at h_sum_S_val
    have h_contr : (0 : ℝ) ≠ (420 : ℝ) := by norm_num
    exact h_contr h_sum_S_val
  have subprob_W_bounds_from_def_proof : ((↑W_actual + (1 : ℕ) : ℝ)⁻¹ ≤ k_actual ∧ k_actual < ((↑W_actual) : ℝ)⁻¹) := by
    mkOpaque
    let Y_val : ℝ := (1 : ℝ) / k_actual
    have Y_val_def : Y_val = (1 : ℝ) / k_actual := rfl
    have hY_val_pos : Y_val > 0 := by
      rw [Y_val_def]
      apply div_pos
      norm_num
      exact subprob_k_actual_pos_proof
    have h_ceil_Y_val_ge_2 : ⌈Y_val⌉₊ ≥ 2 := by
      rw [W_actual_def] at subprob_W_actual_ge_1_proof
      rw [← Y_val_def] at subprob_W_actual_ge_1_proof
      have h_one_le_ceil_Y_val : 1 ≤ ⌈Y_val⌉₊ := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro h_ceil_Y_val_eq_zero
        have h_rewritten_subprob : ⌈Y_val⌉₊ - 1 ≥ 1 := subprob_W_actual_ge_1_proof
        rw [h_ceil_Y_val_eq_zero] at h_rewritten_subprob
        rw [Nat.zero_sub] at h_rewritten_subprob
        exact Nat.not_succ_le_zero 0 h_rewritten_subprob
      have h_intermediate_ineq : ⌈Y_val⌉₊ ≥ 1 + 1 := (Nat.le_sub_iff_add_le h_one_le_ceil_Y_val).mp subprob_W_actual_ge_1_proof
      exact h_intermediate_ineq
    have h_ceil_Y_val_ge_1 : ⌈Y_val⌉₊ ≥ 1 := by linarith [h_ceil_Y_val_ge_2]
    apply And.intro
    . have h_W_plus_1_eq_ceil_Y_val : W_actual + 1 = ⌈Y_val⌉₊ := by
        rw [W_actual_def]
        rw [← Y_val_def]
        apply Nat.sub_add_cancel
        exact h_ceil_Y_val_ge_1
      have h_denom_eq_ceil_Y_val_cast : (↑W_actual + (1 : ℕ) : ℝ) = (↑(⌈Y_val⌉₊) : ℝ) := by
        rw [Nat.cast_one]
        rw [(Nat.cast_add_one W_actual).symm]
        rw [h_W_plus_1_eq_ceil_Y_val]
      rw [h_denom_eq_ceil_Y_val_cast]
      have h_ceil_Y_val_cast_pos : (↑(⌈Y_val⌉₊) : ℝ) > 0 := by
        rw [gt_iff_lt]
        rw [Nat.cast_pos]
        linarith [h_ceil_Y_val_ge_2]
      rw [inv_pos_le_iff_one_le_mul h_ceil_Y_val_cast_pos]
      rw [mul_comm]
      rw [← div_le_iff subprob_k_actual_pos_proof]
      rw [← Y_val_def]
      exact Nat.le_ceil Y_val
    . have h_W_actual_cast_pos : (↑W_actual : ℝ) > 0 := by
        apply Nat.cast_pos.mpr
        apply Nat.lt_of_succ_le
        exact subprob_W_actual_ge_1_proof
      rw [inv_eq_one_div]
      rw [lt_div_iff h_W_actual_cast_pos]
      have h_key_rewrite : k_actual * (↑W_actual : ℝ) < 1 ↔ (↑W_actual : ℝ) < k_actual⁻¹ := by
        rw [mul_comm]
        conv_rhs => rw [← mul_lt_mul_iff_of_pos_right subprob_k_actual_pos_proof]
        rw [inv_mul_cancel (ne_of_gt subprob_k_actual_pos_proof)]
      rw [h_key_rewrite]
      rw [inv_eq_one_div]
      rw [← Y_val_def]
      have h_cast_W_actual : (↑W_actual : ℝ) = (↑(⌈Y_val⌉₊) : ℝ) - 1 := by
        rw [W_actual_def]
        rw [← Y_val_def]
        rw [Nat.cast_sub h_ceil_Y_val_ge_1]
        rw [Nat.cast_one]
      rw [h_cast_W_actual]
      rw [sub_lt_iff_lt_add]
      exact Nat.ceil_lt_add_one (le_of_lt hY_val_pos)
  have subprob_W_actual_is_28_proof : W_actual = 28 := by
    mkOpaque
    let W_R : ℝ := ↑W_actual
    have h_W_R_ge_1 : W_R ≥ 1 := by
      rw [← Nat.cast_one]
      rw [ge_iff_le]
      rw [Nat.cast_le (α := ℝ)]
      exact subprob_W_actual_ge_1_proof
    have h_W_R_pos : W_R > 0 := by linarith [h_W_R_ge_1]
    have h_W_R_plus_1_pos : W_R + 1 > 0 := by linarith [h_W_R_ge_1]
    have h_W_R_ne_zero : W_R ≠ 0 := by linarith [h_W_R_ge_1]
    have h_W_R_plus_1_ne_zero : W_R + 1 ≠ 0 := by linarith [h_W_R_ge_1]
    have eq_main : ((1 : ℝ) + k_actual) * (W_R * (W_R + (1 : ℝ)) / (2 : ℝ)) = (420 : ℝ) := by
      convert subprob_main_eq_W_k_proof using 1
      simp
    have h_k_bounds := subprob_W_bounds_from_def_proof
    have h_k_lower : 1 / (W_R + 1) ≤ k_actual := by
      have temp := h_k_bounds.1
      norm_cast at temp
      convert temp
      · funext x
        rw [one_div]
      · simp only [Nat.cast_add, Nat.cast_one]
    have h_k_upper : k_actual < 1 / W_R := by
      have temp := h_k_bounds.2
      norm_cast at temp
      rw [one_div]
      exact temp
    have h_W_actual_le_28 : W_actual ≤ 28 := by
      have h1_1 : 1 + 1 / (W_R + 1) ≤ 1 + k_actual := add_le_add_left h_k_lower 1
      have h1_2 : 1 + 1 / (W_R + 1) = (W_R + 2) / (W_R + 1) := by
        field_simp [h_W_R_plus_1_ne_zero]
        ring
      rw [h1_2] at h1_1
      let factor_val : ℝ := W_R * (W_R + (1 : ℝ)) / (2 : ℝ)
      have factor_nonneg : factor_val ≥ 0 := by
        apply div_nonneg
        · apply mul_nonneg
          · exact le_of_lt h_W_R_pos
          · exact le_of_lt h_W_R_plus_1_pos
        · norm_num
      have h1_3 : ((W_R + 2) / (W_R + 1)) * factor_val ≤ ((1 + k_actual) * factor_val) := mul_le_mul_of_nonneg_right h1_1 factor_nonneg
      rw [eq_main] at h1_3
      have h1_4_lhs_simp : ((W_R + 2) / (W_R + 1)) * (W_R * (W_R + (1 : ℝ)) / (2 : ℝ)) = W_R * (W_R + 2) / (2 : ℝ) := by
        field_simp [h_W_R_plus_1_ne_zero]
        ring
      rw [h1_4_lhs_simp] at h1_3
      have h1_5 : W_R * (W_R + 2) ≤ 840 := by
        have temp := (mul_le_mul_left (by norm_num : (0 : ℝ) < 2)).mpr h1_3
        have eq_lhs : (2 : ℝ) * (W_R * (W_R + (2 : ℝ)) / (2 : ℝ)) = W_R * (W_R + (2 : ℝ)) := by field_simp
        have eq_rhs : (2 : ℝ) * (420 : ℝ) = (840 : ℝ) := by norm_num
        rw [eq_lhs, eq_rhs] at temp
        exact temp
      have h1_6 : W_R ^ 2 + 2 * W_R ≤ 840 := by
        have algebra_eq : W_R ^ 2 + 2 * W_R = W_R * (W_R + 2) := by ring
        rw [algebra_eq]
        exact h1_5
      have h1_7 : W_R ^ 2 + 2 * W_R - 840 ≤ 0 := by linarith [h1_6]
      have h1_8_factor_form : (W_R - 28) * (W_R + 30) = W_R ^ 2 + 2 * W_R - 840 := by ring
      rw [← h1_8_factor_form] at h1_7
      have h1_9_WR_plus_30_pos : W_R + 30 > 0 := by linarith [h_W_R_ge_1]
      have h1_10_WR_minus_28_le_0 : W_R - 28 ≤ 0 := by exact nonpos_of_mul_nonpos_left h1_7 h1_9_WR_plus_30_pos
      have h1_11_WR_le_28 : W_R ≤ 28 := by linarith [h1_10_WR_minus_28_le_0]
      rw [show (28 : ℝ) = ↑(28 : ℕ) by norm_cast] at h1_11_WR_le_28
      exact (Nat.cast_le (α := ℝ)).mp h1_11_WR_le_28
    have h_W_actual_ge_28 : W_actual ≥ 28 := by
      have h2_1 : 1 + k_actual < 1 + 1 / W_R := add_lt_add_left h_k_upper 1
      have h2_2 : 1 + 1 / W_R = (W_R + 1) / W_R := by field_simp [h_W_R_ne_zero]
      rw [h2_2] at h2_1
      let factor_val : ℝ := W_R * (W_R + (1 : ℝ)) / (2 : ℝ)
      have factor_pos : factor_val > 0 := by
        apply div_pos
        · exact mul_pos h_W_R_pos h_W_R_plus_1_pos
        · norm_num
      have h2_3 : ((1 + k_actual) * factor_val) < ((W_R + 1) / W_R) * factor_val := (mul_lt_mul_right factor_pos).mpr h2_1
      rw [eq_main] at h2_3
      have h2_4_rhs_simp : ((W_R + 1) / W_R) * (W_R * (W_R + (1 : ℝ)) / (2 : ℝ)) = (W_R + 1) ^ 2 / (2 : ℝ) := by
        field_simp [h_W_R_ne_zero]
        ring
      rw [h2_4_rhs_simp] at h2_3
      have h2_5 : 840 < (W_R + 1) ^ 2 := by
        have temp := (mul_lt_mul_left (by norm_num : (0 : ℝ) < 2)).mpr h2_3
        have simplify_lhs : (2 : ℝ) * (420 : ℝ) = (840 : ℝ) := by norm_num
        have simplify_rhs : (2 : ℝ) * ((W_R + (1 : ℝ)) ^ (2 : ℕ) / (2 : ℝ)) = (W_R + (1 : ℝ)) ^ (2 : ℕ) := by
          have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
          field_simp [h_two_ne_zero]
        rw [simplify_lhs, simplify_rhs] at temp
        exact temp
      by_contra hc_WR_lt_28_contra_hyp
      simp [not_le] at hc_WR_lt_28_contra_hyp
      have h_WR_lt_28_nat_cast : W_R < (↑28 : ℝ) := by exact (Nat.cast_lt (α := ℝ)).mpr hc_WR_lt_28_contra_hyp
      have h_Wactual_lt_28 : W_actual < 28 := (Nat.cast_lt (α := ℝ)).mp h_WR_lt_28_nat_cast
      have h_Wactual_le_27 : W_actual ≤ 27 := by
        rw [← Nat.lt_succ_iff]
        exact h_Wactual_lt_28
      have h_WR_le_27 : W_R ≤ 27 := by exact (Nat.cast_le (α := ℝ)).mpr h_Wactual_le_27
      have h_WR_plus_1_le_28 : W_R + 1 ≤ 28 := by linarith [h_WR_le_27]
      have h_WR_plus_1_sq_le_28_sq : (W_R + 1) ^ 2 ≤ 28 ^ 2 := by apply pow_le_pow_of_le_left (le_of_lt h_W_R_plus_1_pos) h_WR_plus_1_le_28
      have h_28_sq_val : (28 : ℝ) ^ 2 = 784 := by norm_num
      rw [h_28_sq_val] at h_WR_plus_1_sq_le_28_sq
      have h_absurd_ineq : (840 : ℝ) < 784 := by linarith [h2_5, h_WR_plus_1_sq_le_28_sq]
      have h_not_absurd_ineq : ¬((840 : ℝ) < 784) := by norm_num
      contradiction
    exact Nat.le_antisymm h_W_actual_le_28 h_W_actual_ge_28
  have subprob_k_actual_is_1_29_proof : k_actual = (1 : ℝ) / (29 : ℝ) := by
    mkOpaque
    have h_main_eq : ((1 : ℝ) + k_actual) * ((↑(W_actual) : ℝ) * ((↑(W_actual) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ)) = (420 : ℝ) := subprob_main_eq_W_k_proof
    have h_main_eq_W28 : ((1 : ℝ) + k_actual) * ((↑(28 : ℕ) : ℝ) * ((↑(28 : ℕ) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ)) = (420 : ℝ) := by
      rw [subprob_W_actual_is_28_proof] at h_main_eq
      exact h_main_eq
    have h_coeff_val : (↑(28 : ℕ) : ℝ) * ((↑(28 : ℕ) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ) = (406 : ℝ) := by
      norm_cast
      norm_num
    have h_simplified_eq : ((1 : ℝ) + k_actual) * (406 : ℝ) = (420 : ℝ) := by
      rw [h_coeff_val] at h_main_eq_W28
      exact h_main_eq_W28
    have h_406_ne_zero : (406 : ℝ) ≠ (0 : ℝ) := by norm_num
    have h_1_plus_k_eq_frac : (1 : ℝ) + k_actual = (420 : ℝ) / (406 : ℝ) := by exact eq_div_of_mul_eq h_406_ne_zero h_simplified_eq
    have h_frac_simp : (420 : ℝ) / (406 : ℝ) = (30 : ℝ) / (29 : ℝ) := by norm_num
    have h_1_plus_k_final : (1 : ℝ) + k_actual = (30 : ℝ) / (29 : ℝ) := by rw [h_1_plus_k_eq_frac, h_frac_simp]
    have h_k_actual_expr : k_actual = (30 : ℝ) / (29 : ℝ) - (1 : ℝ) := by linarith [h_1_plus_k_final]
    have h_final_calc : (30 : ℝ) / (29 : ℝ) - (1 : ℝ) = (1 : ℝ) / (29 : ℝ) := by norm_num
    rw [h_k_actual_expr, h_final_calc]
  have subprob_a_solve1_proof : (1 : ℝ) / (29 : ℝ) = (((1 : ℝ) - (2 : ℝ) * a_real) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * a_real)) / ((2 : ℝ) * a_real) := by
    mkOpaque
    rw [← subprob_k_actual_is_1_29_proof]
    exact k_actual_def
  have subprob_a_solve2_proof : ((2 : ℝ) * a_real) / (29 : ℝ) = ((1 : ℝ) - (2 : ℝ) * a_real) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * a_real) := by
    mkOpaque
    let D_val := (2 : ℝ) * (↑a_real : ℝ)
    let N_val := (1 : ℝ) - (2 : ℝ) * (↑a_real : ℝ) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ))
    have hD_val_ne_zero : D_val ≠ 0 := by
      have h_a_real_pos : (↑a_real : ℝ) > 0 := subprob_a_real_pos_proof
      have h_a_real_ne_zero : (↑a_real : ℝ) ≠ 0 := ne_of_gt h_a_real_pos
      have h_two_ne_zero : (2 : ℝ) ≠ 0 := two_ne_zero
      exact mul_ne_zero h_two_ne_zero h_a_real_ne_zero
    have h_intermediate_eq : (1 : ℝ) / (29 : ℝ) * D_val = N_val := by exact (eq_div_iff_mul_eq hD_val_ne_zero).mp subprob_a_solve1_proof
    rw [one_div_mul_eq_div (29 : ℝ) D_val] at h_intermediate_eq
    exact h_intermediate_eq
  have subprob_a_solve3_proof : Real.sqrt ((1 : ℝ) - (4 : ℝ) * a_real) = ((1 : ℝ) - (2 : ℝ) * a_real) - ((2 : ℝ) * a_real) / (29 : ℝ) := by
    mkOpaque
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    rw [subprob_a_solve2_proof]
    rw [sub_add_cancel]
  have subprob_a_solve4_proof : Real.sqrt ((1 : ℝ) - (4 : ℝ) * a_real) = (1 : ℝ) - ((60 : ℝ) / (29 : ℝ)) * a_real := by
    mkOpaque
    rw [subprob_a_solve3_proof]
    ring
  have subprob_rhs_nonneg_for_squaring_proof : (1 : ℝ) - ((60 : ℝ) / (29 : ℝ)) * a_real ≥ (0 : ℝ) := by
    mkOpaque
    have h_W_actual_ge_1 : W_actual ≥ 1 := subprob_W_actual_ge_1_proof
    have h_one_in_Icc : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) W_actual := by
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.le_refl 1
      · exact h_W_actual_ge_1
    let x_val := (↑(1 : ℕ) : ℝ) * (1 + k_actual)
    have h_x_val_in_image : x_val ∈ Finset.image (fun (w_nat : ℕ) ↦ (↑w_nat : ℝ) * (1 + k_actual)) (@Finset.Icc ℕ _ _ (1 : ℕ) W_actual) := by
      apply Finset.mem_image_of_mem (f := fun w_nat : ℕ ↦ (↑w_nat : ℝ) * (1 + k_actual)) (a := (1 : ℕ))
      exact h_one_in_Icc
    have h_x_val_in_S : x_val ∈ S := by
      rw [subprob_S_elements_form_proof]
      apply Finset.mem_union_left
      exact h_x_val_in_image
    have h_k_actual_val : k_actual = (1 : ℝ) / (29 : ℝ) := subprob_k_actual_is_1_29_proof
    have h_k_actual_pos : k_actual > 0 := by
      rw [h_k_actual_val]
      norm_num
    have h_one_plus_k_actual_pos : 1 + k_actual > 0 := by linarith [h_k_actual_pos]
    have h_x_val_ne_zero : x_val ≠ 0 := by
      simp only [x_val, Nat.cast_one, one_mul]
      linarith [h_one_plus_k_actual_pos]
    have h_a_real_le_one_quarter : (↑a_real : ℝ) ≤ (1 : ℝ) / (4 : ℝ) := by apply subprob_a_real_le_one_quarter_proof x_val h_x_val_in_S h_x_val_ne_zero
    have h_four_a_real_le_one : (4 : ℝ) * ↑a_real ≤ 1 := by
      rw [mul_comm]
      have h_pos_4 : (0 : ℝ) < (4 : ℝ) := by norm_num
      rw [← le_div_iff h_pos_4]
      exact h_a_real_le_one_quarter
    have h_term_under_sqrt_nonneg : (1 : ℝ) - (4 : ℝ) * ↑a_real ≥ 0 := by exact sub_nonneg_of_le h_four_a_real_le_one
    rw [← subprob_a_solve4_proof]
    apply Real.sqrt_nonneg
  have subprob_a_solve5_proof : (1 : ℝ) - (4 : ℝ) * a_real = ((1 : ℝ) - ((60 : ℝ) / (29 : ℝ)) * a_real) ^ 2 := by
    mkOpaque
    have h_W_actual_ge_1 : W_actual ≥ 1 := subprob_W_actual_ge_1_proof
    let x_val := (↑(1 : ℕ) : ℝ) * ((1 : ℝ) + k_actual)
    have h_x_val_in_S : x_val ∈ S := by
      rw [subprob_S_elements_form_proof]
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      use(1 : ℕ)
      refine' ⟨_, rfl⟩
      rw [Finset.mem_Icc]
      exact ⟨le_rfl, h_W_actual_ge_1⟩
    have h_k_actual_pos : k_actual > 0 := by
      rw [subprob_k_actual_is_1_29_proof]
      norm_num
    have h_x_val_ne_zero : x_val ≠ 0 := by
      simp only [x_val, Nat.cast_one, one_mul]
      linarith [h_k_actual_pos]
    have h_a_real_le_one_quarter : (↑a_real : ℝ) ≤ (1 : ℝ) / (4 : ℝ) := subprob_a_real_le_one_quarter_proof x_val h_x_val_in_S h_x_val_ne_zero
    have h_term_under_sqrt_nonneg : (1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ) ≥ 0 := by
      have h_four_pos : (4 : ℝ) > 0 := by norm_num
      have h_mul_le : (4 : ℝ) * (↑a_real : ℝ) ≤ (4 : ℝ) * (1 / 4) := by
        apply (mul_le_mul_left h_four_pos).mpr
        exact h_a_real_le_one_quarter
      have h_rhs_eq_one : (4 : ℝ) * (1 / 4) = 1 := by norm_num
      rw [h_rhs_eq_one] at h_mul_le
      linarith [h_mul_le]
    apply Eq.symm
    apply (Real.sqrt_eq_iff_sq_eq h_term_under_sqrt_nonneg subprob_rhs_nonneg_for_squaring_proof).mp
    exact subprob_a_solve4_proof
  have subprob_a_solve6_proof : (1 : ℝ) - (4 : ℝ) * a_real = (1 : ℝ) - (2 : ℝ) * ((60 : ℝ) / (29 : ℝ)) * a_real + (((60 : ℝ) / (29 : ℝ)) * a_real) ^ 2 := by
    mkOpaque
    have h_expansion : ((1 : ℝ) - (60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ)) ^ (2 : ℕ) = (1 : ℝ) - (2 : ℝ) * ((60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ)) + (((60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ))) ^ 2 := by ring
    rw [subprob_a_solve5_proof, h_expansion]
    ring
  have subprob_a_solve7_proof : -(4 : ℝ) * a_real = -((120 : ℝ) / (29 : ℝ)) * a_real + (((3600 : ℝ) / ((29 : ℝ) ^ 2))) * a_real ^ 2 := by
    mkOpaque
    have h_derived : -(4 : ℝ) * (↑a_real : ℝ) = -(2 : ℝ) * ((60 : ℝ) / (29 : ℝ)) * (↑a_real : ℝ) + ((60 : ℝ) / (29 : ℝ) * (↑(a_real) : ℝ)) ^ (2 : ℕ) := by
      have h_temp := subprob_a_solve6_proof
      rw [sub_eq_add_neg, sub_eq_add_neg] at h_temp
      replace h_temp := congr_arg (fun (val : ℝ) => -(1 : ℝ) + val) h_temp
      dsimp at h_temp
      simp only [neg_add_cancel_left, add_assoc] at h_temp
      rw [← neg_mul (4 : ℝ) (↑a_real), ← neg_mul ((2 : ℝ) * ((60 : ℝ) / (29 : ℝ))) (↑a_real)] at h_temp
      rw [← neg_mul (2 : ℝ) ((60 : ℝ) / (29 : ℝ))] at h_temp
      exact h_temp
    rw [h_derived]
    ring
  have subprob_a_solve8_proof : -(4 : ℝ) = -((120 : ℝ) / (29 : ℝ)) + (((3600 : ℝ) / ((29 : ℝ) ^ 2))) * a_real := by
    mkOpaque
    let ar := (↑a_real : ℝ)
    have ar_ne_zero : ar ≠ 0 := by linarith [subprob_a_real_pos_proof]
    have h_eq := subprob_a_solve7_proof
    simp only [pow_two] at h_eq
    have h_rhs_factor : -((120 : ℝ) / (29 : ℝ)) * ar + (3600 : ℝ) / ((29 : ℝ) * (29 : ℝ)) * (ar * ar) = (-((120 : ℝ) / (29 : ℝ)) + (3600 : ℝ) / ((29 : ℝ) * (29 : ℝ)) * ar) * ar := by ring
    rw [h_rhs_factor] at h_eq
    rw [mul_eq_mul_right_iff] at h_eq
    simp [ar_ne_zero] at h_eq
    rw [← pow_two (29 : ℝ)] at h_eq
    exact h_eq
  have subprob_a_solve9_proof : ((120 : ℝ) / (29 : ℝ)) - (4 : ℝ) = (((3600 : ℝ) / ((29 : ℝ) ^ 2))) * a_real := by
    mkOpaque
    rw [sub_eq_add_neg]
    rw [subprob_a_solve8_proof]
    rw [← add_assoc]
    rw [add_right_neg]
    rw [zero_add]
  have subprob_a_solve10_proof : (4 : ℝ) / (29 : ℝ) = (((3600 : ℝ) / ((29 : ℝ) ^ 2))) * a_real := by
    mkOpaque
    have h_lhs_equiv : (120 : ℝ) / (29 : ℝ) - (4 : ℝ) = (4 : ℝ) / (29 : ℝ) := by norm_num
    rw [h_lhs_equiv.symm]
    exact subprob_a_solve9_proof
  have subprob_a_solve11_proof : a_real = ((4 : ℝ) / (29 : ℝ)) * (((29 : ℝ) ^ 2) / ((3600 : ℝ))) := by
    mkOpaque
    have h_main := subprob_a_solve10_proof
    let Coeff := (3600 : ℝ) / ((29 : ℝ) ^ (2 : ℕ))
    have hCoeffNum_ne_zero : (3600 : ℝ) ≠ 0 := by norm_num
    have h29_ne_zero : (29 : ℝ) ≠ 0 := by norm_num
    have hCoeffDen_ne_zero : (29 : ℝ) ^ (2 : ℕ) ≠ 0 := by
      apply pow_ne_zero
      exact h29_ne_zero
    have hCoeff_ne_zero : Coeff ≠ 0 := by apply div_ne_zero hCoeffNum_ne_zero hCoeffDen_ne_zero
    have h_main_symm : Coeff * (↑a_real : ℝ) = (4 : ℝ) / (29 : ℝ) := Eq.symm h_main
    have h_a_real_eq : (↑a_real : ℝ) = Coeff⁻¹ * ((4 : ℝ) / (29 : ℝ)) := by exact (eq_inv_mul_iff_mul_eq₀ hCoeff_ne_zero).mpr h_main_symm
    rw [h_a_real_eq]
    rw [mul_comm (Coeff⁻¹) (((4 : ℝ) / (29 : ℝ)))]
    have h_factor_ne_zero : (4 : ℝ) / (29 : ℝ) ≠ 0 := by
      apply div_ne_zero
      . norm_num
      . norm_num
    simp only [mul_eq_mul_left_iff, h_factor_ne_zero]
    rw [inv_div]
    simp only [or_false]
  have subprob_a_real_is_29_900_proof : a_real = (29 : ℝ) / (900 : ℝ) := by
    mkOpaque
    rw [subprob_a_solve11_proof]
    have h_29_ne_0 : (29 : ℝ) ≠ 0 := by norm_num
    have h_3600_ne_0 : (3600 : ℝ) ≠ 0 := by norm_num
    have h_900_ne_0 : (900 : ℝ) ≠ 0 := by norm_num
    field_simp [h_29_ne_0, h_3600_ne_0, h_900_ne_0]
    norm_num
  have subprob_a_rat_is_29_900_proof : a = (29 : ℚ) / (900 : ℚ) := by
    mkOpaque
    apply (@Rat.cast_inj ℝ _ _).mp
    rw [← a_real_def]
    rw [subprob_a_real_is_29_900_proof]
    simp
  have subprob_coprime_29_900_proof : Nat.Coprime 29 900 := by
    mkOpaque
    rw [Nat.coprime_iff_gcd_eq_one]
    have h_prime_29 : Nat.Prime 29 := by norm_num
    rw [← Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd h_prime_29]
    rw [Nat.dvd_iff_mod_eq_zero]
    have h_mod_val : 900 % 29 = 1 := by norm_num
    rw [h_mod_val]
    norm_num
  have subprob_a_num_is_29_proof : a.num = 29 := by
    mkOpaque
    rw [subprob_a_rat_is_29_900_proof]
    have h900_ne_zero_nat : (900 : ℕ) ≠ 0 := by norm_num
    change Rat.num ((Nat.cast 29 : ℚ) / (Nat.cast 900 : ℚ)) = (29 : ℤ)
    rw [Rat.natCast_div_eq_divInt (29 : ℕ) (900 : ℕ)]
    unfold Rat.divInt
    dsimp only
    change Rat.num (mkRat (29 : ℤ) (900 : ℕ)) = (29 : ℤ)
    unfold mkRat
    rw [dif_neg h900_ne_zero_nat]
    have h_norm_eq : (Rat.normalize (29 : ℤ) (900 : ℕ) h900_ne_zero_nat).num = (29 : ℤ) / ↑(Nat.gcd (Int.natAbs (29 : ℤ)) (900 : ℕ)) := by rfl
    rw [h_norm_eq]
    have hg : Nat.gcd (Int.natAbs (29 : ℤ)) (900 : ℕ) = 1 := by simp
    rw [hg]
    rw [Nat.cast_one]
    simp
  have subprob_a_den_is_900_proof : a.den = 900 := by
    mkOpaque
    have h_a_eq_div : a = (29 : ℚ) / (900 : ℚ) := subprob_a_rat_is_29_900_proof
    have h_div_as_mk : (29 : ℚ) / (900 : ℚ) = Rat.divInt (↑29 : ℤ) (↑900 : ℤ) := by
      rw [Rat.divInt_eq_div]
      rfl
    rw [h_div_as_mk] at h_a_eq_div
    have h_900_pos : (↑900 : ℤ) > 0 := by
      apply Int.coe_nat_pos.mpr
      exact Nat.zero_lt_of_lt (by norm_num : (0 : ℕ) < 900)
    have h_nat_coprime : Nat.Coprime 29 900 := subprob_coprime_29_900_proof
    have h_int_coprime : IsCoprime (↑29 : ℤ) (↑900 : ℤ) := Nat.Coprime.isCoprime h_nat_coprime
    have h_num_den_eq : ((Rat.divInt (Nat.cast 29 : ℤ) (Nat.cast 900 : ℤ)).num = (Nat.cast 29 : ℤ) ∧ (Rat.divInt (Nat.cast 29 : ℤ) (Nat.cast 900 : ℤ)).den = Int.natAbs (Nat.cast 900 : ℤ)) := by
      apply And.intro
      · rw [Rat.divInt_eq_div]
        apply Rat.num_div_eq_of_coprime
        · exact h_900_pos
        · simp only [Int.natAbs_ofNat]
          exact h_nat_coprime
      · rw [Rat.divInt_eq_div]
        rw [← Nat.cast_inj (R := ℤ)]
        simp only [Int.natAbs_ofNat]
        apply Rat.den_div_eq_of_coprime
        · exact h_900_pos
        · simp only [Int.natAbs_ofNat]
          exact h_nat_coprime
    have h_den_val : (Rat.divInt (↑29 : ℤ) (↑900 : ℤ)).den = Int.natAbs (↑900 : ℤ) := h_num_den_eq.right
    rw [h_a_eq_div, h_den_val]
    rfl
  have subprob_target_calc_proof : ↑(a.den) + a.num = ↑(900 : ℕ) + (29 : ℤ) := by
    mkOpaque
    rw [subprob_a_den_is_900_proof]
    rw [subprob_a_num_is_29_proof]
  have subprob_final_value_proof : ↑(900 : ℕ) + (29 : ℤ) = (929 : ℤ) := by
    mkOpaque
    norm_num
  exact
    show ↑a.den + a.num = 929 by
      mkOpaque
      rw [subprob_target_calc_proof]
      exact subprob_final_value_proof

#print axioms amc12a_2020_p25

/-Sketch
variable (a : ℚ) (S : Finset ℝ) (h₀ : ∀ (x : ℝ), x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2) (h₁ : ∑ k in S, k = 420)
play
  a_real := ↑a

  subprob_a_num_pos_assumption :≡ a.num > 0
  subprob_a_num_pos_assumption_proof ⇐ show subprob_a_num_pos_assumption by sorry
  subprob_a_den_pos_assumption :≡ a.den > 0
  subprob_a_den_pos_assumption_proof ⇐ show subprob_a_den_pos_assumption by sorry

  subprob_a_real_pos :≡ a_real > (0 : ℝ)
  subprob_a_real_pos_proof ⇐ show subprob_a_real_pos by sorry

  subprob_zero_in_S :≡ (0 : ℝ) ∈ S
  subprob_zero_in_S_proof ⇐ show subprob_zero_in_S by sorry

  suppose (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ 0) then
    w_int_x := ⌊x⌋
    f_real_x := x - ↑(⌊x⌋)
    w_real_x := ↑(⌊x⌋)

    subprob_wf_eq_ax2 :≡ w_real_x * f_real_x = a_real * x ^ 2
    subprob_wf_eq_ax2_proof ⇐ show subprob_wf_eq_ax2 by sorry

    subprob_ax2_pos :≡ a_real * x ^ 2 > (0:ℝ)
    subprob_ax2_pos_proof ⇐ show subprob_ax2_pos by sorry

    subprob_wf_pos :≡ w_real_x * f_real_x > (0:ℝ)
    subprob_wf_pos_proof ⇐ show subprob_wf_pos by sorry

    subprob_f_real_x_bounds :≡ (0 : ℝ) ≤ f_real_x ∧ f_real_x < (1 : ℝ)
    subprob_f_real_x_bounds_proof ⇐ show subprob_f_real_x_bounds by sorry

    subprob_f_real_x_ne_zero :≡ f_real_x ≠ (0:ℝ)
    subprob_f_real_x_ne_zero_proof ⇐ show subprob_f_real_x_ne_zero by sorry
    subprob_f_real_x_pos :≡ f_real_x > (0:ℝ)
    subprob_f_real_x_pos_proof ⇐ show subprob_f_real_x_pos by sorry

    subprob_w_real_x_pos :≡ w_real_x > (0:ℝ)
    subprob_w_real_x_pos_proof ⇐ show subprob_w_real_x_pos by sorry
    subprob_w_int_x_ge_1 :≡ w_int_x ≥ 1
    subprob_w_int_x_ge_1_proof ⇐ show subprob_w_int_x_ge_1 by sorry

    subprob_quadratic_in_f :≡ a_real * f_real_x ^ 2 + ((2:ℝ)*a_real - (1:ℝ))*w_real_x*f_real_x + a_real*w_real_x ^ 2 = (0:ℝ)
    subprob_quadratic_in_f_proof ⇐ show subprob_quadratic_in_f by sorry

    discriminant_val := w_real_x ^ 2 * ((1:ℝ) - (4:ℝ)*a_real)
    subprob_discriminant_val_nonneg :≡ discriminant_val ≥ (0:ℝ)
    subprob_discriminant_val_nonneg_proof ⇐ show subprob_discriminant_val_nonneg by sorry

    subprob_a_real_le_one_quarter :≡ a_real ≤ (1:ℝ)/(4:ℝ)
    subprob_a_real_le_one_quarter_proof ⇐ show subprob_a_real_le_one_quarter by sorry

    k_expr_fn_of_a := fun (cur_a_real : ℝ) => (((1:ℝ) - (2:ℝ)*cur_a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*cur_a_real)) / ((2:ℝ)*cur_a_real)
    k_val_for_x := k_expr_fn_of_a a_real

    subprob_f_eq_w_k :≡ f_real_x = w_real_x * k_val_for_x
    subprob_f_eq_w_k_proof ⇐ show subprob_f_eq_w_k by sorry
    subprob_k_val_for_x_pos :≡ k_val_for_x > (0:ℝ)
    subprob_k_val_for_x_pos_proof ⇐ show subprob_k_val_for_x_pos by sorry

  k_actual := (((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)) / ((2:ℝ)*a_real)
  subprob_k_actual_pos :≡ k_actual > (0:ℝ)
  subprob_k_actual_pos_proof ⇐ show subprob_k_actual_pos by sorry

  W_actual := Nat.ceil ((1:ℝ)/k_actual) - 1

  subprob_S_elements_form :≡ S = Finset.image (fun (w_nat : ℕ) => (↑w_nat : ℝ) * ((1:ℝ) + k_actual)) (Finset.Icc 1 W_actual) ∪ {(0:ℝ)}
  subprob_S_elements_form_proof ⇐ show subprob_S_elements_form by sorry

  subprob_sum_eq_420_expanded :≡ (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ) * ((1:ℝ) + k_actual)) = (420:ℝ)
  subprob_sum_eq_420_expanded_proof ⇐ show subprob_sum_eq_420_expanded by sorry

  subprob_sum_rewritten :≡ ((1:ℝ) + k_actual) * (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (420:ℝ)
  subprob_sum_rewritten_proof ⇐ show subprob_sum_rewritten by sorry
  subprob_sum_arith_series :≡ (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (↑W_actual : ℝ) * (↑W_actual + (1:ℕ)) / (2:ℝ)
  subprob_sum_arith_series_proof ⇐ show subprob_sum_arith_series by sorry
  subprob_main_eq_W_k :≡ ((1:ℝ) + k_actual) * ((↑W_actual : ℝ) * (↑W_actual + (1:ℕ)) / (2:ℝ)) = (420:ℝ)
  subprob_main_eq_W_k_proof ⇐ show subprob_main_eq_W_k by sorry

  subprob_W_actual_ge_1 :≡ W_actual ≥ 1
  subprob_W_actual_ge_1_proof ⇐ show subprob_W_actual_ge_1 by sorry
  subprob_W_bounds_from_def :≡ ((↑W_actual + (1:ℕ) : ℝ)⁻¹ ≤ k_actual ∧ k_actual < ((↑W_actual) : ℝ)⁻¹)
  subprob_W_bounds_from_def_proof ⇐ show subprob_W_bounds_from_def by sorry

  subprob_W_actual_is_28 :≡ W_actual = 28
  subprob_W_actual_is_28_proof ⇐ show subprob_W_actual_is_28 by sorry
  subprob_k_actual_is_1_29 :≡ k_actual = (1:ℝ)/(29:ℝ)
  subprob_k_actual_is_1_29_proof ⇐ show subprob_k_actual_is_1_29 by sorry

  subprob_a_solve1 :≡ (1:ℝ)/(29:ℝ) = (((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)) / ((2:ℝ)*a_real)
  subprob_a_solve1_proof ⇐ show subprob_a_solve1 by sorry
  subprob_a_solve2 :≡ ((2:ℝ)*a_real)/(29:ℝ) = ((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)
  subprob_a_solve2_proof ⇐ show subprob_a_solve2 by sorry
  subprob_a_solve3 :≡ Real.sqrt ((1:ℝ) - (4:ℝ)*a_real) = ((1:ℝ) - (2:ℝ)*a_real) - ((2:ℝ)*a_real)/(29:ℝ)
  subprob_a_solve3_proof ⇐ show subprob_a_solve3 by sorry
  subprob_a_solve4 :≡ Real.sqrt ((1:ℝ) - (4:ℝ)*a_real) = (1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real
  subprob_a_solve4_proof ⇐ show subprob_a_solve4 by sorry

  subprob_rhs_nonneg_for_squaring :≡ (1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real ≥ (0:ℝ)
  subprob_rhs_nonneg_for_squaring_proof ⇐ show subprob_rhs_nonneg_for_squaring by sorry

  subprob_a_solve5 :≡ (1:ℝ) - (4:ℝ)*a_real = ((1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real) ^ 2
  subprob_a_solve5_proof ⇐ show subprob_a_solve5 by sorry
  subprob_a_solve6 :≡ (1:ℝ) - (4:ℝ)*a_real = (1:ℝ) - (2:ℝ)*((60:ℝ)/(29:ℝ))*a_real + (((60:ℝ)/(29:ℝ))*a_real) ^ 2
  subprob_a_solve6_proof ⇐ show subprob_a_solve6 by sorry
  subprob_a_solve7 :≡ -(4:ℝ)*a_real = -((120:ℝ)/(29:ℝ))*a_real + (((3600:ℝ)/((29:ℝ)^2)))*a_real ^ 2
  subprob_a_solve7_proof ⇐ show subprob_a_solve7 by sorry

  subprob_a_solve8 :≡ -(4:ℝ) = -((120:ℝ)/(29:ℝ)) + (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve8_proof ⇐ show subprob_a_solve8 by sorry
  subprob_a_solve9 :≡ ((120:ℝ)/(29:ℝ)) - (4:ℝ) = (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve9_proof ⇐ show subprob_a_solve9 by sorry
  subprob_a_solve10 :≡ (4:ℝ)/(29:ℝ) = (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve10_proof ⇐ show subprob_a_solve10 by sorry
  subprob_a_solve11 :≡ a_real = ((4:ℝ)/(29:ℝ)) * (((29:ℝ)^2)/((3600:ℝ)))
  subprob_a_solve11_proof ⇐ show subprob_a_solve11 by sorry
  subprob_a_real_is_29_900 :≡ a_real = (29:ℝ)/(900:ℝ)
  subprob_a_real_is_29_900_proof ⇐ show subprob_a_real_is_29_900 by sorry

  subprob_a_rat_is_29_900 :≡ a = (29:ℚ)/(900:ℚ)
  subprob_a_rat_is_29_900_proof ⇐ show subprob_a_rat_is_29_900 by sorry

  subprob_coprime_29_900 :≡ Nat.Coprime 29 900
  subprob_coprime_29_900_proof ⇐ show subprob_coprime_29_900 by sorry

  subprob_a_num_is_29 :≡ a.num = 29
  subprob_a_num_is_29_proof ⇐ show subprob_a_num_is_29 by sorry
  subprob_a_den_is_900 :≡ a.den = 900
  subprob_a_den_is_900_proof ⇐ show subprob_a_den_is_900 by sorry

  subprob_target_calc :≡ ↑(a.den) + a.num = ↑(900 : ℕ) + (29 : ℤ)
  subprob_target_calc_proof ⇐ show subprob_target_calc by sorry
  subprob_final_value :≡ ↑(900 : ℕ) + (29 : ℤ) = (929 : ℤ)
  subprob_final_value_proof ⇐ show subprob_final_value by sorry

  subprob_final_goal :≡ ↑a.den + a.num = 929
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
variable (a : ℚ) (S : Finset ℝ) (h₀ : ∀ (x : ℝ), x ∈ S ↔ ↑⌊x⌋ * (x - ↑⌊x⌋) = ↑a * x ^ 2) (h₁ : ∑ k in S, k = 420)
play
  a_real := ↑a

  subprob_a_num_pos_assumption :≡ a.num > 0
  subprob_a_num_pos_assumption_proof ⇐ show subprob_a_num_pos_assumption by

    have ha_ne_zero : a ≠ 0 := by
      intro ha_eq_zero
      let M := {x : ℝ | (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑(0:ℚ) : ℝ) * x ^ (2 : ℕ)}
      have M_infinite : M.Infinite := by
        have M_contains_all_integers : Set.range (Int.cast : ℤ → ℝ) ⊆ M := by
          intro x hx_in_range
          simp only [Set.mem_range] at hx_in_range
          rcases hx_in_range with ⟨n, rfl⟩
          simp only [M, Set.mem_setOf_eq, Int.floor_intCast, sub_self, mul_zero, Rat.cast_zero, zero_mul]
        apply Set.Infinite.mono M_contains_all_integers
        apply (Set.infinite_range_iff Int.cast_injective).mpr
        exact Int.infinite
      have S_toSet_eq_M : (S : Set ℝ) = M := by
        ext x
        specialize h₀ x
        rw [ha_eq_zero] at h₀
        simp only [Rat.cast_zero, zero_mul] at h₀
        simp only [Finset.mem_coe, M, Set.mem_setOf_eq, Rat.cast_zero, zero_mul]
        exact h₀
      rw [← S_toSet_eq_M] at M_infinite
      apply M_infinite
      exact Finset.finite_toSet S

    have ha_not_neg : ¬ (a < 0) := by
      intro ha_neg
      have all_elements_le_zero : ∀ x ∈ S, x ≤ 0 := by
        intro x hxS
        by_cases hx_eq_zero : x = 0
        . rw [hx_eq_zero]
        .
          have h_prop := (h₀ x).mp hxS
          have ax2_neg_cond : ↑a * x ^ 2 < 0 := by
            refine mul_neg_of_neg_of_pos ?_ (sq_pos_of_ne_zero hx_eq_zero)
            exact_mod_cast ha_neg

          have floor_times_raw_fract_neg : ↑(⌊x⌋) * (x - ↑(⌊x⌋)) < 0 := by
            rw [h_prop]
            exact ax2_neg_cond

          have floor_mul_fract_neg : (↑(⌊x⌋) : ℝ) * Int.fract x < 0 := by
            rw [eq_sub_of_add_eq (Int.fract_add_floor x)]
            exact floor_times_raw_fract_neg

          have fract_x_pos : Int.fract x > 0 := by
            apply lt_of_le_of_ne (Int.fract_nonneg x)
            intro h_fract_eq_zero
            have h_lhs_eq_zero : (↑(⌊x⌋) : ℝ) * Int.fract x = (↑(⌊x⌋) : ℝ) * 0 := by rw [h_fract_eq_zero]
            have h_rhs_is_zero : (↑(⌊x⌋) : ℝ) * 0 = 0 := by simp only [mul_zero]
            have h_zero_lt_zero : (0 : ℝ) < 0 := (h_lhs_eq_zero.trans h_rhs_is_zero) ▸ floor_mul_fract_neg
            linarith [h_zero_lt_zero]

          have h_floor_real_neg : ↑(⌊x⌋) < 0 := by
            rcases mul_neg_iff.mp floor_mul_fract_neg with (⟨h_floor_lt_0, _⟩ | ⟨actual_floor_neg, h_fract_lt_0⟩)
            . exfalso; linarith [fract_x_pos]
            .
              exact (Int.cast_lt_zero.mp actual_floor_neg)

          have h_floor_int_neg : ⌊x⌋ < 0 := Int.cast_lt_zero.mp h_floor_real_neg
          have h_floor_le_minus_one : ⌊x⌋ ≤ -1 := Int.le_sub_one_of_lt h_floor_int_neg

          apply le_of_lt
          have h_step1 : x = (↑(⌊x⌋) : ℝ) + Int.fract x := by rw [Int.floor_add_fract x]
          have h_step2 : (↑(⌊x⌋) : ℝ) + Int.fract x < (↑(⌊x⌋) : ℝ) + 1 := by
            apply (Real.add_lt_add_iff_left ((↑(⌊x⌋)) : ℝ)).mpr
            exact Int.fract_lt_one x
          have h_step3 : (↑(⌊x⌋) : ℝ) + 1 ≤ (↑(-1 : ℤ) : ℝ) + 1 := by
            simp only [add_le_add_iff_right, Int.cast_le]; exact h_floor_le_minus_one
          have h_step4 : (↑(-1 : ℤ) : ℝ) + 1 = 0 := by simp
          rw [h_step1]
          linarith [h_step2, h_step3, h_step4]

      have sum_S_le_zero : ∑ k ∈ S, k ≤ 0 := Finset.sum_nonpos all_elements_le_zero
      rw [h₁] at sum_S_le_zero
      linarith
    rcases lt_trichotomy a (0:ℚ) with h_lt | h_eq | h_gt
    .
      contradiction
    .
      exact (ha_ne_zero h_eq).elim
    .
      exact Rat.num_pos_iff_pos.mpr h_gt

  subprob_a_den_pos_assumption :≡ a.den > 0
  subprob_a_den_pos_assumption_proof ⇐ show subprob_a_den_pos_assumption by






    apply Rat.den_pos

  subprob_a_real_pos :≡ a_real > (0 : ℝ)
  subprob_a_real_pos_proof ⇐ show subprob_a_real_pos by





    rw [a_real_def]

    apply Rat.cast_pos.mpr

    rw [← Rat.num_pos]

    exact subprob_a_num_pos_assumption_proof


  subprob_zero_in_S :≡ (0 : ℝ) ∈ S
  subprob_zero_in_S_proof ⇐ show subprob_zero_in_S by


    rw [h₀]

    have lhs_eq_zero : (↑(⌊(0:ℝ)⌋) : ℝ) * (0 - ↑(⌊(0:ℝ)⌋)) = 0 := by
      simp only [Int.floor_zero, Int.cast_zero, sub_self, mul_zero]

    have rhs_eq_zero : (↑(a) : ℝ) * (0 : ℝ) ^ (2 : ℕ) = 0 := by
      have h_zero_pow_two : (0 : ℝ) ^ (2 : ℕ) = 0 := by
        apply zero_pow
        norm_num
      simp only [h_zero_pow_two, mul_zero]

    rw [lhs_eq_zero, rhs_eq_zero]


  suppose (x : ℝ) (hxS : x ∈ S) (hxne0 : x ≠ 0) then
    w_int_x := ⌊x⌋
    f_real_x := x - ↑(⌊x⌋)
    w_real_x := ↑(⌊x⌋)

    subprob_wf_eq_ax2 :≡ w_real_x * f_real_x = a_real * x ^ 2
    subprob_wf_eq_ax2_proof ⇐ show subprob_wf_eq_ax2 by

      have h_equality_from_h0 : (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑a : ℝ) * x ^ 2 := by
        apply (h₀ x).mp
        exact hxS

      rw [w_real_x_def]

      rw [f_real_x_def]

      rw [a_real_def]

      exact h_equality_from_h0

    subprob_ax2_pos :≡ a_real * x ^ 2 > (0:ℝ)
    subprob_ax2_pos_proof ⇐ show subprob_ax2_pos by



      have h_x_sq_pos : x ^ (2 : ℕ) > 0 := by
        apply sq_pos_of_ne_zero
        exact hxne0

      apply mul_pos
      . exact subprob_a_real_pos_proof
      . exact h_x_sq_pos


    subprob_wf_pos :≡ w_real_x * f_real_x > (0:ℝ)
    subprob_wf_pos_proof ⇐ show subprob_wf_pos by

      rw [subprob_wf_eq_ax2_proof]
      exact subprob_ax2_pos_proof

    subprob_f_real_x_bounds :≡ (0 : ℝ) ≤ f_real_x ∧ f_real_x < (1 : ℝ)
    subprob_f_real_x_bounds_proof ⇐ show subprob_f_real_x_bounds by



      rw [f_real_x_def]

      change (0 : ℝ) ≤ Int.fract x ∧ Int.fract x < (1 : ℝ)

      apply And.intro

      .
        apply Int.fract_nonneg

      .
        apply Int.fract_lt_one


    subprob_f_real_x_ne_zero :≡ f_real_x ≠ (0:ℝ)
    subprob_f_real_x_ne_zero_proof ⇐ show subprob_f_real_x_ne_zero by
      intro h_f_real_x_eq_zero
      have h_prod_gt_zero : (↑w_real_x : ℝ) * f_real_x > (0 : ℝ) := subprob_wf_pos_proof
      rw [h_f_real_x_eq_zero] at h_prod_gt_zero
      simp only [mul_zero] at h_prod_gt_zero
      exact lt_irrefl (0 : ℝ) h_prod_gt_zero
    subprob_f_real_x_pos :≡ f_real_x > (0:ℝ)
    subprob_f_real_x_pos_proof ⇐ show subprob_f_real_x_pos by



      apply lt_of_le_of_ne'
      · exact subprob_f_real_x_bounds_proof.left
      · exact subprob_f_real_x_ne_zero_proof


    subprob_w_real_x_pos :≡ w_real_x > (0:ℝ)
    subprob_w_real_x_pos_proof ⇐ show subprob_w_real_x_pos by












      have h_main_ineq : (↑w_real_x : ℝ) * f_real_x > (0 : ℝ) * f_real_x := by
        rw [zero_mul f_real_x]
        exact subprob_wf_pos_proof

      exact (mul_lt_mul_iff_of_pos_right subprob_f_real_x_pos_proof).mp h_main_ineq

    subprob_w_int_x_ge_1 :≡ w_int_x ≥ 1
    subprob_w_int_x_ge_1_proof ⇐ show subprob_w_int_x_ge_1 by




      have h_w_eq : w_real_x = w_int_x := by
        rw [w_real_x_def]
        rw [w_int_x_def]

      have h_w_int_x_cast_pos : (↑(w_int_x) : ℝ) > (0 : ℝ) := by
        rw [← h_w_eq]
        exact subprob_w_real_x_pos_proof

      have h_w_int_x_pos : 0 < w_int_x :=
        Int.cast_pos.mp h_w_int_x_cast_pos

      apply (Int.pos_iff_one_le).mp
      exact h_w_int_x_pos


    subprob_quadratic_in_f :≡ a_real * f_real_x ^ 2 + ((2:ℝ)*a_real - (1:ℝ))*w_real_x*f_real_x + a_real*w_real_x ^ 2 = (0:ℝ)
    subprob_quadratic_in_f_proof ⇐ show subprob_quadratic_in_f by
      have h_f_real_x_is_sub : f_real_x = x - ↑w_real_x := by
        rw [f_real_x_def, w_real_x_def]
      have h_sum_eq_x : f_real_x + (↑w_real_x : ℝ) = x := by
        rw [h_f_real_x_is_sub, sub_add_cancel]
      have h_lhs_transformed : (↑a_real : ℝ) * f_real_x ^ 2 + ((2 : ℝ) * ↑a_real - (1 : ℝ)) * (↑w_real_x : ℝ) * f_real_x + (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ 2 = (↑a_real : ℝ) * (f_real_x + ↑w_real_x)^2 - (↑w_real_x : ℝ) * f_real_x := by
        ring
      rw [h_lhs_transformed]
      rw [h_sum_eq_x]
      rw [subprob_wf_eq_ax2_proof]
      simp

    discriminant_val := w_real_x ^ 2 * ((1:ℝ) - (4:ℝ)*a_real)
    subprob_discriminant_val_nonneg :≡ discriminant_val ≥ (0:ℝ)
    subprob_discriminant_val_nonneg_proof ⇐ show subprob_discriminant_val_nonneg by














      let A_coeff := (↑a_real : ℝ)
      let B_coeff := ((2 : ℝ) * (↑a_real : ℝ) - (1 : ℝ)) * (↑w_real_x : ℝ)
      let C_coeff := (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ (2 : ℕ)

      have h_quadratic_eq : A_coeff * f_real_x ^ (2 : ℕ) + B_coeff * f_real_x + C_coeff = 0 := by
        exact subprob_quadratic_in_f_proof

      have hA_ne_zero : A_coeff ≠ 0 := by
        linarith [subprob_a_real_pos_proof]

      have h_disc_ge_zero : B_coeff ^ 2 - 4 * A_coeff * C_coeff ≥ 0 := by
        have h_quadratic_eq_for_thm : A_coeff * f_real_x * f_real_x + B_coeff * f_real_x + C_coeff = 0 := by
          rw [mul_assoc]
          rw [← pow_two f_real_x]
          exact h_quadratic_eq

        have h_disc_is_sq : discrim A_coeff B_coeff C_coeff = ((2 : ℝ) * A_coeff * f_real_x + B_coeff) ^ (2 : ℕ) :=
          discrim_eq_sq_of_quadratic_eq_zero h_quadratic_eq_for_thm
        change (discrim A_coeff B_coeff C_coeff ≥ (0 : ℝ))
        rw [h_disc_is_sq]
        apply sq_nonneg ((2 : ℝ) * A_coeff * f_real_x + B_coeff)

      have h_calc_discr : B_coeff ^ 2 - 4 * A_coeff * C_coeff = (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) := by
        simp only [A_coeff, B_coeff, C_coeff]
        ring

      rw [h_calc_discr] at h_disc_ge_zero

      rw [discriminant_val_def]
      exact h_disc_ge_zero



    subprob_a_real_le_one_quarter :≡ a_real ≤ (1:ℝ)/(4:ℝ)
    subprob_a_real_le_one_quarter_proof ⇐ show subprob_a_real_le_one_quarter by






      have h_disc_formula_nonneg : (↑(w_real_x) : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ)) ≥ (0 : ℝ) := by
        rw [← discriminant_val_def]
        exact subprob_discriminant_val_nonneg_proof

      have h_w_real_x_sq_pos : (↑(w_real_x) : ℝ) ^ (2 : ℕ) > (0 : ℝ) := by
        exact pow_pos subprob_w_real_x_pos_proof (2 : ℕ)

      have h_factor_nonneg : (1 : ℝ) - (4 : ℝ) * (↑(a_real) : ℝ) ≥ (0 : ℝ) := by
        exact nonneg_of_mul_nonneg_left (by {rw [mul_comm]; exact h_disc_formula_nonneg}) h_w_real_x_sq_pos

      have h_one_ge_four_a : (1 : ℝ) ≥ (4 : ℝ) * (↑(a_real) : ℝ) := by
        exact sub_nonneg.mp h_factor_nonneg

      have four_pos : (4 : ℝ) > 0 := by
        norm_num

      have h_a_mul_four_le_one : (↑(a_real) : ℝ) * (4 : ℝ) ≤ (1 : ℝ) := by
        rw [mul_comm]
        exact h_one_ge_four_a

      rw [(le_div_iff' four_pos)]
      rw [mul_comm]
      exact h_a_mul_four_le_one


    k_expr_fn_of_a := fun (cur_a_real : ℝ) => (((1:ℝ) - (2:ℝ)*cur_a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*cur_a_real)) / ((2:ℝ)*cur_a_real)
    k_val_for_x := k_expr_fn_of_a a_real

    subprob_f_eq_w_k :≡ f_real_x = w_real_x * k_val_for_x
    subprob_f_eq_w_k_proof ⇐ show subprob_f_eq_w_k by





















      let A_coeff := (↑a_real : ℝ)
      let B_coeff := ((2 : ℝ) * (↑a_real : ℝ) - (1 : ℝ)) * (↑w_real_x : ℝ)
      let C_coeff := (↑a_real : ℝ) * (↑w_real_x : ℝ) ^ (2 : ℕ)

      have h_quadratic_eq : A_coeff * f_real_x * f_real_x + B_coeff * f_real_x + C_coeff = 0 := by
        rw [mul_assoc A_coeff f_real_x f_real_x]
        rw [← pow_two f_real_x]
        simp [A_coeff, B_coeff, C_coeff, subprob_quadratic_in_f_proof]

      have hA_coeff_ne_zero : A_coeff ≠ 0 := by
        linarith [subprob_a_real_pos_proof]

      have h_discrim_formula_eq_discriminant_val : B_coeff ^ 2 - 4 * A_coeff * C_coeff = discriminant_val := by
        simp only [A_coeff, B_coeff, C_coeff, discriminant_val_def]
        ring

      have h_discrim_eq_sqrt_sq : discrim A_coeff B_coeff C_coeff = (Real.sqrt discriminant_val) * (Real.sqrt discriminant_val) := by
        rw [discrim]
        rw [h_discrim_formula_eq_discriminant_val]
        exact (Real.mul_self_sqrt subprob_discriminant_val_nonneg_proof).symm

      have h_solutions := (quadratic_eq_zero_iff hA_coeff_ne_zero h_discrim_eq_sqrt_sq f_real_x).mp h_quadratic_eq

      have h_sqrt_discriminant_val_expr : Real.sqrt discriminant_val = (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ)) := by
        rw [discriminant_val_def]
        have hw_real_x_nonneg : (↑w_real_x : ℝ) ≥ 0 := by
          linarith [subprob_w_real_x_pos_proof]
        have h_term_nonneg : (1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ) ≥ 0 := by
          have h := subprob_a_real_le_one_quarter_proof
          linarith
        have h_sqrt_mul_eq : Real.sqrt ((↑w_real_x : ℝ) ^ (2 : ℕ) * ((1 : ℝ) - (4 : ℝ) * ↑a_real)) = Real.sqrt ((↑w_real_x : ℝ) ^ (2 : ℕ)) * Real.sqrt ((1 : ℝ) - (4 : ℝ) * ↑a_real) := by
          apply Real.sqrt_mul
          exact sq_nonneg (↑w_real_x : ℝ)
        rw [h_sqrt_mul_eq]
        rw [Real.sqrt_sq_eq_abs]
        rw [_root_.abs_of_nonneg hw_real_x_nonneg]

      rw [h_sqrt_discriminant_val_expr] at h_solutions

      let sol1 := (-B_coeff + (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * A_coeff)
      let sol2 := (-B_coeff - (↑w_real_x : ℝ) * Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * A_coeff)

      have h_sol2_eq_target : sol2 = (↑w_real_x : ℝ) * k_val_for_x := by
        simp only [sol2, B_coeff, A_coeff, k_val_for_x_def, k_expr_fn_of_a_def]
        have h_denom_ne_zero : (2 : ℝ) * (↑a_real : ℝ) ≠ 0 := by
          have h_denom_pos : (2 : ℝ) * (↑a_real : ℝ) > 0 := mul_pos (by norm_num) subprob_a_real_pos_proof
          exact ne_of_gt h_denom_pos
        field_simp [h_denom_ne_zero]
        ring

      have h_a_real_lt_one_quarter : (↑a_real : ℝ) < 1/4 := by
        apply lt_of_le_of_ne subprob_a_real_le_one_quarter_proof
        intro h_a_real_eq_one_quarter
        have h_discriminant_zero : discriminant_val = 0 := by
          rw [discriminant_val_def, h_a_real_eq_one_quarter]
          norm_num
        have h_sqrt_discriminant_zero : Real.sqrt discriminant_val = 0 := by
          rw [h_discriminant_zero]
          simp
        have h_f_real_x_is_unique_sol : f_real_x = -B_coeff / (2 * A_coeff) := by
          have h_sqrt_term_zero_if_a_eq_one_quarter : Real.sqrt (1 - 4 * (↑a_real : ℝ)) = 0 := by
            rw [h_a_real_eq_one_quarter]
            norm_num
          rw [h_sqrt_term_zero_if_a_eq_one_quarter] at h_solutions
          simp only [mul_zero, add_zero, sub_zero, or_self] at h_solutions
          exact h_solutions
        have h_f_real_x_val_if_a_eq_one_quarter : f_real_x = (↑w_real_x : ℝ) := by
          rw [h_f_real_x_is_unique_sol]
          simp only [B_coeff, A_coeff, h_a_real_eq_one_quarter]
          field_simp [show (2 : ℝ) * (1 / 4 : ℝ) ≠ 0 by norm_num]
          ring
        have h_f_lt_1 := subprob_f_real_x_bounds_proof.2
        rw [h_f_real_x_val_if_a_eq_one_quarter] at h_f_lt_1
        have h_w_int_eq_w_real : w_int_x = w_real_x := by rw [w_int_x_def, w_real_x_def]
        have h_w_real_x_ge_1 : (↑w_real_x : ℝ) ≥ 1 := by
          rw [← h_w_int_eq_w_real]
          rw [ge_iff_le]
          rw [← Int.cast_one]
          exact (Int.cast_le (R := ℝ)).mpr subprob_w_int_x_ge_1_proof
        linarith [h_f_lt_1, h_w_real_x_ge_1]

      have h_sqrt_term_pos : 1 - 4 * (↑a_real : ℝ) > 0 := by
        linarith [h_a_real_lt_one_quarter]
      have h_Real_sqrt_pos : Real.sqrt (1 - 4 * (↑a_real : ℝ)) > 0 := Real.sqrt_pos_of_pos h_sqrt_term_pos

      have h_sol1_form : sol1 = (↑w_real_x : ℝ) * (((1 - 2 * (↑a_real : ℝ)) + Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * (↑a_real : ℝ))) := by
        simp only [sol1, B_coeff, A_coeff]
        field_simp [_root_.ne_of_gt subprob_a_real_pos_proof]
        ring

      have h_k_plus_val_gt_1 : ((1 - 2 * (↑a_real : ℝ)) + Real.sqrt (1 - 4 * (↑a_real : ℝ))) / (2 * (↑a_real : ℝ)) > 1 := by
        have h_2a_pos : 2 * (↑a_real : ℝ) > 0 := by
          exact mul_pos (by norm_num) subprob_a_real_pos_proof
        apply (lt_div_iff' h_2a_pos).mpr
        rw [mul_one]
        have h_intermediate_goal : 1 + Real.sqrt (1 - 4 * (↑a_real : ℝ)) > 4 * (↑a_real : ℝ) := by
          set y_val := Real.sqrt (1 - 4 * (↑a_real : ℝ)) with hy_val_def

          have h_identity_for_4a : 4 * (↑a_real : ℝ) = 1 - y_val^2 := by
            rw [eq_comm]
            simp only [hy_val_def]
            rw [Real.sq_sqrt (le_of_lt h_sqrt_term_pos)]
            ring

          rw [h_identity_for_4a]

          have h_y_val_plus_y_val_sq_pos : y_val + y_val^2 > 0 := by
            have hy_val_pos : y_val > 0 := by
              rw [hy_val_def]
              exact h_Real_sqrt_pos
            have h_one_plus_y_val_pos : 1 + y_val > 0 := by
              linarith [hy_val_pos]
            have H_factor : y_val + y_val^2 = y_val * (1 + y_val) := by ring
            rw [H_factor]
            exact mul_pos hy_val_pos h_one_plus_y_val_pos

          linarith [h_y_val_plus_y_val_sq_pos]
        linarith [h_intermediate_goal]

      have h_w_real_x_ge_1 : (↑w_real_x : ℝ) ≥ 1 := by
        have h_w_int_eq_w_real : w_int_x = w_real_x := by rw [w_int_x_def, w_real_x_def]
        rw [← h_w_int_eq_w_real]
        rw [ge_iff_le]
        rw [← Int.cast_one]
        exact (Int.cast_le (R := ℝ)).mpr subprob_w_int_x_ge_1_proof

      have h_sol1_gt_1 : sol1 > 1 := by
        rw [h_sol1_form]
        apply one_lt_mul_of_le_of_lt h_w_real_x_ge_1 h_k_plus_val_gt_1

      have h_f_real_x_lt_1 : f_real_x < 1 := subprob_f_real_x_bounds_proof.2

      rcases h_solutions with h_f_eq_sol1 | h_f_eq_sol2
      .
        exfalso
        linarith [h_f_eq_sol1, h_sol1_gt_1, h_f_real_x_lt_1]
      .
        rw [h_f_eq_sol2]
        exact h_sol2_eq_target

    subprob_k_val_for_x_pos :≡ k_val_for_x > (0:ℝ)
    subprob_k_val_for_x_pos_proof ⇐ show subprob_k_val_for_x_pos by

      let h_f_pos := subprob_f_real_x_pos_proof
      let h_w_pos := subprob_w_real_x_pos_proof
      let h_eq := subprob_f_eq_w_k_proof

      have h_prod_pos : (↑w_real_x : ℝ) * k_val_for_x > 0 := by
        rw [←h_eq]
        exact h_f_pos


      exact (mul_pos_iff_of_pos_left h_w_pos).mp h_prod_pos

  k_actual := (((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)) / ((2:ℝ)*a_real)
  subprob_k_actual_pos :≡ k_actual > (0:ℝ)
  subprob_k_actual_pos_proof ⇐ show subprob_k_actual_pos by

    have h_exists_nonzero_in_S : ∃ x, x ∈ S ∧ x ≠ 0 := by
      by_contra! h_all_elements_in_S_are_zero
      have h_sum_is_zero : ∑ k in S, k = (0 : ℝ) := by
        apply Finset.sum_eq_zero
        exact h_all_elements_in_S_are_zero
      have h_420_eq_0 : (420 : ℝ) = (0 : ℝ) := by
        rw [← h₁]
        exact h_sum_is_zero
      norm_num at h_420_eq_0

    rcases h_exists_nonzero_in_S with ⟨x₀, hx₀S, hx₀ne0⟩

    rw [k_actual_def]
    rw [←k_expr_fn_of_a_def' x₀ hx₀S hx₀ne0 (↑a_real)]
    rw [←k_val_for_x_def' x₀ hx₀S hx₀ne0]
    exact subprob_k_val_for_x_pos_proof x₀ hx₀S hx₀ne0

  W_actual := Nat.ceil ((1:ℝ)/k_actual) - 1

  subprob_S_elements_form :≡ S = Finset.image (fun (w_nat : ℕ) => (↑w_nat : ℝ) * ((1:ℝ) + k_actual)) (Finset.Icc 1 W_actual) ∪ {(0:ℝ)}
  subprob_S_elements_form_proof ⇐ show subprob_S_elements_form by



    let T := Finset.image (fun (w_nat : ℕ) => (↑w_nat : ℝ) * ((1 : ℝ) + k_actual)) (Finset.Icc 1 W_actual) ∪ {(0 : ℝ)}
    apply Finset.ext_iff.mpr
    intro x
    constructor
    . intro hxS
      by_cases hx_eq_zero : x = 0
      . rw [hx_eq_zero]
        apply Finset.mem_union_right
        apply Finset.mem_singleton_self
      .
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        let w_int := w_int_x x hxS hx_eq_zero
        have hw_int_def : w_int = ⌊x⌋ := by simp [w_int, w_int_x_def]
        have hw_int_ge_1 : w_int ≥ 1 := subprob_w_int_x_ge_1_proof x hxS hx_eq_zero
        let w_nat := Int.toNat w_int
        have hw_nat_ge_1 : w_nat ≥ 1 := by
          apply Nat.one_le_iff_ne_zero.mpr
          change (Int.toNat w_int) ≠ 0
          change ¬(Int.toNat w_int = 0)
          rw [Int.toNat_eq_zero]
          rw [not_le]
          linarith [hw_int_ge_1]
        have cast_w_nat_eq_w_int : (↑w_nat : ℤ) = w_int := by
          exact (Int.toNat_of_nonneg (Int.le_trans (by norm_num) hw_int_ge_1))
        have cast_w_nat_eq_w_int_real : (↑w_nat : ℝ) = (↑w_int : ℝ) := by
          norm_cast

        let f_x := f_real_x x hxS hx_eq_zero
        have hf_x_def : f_x = x - ↑⌊x⌋ := by simp [f_x, f_real_x_def]
        rw [←hw_int_def] at hf_x_def
        rw [←cast_w_nat_eq_w_int_real] at hf_x_def
        have hw_real_x_def : w_real_x x hxS hx_eq_zero = ⌊x⌋ := by rw [w_real_x_def]
        rw [←hw_int_def] at hw_real_x_def
        have hf_eq_wk : f_x = (↑w_int : ℝ) * k_val_for_x x hxS hx_eq_zero := by
          simp [f_x, subprob_f_eq_w_k_proof x hxS hx_eq_zero, hw_real_x_def]
        rw [k_val_for_x_def'] at hf_eq_wk
        rw [k_expr_fn_of_a_def'] at hf_eq_wk
        rw [← k_actual_def] at hf_eq_wk
        rw [← cast_w_nat_eq_w_int_real] at hf_eq_wk

        have hx_expr : x = (↑w_nat : ℝ) * (1 + k_actual) := by
          have h_x_eq_fx_plus_wnat : x = f_x + (↑w_nat : ℝ) := by
            exact eq_add_of_sub_eq (Eq.symm hf_x_def)
          rw [h_x_eq_fx_plus_wnat]
          rw [hf_eq_wk]
          ring

        use w_nat
        constructor
        . rw [Finset.mem_Icc]
          apply And.intro
          . exact hw_nat_ge_1
          . rw [W_actual_def]
            have hM_ge_1 : 1 ≤ ⌈(1 : ℝ) / k_actual⌉₊ := by
              apply Nat.one_le_of_lt
              apply Nat.ceil_pos.mpr
              apply one_div_pos.mpr
              exact subprob_k_actual_pos_proof
            rw [Nat.le_sub_iff_add_le hM_ge_1]
            rw [Nat.succ_le_iff]
            have h_inv_k_pos : (1 : ℝ) / k_actual > 0 := one_div_pos.mpr subprob_k_actual_pos_proof
            apply (Nat.lt_ceil).mpr
            rw [lt_div_iff' subprob_k_actual_pos_proof]
            rw [mul_comm]
            rw [← hf_eq_wk]
            exact (subprob_f_real_x_bounds_proof x hxS hx_eq_zero).right
        . exact (Eq.symm hx_expr)
    . intro hyT
      rw [Finset.mem_union] at hyT
      cases hyT
      . rename_i hy_in_image
        rw [Finset.mem_image] at hy_in_image
        rcases hy_in_image with ⟨w_nat, hw_nat_interval, hy_expr⟩
        apply (h₀ x).mpr
        rw [←a_real_def]

        have hy_expanded : x = (↑w_nat : ℝ) + (↑w_nat : ℝ) * k_actual := by
          rw [←hy_expr]
          ring

        have h_w_nat_ge_1 : w_nat ≥ 1 := (Finset.mem_Icc.mp hw_nat_interval).left
        have h_w_nat_le_W : w_nat ≤ W_actual := (Finset.mem_Icc.mp hw_nat_interval).right

        have w_k_pos : (↑w_nat : ℝ) * k_actual > 0 := by
          apply mul_pos
          . apply Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_w_nat_ge_1)
          . exact subprob_k_actual_pos_proof

        have w_k_lt_1 : (↑w_nat : ℝ) * k_actual < 1 := by
          rw [W_actual_def] at h_w_nat_le_W
          have h_ceil_ge_one : 1 ≤ ⌈1 / k_actual⌉₊ := by
            apply Nat.one_le_of_lt
            apply Nat.ceil_pos.mpr
            apply one_div_pos.mpr
            exact subprob_k_actual_pos_proof
          have h_lt_ceil : w_nat < ⌈1 / k_actual⌉₊ := by
            rw [Nat.le_sub_iff_add_le h_ceil_ge_one] at h_w_nat_le_W
            rw [Nat.succ_le_iff] at h_w_nat_le_W
            exact h_w_nat_le_W
          have cast_w_nat_lt_inv_k : (↑w_nat : ℝ) < 1 / k_actual := by
            apply Nat.lt_ceil.mp
            exact h_lt_ceil
          rw [mul_comm]
          rw [← lt_div_iff' subprob_k_actual_pos_proof]
          exact cast_w_nat_lt_inv_k

        have h_floor_y : ⌊x⌋ = (w_nat : ℤ) := by
          rw [hy_expanded]
          apply Int.floor_eq_iff.mpr
          constructor
          .
            rw [Int.cast_natCast]
            rw [le_add_iff_nonneg_right]
            exact le_of_lt w_k_pos
          .
            rw [Int.cast_natCast w_nat]
            rw [Real.add_lt_add_iff_left (↑w_nat : ℝ)]
            exact w_k_lt_1

        have lhs_eq : (↑(⌊x⌋) : ℝ) * (x - (↑(⌊x⌋) : ℝ)) = (↑w_nat : ℝ)^2 * k_actual := by
          rw [h_floor_y, hy_expanded]
          simp only [Int.cast_natCast]
          ring
        rw [lhs_eq]

        have rhs_eq : (↑a_real : ℝ) * x^2 = (↑a_real : ℝ) * (↑w_nat : ℝ)^2 * (1 + k_actual)^2 := by
          rw [←hy_expr]
          ring
        rw [rhs_eq]

        have w_nat_sq_pos : (↑w_nat : ℝ)^2 > 0 := by
          apply sq_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_le_iff.mp h_w_nat_ge_1))

        rw [mul_comm (↑a_real : ℝ) ((↑w_nat : ℝ) ^ 2)]
        rw [mul_assoc ((↑w_nat : ℝ) ^ 2) (↑a_real : ℝ) (((1 : ℝ) + k_actual) ^ (2 :ℕ))]
        rw [mul_right_inj' (ne_of_gt w_nat_sq_pos)]

        have h_k_equation: (↑a_real : ℝ) * k_actual^2 + (2 * (↑a_real : ℝ) - 1) * k_actual + (↑a_real : ℝ) = 0 := by
          let A := (↑a_real : ℝ)
          have hA_pos : A > 0 := subprob_a_real_pos_proof
          have hA_ne_zero : A ≠ 0 := ne_of_gt hA_pos
          have h_sum_ne_zero : ∑ k in S, k ≠ 0 := by { rw [h₁]; norm_num }
          have exists_nonzero_elem : ∃ x_elem ∈ S, x_elem ≠ 0 := by {
            contrapose! h_sum_ne_zero;
            exact Finset.sum_eq_zero h_sum_ne_zero;
          }
          rcases exists_nonzero_elem with ⟨x_specific, hx_specific_S, hx_specific_ne0⟩
          have discriminant_prop := subprob_discriminant_val_nonneg_proof x_specific hx_specific_S hx_specific_ne0
          rw [discriminant_val_def'] at discriminant_prop
          have w_val_specific_pos : (↑(w_real_x x_specific hx_specific_S hx_specific_ne0) : ℝ) > 0 :=
            subprob_w_real_x_pos_proof x_specific hx_specific_S hx_specific_ne0
          have w_sq_pos_specific : (↑(w_real_x x_specific hx_specific_S hx_specific_ne0) : ℝ) ^ 2 > 0 :=
            pow_pos w_val_specific_pos 2
          have h_sqrt_term_nonneg : (1 : ℝ) - (4 : ℝ) * A ≥ 0 := nonneg_of_mul_nonneg_right discriminant_prop w_sq_pos_specific
          have h_k_eq_root : k_actual = ((1 - 2 * A - Real.sqrt (1 - 4 * A)) / (2 * A)) := k_actual_def
          rw [h_k_eq_root]
          field_simp [hA_ne_zero]
          ring_nf
          simp only [pow_two]
          have h_sqrt_term_target_nonneg : (1 : ℝ) - A * (4 : ℝ) ≥ 0 := by
            rw [mul_comm A (4 : ℝ)]
            exact h_sqrt_term_nonneg
          rw [Real.mul_self_sqrt h_sqrt_term_target_nonneg]
          ring
        rw [add_eq_zero_iff_eq_neg] at h_k_equation
        have h_target_rewrite: (↑a_real : ℝ) * (1 + k_actual) ^ 2 = (↑a_real : ℝ) + k_actual + ((↑a_real : ℝ) * k_actual ^ 2 + (2 * (↑a_real : ℝ) - 1) * k_actual) := by
          ring
        rw [h_target_rewrite]
        rw [h_k_equation]
        ring
      . rename_i hy_is_zero
        have hx_eq_zero_val : x = (0 : ℝ) := Finset.mem_singleton.mp hy_is_zero
        rw [hx_eq_zero_val]
        exact subprob_zero_in_S_proof


  subprob_sum_eq_420_expanded :≡ (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ) * ((1:ℝ) + k_actual)) = (420:ℝ)
  subprob_sum_eq_420_expanded_proof ⇐ show subprob_sum_eq_420_expanded by


    let g := fun (w_nat : ℕ) => (↑w_nat : ℝ) * (1 + k_actual)
    let S' := Finset.image g (Finset.Icc 1 W_actual)

    have h_zero_not_in_S' : (0 : ℝ) ∉ S' := by
      rw [Finset.mem_image]
      rintro ⟨w_nat, hw_nat_mem_Icc, h_g_w_nat_eq_zero⟩
      have h_w_nat_ge_one : 1 ≤ w_nat := by
        rw [Finset.mem_Icc] at hw_nat_mem_Icc
        exact hw_nat_mem_Icc.left
      have h_w_nat_cast_pos : (↑w_nat : ℝ) > 0 := by
        simp only [Nat.cast_pos]
        exact lt_of_lt_of_le Nat.zero_lt_one h_w_nat_ge_one
      have h_one_plus_k_actual_pos : (1 : ℝ) + k_actual > 0 := by
        linarith [subprob_k_actual_pos_proof]
      have h_g_w_nat_pos : g w_nat > 0 := by
        simp only [g]
        exact mul_pos h_w_nat_cast_pos h_one_plus_k_actual_pos
      linarith [h_g_w_nat_pos, h_g_w_nat_eq_zero]

    have h_S'_disjoint_singleton_zero : Disjoint S' {(0 : ℝ)} := by
      apply Finset.disjoint_singleton_right.mpr
      exact h_zero_not_in_S'

    have h_sum_S_expanded : ∑ k ∈ S, k = (∑ k ∈ S', k) + (∑ k ∈ {(0 : ℝ)}, k) := by
      rw [subprob_S_elements_form_proof]
      exact Finset.sum_union h_S'_disjoint_singleton_zero

    have h_sum_singleton_zero : ∑ k ∈ {(0 : ℝ)}, k = (0 : ℝ) := by
      simp

    let sum_S := ∑ k ∈ S, k
    let sum_S' := ∑ k ∈ S', k
    have h_sum_S_eq_sum_S' : sum_S = sum_S' := by
      simp only [sum_S]
      rw [h_sum_S_expanded]
      rw [h_sum_singleton_zero]
      rw [add_zero]

    have h_sum_S'_eq_420 : (∑ k ∈ S', k) = (420 : ℝ) := by
      change sum_S' = (420 : ℝ)
      rw [←h_sum_S_eq_sum_S']
      exact h₁

    have h_g_inj_on_Icc : Set.InjOn g (Finset.Icc 1 W_actual : Set ℕ) := by
      intro w₁ hw₁_mem_Icc w₂ hw₂_mem_Icc h_g_w₁_eq_g_w₂
      simp only [g] at h_g_w₁_eq_g_w₂
      have h_one_plus_k_actual_pos : (1 : ℝ) + k_actual > 0 := by
        linarith [subprob_k_actual_pos_proof]
      have h_one_plus_k_actual_ne_zero : (1 : ℝ) + k_actual ≠ 0 := by
        linarith [h_one_plus_k_actual_pos]
      have h_cast_w₁_eq_cast_w₂ : (↑w₁ : ℝ) = (↑w₂ : ℝ) := by
        exact (mul_left_inj' h_one_plus_k_actual_ne_zero).mp h_g_w₁_eq_g_w₂
      exact Nat.cast_inj.mp h_cast_w₁_eq_cast_w₂

    have h_sum_S'_eq_sum_g_over_Icc : ∑ k ∈ S', k = ∑ w_nat ∈ Finset.Icc 1 W_actual, g w_nat := by
      simp only [S']
      exact Finset.sum_image h_g_inj_on_Icc

    rw [h_sum_S'_eq_sum_g_over_Icc] at h_sum_S'_eq_420
    exact h_sum_S'_eq_420



  subprob_sum_rewritten :≡ ((1:ℝ) + k_actual) * (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (420:ℝ)
  subprob_sum_rewritten_proof ⇐ show subprob_sum_rewritten by


    rw [mul_comm]

    rw [Finset.sum_mul]

    exact subprob_sum_eq_420_expanded_proof

  subprob_sum_arith_series :≡ (∑ w_nat in (Finset.Icc 1 W_actual), (↑w_nat : ℝ)) = (↑W_actual : ℝ) * (↑W_actual + (1:ℕ)) / (2:ℝ)
  subprob_sum_arith_series_proof ⇐ show subprob_sum_arith_series by















    rw [← Nat.cast_sum (Finset.Icc 1 W_actual) (fun x => x)]

    have h_nat_sum_formula : (∑ x ∈ Finset.Icc (1 : ℕ) W_actual, x) = W_actual * (W_actual + 1) / 2 := by

      change (∑ x ∈ Finset.Ico 1 (W_actual + 1), x) = W_actual * (W_actual + 1) / 2

      rw [Finset.sum_Ico_eq_sum_range (fun i : ℕ => i) 1 (W_actual + 1)]

      simp only [Nat.add_one_sub_one]

      rw [Finset.sum_add_distrib]

      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

      rw [add_comm]
      rw [Nat.mul_comm W_actual (W_actual + 1)]

      have h_rhs_is_sum_range_succ : (W_actual + 1) * W_actual / 2 = ∑ i in Finset.range (W_actual + 1), i := by
        rw [Finset.sum_range_id (W_actual + 1)]
        rw [Nat.add_one_sub_one W_actual]
      rw [h_rhs_is_sum_range_succ]
      exact (Finset.sum_range_succ id W_actual).symm

    rw [h_nat_sum_formula]

    have h_rhs_transformed : (↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (↑(2 : ℕ) : ℝ) := by
      have h1 : (↑W_actual : ℝ) * (↑W_actual + (1 : ℕ)) / (2 : ℝ) = (↑W_actual : ℝ) * (↑W_actual + (1 : ℝ)) / (2 : ℝ) := by
        simp only [Nat.cast_one]
      have h2 : (↑W_actual : ℝ) * (↑W_actual + (1 : ℝ)) / (2 : ℝ) = (↑W_actual : ℝ) * (↑(W_actual + 1) : ℝ) / (2 : ℝ) := by
        rw [← Nat.cast_add_one W_actual]
      have h3 : (↑W_actual : ℝ) * (↑(W_actual + 1) : ℝ) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (2 : ℝ) := by
        rw [← Nat.cast_mul W_actual (W_actual + 1)]
      have h4 : (↑(W_actual * (W_actual + 1)) : ℝ) / (2 : ℝ) = (↑(W_actual * (W_actual + 1)) : ℝ) / (↑(2 : ℕ) : ℝ) := by
        rw [← Nat.cast_two]
      rw [h1, h2, h3, h4]

    rw [h_rhs_transformed]

    have h_dvd : 2 ∣ W_actual * (W_actual + 1) :=
      even_iff_two_dvd.mp (Nat.even_mul_succ_self W_actual)

    rw [Nat.cast_div h_dvd (by simp : (↑(2 : ℕ) : ℝ) ≠ (0 : ℝ))]

  subprob_main_eq_W_k :≡ ((1:ℝ) + k_actual) * ((↑W_actual : ℝ) * (↑W_actual + (1:ℕ)) / (2:ℝ)) = (420:ℝ)
  subprob_main_eq_W_k_proof ⇐ show subprob_main_eq_W_k by






    rw [← subprob_sum_arith_series_proof]


    exact subprob_sum_rewritten_proof


  subprob_W_actual_ge_1 :≡ W_actual ≥ 1
  subprob_W_actual_ge_1_proof ⇐ show subprob_W_actual_ge_1 by

    apply Nat.one_le_iff_ne_zero.mpr
    by_contra h_W_actual_is_zero
    have h_S_def : S = Finset.image (fun (w_nat : ℕ) => (↑(w_nat) : ℝ) * ((1 : ℝ) + k_actual)) (Finset.Icc (1 : ℕ) W_actual) ∪ ({(0 : ℝ)} : Finset ℝ) := subprob_S_elements_form_proof
    rw [h_W_actual_is_zero] at h_S_def
    have h_Icc_empty : Finset.Icc (1 : ℕ) 0 = ∅ := by
      apply Finset.Icc_eq_empty
      apply Nat.not_le_of_gt
      exact Nat.zero_lt_one
    rw [h_Icc_empty] at h_S_def
    rw [Finset.image_empty] at h_S_def
    rw [Finset.empty_union] at h_S_def
    have h_sum_S_val : ∑ k ∈ S, k = (420 : ℝ) := h₁
    rw [h_S_def] at h_sum_S_val
    simp only [Finset.sum_singleton] at h_sum_S_val
    have h_contr : (0 : ℝ) ≠ (420 : ℝ) := by
      norm_num
    exact h_contr h_sum_S_val

  subprob_W_bounds_from_def :≡ ((↑W_actual + (1:ℕ) : ℝ)⁻¹ ≤ k_actual ∧ k_actual < ((↑W_actual) : ℝ)⁻¹)
  subprob_W_bounds_from_def_proof ⇐ show subprob_W_bounds_from_def by




    let Y_val : ℝ := (1 : ℝ) / k_actual
    have Y_val_def : Y_val = (1 : ℝ) / k_actual := rfl
    have hY_val_pos : Y_val > 0 := by
      rw [Y_val_def]
      apply div_pos
      norm_num
      exact subprob_k_actual_pos_proof
    have h_ceil_Y_val_ge_2 : ⌈Y_val⌉₊ ≥ 2 := by
      rw [W_actual_def] at subprob_W_actual_ge_1_proof
      rw [←Y_val_def] at subprob_W_actual_ge_1_proof
      have h_one_le_ceil_Y_val : 1 ≤ ⌈Y_val⌉₊ := by
        apply Nat.one_le_iff_ne_zero.mpr
        intro h_ceil_Y_val_eq_zero
        have h_rewritten_subprob : ⌈Y_val⌉₊ - 1 ≥ 1 := subprob_W_actual_ge_1_proof
        rw [h_ceil_Y_val_eq_zero] at h_rewritten_subprob
        rw [Nat.zero_sub] at h_rewritten_subprob
        exact Nat.not_succ_le_zero 0 h_rewritten_subprob
      have h_intermediate_ineq : ⌈Y_val⌉₊ ≥ 1 + 1 :=
        (Nat.le_sub_iff_add_le h_one_le_ceil_Y_val).mp subprob_W_actual_ge_1_proof
      exact h_intermediate_ineq
    have h_ceil_Y_val_ge_1 : ⌈Y_val⌉₊ ≥ 1 := by linarith [h_ceil_Y_val_ge_2]
    apply And.intro
    .
      have h_W_plus_1_eq_ceil_Y_val : W_actual + 1 = ⌈Y_val⌉₊ := by
        rw [W_actual_def]
        rw [←Y_val_def]
        apply Nat.sub_add_cancel
        exact h_ceil_Y_val_ge_1
      have h_denom_eq_ceil_Y_val_cast : (↑W_actual + (1 : ℕ) : ℝ) = (↑(⌈Y_val⌉₊) : ℝ) := by
        rw [Nat.cast_one]
        rw [(Nat.cast_add_one W_actual).symm]
        rw [h_W_plus_1_eq_ceil_Y_val]
      rw [h_denom_eq_ceil_Y_val_cast]
      have h_ceil_Y_val_cast_pos : (↑(⌈Y_val⌉₊) : ℝ) > 0 := by
        rw [gt_iff_lt]
        rw [Nat.cast_pos]
        linarith [h_ceil_Y_val_ge_2]
      rw [inv_pos_le_iff_one_le_mul h_ceil_Y_val_cast_pos]
      rw [mul_comm]
      rw [← div_le_iff subprob_k_actual_pos_proof]
      rw [←Y_val_def]
      exact Nat.le_ceil Y_val
    .
      have h_W_actual_cast_pos : (↑W_actual : ℝ) > 0 := by
        apply Nat.cast_pos.mpr
        apply Nat.lt_of_succ_le
        exact subprob_W_actual_ge_1_proof
      rw [inv_eq_one_div]
      rw [lt_div_iff h_W_actual_cast_pos]
      have h_key_rewrite : k_actual * (↑W_actual : ℝ) < 1 ↔ (↑W_actual : ℝ) < k_actual⁻¹ := by
        rw [mul_comm]
        conv_rhs => rw [← mul_lt_mul_iff_of_pos_right subprob_k_actual_pos_proof]
        rw [inv_mul_cancel (ne_of_gt subprob_k_actual_pos_proof)]
      rw [h_key_rewrite]
      rw [inv_eq_one_div]
      rw [←Y_val_def]
      have h_cast_W_actual : (↑W_actual : ℝ) = (↑(⌈Y_val⌉₊) : ℝ) - 1 := by
        rw [W_actual_def]
        rw [←Y_val_def]
        rw [Nat.cast_sub h_ceil_Y_val_ge_1]
        rw [Nat.cast_one]
      rw [h_cast_W_actual]
      rw [sub_lt_iff_lt_add]
      exact Nat.ceil_lt_add_one (le_of_lt hY_val_pos)



  subprob_W_actual_is_28 :≡ W_actual = 28
  subprob_W_actual_is_28_proof ⇐ show subprob_W_actual_is_28 by


    let W_R : ℝ := ↑W_actual
    have h_W_R_ge_1 : W_R ≥ 1 := by
      rw [←Nat.cast_one]
      rw [ge_iff_le]
      rw [Nat.cast_le (α := ℝ)]
      exact subprob_W_actual_ge_1_proof
    have h_W_R_pos : W_R > 0 := by linarith [h_W_R_ge_1]
    have h_W_R_plus_1_pos : W_R + 1 > 0 := by linarith [h_W_R_ge_1]
    have h_W_R_ne_zero : W_R ≠ 0 := by linarith [h_W_R_ge_1]
    have h_W_R_plus_1_ne_zero : W_R + 1 ≠ 0 := by linarith [h_W_R_ge_1]

    have eq_main : ((1 : ℝ) + k_actual) * (W_R * (W_R + (1 : ℝ)) / (2 : ℝ)) = (420 : ℝ) := by
      convert subprob_main_eq_W_k_proof using 1
      simp
    have h_k_bounds := subprob_W_bounds_from_def_proof
    have h_k_lower : 1 / (W_R + 1) ≤ k_actual := by
      have temp := h_k_bounds.1
      norm_cast at temp
      convert temp
      ·
        funext x
        rw [one_div]
      ·
        simp only [Nat.cast_add, Nat.cast_one]
    have h_k_upper : k_actual < 1 / W_R := by
      have temp := h_k_bounds.2
      norm_cast at temp
      rw [one_div]
      exact temp

    have h_W_actual_le_28 : W_actual ≤ 28 := by
      have h1_1 : 1 + 1 / (W_R + 1) ≤ 1 + k_actual := add_le_add_left h_k_lower 1
      have h1_2 : 1 + 1 / (W_R + 1) = (W_R + 2) / (W_R + 1) := by
        field_simp [h_W_R_plus_1_ne_zero]
        ring
      rw [h1_2] at h1_1

      let factor_val : ℝ := W_R * (W_R + (1:ℝ)) / (2:ℝ)
      have factor_nonneg : factor_val ≥ 0 := by
        apply div_nonneg
        · apply mul_nonneg
          · exact le_of_lt h_W_R_pos
          · exact le_of_lt h_W_R_plus_1_pos
        · norm_num

      have h1_3 : ((W_R + 2) / (W_R + 1)) * factor_val ≤ ((1 + k_actual) * factor_val) :=
        mul_le_mul_of_nonneg_right h1_1 factor_nonneg

      rw [eq_main] at h1_3

      have h1_4_lhs_simp : ((W_R + 2) / (W_R + 1)) * (W_R * (W_R + (1:ℝ)) / (2:ℝ)) = W_R * (W_R + 2) / (2:ℝ) := by
        field_simp [h_W_R_plus_1_ne_zero]
        ring
      rw [h1_4_lhs_simp] at h1_3

      have h1_5 : W_R * (W_R + 2) ≤ 840 := by
        have temp := (mul_le_mul_left (by norm_num : (0 : ℝ) < 2)).mpr h1_3
        have eq_lhs : (2 : ℝ) * (W_R * (W_R + (2 : ℝ)) / (2 : ℝ)) = W_R * (W_R + (2 : ℝ)) := by
          field_simp
        have eq_rhs : (2 : ℝ) * (420 : ℝ) = (840 : ℝ) := by
          norm_num
        rw [eq_lhs, eq_rhs] at temp
        exact temp

      have h1_6 : W_R^2 + 2*W_R ≤ 840 := by
        have algebra_eq : W_R^2 + 2*W_R = W_R * (W_R + 2) := by
          ring
        rw [algebra_eq]
        exact h1_5

      have h1_7 : W_R^2 + 2*W_R - 840 ≤ 0 := by linarith [h1_6]

      have h1_8_factor_form : (W_R - 28) * (W_R + 30) = W_R^2 + 2*W_R - 840 := by ring
      rw [← h1_8_factor_form] at h1_7

      have h1_9_WR_plus_30_pos : W_R + 30 > 0 := by linarith [h_W_R_ge_1]

      have h1_10_WR_minus_28_le_0 : W_R - 28 ≤ 0 := by
        exact nonpos_of_mul_nonpos_left h1_7 h1_9_WR_plus_30_pos

      have h1_11_WR_le_28 : W_R ≤ 28 := by linarith [h1_10_WR_minus_28_le_0]

      rw [show (28 : ℝ) = ↑(28 : ℕ) by norm_cast] at h1_11_WR_le_28
      exact (Nat.cast_le (α := ℝ)).mp h1_11_WR_le_28

    have h_W_actual_ge_28 : W_actual ≥ 28 := by
      have h2_1 : 1 + k_actual < 1 + 1 / W_R := add_lt_add_left h_k_upper 1
      have h2_2 : 1 + 1 / W_R = (W_R + 1) / W_R := by
        field_simp [h_W_R_ne_zero]
      rw [h2_2] at h2_1

      let factor_val : ℝ := W_R * (W_R + (1:ℝ)) / (2:ℝ)
      have factor_pos : factor_val > 0 := by
        apply div_pos
        · exact mul_pos h_W_R_pos h_W_R_plus_1_pos
        · norm_num

      have h2_3 : ((1 + k_actual) * factor_val) < ((W_R + 1) / W_R) * factor_val :=
        (mul_lt_mul_right factor_pos).mpr h2_1

      rw [eq_main] at h2_3

      have h2_4_rhs_simp : ((W_R + 1) / W_R) * (W_R * (W_R + (1:ℝ)) / (2:ℝ)) = (W_R + 1)^2 / (2:ℝ) := by
        field_simp [h_W_R_ne_zero]
        ring
      rw [h2_4_rhs_simp] at h2_3

      have h2_5 : 840 < (W_R + 1)^2 := by
        have temp := (mul_lt_mul_left (by norm_num : (0 : ℝ) < 2)).mpr h2_3
        have simplify_lhs : (2 : ℝ) * (420 : ℝ) = (840 : ℝ) := by norm_num
        have simplify_rhs : (2 : ℝ) * ((W_R + (1 : ℝ)) ^ (2 : ℕ) / (2 : ℝ)) = (W_R + (1 : ℝ)) ^ (2 : ℕ) := by
          have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
          field_simp [h_two_ne_zero]
        rw [simplify_lhs, simplify_rhs] at temp
        exact temp

      by_contra hc_WR_lt_28_contra_hyp
      simp [not_le] at hc_WR_lt_28_contra_hyp
      have h_WR_lt_28_nat_cast : W_R < (↑28 : ℝ) := by
          exact (Nat.cast_lt (α := ℝ)).mpr hc_WR_lt_28_contra_hyp
      have h_Wactual_lt_28 : W_actual < 28 := (Nat.cast_lt (α := ℝ)).mp h_WR_lt_28_nat_cast
      have h_Wactual_le_27 : W_actual ≤ 27 := by
        rw [←Nat.lt_succ_iff]
        exact h_Wactual_lt_28

      have h_WR_le_27 : W_R ≤ 27 := by
          exact (Nat.cast_le (α := ℝ)).mpr h_Wactual_le_27

      have h_WR_plus_1_le_28 : W_R + 1 ≤ 28 := by linarith [h_WR_le_27]

      have h_WR_plus_1_sq_le_28_sq : (W_R + 1)^2 ≤ 28^2 := by
        apply pow_le_pow_of_le_left (le_of_lt h_W_R_plus_1_pos) h_WR_plus_1_le_28

      have h_28_sq_val : (28 : ℝ)^2 = 784 := by norm_num
      rw [h_28_sq_val] at h_WR_plus_1_sq_le_28_sq

      have h_absurd_ineq : (840 : ℝ) < 784 := by linarith [h2_5, h_WR_plus_1_sq_le_28_sq]
      have h_not_absurd_ineq : ¬((840 : ℝ) < 784) := by norm_num
      contradiction

    exact Nat.le_antisymm h_W_actual_le_28 h_W_actual_ge_28



  subprob_k_actual_is_1_29 :≡ k_actual = (1:ℝ)/(29:ℝ)
  subprob_k_actual_is_1_29_proof ⇐ show subprob_k_actual_is_1_29 by

    have h_main_eq : ((1 : ℝ) + k_actual) * ((↑(W_actual) : ℝ) * ((↑(W_actual) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ)) = (420 : ℝ) :=
      subprob_main_eq_W_k_proof

    have h_main_eq_W28 : ((1 : ℝ) + k_actual) * ((↑(28 : ℕ) : ℝ) * ((↑(28 : ℕ) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ)) = (420 : ℝ) := by
      rw [subprob_W_actual_is_28_proof] at h_main_eq
      exact h_main_eq

    have h_coeff_val : (↑(28 : ℕ) : ℝ) * ((↑(28 : ℕ) : ℝ) + (↑((1 : ℕ)) : ℝ)) / (2 : ℝ) = (406 : ℝ) := by
      norm_cast
      norm_num

    have h_simplified_eq : ((1 : ℝ) + k_actual) * (406 : ℝ) = (420 : ℝ) := by
      rw [h_coeff_val] at h_main_eq_W28
      exact h_main_eq_W28

    have h_406_ne_zero : (406 : ℝ) ≠ (0 : ℝ) := by norm_num
    have h_1_plus_k_eq_frac : (1 : ℝ) + k_actual = (420 : ℝ) / (406 : ℝ) := by
      exact eq_div_of_mul_eq h_406_ne_zero h_simplified_eq

    have h_frac_simp : (420 : ℝ) / (406 : ℝ) = (30 : ℝ) / (29 : ℝ) := by
      norm_num

    have h_1_plus_k_final : (1 : ℝ) + k_actual = (30 : ℝ) / (29 : ℝ) := by
      rw [h_1_plus_k_eq_frac, h_frac_simp]

    have h_k_actual_expr : k_actual = (30 : ℝ) / (29 : ℝ) - (1 : ℝ) := by
      linarith [h_1_plus_k_final]

    have h_final_calc : (30 : ℝ) / (29 : ℝ) - (1 : ℝ) = (1 : ℝ) / (29 : ℝ) := by
      norm_num

    rw [h_k_actual_expr, h_final_calc]

  subprob_a_solve1 :≡ (1:ℝ)/(29:ℝ) = (((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)) / ((2:ℝ)*a_real)
  subprob_a_solve1_proof ⇐ show subprob_a_solve1 by



    rw [← subprob_k_actual_is_1_29_proof]
    exact k_actual_def
  subprob_a_solve2 :≡ ((2:ℝ)*a_real)/(29:ℝ) = ((1:ℝ) - (2:ℝ)*a_real) - Real.sqrt ((1:ℝ) - (4:ℝ)*a_real)
  subprob_a_solve2_proof ⇐ show subprob_a_solve2 by
    let D_val := (2 : ℝ) * (↑a_real : ℝ)
    let N_val := (1 : ℝ) - (2 : ℝ) * (↑a_real : ℝ) - Real.sqrt ((1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ))

    have hD_val_ne_zero : D_val ≠ 0 := by
      have h_a_real_pos : (↑a_real : ℝ) > 0 := subprob_a_real_pos_proof
      have h_a_real_ne_zero : (↑a_real : ℝ) ≠ 0 := ne_of_gt h_a_real_pos
      have h_two_ne_zero : (2 : ℝ) ≠ 0 := two_ne_zero
      exact mul_ne_zero h_two_ne_zero h_a_real_ne_zero


    have h_intermediate_eq : (1 : ℝ) / (29 : ℝ) * D_val = N_val := by
      exact (eq_div_iff_mul_eq hD_val_ne_zero).mp subprob_a_solve1_proof

    rw [one_div_mul_eq_div (29 : ℝ) D_val] at h_intermediate_eq

    exact h_intermediate_eq
  subprob_a_solve3 :≡ Real.sqrt ((1:ℝ) - (4:ℝ)*a_real) = ((1:ℝ) - (2:ℝ)*a_real) - ((2:ℝ)*a_real)/(29:ℝ)
  subprob_a_solve3_proof ⇐ show subprob_a_solve3 by

    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    rw [subprob_a_solve2_proof]
    rw [sub_add_cancel]
  subprob_a_solve4 :≡ Real.sqrt ((1:ℝ) - (4:ℝ)*a_real) = (1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real
  subprob_a_solve4_proof ⇐ show subprob_a_solve4 by

    rw [subprob_a_solve3_proof]

    ring

  subprob_rhs_nonneg_for_squaring :≡ (1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real ≥ (0:ℝ)
  subprob_rhs_nonneg_for_squaring_proof ⇐ show subprob_rhs_nonneg_for_squaring by


    have h_W_actual_ge_1 : W_actual ≥ 1 := subprob_W_actual_ge_1_proof
    have h_one_in_Icc : (1 : ℕ) ∈ Finset.Icc (1 : ℕ) W_actual := by
      apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.le_refl 1
      · exact h_W_actual_ge_1

    let x_val := (↑(1 : ℕ) : ℝ) * (1 + k_actual)
    have h_x_val_in_image : x_val ∈ Finset.image (fun (w_nat : ℕ) ↦ (↑w_nat : ℝ) * (1 + k_actual)) (@Finset.Icc ℕ _ _ (1 : ℕ) W_actual) := by
      apply Finset.mem_image_of_mem (f := fun w_nat : ℕ ↦ (↑w_nat : ℝ) * (1 + k_actual)) (a := (1:ℕ))
      exact h_one_in_Icc

    have h_x_val_in_S : x_val ∈ S := by
      rw [subprob_S_elements_form_proof]
      apply Finset.mem_union_left
      exact h_x_val_in_image

    have h_k_actual_val : k_actual = (1 : ℝ) / (29 : ℝ) := subprob_k_actual_is_1_29_proof
    have h_k_actual_pos : k_actual > 0 := by
      rw [h_k_actual_val]
      norm_num

    have h_one_plus_k_actual_pos : 1 + k_actual > 0 := by
      linarith [h_k_actual_pos]

    have h_x_val_ne_zero : x_val ≠ 0 := by
      simp only [x_val, Nat.cast_one, one_mul]
      linarith [h_one_plus_k_actual_pos]

    have h_a_real_le_one_quarter : (↑a_real : ℝ) ≤ (1 : ℝ) / (4 : ℝ) := by
      apply subprob_a_real_le_one_quarter_proof x_val h_x_val_in_S h_x_val_ne_zero

    have h_four_a_real_le_one : (4 : ℝ) * ↑a_real ≤ 1 := by
      rw [mul_comm]
      have h_pos_4 : (0 : ℝ) < (4 : ℝ) := by norm_num
      rw [← le_div_iff h_pos_4]
      exact h_a_real_le_one_quarter
    have h_term_under_sqrt_nonneg : (1 : ℝ) - (4 : ℝ) * ↑a_real ≥ 0 := by
      exact sub_nonneg_of_le h_four_a_real_le_one

    rw [← subprob_a_solve4_proof]

    apply Real.sqrt_nonneg




  subprob_a_solve5 :≡ (1:ℝ) - (4:ℝ)*a_real = ((1:ℝ) - ((60:ℝ)/(29:ℝ))*a_real) ^ 2
  subprob_a_solve5_proof ⇐ show subprob_a_solve5 by








    have h_W_actual_ge_1 : W_actual ≥ 1 := subprob_W_actual_ge_1_proof

    let x_val := (↑(1 : ℕ) : ℝ) * ((1 : ℝ) + k_actual)

    have h_x_val_in_S : x_val ∈ S := by
      rw [subprob_S_elements_form_proof]
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      use (1 : ℕ)
      refine' ⟨_, rfl⟩
      rw [Finset.mem_Icc]
      exact ⟨le_rfl, h_W_actual_ge_1⟩

    have h_k_actual_pos : k_actual > 0 := by
      rw [subprob_k_actual_is_1_29_proof]
      norm_num

    have h_x_val_ne_zero : x_val ≠ 0 := by
      simp only [x_val, Nat.cast_one, one_mul]
      linarith [h_k_actual_pos]

    have h_a_real_le_one_quarter : (↑a_real : ℝ) ≤ (1 : ℝ) / (4 : ℝ) :=
      subprob_a_real_le_one_quarter_proof x_val h_x_val_in_S h_x_val_ne_zero

    have h_term_under_sqrt_nonneg : (1 : ℝ) - (4 : ℝ) * (↑a_real : ℝ) ≥ 0 := by
      have h_four_pos : (4 : ℝ) > 0 := by norm_num
      have h_mul_le : (4 : ℝ) * (↑a_real : ℝ) ≤ (4 : ℝ) * (1 / 4) := by
        apply (mul_le_mul_left h_four_pos).mpr
        exact h_a_real_le_one_quarter
      have h_rhs_eq_one : (4 : ℝ) * (1 / 4) = 1 := by norm_num
      rw [h_rhs_eq_one] at h_mul_le
      linarith [h_mul_le]

    apply Eq.symm
    apply (Real.sqrt_eq_iff_sq_eq h_term_under_sqrt_nonneg subprob_rhs_nonneg_for_squaring_proof).mp
    exact subprob_a_solve4_proof
  subprob_a_solve6 :≡ (1:ℝ) - (4:ℝ)*a_real = (1:ℝ) - (2:ℝ)*((60:ℝ)/(29:ℝ))*a_real + (((60:ℝ)/(29:ℝ))*a_real) ^ 2
  subprob_a_solve6_proof ⇐ show subprob_a_solve6 by



    have h_expansion :
      ((1 : ℝ) - (60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ)) ^ (2 : ℕ) =
      (1 : ℝ) - (2 : ℝ) * ((60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ)) + (((60 : ℝ) / (29 : ℝ) * (↑a_real : ℝ))) ^ 2 := by
      ring

    rw [subprob_a_solve5_proof, h_expansion]
    ring

  subprob_a_solve7 :≡ -(4:ℝ)*a_real = -((120:ℝ)/(29:ℝ))*a_real + (((3600:ℝ)/((29:ℝ)^2)))*a_real ^ 2
  subprob_a_solve7_proof ⇐ show subprob_a_solve7 by


    have h_derived : -(4 : ℝ) * (↑a_real : ℝ) = -(2 : ℝ) * ((60 : ℝ) / (29 : ℝ)) * (↑a_real : ℝ) + ((60 : ℝ) / (29 : ℝ) * (↑(a_real) : ℝ)) ^ (2 : ℕ) := by
      have h_temp := subprob_a_solve6_proof
      rw [sub_eq_add_neg, sub_eq_add_neg] at h_temp
      replace h_temp := congr_arg (fun (val : ℝ) => -(1:ℝ) + val) h_temp
      dsimp at h_temp
      simp only [neg_add_cancel_left, add_assoc] at h_temp

      rw [← neg_mul (4:ℝ) (↑a_real), ← neg_mul ((2:ℝ)*((60:ℝ)/(29:ℝ))) (↑a_real)] at h_temp
      rw [← neg_mul (2:ℝ) ((60:ℝ)/(29:ℝ))] at h_temp
      exact h_temp
    rw [h_derived]
    ring


  subprob_a_solve8 :≡ -(4:ℝ) = -((120:ℝ)/(29:ℝ)) + (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve8_proof ⇐ show subprob_a_solve8 by





    let ar := (↑a_real : ℝ)

    have ar_ne_zero : ar ≠ 0 := by
      linarith [subprob_a_real_pos_proof]

    have h_eq := subprob_a_solve7_proof

    simp only [pow_two] at h_eq

    have h_rhs_factor : -((120 : ℝ) / (29 : ℝ)) * ar + (3600 : ℝ) / ((29 : ℝ) * (29 : ℝ)) * (ar * ar) =
                        (-((120 : ℝ) / (29 : ℝ)) + (3600 : ℝ) / ((29 : ℝ) * (29 : ℝ)) * ar) * ar := by
      ring

    rw [h_rhs_factor] at h_eq

    rw [mul_eq_mul_right_iff] at h_eq
    simp [ar_ne_zero] at h_eq

    rw [← pow_two (29 : ℝ)] at h_eq
    exact h_eq
  subprob_a_solve9 :≡ ((120:ℝ)/(29:ℝ)) - (4:ℝ) = (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve9_proof ⇐ show subprob_a_solve9 by


    rw [sub_eq_add_neg]

    rw [subprob_a_solve8_proof]

    rw [←add_assoc]

    rw [add_right_neg]

    rw [zero_add]

  subprob_a_solve10 :≡ (4:ℝ)/(29:ℝ) = (((3600:ℝ)/((29:ℝ)^2)))*a_real
  subprob_a_solve10_proof ⇐ show subprob_a_solve10 by

    have h_lhs_equiv : (120 : ℝ) / (29 : ℝ) - (4 : ℝ) = (4 : ℝ) / (29 : ℝ) := by
      norm_num

    rw [h_lhs_equiv.symm]
    exact subprob_a_solve9_proof
  subprob_a_solve11 :≡ a_real = ((4:ℝ)/(29:ℝ)) * (((29:ℝ)^2)/((3600:ℝ)))
  subprob_a_solve11_proof ⇐ show subprob_a_solve11 by






    have h_main := subprob_a_solve10_proof


    let Coeff := (3600 : ℝ) / ((29 : ℝ) ^ (2 : ℕ))

    have hCoeffNum_ne_zero : (3600 : ℝ) ≠ 0 := by norm_num
    have h29_ne_zero : (29 : ℝ) ≠ 0 := by norm_num
    have hCoeffDen_ne_zero : (29 : ℝ) ^ (2 : ℕ) ≠ 0 := by
      apply pow_ne_zero
      exact h29_ne_zero
    have hCoeff_ne_zero : Coeff ≠ 0 := by
      apply div_ne_zero hCoeffNum_ne_zero hCoeffDen_ne_zero

    have h_main_symm : Coeff * (↑a_real : ℝ) = (4 : ℝ) / (29 : ℝ) := Eq.symm h_main

    have h_a_real_eq : (↑a_real : ℝ) = Coeff⁻¹ * ((4 : ℝ) / (29 : ℝ)) := by
      exact (eq_inv_mul_iff_mul_eq₀ hCoeff_ne_zero).mpr h_main_symm

    rw [h_a_real_eq]

    rw [mul_comm (Coeff⁻¹) (((4 : ℝ) / (29 : ℝ)))]

    have h_factor_ne_zero : (4 : ℝ) / (29 : ℝ) ≠ 0 := by
      apply div_ne_zero
      . norm_num
      . norm_num

    simp only [mul_eq_mul_left_iff, h_factor_ne_zero]


    rw [inv_div]
    simp only [or_false]



  subprob_a_real_is_29_900 :≡ a_real = (29:ℝ)/(900:ℝ)
  subprob_a_real_is_29_900_proof ⇐ show subprob_a_real_is_29_900 by

    rw [subprob_a_solve11_proof]

    have h_29_ne_0 : (29 : ℝ) ≠ 0 := by
      norm_num
    have h_3600_ne_0 : (3600 : ℝ) ≠ 0 := by
      norm_num
    have h_900_ne_0 : (900 : ℝ) ≠ 0 := by
      norm_num

    field_simp [h_29_ne_0, h_3600_ne_0, h_900_ne_0]

    norm_num

  subprob_a_rat_is_29_900 :≡ a = (29:ℚ)/(900:ℚ)
  subprob_a_rat_is_29_900_proof ⇐ show subprob_a_rat_is_29_900 by




    apply (@Rat.cast_inj ℝ _ _).mp

    rw [← a_real_def]

    rw [subprob_a_real_is_29_900_proof]

    simp

  subprob_coprime_29_900 :≡ Nat.Coprime 29 900
  subprob_coprime_29_900_proof ⇐ show subprob_coprime_29_900 by



    rw [Nat.coprime_iff_gcd_eq_one]

    have h_prime_29 : Nat.Prime 29 := by
      norm_num

    rw [← Nat.coprime_iff_gcd_eq_one, Nat.Prime.coprime_iff_not_dvd h_prime_29]

    rw [Nat.dvd_iff_mod_eq_zero]

    have h_mod_val : 900 % 29 = 1 := by
      norm_num

    rw [h_mod_val]

    norm_num


  subprob_a_num_is_29 :≡ a.num = 29
  subprob_a_num_is_29_proof ⇐ show subprob_a_num_is_29 by


















    rw [subprob_a_rat_is_29_900_proof]

    have h900_ne_zero_nat : (900 : ℕ) ≠ 0 := by
      norm_num

    change Rat.num ((Nat.cast 29 : ℚ) / (Nat.cast 900 : ℚ)) = (29 : ℤ)


    rw [Rat.natCast_div_eq_divInt (29 : ℕ) (900 : ℕ)]

    unfold Rat.divInt
    dsimp only


    change Rat.num (mkRat (29 : ℤ) (900 : ℕ)) = (29 : ℤ)
    unfold mkRat
    rw [dif_neg h900_ne_zero_nat]

    have h_norm_eq : (Rat.normalize (29 : ℤ) (900 : ℕ) h900_ne_zero_nat).num =
        (29 : ℤ) / ↑(Nat.gcd (Int.natAbs (29 : ℤ)) (900 : ℕ)) := by
      rfl
    rw [h_norm_eq]

    have hg : Nat.gcd (Int.natAbs (29 : ℤ)) (900 : ℕ) = 1 := by
      simp

    rw [hg]

    rw [Nat.cast_one]
    simp

  subprob_a_den_is_900 :≡ a.den = 900
  subprob_a_den_is_900_proof ⇐ show subprob_a_den_is_900 by

    have h_a_eq_div : a = (29 : ℚ) / (900 : ℚ) := subprob_a_rat_is_29_900_proof

    have h_div_as_mk : (29 : ℚ) / (900 : ℚ) = Rat.divInt (↑29 : ℤ) (↑900 : ℤ) := by
      rw [Rat.divInt_eq_div]
      rfl

    rw [h_div_as_mk] at h_a_eq_div

    have h_900_pos : (↑900 : ℤ) > 0 := by
      apply Int.coe_nat_pos.mpr
      exact Nat.zero_lt_of_lt (by norm_num : (0 : ℕ) < 900)

    have h_nat_coprime : Nat.Coprime 29 900 := subprob_coprime_29_900_proof
    have h_int_coprime : IsCoprime (↑29 : ℤ) (↑900 : ℤ) := Nat.Coprime.isCoprime h_nat_coprime

    have h_num_den_eq : ((Rat.divInt (Nat.cast 29 : ℤ) (Nat.cast 900 : ℤ)).num = (Nat.cast 29 : ℤ) ∧
                        (Rat.divInt (Nat.cast 29 : ℤ) (Nat.cast 900 : ℤ)).den = Int.natAbs (Nat.cast 900 : ℤ)) := by
      apply And.intro
      ·
        rw [Rat.divInt_eq_div]
        apply Rat.num_div_eq_of_coprime
        ·
          exact h_900_pos
        ·
          simp only [Int.natAbs_ofNat]
          exact h_nat_coprime
      ·
        rw [Rat.divInt_eq_div]
        rw [← Nat.cast_inj (R := ℤ)]
        simp only [Int.natAbs_ofNat]
        apply Rat.den_div_eq_of_coprime
        ·
          exact h_900_pos
        ·
          simp only [Int.natAbs_ofNat]
          exact h_nat_coprime

    have h_den_val : (Rat.divInt (↑29 : ℤ) (↑900 : ℤ)).den = Int.natAbs (↑900 : ℤ) := h_num_den_eq.right

    rw [h_a_eq_div, h_den_val]
    rfl





  subprob_target_calc :≡ ↑(a.den) + a.num = ↑(900 : ℕ) + (29 : ℤ)
  subprob_target_calc_proof ⇐ show subprob_target_calc by



    rw [subprob_a_den_is_900_proof]

    rw [subprob_a_num_is_29_proof]

  subprob_final_value :≡ ↑(900 : ℕ) + (29 : ℤ) = (929 : ℤ)
  subprob_final_value_proof ⇐ show subprob_final_value by
    norm_num

  subprob_final_goal :≡ ↑a.den + a.num = 929
  subprob_final_goal_proof ⇐ show subprob_final_goal by

    rw [subprob_target_calc_proof]
    exact subprob_final_value_proof
-/
