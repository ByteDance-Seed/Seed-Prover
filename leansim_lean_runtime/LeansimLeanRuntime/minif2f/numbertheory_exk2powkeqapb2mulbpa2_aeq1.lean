import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

-- erroneous

theorem numbertheory_exk2powkeqapb2mulbpa2_aeq1
  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : ∃ k > 0, 2^k = (a + b^2) * (b + a^2)) :
  a = 1 := by sorry

#print axioms numbertheory_exk2powkeqapb2mulbpa2_aeq1

/- Sketch
variable (a b : ℕ) (h₀ : 0 < a ∧ 0 < b) (h₁ : ∃ k > 0, 2^k = (a + b^2) * (b + a^2))
play
  -- Deconstruct h₀ and h₁
  h₀_a := h₀.left
  h₀_b := h₀.right
  ⟨k_val, hk_k_pos, hk_eq⟩ := h₁

  -- Step 1: Factors are powers of 2
  val1 := a + b^2
  val2 := b + a^2

  subprob_val1_pos :≡ val1 > 0
  subprob_val1_pos_proof ⇐ show subprob_val1_pos by sorry
  subprob_val2_pos :≡ val2 > 0
  subprob_val2_pos_proof ⇐ show subprob_val2_pos by sorry

  subprob_val1_is_pow2 :≡ ∃ m : ℕ, val1 = 2^m
  subprob_val1_is_pow2_proof ⇐ show subprob_val1_is_pow2 by sorry
  ⟨m_val, hm_eq⟩ := subprob_val1_is_pow2_proof

  subprob_val2_is_pow2 :≡ ∃ n : ℕ, val2 = 2^n
  subprob_val2_is_pow2_proof ⇐ show subprob_val2_is_pow2 by sorry
  ⟨n_val, hn_eq⟩ := subprob_val2_is_pow2_proof

  subprob_m_val_ge_1 :≡ m_val ≥ 1
  subprob_m_val_ge_1_proof ⇐ show subprob_m_val_ge_1 by sorry
  subprob_n_val_ge_1 :≡ n_val ≥ 1
  subprob_n_val_ge_1_proof ⇐ show subprob_n_val_ge_1 by sorry

  -- Step 2: Parity argument
  subprob_apb2_even :≡ (a + b^2) % 2 = 0
  subprob_apb2_even_proof ⇐ show subprob_apb2_even by sorry
  subprob_parity_b_sq_eq_b :≡ b^2 % 2 = b % 2
  subprob_parity_b_sq_eq_b_proof ⇐ show subprob_parity_b_sq_eq_b by sorry
  subprob_apb_even :≡ (a + b) % 2 = 0
  subprob_apb_even_proof ⇐ show subprob_apb_even by sorry
  subprob_apbm1_pos :≡ a + b - 1 > 0
  subprob_apbm1_pos_proof ⇐ show subprob_apbm1_pos by sorry
  subprob_apbm1_odd :≡ (a + b - 1) % 2 = 1
  subprob_apbm1_odd_proof ⇐ show subprob_apbm1_odd by sorry

  -- Step 3 & 4: Show m=n, leading to a=b
  lhs_int : ℤ := ((a : ℤ) + (b : ℤ)^2) - ((b : ℤ) + (a : ℤ)^2)
  rhs_int : ℤ := (2 : ℤ)^m_val - (2 : ℤ)^n_val
  subprob_lhs_eq_rhs_int :≡ lhs_int = rhs_int
  subprob_lhs_eq_rhs_int_proof ⇐ show subprob_lhs_eq_rhs_int by sorry

  subprob_lhs_factor_int :≡ lhs_int = ((a : ℤ) - (b : ℤ)) * (1 - ((a : ℤ) + (b : ℤ)))
  subprob_lhs_factor_int_proof ⇐ show subprob_lhs_factor_int by sorry

  term_1_minus_apb_int := 1 - ((a : ℤ) + (b : ℤ))
  subprob_1_minus_apb_neq_0 :≡ term_1_minus_apb_int ≠ 0
  subprob_1_minus_apb_neq_0_proof ⇐ show subprob_1_minus_apb_neq_0 by sorry
  subprob_1_minus_apb_is_odd :≡ term_1_minus_apb_int % 2 ≠ 0
  subprob_1_minus_apb_is_odd_proof ⇐ show subprob_1_minus_apb_is_odd by sorry

  -- Case m_val = n_val
  suppose (h_m_eq_n : m_val = n_val) then
    subprob_rhs_zero_if_m_eq_n :≡ rhs_int = 0
    subprob_rhs_zero_if_m_eq_n_proof ⇐ show subprob_rhs_zero_if_m_eq_n by sorry
    subprob_amb_times_omapb_eq_zero :≡ ((a : ℤ) - (b : ℤ)) * term_1_minus_apb_int = 0
    subprob_amb_times_omapb_eq_zero_proof ⇐ show subprob_amb_times_omapb_eq_zero by sorry
    subprob_a_minus_b_eq_zero_if_m_eq_n :≡ (a : ℤ) - (b : ℤ) = 0
    subprob_a_minus_b_eq_zero_if_m_eq_n_proof ⇐ show subprob_a_minus_b_eq_zero_if_m_eq_n by sorry
    subprob_a_eq_b_if_m_eq_n :≡ a = b
    subprob_a_eq_b_if_m_eq_n_proof ⇐ show subprob_a_eq_b_if_m_eq_n by sorry

  subprob_a_eq_b_if_m_eq_n_lifted :≡ (m_val = n_val) → a = b
  subprob_a_eq_b_if_m_eq_n_lifted_proof ⇐ show subprob_a_eq_b_if_m_eq_n_lifted by sorry

  -- Case m_val > n_val (leads to contradiction)
  suppose (h_m_gt_n : m_val > n_val) then
    p_val1 := m_val - n_val
    subprob_p_val1_pos :≡ p_val1 > 0
    subprob_p_val1_pos_proof ⇐ show subprob_p_val1_pos by sorry
    subprob_rhs_factor_if_m_gt_n :≡ rhs_int = (2 : ℤ)^n_val * ((2 : ℤ)^p_val1 - 1)
    subprob_rhs_factor_if_m_gt_n_proof ⇐ show subprob_rhs_factor_if_m_gt_n by sorry
    term_2p1_minus_1_int := (2 : ℤ)^p_val1 - 1
    subprob_2p1_minus_1_is_odd :≡ term_2p1_minus_1_int % 2 ≠ 0
    subprob_2p1_minus_1_is_odd_proof ⇐ show subprob_2p1_minus_1_is_odd by sorry
    subprob_2p1_minus_1_pos :≡ term_2p1_minus_1_int > 0
    subprob_2p1_minus_1_pos_proof ⇐ show subprob_2p1_minus_1_pos by sorry
    subprob_rhs_pos_if_m_gt_n :≡ rhs_int > 0
    subprob_rhs_pos_if_m_gt_n_proof ⇐ show subprob_rhs_pos_if_m_gt_n by sorry
    subprob_lhs_pos_if_m_gt_n :≡ lhs_int > 0
    subprob_lhs_pos_if_m_gt_n_proof ⇐ show subprob_lhs_pos_if_m_gt_n by sorry
    subprob_a_lt_b_if_m_gt_n :≡ a < b
    subprob_a_lt_b_if_m_gt_n_proof ⇐ show subprob_a_lt_b_if_m_gt_n by sorry
    subprob_2pown_dvd_a_minus_b_int :≡ (2 : ℤ)^n_val ∣ ((a : ℤ) - (b : ℤ))
    subprob_2pown_dvd_a_minus_b_int_proof ⇐ show subprob_2pown_dvd_a_minus_b_int by sorry
    ⟨d1_int, hd1_int_def⟩ := subprob_2pown_dvd_a_minus_b_int_proof
    subprob_d1_int_neg :≡ d1_int < 0
    subprob_d1_int_neg_proof ⇐ show subprob_d1_int_neg by sorry
    eq_for_a_plus_a_sq :≡ (a:ℤ) + (a:ℤ)^2 = (2:ℤ)^n_val * (1 + d1_int)
    eq_for_a_plus_a_sq_proof ⇐ show eq_for_a_plus_a_sq by sorry
    subprob_a_plus_a_sq_pos :≡ (a:ℤ) + (a:ℤ)^2 > 0
    subprob_a_plus_a_sq_pos_proof ⇐ show subprob_a_plus_a_sq_pos by sorry
    subprob_1_plus_d1_int_pos :≡ 1 + d1_int > 0
    subprob_1_plus_d1_int_pos_proof ⇐ show subprob_1_plus_d1_int_pos by sorry
    subprob_false_if_m_gt_n :≡ False
    subprob_false_if_m_gt_n_proof ⇐ show subprob_false_if_m_gt_n by sorry

  subprob_false_if_m_gt_n_lifted :≡ (m_val > n_val) → False
  subprob_false_if_m_gt_n_lifted_proof ⇐ show subprob_false_if_m_gt_n_lifted by sorry

  -- Case n_val > m_val (leads to contradiction, symmetric to m_val > n_val)
  suppose (h_n_gt_m : n_val > m_val) then
    p_val2 := n_val - m_val
    subprob_p_val2_pos :≡ p_val2 > 0
    subprob_p_val2_pos_proof ⇐ show subprob_p_val2_pos by sorry
    subprob_rhs_factor_if_n_gt_m :≡ rhs_int = -((2 : ℤ)^m_val * ((2 : ℤ)^p_val2 - 1))
    subprob_rhs_factor_if_n_gt_m_proof ⇐ show subprob_rhs_factor_if_n_gt_m by sorry
    term_2p2_minus_1_int := (2 : ℤ)^p_val2 - 1
    subprob_2p2_minus_1_is_odd :≡ term_2p2_minus_1_int % 2 ≠ 0
    subprob_2p2_minus_1_is_odd_proof ⇐ show subprob_2p2_minus_1_is_odd by sorry
    subprob_2p2_minus_1_pos :≡ term_2p2_minus_1_int > 0
    subprob_2p2_minus_1_pos_proof ⇐ show subprob_2p2_minus_1_pos by sorry
    subprob_rhs_neg_if_n_gt_m :≡ rhs_int < 0
    subprob_rhs_neg_if_n_gt_m_proof ⇐ show subprob_rhs_neg_if_n_gt_m by sorry
    subprob_lhs_neg_if_n_gt_m :≡ lhs_int < 0
    subprob_lhs_neg_if_n_gt_m_proof ⇐ show subprob_lhs_neg_if_n_gt_m by sorry
    subprob_a_gt_b_if_n_gt_m :≡ a > b
    subprob_a_gt_b_if_n_gt_m_proof ⇐ show subprob_a_gt_b_if_n_gt_m by sorry
    subprob_2powm_dvd_a_minus_b_int :≡ (2 : ℤ)^m_val ∣ ((a : ℤ) - (b : ℤ))
    subprob_2powm_dvd_a_minus_b_int_proof ⇐ show subprob_2powm_dvd_a_minus_b_int by sorry
    ⟨d2_int, hd2_int_def⟩ := subprob_2powm_dvd_a_minus_b_int_proof
    subprob_d2_int_pos :≡ d2_int > 0
    subprob_d2_int_pos_proof ⇐ show subprob_d2_int_pos by sorry
    eq_for_b_plus_b_sq :≡ (b:ℤ) + (b:ℤ)^2 = (2:ℤ)^m_val * (1 - d2_int)
    eq_for_b_plus_b_sq_proof ⇐ show eq_for_b_plus_b_sq by sorry
    subprob_b_plus_b_sq_pos :≡ (b:ℤ) + (b:ℤ)^2 > 0
    subprob_b_plus_b_sq_pos_proof ⇐ show subprob_b_plus_b_sq_pos by sorry
    subprob_1_minus_d2_int_pos :≡ 1 - d2_int > 0
    subprob_1_minus_d2_int_pos_proof ⇐ show subprob_1_minus_d2_int_pos by sorry
    subprob_false_if_n_gt_m :≡ False
    subprob_false_if_n_gt_m_proof ⇐ show subprob_false_if_n_gt_m by sorry

  subprob_false_if_n_gt_m_lifted :≡ (n_val > m_val) → False
  subprob_false_if_n_gt_m_lifted_proof ⇐ show subprob_false_if_n_gt_m_lifted by sorry

  -- Conclude m_val = n_val by trichotomy
  subprob_m_val_eq_n_val :≡ m_val = n_val
  subprob_m_val_eq_n_val_proof ⇐ show subprob_m_val_eq_n_val by sorry
  subprob_a_eq_b :≡ a = b
  subprob_a_eq_b_proof ⇐ show subprob_a_eq_b by sorry

  -- Step 5: Solve for a, using a=b
  subst_b_eq_a_in_hm_eq :≡ a + a^2 = 2^m_val
  subst_b_eq_a_in_hm_eq_proof ⇐ show subst_b_eq_a_in_hm_eq by sorry
  prod_form_a_aplus1 :≡ a * (a+1) = 2^m_val
  prod_form_a_aplus1_proof ⇐ show prod_form_a_aplus1 by sorry

  subprob_a_ap1_coprime :≡ Nat.Coprime a (a+1)
  subprob_a_ap1_coprime_proof ⇐ show subprob_a_ap1_coprime by sorry

  subprob_a_is_pow2 :≡ ∃ x : ℕ, a = 2^x
  subprob_a_is_pow2_proof ⇐ show subprob_a_is_pow2 by sorry
  ⟨x_val, ha_eq_2x⟩ := subprob_a_is_pow2_proof

  subprob_ap1_is_pow2 :≡ ∃ y : ℕ, a+1 = 2^y
  subprob_ap1_is_pow2_proof ⇐ show subprob_ap1_is_pow2 by sorry
  ⟨y_val, hap1_eq_2y⟩ := subprob_ap1_is_pow2_proof

  subprob_y_gt_x :≡ y_val > x_val
  subprob_y_gt_x_proof ⇐ show subprob_y_gt_x by sorry

  subprob_2y_minus_2x_eq_1_int :≡ (2:ℤ)^y_val - (2:ℤ)^x_val = 1
  subprob_2y_minus_2x_eq_1_int_proof ⇐ show subprob_2y_minus_2x_eq_1_int by sorry

  subprob_2x_eq_1_and_2ymx_minus_1_eq_1 :≡ (2:ℤ)^x_val = 1 ∧ (2:ℤ)^(y_val - x_val) - 1 = 1
  subprob_2x_eq_1_and_2ymx_minus_1_eq_1_proof ⇐ show subprob_2x_eq_1_and_2ymx_minus_1_eq_1 by sorry

  subprob_x_val_eq_0 :≡ x_val = 0
  subprob_x_val_eq_0_proof ⇐ show subprob_x_val_eq_0 by sorry

  subprob_a_eq_1_final :≡ a = 1
  subprob_a_eq_1_final_proof ⇐ show subprob_a_eq_1_final by sorry
-/

/- Sketch with proof
variable (a: ℕ) (b: ℕ) (h₀: (0: ℕ) < a ∧ (0: ℕ) < b) (h₁: ∃ (k: ℕ), k > (0: ℕ) ∧ (2: ℕ) ^ k = (a + b ^ (2: ℕ)) * (b + a ^ (2: ℕ)))
play
  h₀_a:= h₀.left
  h₀_b:= h₀.right
  ⟨k_val, hk_k_pos, hk_eq⟩:= h₁
  val1:= a + b^2
  val2:= b + a^2
  subprob_val1_pos:≡ val1 > 0
  subprob_val1_pos_proof ⇐ show subprob_val1_pos by
    have h₀: 0 < a + b ^ 2:= by
      positivity
    simp_all
  subprob_val2_pos:≡ val2 > 0
  subprob_val2_pos_proof ⇐ show subprob_val2_pos by
    have h₀_a: 0 < a:= h₀.1
    have h₀_b: 0 < b:= h₀.2
    simp_all [Nat.pos_iff_ne_zero]
    <;> nlinarith
  subprob_val1_is_pow2:≡ ∃ m: ℕ, val1 = 2^m
  subprob_val1_is_pow2_proof ⇐ show subprob_val1_is_pow2 by
    have H_prime_two: Nat.Prime 2:= Nat.prime_two
    have H_val1_dvd: val1 ∣ 2 ^ k_val:= by
      apply dvd_of_mul_right_eq (c:= val2)
      rw [val1_def, val2_def]
      exact Eq.symm hk_eq
    have H_exists_i_leq_k: ∃ i, i ≤ k_val ∧ val1 = 2 ^ i:= by
      apply (Nat.dvd_prime_pow H_prime_two).mp
      exact H_val1_dvd
    rcases H_exists_i_leq_k with ⟨m, hm_le_k, hm_eq⟩
    exact (Exists.intro m hm_eq)
  ⟨m_val, hm_eq⟩:= subprob_val1_is_pow2_proof
  subprob_val2_is_pow2:≡ ∃ n: ℕ, val2 = 2^n
  subprob_val2_is_pow2_proof ⇐ show subprob_val2_is_pow2 by
    have h_prod_eq: 2 ^ k_val = val1 * val2:= by rw [hk_eq, ← val1_def, ← val2_def]
    rw [hm_eq] at h_prod_eq
    have val2_ne_zero: val2 ≠ 0:= Nat.pos_iff_ne_zero.mp subprob_val2_pos_proof
    have val2_ge_one: val2 ≥ 1:= Nat.one_le_iff_ne_zero.mpr val2_ne_zero
    have h_val2_mul_ge: (2 ^ m_val) * val2 ≥ (2 ^ m_val) * 1:= Nat.mul_le_mul_left (2 ^ m_val) val2_ge_one
    rw [Nat.mul_one] at h_val2_mul_ge
    rw [← h_prod_eq] at h_val2_mul_ge
    have h_base: 1 < 2:= by norm_num
    have k_val_ge_m_val: k_val ≥ m_val:= (Nat.pow_le_iff_le_right h_base).mp h_val2_mul_ge
    have h_2_m_nonzero: 2 ^ m_val ≠ 0:= Nat.pow_eq_zero.not.mpr (by simp)
    have val2_eq_div: val2 = (2 ^ k_val) / (2 ^ m_val):= by
      apply Nat.eq_div_of_mul_eq_right
      exact h_2_m_nonzero
      exact h_prod_eq.symm
    have div_pow_eq_pow_sub: (2 ^ k_val) / (2 ^ m_val) = 2 ^ (k_val - m_val):= by
      apply Eq.symm
      apply Nat.eq_div_of_mul_eq_left
      exact h_2_m_nonzero
      have h_prod_pow: 2 ^ (k_val - m_val) * 2 ^ m_val = 2 ^ ((k_val - m_val) + m_val):= by
        rw [Nat.pow_add]
      have h_exp_sum: (k_val - m_val) + m_val = k_val:= by
        exact Nat.sub_add_cancel k_val_ge_m_val
      rw [h_exp_sum] at h_prod_pow
      exact h_prod_pow
    rw [div_pow_eq_pow_sub] at val2_eq_div
    use (k_val - m_val)
  ⟨n_val, hn_eq⟩:= subprob_val2_is_pow2_proof
  subprob_m_val_ge_1:≡ m_val ≥ 1
  subprob_m_val_ge_1_proof ⇐ show subprob_m_val_ge_1 by
    by_contra! h
    rw [hm_eq] at val1_def
    simp_all
    <;> nlinarith
  subprob_n_val_ge_1:≡ n_val ≥ 1
  subprob_n_val_ge_1_proof ⇐ show subprob_n_val_ge_1 by
    have h₀: val2 ≥ 2:= by
      rw [val2_def]
      nlinarith [h₀_a, h₀_b]
    have h₁: n_val ≥ 1:= by
      rw [hn_eq] at h₀
      cases' n_val with n_val
      · simp at h₀
      · simp
    exact h₁
  subprob_apb2_even:≡ (a + b^2) % 2 = 0
  subprob_apb2_even_proof ⇐ show subprob_apb2_even by
    have h: val1 % 2 = 0:= by
      rw [hm_eq]
      induction m_val with
      | zero => contradiction
      | succ m_val ih =>
        simp [Nat.pow_succ, Nat.mul_mod, ih]
    simp [val1_def] at h
    exact h
  subprob_parity_b_sq_eq_b:≡ b^2 % 2 = b % 2
  subprob_parity_b_sq_eq_b_proof ⇐ show subprob_parity_b_sq_eq_b by
    have h: b % 2 = 0 ∨ b % 2 = 1:= by omega
    rcases h with (h | h)
    simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
    simp [h, pow_two, Nat.mul_mod, Nat.add_mod]
  subprob_apb_even:≡ (a + b) % 2 = 0
  subprob_apb_even_proof ⇐ show subprob_apb_even by
    have h₀_parity: a % 2 = 0 ∨ a % 2 = 1:= by omega
    have h₁_parity: b % 2 = 0 ∨ b % 2 = 1:= by omega
    rcases h₀_parity with (ha | ha) <;> rcases h₁_parity with (hb | hb) <;>
      simp [ha, hb, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, Nat.mod_mod] at *
    <;>
      omega
  subprob_apbm1_pos:≡ a + b - 1 > 0
  subprob_apbm1_pos_proof ⇐ show subprob_apbm1_pos by
    have h₀: a + b - 1 > 0:= by
      omega
    exact h₀
  subprob_apbm1_odd:≡ (a + b - 1) % 2 = 1
  subprob_apbm1_odd_proof ⇐ show subprob_apbm1_odd by
    have h: (a + b) % 2 = 0:= subprob_apb_even_proof
    omega
  lhs_int: ℤ:= ((a: ℤ) + (b: ℤ)^2) - ((b: ℤ) + (a: ℤ)^2)
  rhs_int: ℤ:= (2: ℤ)^m_val - (2: ℤ)^n_val
  subprob_lhs_eq_rhs_int:≡ lhs_int = rhs_int
  subprob_lhs_eq_rhs_int_proof ⇐ show subprob_lhs_eq_rhs_int by
    simp_all only [val1_def, val2_def, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_sub,
      Nat.cast_one, Nat.cast_zero]
    ring
    <;> simp_all
    <;> linarith
  subprob_lhs_factor_int:≡ lhs_int = ((a: ℤ) - (b: ℤ)) * (1 - ((a: ℤ) + (b: ℤ)))
  subprob_lhs_factor_int_proof ⇐ show subprob_lhs_factor_int by
    ring_nf
    simp_all only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub, Nat.cast_one, Nat.cast_zero]
    linarith
  term_1_minus_apb_int:= 1 - ((a: ℤ) + (b: ℤ))
  subprob_1_minus_apb_neq_0:≡ term_1_minus_apb_int ≠ 0
  subprob_1_minus_apb_neq_0_proof ⇐ show subprob_1_minus_apb_neq_0 by
    simp_all [Nat.pow_succ, Nat.mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega
  subprob_1_minus_apb_is_odd:≡ term_1_minus_apb_int % 2 ≠ 0
  subprob_1_minus_apb_is_odd_proof ⇐ show subprob_1_minus_apb_is_odd by
    have h₀_apb_even: (a + b) % 2 = 0:= subprob_apb_even_proof
    simp [term_1_minus_apb_int_def, h₀_apb_even, Int.emod_eq_of_lt]
    omega
  suppose (h_m_eq_n: m_val = n_val) then
    subprob_rhs_zero_if_m_eq_n:≡ rhs_int = 0
    subprob_rhs_zero_if_m_eq_n_proof ⇐ show subprob_rhs_zero_if_m_eq_n by
      rw [h_m_eq_n] at rhs_int_def
      simp [rhs_int_def]
    subprob_amb_times_omapb_eq_zero:≡ ((a: ℤ) - (b: ℤ)) * term_1_minus_apb_int = 0
    subprob_amb_times_omapb_eq_zero_proof ⇐ show subprob_amb_times_omapb_eq_zero by
      rw [h_m_eq_n] at *
      simp_all
      <;> linarith
    subprob_a_minus_b_eq_zero_if_m_eq_n:≡ (a: ℤ) - (b: ℤ) = 0
    subprob_a_minus_b_eq_zero_if_m_eq_n_proof ⇐ show subprob_a_minus_b_eq_zero_if_m_eq_n by
      have h_rhs_zero: rhs_int = 0:= by
        rw [h_m_eq_n] at rhs_int_def
        simp_all
      rw [h_rhs_zero] at subprob_lhs_eq_rhs_int_proof
      have h_amb_zero: (a: ℤ) - (b: ℤ) = 0:= by
        apply eq_of_sub_eq_zero
        apply mul_left_cancel₀ (sub_ne_zero.mpr subprob_1_minus_apb_neq_0_proof)
        linarith
      exact h_amb_zero
    subprob_a_eq_b_if_m_eq_n:≡ a = b
    subprob_a_eq_b_if_m_eq_n_proof ⇐ show subprob_a_eq_b_if_m_eq_n by
      have h₀: a = b:= by
        have h₁: m_val = n_val:= h_m_eq_n
        simp_all [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
      simp_all
  subprob_a_eq_b_if_m_eq_n_lifted:≡ (m_val = n_val) → a = b
  subprob_a_eq_b_if_m_eq_n_lifted_proof ⇐ show subprob_a_eq_b_if_m_eq_n_lifted by
    intro h
    have h₀: a = b:= by
      exact subprob_a_eq_b_if_m_eq_n_proof h
    exact h₀
  suppose (h_m_gt_n: m_val > n_val) then
    p_val1:= m_val - n_val
    subprob_p_val1_pos:≡ p_val1 > 0
    subprob_p_val1_pos_proof ⇐ show subprob_p_val1_pos by
      have h_p_val1_pos: p_val1 > 0:= by
        rw [p_val1_def]
        exact Nat.sub_pos_of_lt h_m_gt_n
      exact h_p_val1_pos
    subprob_rhs_factor_if_m_gt_n:≡ rhs_int = (2: ℤ)^n_val * ((2: ℤ)^p_val1 - 1)
    subprob_rhs_factor_if_m_gt_n_proof ⇐ show subprob_rhs_factor_if_m_gt_n by
      rw [rhs_int_def]
      rw [show m_val = n_val + p_val1 by omega]
      simp [pow_add, mul_sub, mul_one, mul_comm]
      <;> ring
    term_2p1_minus_1_int:= (2: ℤ)^p_val1 - 1
    subprob_2p1_minus_1_is_odd:≡ term_2p1_minus_1_int % 2 ≠ 0
    subprob_2p1_minus_1_is_odd_proof ⇐ show subprob_2p1_minus_1_is_odd by
      simp only [term_2p1_minus_1_int_def]
      have h: p_val1 > 0:= by linarith
      have h₁: (2: ℤ) ^ p_val1 % 2 = 0:= by
        induction p_val1 with
        | zero => contradiction
        | succ p_val1 ih =>
          simp [pow_succ, Int.mul_emod, ih]
      omega
    subprob_2p1_minus_1_pos:≡ term_2p1_minus_1_int > 0
    subprob_2p1_minus_1_pos_proof ⇐ show subprob_2p1_minus_1_pos by
      rw [term_2p1_minus_1_int_def]
      rw [gt_iff_lt]
      rw [Int.sub_pos]
      rw [← pow_zero (2: ℤ)]
      have h_base_gt_one: (2: ℤ) > 1:= by
        norm_num
      apply pow_lt_pow_of_lt_right
      exact h_base_gt_one
      exact subprob_p_val1_pos_proof
    subprob_rhs_pos_if_m_gt_n:≡ rhs_int > 0
    subprob_rhs_pos_if_m_gt_n_proof ⇐ show subprob_rhs_pos_if_m_gt_n by
      have h: rhs_int > 0:= by
        rw [rhs_int_def]
        exact sub_pos.mpr (pow_lt_pow_right (by norm_num) h_m_gt_n)
      exact h
    subprob_lhs_pos_if_m_gt_n:≡ lhs_int > 0
    subprob_lhs_pos_if_m_gt_n_proof ⇐ show subprob_lhs_pos_if_m_gt_n by
      rw [subprob_lhs_eq_rhs_int_proof]
      exact subprob_rhs_pos_if_m_gt_n_proof
    subprob_a_lt_b_if_m_gt_n:≡ a < b
    subprob_a_lt_b_if_m_gt_n_proof ⇐ show subprob_a_lt_b_if_m_gt_n by
      have h_eq_factored: ((↑a: ℤ) - (↑b: ℤ)) * ((1: ℤ) - ((↑a: ℤ) + (↑b: ℤ))) = rhs_int:=
        Eq.trans subprob_lhs_factor_int_proof.symm subprob_lhs_eq_rhs_int_proof
      have h_eq_factored': ((↑a: ℤ) - (↑b: ℤ)) * term_1_minus_apb_int = rhs_int:= by
        rw [term_1_minus_apb_int_def]
        exact h_eq_factored
      have h_rhs_pos: rhs_int > (0: ℤ):= by
        exact subprob_rhs_pos_if_m_gt_n_proof
      have h_lhs_pos: ((↑a: ℤ) - (↑b: ℤ)) * term_1_minus_apb_int > (0: ℤ):= by
        rw [h_eq_factored']
        exact h_rhs_pos
      have ha_ge_1: a ≥ 1:= by exact h₀_a
      have hb_ge_1: b ≥ 1:= by exact h₀_b
      have hapb_ge_2: a + b ≥ 2:= by linarith [ha_ge_1, hb_ge_1]
      have hapb_int_ge_2: (↑(a + b): ℤ) ≥ (2: ℤ):= by norm_cast
      have hapb_int_eq: (↑(a + b): ℤ) = (↑a: ℤ) + (↑b: ℤ):= by norm_cast
      have hapb_int_ge_2': (↑a: ℤ) + (↑b: ℤ) ≥ (2: ℤ):= by
        rw [← hapb_int_eq]
        exact hapb_int_ge_2
      have term_1_minus_apb_int_lt_0: term_1_minus_apb_int < (0: ℤ):= by
        rw [term_1_minus_apb_int_def]
        linarith [hapb_int_ge_2']
      have h_amb_lt_0: (↑a: ℤ) - (↑b: ℤ) < (0: ℤ):= by
        exact neg_of_mul_pos_left h_lhs_pos term_1_minus_apb_int_lt_0.le
      have h_a_lt_b_int: (↑a: ℤ) < (↑b: ℤ):= by
        exact sub_lt_zero.mp h_amb_lt_0
      exact Int.ofNat_lt.mp h_a_lt_b_int
    subprob_2pown_dvd_a_minus_b_int:≡ (2: ℤ)^n_val ∣ ((a: ℤ) - (b: ℤ))
    subprob_2pown_dvd_a_minus_b_int_proof ⇐ show subprob_2pown_dvd_a_minus_b_int by
      have h_eq_prod_correct: (((↑a): ℤ) - (↑b)) * term_1_minus_apb_int = (2: ℤ) ^ n_val * term_2p1_minus_1_int:= by
        rw [← term_1_minus_apb_int_def] at subprob_lhs_factor_int_proof
        rw [← subprob_lhs_factor_int_proof]
        rw [← term_2p1_minus_1_int_def] at subprob_rhs_factor_if_m_gt_n_proof
        rw [← subprob_rhs_factor_if_m_gt_n_proof]
        exact subprob_lhs_eq_rhs_int_proof
      have h_dvd_prod: (2: ℤ) ^ n_val ∣ (((↑a): ℤ) - (↑b)) * term_1_minus_apb_int:= by
        rw [h_eq_prod_correct]
        apply dvd_mul_right
      have hn_pos: 0 < n_val:= by
        apply (Iff.mpr Nat.pos_iff_ne_zero)
        intro h_n_zero_eq
        rw [h_n_zero_eq] at subprob_n_val_ge_1_proof
        contradiction
      have h_gcd_eq_1: Int.gcd ((2: ℤ) ^ n_val) term_1_minus_apb_int = (1: ℕ):= by
        apply Int.gcd_eq_one_iff_coprime.mpr
        apply (IsCoprime.pow_left_iff hn_pos).mpr
        rw [Prime.coprime_iff_not_dvd Int.prime_two]
        rw [← Int.modEq_zero_iff_dvd]
        exact subprob_1_minus_apb_is_odd_proof
      apply Int.dvd_of_dvd_mul_left_of_gcd_one h_dvd_prod h_gcd_eq_1
    ⟨d1_int, hd1_int_def⟩:= subprob_2pown_dvd_a_minus_b_int_proof
    subprob_d1_int_neg:≡ d1_int < 0
    subprob_d1_int_neg_proof ⇐ show subprob_d1_int_neg by
      have h_a_lt_b_int: (↑a: ℤ) < (↑b: ℤ):= by
        exact Int.ofNat_lt.mpr subprob_a_lt_b_if_m_gt_n_proof
      have h_diff_neg: (↑a: ℤ) - (↑b: ℤ) < 0:= by
        linarith [h_a_lt_b_int]
      have h_2_pos: (2: ℤ) > 0:= by norm_num
      have h_2pown_pos: (2: ℤ) ^ n_val > 0:= by
        apply pow_pos
        exact h_2_pos
      have h_prod_neg: (2: ℤ) ^ n_val * d1_int < 0:= by
        rw [← hd1_int_def]
        exact h_diff_neg
      exact Left.neg_of_mul_neg_left h_prod_neg (le_of_lt h_2pown_pos)
    eq_for_a_plus_a_sq:≡ (a:ℤ) + (a:ℤ)^2 = (2:ℤ)^n_val * (1 + d1_int)
    eq_for_a_plus_a_sq_proof ⇐ show eq_for_a_plus_a_sq by
      have h₀: (a: ℤ) + (a: ℤ) ^ 2 = (2: ℤ) ^ n_val * (1 + d1_int):= by
        linarith [hd1_int_def, subprob_rhs_factor_if_m_gt_n_proof, subprob_2p1_minus_1_pos_proof,
          subprob_2p1_minus_1_is_odd_proof, subprob_rhs_pos_if_m_gt_n_proof, subprob_lhs_pos_if_m_gt_n_proof,
          subprob_a_lt_b_if_m_gt_n_proof, subprob_2pown_dvd_a_minus_b_int_proof, subprob_d1_int_neg_proof]
      exact h₀
    subprob_a_plus_a_sq_pos:≡ (a:ℤ) + (a:ℤ)^2 > 0
    subprob_a_plus_a_sq_pos_proof ⇐ show subprob_a_plus_a_sq_pos by
      have h₀_a: (0: ℕ) < a:= h₀.1
      have h₀_a': (1: ℕ) ≤ a:= by linarith
      have h₀_a_sq: (0: ℕ) < a ^ 2:= by positivity
      have h₀_a_sum: (0: ℕ) < a + a ^ 2:= by linarith
      norm_cast at h₀_a_sum
      linarith
    subprob_1_plus_d1_int_pos:≡ 1 + d1_int > 0
    subprob_1_plus_d1_int_pos_proof ⇐ show subprob_1_plus_d1_int_pos by
      have h: (1: ℤ) + d1_int > 0:= by
        have h₀: (↑(a): ℤ) + (↑(a): ℤ) ^ (2: ℕ) > 0:= subprob_a_plus_a_sq_pos_proof
        have h₁: (↑(a): ℤ) + (↑(a): ℤ) ^ (2: ℕ) = (2: ℤ) ^ n_val * ((1: ℤ) + d1_int):= eq_for_a_plus_a_sq_proof
        have h₂: (2: ℤ) ^ n_val > 0:= by positivity
        exact mul_pos_iff_of_pos_right h₂ |>.mp (by linarith)
      exact h
    subprob_false_if_m_gt_n:≡ False
    subprob_false_if_m_gt_n_proof ⇐ show subprob_false_if_m_gt_n by
      have h₀:= hk_eq
      simp_all [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      omega
  subprob_false_if_m_gt_n_lifted:≡ (m_val > n_val) → False
  subprob_false_if_m_gt_n_lifted_proof ⇐ show subprob_false_if_m_gt_n_lifted by
    intro h_m_gt_n
    have h_contradiction:= subprob_false_if_m_gt_n_proof h_m_gt_n
    exact h_contradiction
  suppose (h_n_gt_m: n_val > m_val) then
    p_val2:= n_val - m_val
    subprob_p_val2_pos:≡ p_val2 > 0
    subprob_p_val2_pos_proof ⇐ show subprob_p_val2_pos by
      have h: n_val > m_val:= h_n_gt_m
      rw [p_val2_def]
      omega
    subprob_rhs_factor_if_n_gt_m:≡ rhs_int = -((2: ℤ)^m_val * ((2: ℤ)^p_val2 - 1))
    subprob_rhs_factor_if_n_gt_m_proof ⇐ show subprob_rhs_factor_if_n_gt_m by
      have h_n_val: n_val = m_val + p_val2:= by omega
      rw [h_n_val] at rhs_int_def
      rw [rhs_int_def]
      ring_nf
      <;> simp_all
      <;> omega
    term_2p2_minus_1_int:= (2: ℤ)^p_val2 - 1
    subprob_2p2_minus_1_is_odd:≡ term_2p2_minus_1_int % 2 ≠ 0
    subprob_2p2_minus_1_is_odd_proof ⇐ show subprob_2p2_minus_1_is_odd by
      simp [term_2p2_minus_1_int_def]
      have h: p_val2 > 0:= subprob_p_val2_pos_proof
      have h': (2: ℤ) ^ p_val2 % 2 = 0:= by
        induction p_val2 with
        | zero => contradiction
        | succ p_val2 ih =>
          simp [pow_succ, Int.mul_emod, ih]
      omega
    subprob_2p2_minus_1_pos:≡ term_2p2_minus_1_int > 0
    subprob_2p2_minus_1_pos_proof ⇐ show subprob_2p2_minus_1_pos by
      rw [term_2p2_minus_1_int_def]
      apply Int.sub_pos.mpr
      apply _root_.one_lt_pow
      . norm_num
      exact Nat.pos_iff_ne_zero.mp subprob_p_val2_pos_proof
    subprob_rhs_neg_if_n_gt_m:≡ rhs_int < 0
    subprob_rhs_neg_if_n_gt_m_proof ⇐ show subprob_rhs_neg_if_n_gt_m by
      have h_n_gt_m: n_val > m_val:= h_n_gt_m
      rw [subprob_rhs_factor_if_n_gt_m_proof]
      simp [term_2p2_minus_1_int_def]
      linarith [subprob_2p2_minus_1_pos_proof, subprob_2p2_minus_1_is_odd_proof]
    subprob_lhs_neg_if_n_gt_m:≡ lhs_int < 0
    subprob_lhs_neg_if_n_gt_m_proof ⇐ show subprob_lhs_neg_if_n_gt_m by
      have h_lhs_eq_rhs: lhs_int = rhs_int:= subprob_lhs_eq_rhs_int_proof
      have h_rhs_neg: rhs_int < 0:= subprob_rhs_neg_if_n_gt_m_proof
      rw [h_lhs_eq_rhs]
      exact h_rhs_neg
    subprob_a_gt_b_if_n_gt_m:≡ a > b
    subprob_a_gt_b_if_n_gt_m_proof ⇐ show subprob_a_gt_b_if_n_gt_m by
      have H_lhs_neg: lhs_int < (0: ℤ):= subprob_lhs_neg_if_n_gt_m_proof
      have H_lhs_factor: lhs_int = ((↑(a): ℤ) - (↑(b): ℤ)) * term_1_minus_apb_int:= by
        rw [subprob_lhs_factor_int_proof]
        rw [term_1_minus_apb_int_def]
      have H_prod_neg: ((↑a: ℤ) - (↑b: ℤ)) * term_1_minus_apb_int < 0:= by
        rwa [H_lhs_factor] at H_lhs_neg
      have H_a_pos_int: (↑a: ℤ) > (0: ℤ):= Int.ofNat_pos.mpr h₀_a
      have H_b_pos_int: (↑b: ℤ) > (0: ℤ):= Int.ofNat_pos.mpr h₀_b
      have H_a_ge_1_nat: a ≥ 1:= Nat.succ_le_of_lt h₀_a
      have H_b_ge_1_nat: b ≥ 1:= Nat.succ_le_of_lt h₀_b
      have H_apb_ge_2_nat: a + b ≥ 2:= Nat.add_le_add H_a_ge_1_nat H_b_ge_1_nat
      have H_apb_ge_2_int: (↑(a + b): ℤ) ≥ (2: ℤ):= by norm_cast
      have H_term_1_minus_apb_le_neg_1_int: term_1_minus_apb_int ≤ (-1: ℤ):= by
        rw [term_1_minus_apb_int_def]
        have H_neg_1_eq_1_minus_2: (-1: ℤ) = (1: ℤ) - (2: ℤ):= by norm_num
        rw [H_neg_1_eq_1_minus_2]
        apply sub_le_sub_left H_apb_ge_2_int (1: ℤ)
      have H_neg_1_lt_0: (-1: ℤ) < (0: ℤ):= by norm_num
      have H_term_1_minus_apb_neg: term_1_minus_apb_int < (0: ℤ):= lt_of_le_of_lt H_term_1_minus_apb_le_neg_1_int H_neg_1_lt_0
      have H_prod_ordered: term_1_minus_apb_int * ((↑a: ℤ) - (↑b: ℤ)) < 0:= by
        rw [mul_comm]
        exact H_prod_neg
      have H_iff: term_1_minus_apb_int * ((↑a: ℤ) - (↑b: ℤ)) < 0 ↔ (0: ℤ) < ((↑a: ℤ) - (↑b: ℤ)):=
        smul_neg_iff_of_neg_left H_term_1_minus_apb_neg
      have H_a_minus_b_pos_int: (0: ℤ) < (↑a: ℤ) - (↑b: ℤ):= H_iff.mp H_prod_ordered
      have H_a_gt_b_int: (↑a: ℤ) > (↑b: ℤ):= Int.sub_pos.mp H_a_minus_b_pos_int
      exact Nat.cast_lt.mp H_a_gt_b_int
    subprob_2powm_dvd_a_minus_b_int:≡ (2: ℤ)^m_val ∣ ((a: ℤ) - (b: ℤ))
    subprob_2powm_dvd_a_minus_b_int_proof ⇐ show subprob_2powm_dvd_a_minus_b_int by
      have h_eq: ((↑(a): ℤ) - (↑(b): ℤ)) * term_1_minus_apb_int = -((2: ℤ) ^ m_val * term_2p2_minus_1_int):= by
        have h_eq_step:= subprob_lhs_eq_rhs_int_proof
        rw [subprob_lhs_factor_int_proof] at h_eq_step
        rw [subprob_rhs_factor_if_n_gt_m_proof] at h_eq_step
        rw [←term_1_minus_apb_int_def] at h_eq_step
        rw [←term_2p2_minus_1_int_def] at h_eq_step
        exact h_eq_step
      have h_dvd: (2: ℤ) ^ m_val ∣ ((↑(a): ℤ) - (↑(b): ℤ)) * term_1_minus_apb_int:= by
        rw [h_eq]
        apply dvd_neg.mpr
        apply dvd_mul_right
      have h_gcd: Int.gcd ((2: ℤ) ^ m_val) term_1_minus_apb_int = (1: ℕ):= by
        apply Int.gcd_eq_one_iff_coprime.mpr
        have h_m_val_pos: m_val > 0:= Nat.lt_of_succ_le subprob_m_val_ge_1_proof
        apply (IsCoprime.pow_left_iff h_m_val_pos).mpr
        apply Int.coprime_iff_nat_coprime.mpr
        dsimp
        apply Nat.coprime_two_left.mpr
        have h_odd_int: Odd term_1_minus_apb_int:= Int.odd_iff.mpr (Int.emod_two_ne_zero.mp subprob_1_minus_apb_is_odd_proof)
        exact Int.natAbs_odd.mpr h_odd_int
      exact Int.dvd_of_dvd_mul_left_of_gcd_one h_dvd h_gcd
    ⟨d2_int, hd2_int_def⟩:= subprob_2powm_dvd_a_minus_b_int_proof
    subprob_d2_int_pos:≡ d2_int > 0
    subprob_d2_int_pos_proof ⇐ show subprob_d2_int_pos by
      have h₀: (↑(a): ℤ) - (↑(b): ℤ) = (2: ℤ) ^ m_val * d2_int:= hd2_int_def
      have h₁: a > b:= subprob_a_gt_b_if_n_gt_m_proof
      have h₂: (↑(a): ℤ) - (↑(b): ℤ) > 0:= by simp [h₁]
      rw [h₀] at h₂
      have h₃: (2: ℤ) ^ m_val > 0:= by positivity
      exact mul_pos_iff_of_pos_left h₃ |>.mp h₂
    eq_for_b_plus_b_sq:≡ (b:ℤ) + (b:ℤ)^2 = (2:ℤ)^m_val * (1 - d2_int)
    eq_for_b_plus_b_sq_proof ⇐ show eq_for_b_plus_b_sq by
      rw [← sub_eq_zero] at hd2_int_def
      ring_nf at hd2_int_def ⊢
      linarith [subprob_d2_int_pos_proof]
    subprob_b_plus_b_sq_pos:≡ (b:ℤ) + (b:ℤ)^2 > 0
    subprob_b_plus_b_sq_pos_proof ⇐ show subprob_b_plus_b_sq_pos by
      have h_b_pos: (0: ℤ) < b:= by simp [h₀_b]
      simp [h_b_pos]
      linarith [pow_pos h_b_pos 2]
    subprob_1_minus_d2_int_pos:≡ 1 - d2_int > 0
    subprob_1_minus_d2_int_pos_proof ⇐ show subprob_1_minus_d2_int_pos by
      have h₀: (↑(b): ℤ) + (↑(b): ℤ) ^ (2: ℕ) > (0: ℤ):= by
        simp [subprob_b_plus_b_sq_pos_proof]
      have h₁: (2: ℤ) ^ m_val * ((1: ℤ) - d2_int) > (0: ℤ):= by
        rw [← eq_for_b_plus_b_sq_proof]
        simp [h₀]
      have h₂: (2: ℤ) ^ m_val > (0: ℤ):= by
        simp [pow_pos (by norm_num: (0: ℤ) < 2) m_val]
      exact mul_pos_iff_of_pos_left h₂ |>.mp h₁
    subprob_false_if_n_gt_m:≡ False
    subprob_false_if_n_gt_m_proof ⇐ show subprob_false_if_n_gt_m by
      have h₀: 0 < a ∧ 0 < b:= ⟨h₀_a, h₀_b⟩
      have h₁: ∃ k: ℕ, k > 0 ∧ 2 ^ k = (a + b ^ 2) * (b + a ^ 2):= h₁
      rcases h₁ with ⟨k_val, hk_k_pos, hk_eq⟩
      norm_num at hk_eq
      have h₂: a = b:= by
        linarith [subprob_apb_even_proof, subprob_parity_b_sq_eq_b_proof, subprob_apb2_even_proof]
      rw [h₂] at hk_eq
      norm_num at hk_eq
      linarith [hk_eq]
  subprob_false_if_n_gt_m_lifted:≡ (n_val > m_val) → False
  subprob_false_if_n_gt_m_lifted_proof ⇐ show subprob_false_if_n_gt_m_lifted by
    intro h_n_gt_m
    have h₁:= subprob_false_if_n_gt_m_proof h_n_gt_m
    exact h₁
  subprob_m_val_eq_n_val:≡ m_val = n_val
  subprob_m_val_eq_n_val_proof ⇐ show subprob_m_val_eq_n_val by
    by_contra h
    have h₁: m_val > n_val ∨ n_val > m_val:= by omega
    rcases h₁ with (h₁ | h₁)
    . exact subprob_false_if_m_gt_n_lifted_proof h₁
    . exact subprob_false_if_n_gt_m_lifted_proof h₁
  subprob_a_eq_b:≡ a = b
  subprob_a_eq_b_proof ⇐ show subprob_a_eq_b by
    have h₀: a = b:= by
      apply subprob_a_eq_b_if_m_eq_n_proof
      exact subprob_m_val_eq_n_val_proof
    exact h₀
  subst_b_eq_a_in_hm_eq:≡ a + a^2 = 2^m_val
  subst_b_eq_a_in_hm_eq_proof ⇐ show subst_b_eq_a_in_hm_eq by
    rw [subprob_a_eq_b_proof]
    simp_all [val1_def, val2_def]
    <;> simp_all
    <;> linarith
  prod_form_a_aplus1:≡ a * (a+1) = 2^m_val
  prod_form_a_aplus1_proof ⇐ show prod_form_a_aplus1 by
    have h: a + a ^ 2 = 2 ^ m_val:= by assumption
    have h': a * (a + 1) = 2 ^ m_val:= by
      linarith [h]
    exact h'
  subprob_a_ap1_coprime:≡ Nat.Coprime a (a+1)
  subprob_a_ap1_coprime_proof ⇐ show subprob_a_ap1_coprime by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    rw [Nat.gcd_comm]
    simp [Nat.gcd_succ]
  subprob_a_is_pow2:≡ ∃ x: ℕ, a = 2^x
  subprob_a_is_pow2_proof ⇐ show subprob_a_is_pow2 by
    have h_only_prime_divisor_a: ∀ {d: ℕ}, Nat.Prime d → d ∣ a → d = 2:= by
      intro d hd_prime hd_dvd_a
      have hd_dvd_a_mul_ap1: d ∣ a * (a + (1: ℕ)):= by
        rw [← mul_comm]
        exact dvd_mul_of_dvd_right hd_dvd_a (a + 1)
      rw [prod_form_a_aplus1_proof] at hd_dvd_a_mul_ap1
      have hd_dvd_two_pow_m: d ∣ (2: ℕ) ^ m_val:= hd_dvd_a_mul_ap1
      have hd_dvd_two: d ∣ (2: ℕ):= Nat.Prime.dvd_of_dvd_pow hd_prime hd_dvd_two_pow_m
      have hd_eq_one_or_two: d = 1 ∨ d = 2:= Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two d hd_dvd_two
      have hd_ne_one: d ≠ 1:= Nat.Prime.ne_one hd_prime
      exact Or.resolve_left hd_eq_one_or_two hd_ne_one
    have h_a_is_pow2: a = (2: ℕ) ^ a.factors.length:= Nat.eq_prime_pow_of_unique_prime_dvd (Nat.pos_iff_ne_zero.mp h₀_a) h_only_prime_divisor_a
    exact Exists.intro a.factors.length h_a_is_pow2
  ⟨x_val, ha_eq_2x⟩:= subprob_a_is_pow2_proof
  subprob_ap1_is_pow2:≡ ∃ y: ℕ, a+1 = 2^y
  subprob_ap1_is_pow2_proof ⇐ show subprob_ap1_is_pow2 by
    have h_prime_two: Nat.Prime 2:= Nat.prime_two
    have h_step1:= mul_eq_mul_prime_pow (Nat.prime_iff.mp h_prime_two) (show a * (a + 1) = 1 * 2 ^ m_val from by rw [one_mul]; exact prod_form_a_aplus1_proof)
    rcases h_step1 with ⟨i_val, j_val, b_val, c_val, h_sum_ij, h_a_bc, h_a_bpi, h_ap1_cpj⟩
    have h_a_bc_symm: b_val * c_val = 1:= Eq.symm h_a_bc
    have h_b_one: b_val = 1:= Nat.eq_one_of_mul_eq_one_right h_a_bc_symm
    have h_c_one: c_val = 1:= Nat.eq_one_of_mul_eq_one_left h_a_bc_symm
    have h_a_pow: a = 2 ^ i_val:= by rw [h_b_one, one_mul] at h_a_bpi; exact h_a_bpi
    have h_ap1_pow: a + 1 = 2 ^ j_val:= by rw [h_c_one, one_mul] at h_ap1_cpj; exact h_ap1_cpj
    use j_val
  ⟨y_val, hap1_eq_2y⟩:= subprob_ap1_is_pow2_proof
  subprob_y_gt_x:≡ y_val > x_val
  subprob_y_gt_x_proof ⇐ show subprob_y_gt_x by
    have h₀: a = 2 ^ x_val:= ha_eq_2x
    have h₁: a + 1 = 2 ^ y_val:= hap1_eq_2y
    have h₂: y_val > x_val:= by
      apply Nat.lt_of_le_of_ne
      ·
        apply Nat.le_of_not_lt
        intro h
        have h₃: 2 ^ y_val < 2 ^ x_val:= Nat.pow_lt_pow_of_lt_right (by norm_num) h
        linarith
      ·
        intro h
        have h₃: 2 ^ y_val = 2 ^ x_val:= by rw [h]
        linarith
    exact h₂
  subprob_2y_minus_2x_eq_1_int:≡ (2:ℤ)^y_val - (2:ℤ)^x_val = 1
  subprob_2y_minus_2x_eq_1_int_proof ⇐ show subprob_2y_minus_2x_eq_1_int by
    simp_all [Nat.pow_succ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    norm_num
    <;> linarith
  subprob_2x_eq_1_and_2ymx_minus_1_eq_1:≡ (2:ℤ)^x_val = 1 ∧ (2:ℤ)^(y_val - x_val) - 1 = 1
  subprob_2x_eq_1_and_2ymx_minus_1_eq_1_proof ⇐ show subprob_2x_eq_1_and_2ymx_minus_1_eq_1 by
    have h_x_le_y: x_val ≤ y_val:= by linarith [subprob_y_gt_x_proof]
    have h_factor: (2: ℤ) ^ x_val * ((2: ℤ) ^ (y_val - x_val) - 1) = (2: ℤ) ^ y_val - (2: ℤ) ^ x_val:= by
      have h_dist: (2: ℤ) ^ x_val * ((2: ℤ) ^ (y_val - x_val) - 1) = (2: ℤ) ^ x_val * (2: ℤ) ^ (y_val - x_val) - (2: ℤ) ^ x_val:= by
        apply mul_sub_one ((2: ℤ) ^ x_val) ((2: ℤ) ^ (y_val - x_val))
      have h_pow_add: (2: ℤ) ^ x_val * (2: ℤ) ^ (y_val - x_val) = (2: ℤ) ^ (x_val + (y_val - x_val)):= by
        rw [pow_add (2: ℤ) x_val (y_val - x_val)]
      have h_add_sub: x_val + (y_val - x_val) = y_val:= by
        omega
      rw [h_add_sub] at h_pow_add
      rw [h_pow_add] at h_dist
      exact h_dist
    rw [subprob_2y_minus_2x_eq_1_int_proof] at h_factor
    have h_pow_x_nonneg: 0 ≤ (2: ℤ) ^ x_val:= by
      apply pow_nonneg
      norm_num
    have h_mul_eq_one_cases: ((2: ℤ) ^ x_val = 1 ∧ ((2: ℤ) ^ (y_val - x_val) - 1) = 1) ∨ ((2: ℤ) ^ x_val = -1 ∧ ((2: ℤ) ^ (y_val - x_val) - 1) = -1):= (Int.mul_eq_one_iff_eq_one_or_neg_one).mp h_factor
    cases h_mul_eq_one_cases with
    | inl h_one_and_one =>
      exact h_one_and_one
    | inr h_neg_one_and_neg_one =>
      have h_A_eq_neg_one: (2: ℤ) ^ x_val = -1:= h_neg_one_and_neg_one.left
      rw [h_A_eq_neg_one] at h_pow_x_nonneg
      linarith
  subprob_x_val_eq_0:≡ x_val = 0
  subprob_x_val_eq_0_proof ⇐ show subprob_x_val_eq_0 by
    have h₀:= subprob_2x_eq_1_and_2ymx_minus_1_eq_1_proof
    have h₁:= subprob_2y_minus_2x_eq_1_int_proof
    have h₂:= subprob_y_gt_x_proof
    have h₃:= hap1_eq_2y
    have h₄:= ha_eq_2x
    have h₅:= subprob_a_ap1_coprime_proof
    have h₆:= subprob_m_val_eq_n_val_proof
    have h₇:= subprob_a_eq_b_proof
    have h₈:= subprob_false_if_n_gt_m_proof
    have h₉:= subprob_false_if_m_gt_n_proof
    cases' x_val with x_val
    · simp_all
    · exfalso
      simp_all [Nat.pow_succ]
      omega
  subprob_a_eq_1_final:≡ a = 1
  subprob_a_eq_1_final_proof ⇐ show subprob_a_eq_1_final by
    have h_a_eq_b: a = b:= by
      apply subprob_a_eq_b_if_m_eq_n_proof
      apply subprob_m_val_eq_n_val_proof
    have h_a_pow2: a = 1:= by
      apply Eq.symm
      apply Eq.symm
      apply Nat.eq_of_le_of_lt_succ
      · simp_all
      · simp_all
    exact h_a_pow2
  original_target:≡ a = (1: ℕ)
  original_target_proof ⇐ show original_target by
    have h₀: a = 1:= subprob_a_eq_1_final_proof
    exact h₀
-/
