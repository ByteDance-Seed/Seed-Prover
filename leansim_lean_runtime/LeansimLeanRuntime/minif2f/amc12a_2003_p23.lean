import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
open Polynomial Nat Real Classical BigOperators

-- erroneous

theorem amc12a_2003_p23
  (S  : Finset ℕ)
  (h₀ : ∀ (k : ℕ), k ∈ S ↔ 0 < k ∧ ((k * k) : ℕ) ∣ (∏ i in (Finset.Icc 1 9), i !)) :
  S.card = 672  := by
  letI P_val := (∏ i in (Finset.Icc (1 : ℕ) (9 : ℕ)), Nat.factorial i)
  retro' P_val_def : P_val = ∏ i ∈ Finset.Icc (1 : ℕ) (9 : ℕ), i ! := by funext; rfl
  have subprob_P_val_pos_proof : P_val > (0 : ℕ) := by
    mkOpaque
    rw [P_val_def]
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp [Finset.mem_Icc] at hi
    norm_num <;> simp [Nat.factorial_ne_zero]
  letI exponent_p_P_val := fun (p : ℕ) => (Nat.factorization P_val) p
  retro' exponent_p_P_val_def : exponent_p_P_val = fun (p : ℕ) => (Nat.factorization P_val) p := by funext; rfl
  retro' exponent_p_P_val_def' : ∀ (p : ℕ), exponent_p_P_val p = (Nat.factorization P_val) p := by intros; rfl
  have subprob_relation_exponent_P_val_to_factorials_proof : ∀ (p : ℕ) (hp : Nat.Prime p), exponent_p_P_val p = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) p) := by
    mkOpaque
    intro p hp
    rw [exponent_p_P_val_def' p]
    rw [P_val_def]
    have h_nonzero : ∀ (x : ℕ), x ∈ Finset.Icc 1 9 → Nat.factorial x ≠ 0 := by
      intro x hx
      apply Nat.factorial_ne_zero
    have h_map_equality : (Finset.prod (Finset.Icc 1 9) Nat.factorial).factorization = ∑ x ∈ Finset.Icc 1 9, (Nat.factorial x).factorization := Nat.factorization_prod h_nonzero
    rw [h_map_equality]
    rfl
  have subprob_prime_2_proof : Nat.Prime (2 : ℕ) := by
    mkOpaque
    apply Nat.prime_two
  have subprob_exp_P_2_eq_sum_factorization_proof : exponent_p_P_val (2 : ℕ) = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2 : ℕ)) := by
    mkOpaque
    rw [subprob_relation_exponent_P_val_to_factorials_proof 2 subprob_prime_2_proof] <;> simp [exponent_p_P_val_def'] <;> norm_num <;> linarith
  have subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof : ∀ (p j : ℕ), Nat.Prime p → (Nat.factorization (Nat.factorial j) p) = padicValNat p (Nat.factorial j) := by
    mkOpaque
    intro p j hp
    simp [padicValNat, Nat.factorization, hp] <;> rfl
  letI sum_factorization_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2 : ℕ))
  retro' sum_factorization_2_jfact_def : sum_factorization_2_jfact = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization j !) (2 : ℕ) := by funext; rfl
  letI sum_padicValNat_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (2 : ℕ) (Nat.factorial j)
  retro' sum_padicValNat_2_jfact_def : sum_padicValNat_2_jfact = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (2 : ℕ) j ! := by funext; rfl
  have subprob_sum_factorization_eq_sum_padicValNat_for_2_proof : sum_factorization_2_jfact = sum_padicValNat_2_jfact := by
    mkOpaque
    have h₁ : ∀ j : ℕ, (Nat.factorization j !) 2 = padicValNat 2 j ! := by
      intro j
      apply subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof
      exact subprob_prime_2_proof
    simp_all [Finset.sum_congr]
  have subprob_exp_P_2_eq_sum_padicValNat_proof : exponent_p_P_val (2 : ℕ) = sum_padicValNat_2_jfact := by
    mkOpaque
    have h₀ := subprob_sum_factorization_eq_sum_padicValNat_for_2_proof
    simp_all
  letI val_1fact_2 := padicValNat (2 : ℕ) (Nat.factorial (1 : ℕ))
  retro' val_1fact_2_def : val_1fact_2 = padicValNat (2 : ℕ) (1 : ℕ)! := by funext; rfl
  letI val_2fact_2 := padicValNat (2 : ℕ) (Nat.factorial (2 : ℕ))
  retro' val_2fact_2_def : val_2fact_2 = padicValNat (2 : ℕ) (2 : ℕ)! := by funext; rfl
  letI val_3fact_2 := padicValNat (2 : ℕ) (Nat.factorial (3 : ℕ))
  retro' val_3fact_2_def : val_3fact_2 = padicValNat (2 : ℕ) (3 : ℕ)! := by funext; rfl
  letI val_4fact_2 := padicValNat (2 : ℕ) (Nat.factorial (4 : ℕ))
  retro' val_4fact_2_def : val_4fact_2 = padicValNat (2 : ℕ) (4 : ℕ)! := by funext; rfl
  letI val_5fact_2 := padicValNat (2 : ℕ) (Nat.factorial (5 : ℕ))
  retro' val_5fact_2_def : val_5fact_2 = padicValNat (2 : ℕ) (5 : ℕ)! := by funext; rfl
  letI val_6fact_2 := padicValNat (2 : ℕ) (Nat.factorial (6 : ℕ))
  retro' val_6fact_2_def : val_6fact_2 = padicValNat (2 : ℕ) (6 : ℕ)! := by funext; rfl
  letI val_7fact_2 := padicValNat (2 : ℕ) (Nat.factorial (7 : ℕ))
  retro' val_7fact_2_def : val_7fact_2 = padicValNat (2 : ℕ) (7 : ℕ)! := by funext; rfl
  letI val_8fact_2 := padicValNat (2 : ℕ) (Nat.factorial (8 : ℕ))
  retro' val_8fact_2_def : val_8fact_2 = padicValNat (2 : ℕ) (8 : ℕ)! := by funext; rfl
  letI val_9fact_2 := padicValNat (2 : ℕ) (Nat.factorial (9 : ℕ))
  retro' val_9fact_2_def : val_9fact_2 = padicValNat (2 : ℕ) (9 : ℕ)! := by funext; rfl
  have subprob_1_fact_val_proof : Nat.factorial (1 : ℕ) = (1 : ℕ) := by
    mkOpaque
    simp [Nat.factorial] <;> simp <;> simp <;> simp
  have subprob_padicValNat_2_1_is_0_proof : padicValNat (2 : ℕ) (1 : ℕ) = (0 : ℕ) := by
    mkOpaque
    simp [val_1fact_2_def, subprob_1_fact_val_proof, padicValNat.one]
  have subprob_val_1fact_2_eq_0_proof : val_1fact_2 = (0 : ℕ) := by
    mkOpaque
    rw [val_1fact_2_def, subprob_1_fact_val_proof]
    exact subprob_padicValNat_2_1_is_0_proof
  have subprob_2_fact_val_proof : Nat.factorial (2 : ℕ) = (2 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> simp_all <;> norm_num <;> linarith
  have subprob_padicValNat_2_2_is_1_proof : padicValNat (2 : ℕ) (2 : ℕ) = (1 : ℕ) := by
    mkOpaque
    simp [padicValNat, subprob_2_fact_val_proof] <;> omega
  have subprob_val_2fact_2_eq_1_proof : val_2fact_2 = (1 : ℕ) := by
    mkOpaque
    simp [val_2fact_2_def, subprob_padicValNat_2_2_is_1_proof]
  have subprob_3_fact_val_proof : Nat.factorial (3 : ℕ) = (6 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> norm_num <;> rfl <;> norm_num <;> rfl
  have subprob_6_eq_2_mul_3_proof : (6 : ℕ) = (2 : ℕ) * (3 : ℕ) := by
    mkOpaque
    have h : (3 : ℕ)! = (6 : ℕ) := subprob_3_fact_val_proof
    simp [Nat.factorial, Nat.mul_succ, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  have subprob_2_ne_zero_proof : (2 : ℕ) ≠ (0 : ℕ) := by
    mkOpaque
    decide
  have subprob_3_ne_zero_proof : (3 : ℕ) ≠ (0 : ℕ) := by
    mkOpaque
    decide
  have subprob_padicValNat_2_6_mul_proof : padicValNat (2 : ℕ) ((2 : ℕ) * (3 : ℕ)) = padicValNat (2 : ℕ) (2 : ℕ) + padicValNat (2 : ℕ) (3 : ℕ) := by
    mkOpaque
    rw [padicValNat.mul] <;> simp [Nat.prime_two] <;> rw [padicValNat.self] <;> norm_num <;> simp [Nat.Prime.dvd_iff_not_coprime] <;> norm_num
  have subprob_padicValNat_2_3_is_0_proof : padicValNat (2 : ℕ) (3 : ℕ) = (0 : ℕ) := by
    mkOpaque
    rw [padicValNat.eq_zero_of_not_dvd]
    norm_num <;> decide
  have subprob_1_plus_0_eq_1_proof : (1 : ℕ) + (0 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [Nat.add_zero]
  have subprob_padicValNat_2_6_is_1_proof : padicValNat (2 : ℕ) (6 : ℕ) = (1 : ℕ) := by
    mkOpaque
    simp_all [padicValNat.mul, Nat.Prime.ne_zero, Nat.Prime.ne_one] <;> decide
  have subprob_val_3fact_2_eq_1_proof : val_3fact_2 = (1 : ℕ) := by
    mkOpaque
    simp_all [val_3fact_2_def, subprob_padicValNat_2_6_is_1_proof] <;> decide
  have subprob_4_fact_val_proof : Nat.factorial (4 : ℕ) = (24 : ℕ) := by
    mkOpaque
    norm_num <;> rfl
  have subprob_24_eq_2p3_mul_3_proof : (24 : ℕ) = (2 : ℕ) ^ 3 * (3 : ℕ) := by
    mkOpaque
    norm_num [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] <;> rfl
  have subprob_2p3_ne_zero_proof : (2 : ℕ) ^ 3 ≠ (0 : ℕ) := by
    mkOpaque
    norm_num <;> decide <;> norm_num <;> decide
  have subprob_padicValNat_2_24_mul_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 3 * (3 : ℕ)) = padicValNat (2 : ℕ) ((2 : ℕ) ^ 3) + padicValNat (2 : ℕ) (3 : ℕ) := by
    mkOpaque
    rw [padicValNat.mul] <;> norm_num <;> simp <;> norm_num <;> simp <;> norm_num
  have subprob_padicValNat_2_2p3_is_3_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 3) = (3 : ℕ) := by
    mkOpaque
    rw [padicValNat.pow] <;> simp [Nat.Prime.ne_zero] <;> norm_num <;> rfl
  have subprob_3_plus_0_eq_3_proof : (3 : ℕ) + (0 : ℕ) = (3 : ℕ) := by
    mkOpaque
    apply add_zero <;> simp <;> linarith
  have subprob_padicValNat_2_24_is_3_proof : padicValNat (2 : ℕ) (24 : ℕ) = (3 : ℕ) := by
    mkOpaque
    rw [subprob_24_eq_2p3_mul_3_proof]
    rw [subprob_padicValNat_2_24_mul_proof]
    rw [subprob_padicValNat_2_2p3_is_3_proof]
    simp [subprob_3_plus_0_eq_3_proof]
  have subprob_val_4fact_2_eq_3_proof : val_4fact_2 = (3 : ℕ) := by
    mkOpaque
    rw [val_4fact_2_def]
    rw [subprob_4_fact_val_proof]
    rw [subprob_padicValNat_2_24_is_3_proof] <;> simp
  have subprob_5_fact_val_proof : Nat.factorial (5 : ℕ) = (120 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> norm_num <;> rfl <;> norm_num <;> rfl
  have subprob_120_eq_2p3_mul_15_proof : (120 : ℕ) = (2 : ℕ) ^ 3 * (15 : ℕ) := by
    mkOpaque
    norm_num [Nat.factorial, Nat.pow_succ, Nat.factorial, Nat.pow_succ] <;> decide
  have subprob_15_ne_zero_proof : (15 : ℕ) ≠ (0 : ℕ) := by
    mkOpaque
    norm_num <;> simp_all <;> norm_num <;> linarith
  have subprob_padicValNat_2_120_mul_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 3 * (15 : ℕ)) = padicValNat (2 : ℕ) ((2 : ℕ) ^ 3) + padicValNat (2 : ℕ) (15 : ℕ) := by
    mkOpaque
    rw [padicValNat.mul] <;> simp [subprob_15_ne_zero_proof] <;> norm_num <;> simp [padicValNat.pow] <;> norm_num
  have subprob_padicValNat_2_15_is_0_proof : padicValNat (2 : ℕ) (15 : ℕ) = (0 : ℕ) := by
    mkOpaque
    apply padicValNat.eq_zero_of_not_dvd
    norm_num <;> decide
  have subprob_padicValNat_2_120_is_3_proof : padicValNat (2 : ℕ) (120 : ℕ) = (3 : ℕ) := by
    mkOpaque
    have h₁ := subprob_padicValNat_2_15_is_0_proof
    have h₂ := subprob_padicValNat_2_2p3_is_3_proof
    have h₃ := subprob_padicValNat_2_2_is_1_proof
    have h₄ := subprob_padicValNat_2_3_is_0_proof
    simp_all [padicValNat.mul, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have subprob_val_5fact_2_eq_3_proof : val_5fact_2 = (3 : ℕ) := by
    mkOpaque
    rw [val_5fact_2_def]
    apply subprob_padicValNat_2_120_is_3_proof
  have subprob_6_fact_val_proof : Nat.factorial (6 : ℕ) = (720 : ℕ) := by
    mkOpaque
    norm_num [Nat.factorial]
  have subprob_720_eq_2p4_mul_45_proof : (720 : ℕ) = (2 : ℕ) ^ 4 * (45 : ℕ) := by
    mkOpaque
    have h₀ : (6 : ℕ)! = (720 : ℕ) := subprob_6_fact_val_proof
    simp [h₀, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] <;> decide
  have subprob_2p4_ne_zero_proof : (2 : ℕ) ^ 4 ≠ (0 : ℕ) := by
    mkOpaque
    norm_num <;> decide
  have subprob_45_ne_zero_proof : (45 : ℕ) ≠ (0 : ℕ) := by
    mkOpaque
    norm_num
  have subprob_padicValNat_2_720_mul_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 4 * (45 : ℕ)) = padicValNat (2 : ℕ) ((2 : ℕ) ^ 4) + padicValNat (2 : ℕ) (45 : ℕ) := by
    mkOpaque
    rw [padicValNat.mul] <;> simp [Nat.prime_two] <;> norm_num <;> assumption <;> ring
  have subprob_padicValNat_2_2p4_is_4_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 4) = (4 : ℕ) := by
    mkOpaque
    rw [padicValNat.pow] <;> simp [Nat.Prime.ne_zero] <;> norm_num <;> linarith
  have subprob_padicValNat_2_45_is_0_proof : padicValNat (2 : ℕ) (45 : ℕ) = (0 : ℕ) := by
    mkOpaque
    rw [show 45 = 15 * 3 by norm_num]
    rw [padicValNat.mul] <;> simp [subprob_padicValNat_2_15_is_0_proof] <;> norm_num
  have subprob_4_plus_0_eq_4_proof : (4 : ℕ) + (0 : ℕ) = (4 : ℕ) := by
    mkOpaque
    norm_num <;> decide <;> decide <;> decide <;> decide
  have subprob_padicValNat_2_720_is_4_proof : padicValNat (2 : ℕ) (720 : ℕ) = (4 : ℕ) := by
    mkOpaque
    rw [subprob_720_eq_2p4_mul_45_proof]
    rw [subprob_padicValNat_2_720_mul_proof]
    rw [subprob_padicValNat_2_2p4_is_4_proof, subprob_padicValNat_2_45_is_0_proof]
  have subprob_val_6fact_2_eq_4_proof : val_6fact_2 = (4 : ℕ) := by
    mkOpaque
    simp_all only [val_6fact_2_def, subprob_padicValNat_2_720_is_4_proof] <;> rfl
  have subprob_7_fact_val_proof : Nat.factorial (7 : ℕ) = (5040 : ℕ) := by
    mkOpaque
    rw [Nat.factorial] <;> norm_num <;> rfl
  have subprob_5040_eq_2p4_mul_315_proof : (5040 : ℕ) = (2 : ℕ) ^ 4 * (315 : ℕ) := by
    mkOpaque
    norm_num [Nat.factorial] <;> norm_num <;> ring <;> linarith
  have subprob_315_ne_zero_proof : (315 : ℕ) ≠ (0 : ℕ) := by
    mkOpaque
    decide
  have subprob_padicValNat_2_5040_mul_proof : padicValNat (2 : ℕ) ((2 : ℕ) ^ 4 * (315 : ℕ)) = padicValNat (2 : ℕ) ((2 : ℕ) ^ 4) + padicValNat (2 : ℕ) (315 : ℕ) := by
    mkOpaque
    rw [padicValNat.mul] <;> norm_num <;> assumption <;> ring <;> norm_num <;> assumption
  have subprob_padicValNat_2_315_is_0_proof : padicValNat (2 : ℕ) (315 : ℕ) = (0 : ℕ) := by
    mkOpaque
    rw [padicValNat.eq_zero_of_not_dvd]
    norm_num <;> decide
  have subprob_padicValNat_2_5040_is_4_proof : padicValNat (2 : ℕ) (5040 : ℕ) = (4 : ℕ) := by
    mkOpaque
    rw [subprob_5040_eq_2p4_mul_315_proof]
    rw [subprob_padicValNat_2_5040_mul_proof]
    rw [subprob_padicValNat_2_2p4_is_4_proof]
    rw [subprob_padicValNat_2_315_is_0_proof] <;> simp
  have subprob_val_7fact_2_eq_4_proof : val_7fact_2 = (4 : ℕ) := by
    mkOpaque
    rw [val_7fact_2_def]
    apply subprob_padicValNat_2_5040_is_4_proof
  have subprob_Nat_log_2_8_proof : Nat.log (2 : ℕ) (8 : ℕ) = (3 : ℕ) := by
    mkOpaque
    rw [Nat.log_eq_iff] <;> norm_num <;> linarith [Nat.pow_succ 2 3] <;> apply Nat.log_eq_iff <;> norm_num <;> linarith [Nat.pow_succ 2 3]
  letI legendre_b_8 := (4 : ℕ)
  retro' legendre_b_8_def : legendre_b_8 = (4 : ℕ) := by funext; rfl
  have subprob_legendre_cond_8_proof : Nat.log (2 : ℕ) (8 : ℕ) < legendre_b_8 := by
    mkOpaque
    rw [subprob_Nat_log_2_8_proof]
    rw [legendre_b_8_def]
    linarith
  letI sum_legendre_8fact_raw := ∑ i ∈ Finset.Ico (1 : ℕ) legendre_b_8, (8 : ℕ) / ((2 : ℕ) ^ i)
  retro' sum_legendre_8fact_raw_def : sum_legendre_8fact_raw = ∑ i ∈ Finset.Ico (1 : ℕ) legendre_b_8, (8 : ℕ) / (2 : ℕ) ^ i := by funext; rfl
  have subprob_padicValNat_2_8fact_legendre_proof : padicValNat (2 : ℕ) (Nat.factorial (8 : ℕ)) = sum_legendre_8fact_raw := by
    mkOpaque
    have h_prime_2 : (2 : ℕ).Prime := subprob_prime_2_proof
    haveI : Fact (2 : ℕ).Prime := ⟨h_prime_2⟩
    rw [padicValNat_factorial (p := (2 : ℕ)) (n := (8 : ℕ)) (b := legendre_b_8) subprob_legendre_cond_8_proof]
    rw [sum_legendre_8fact_raw_def]
  have subprob_Ico_1_4_is_123_proof : Finset.Ico (1 : ℕ) (4 : ℕ) = ({(1 : ℕ), (2 : ℕ), (3 : ℕ)} : Finset ℕ) := by
    mkOpaque
    ext x
    simp [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  have subprob_sum_legendre_8fact_set_rewrite_proof : sum_legendre_8fact_raw = ∑ i ∈ ({(1 : ℕ), (2 : ℕ), (3 : ℕ)} : Finset ℕ), (8 : ℕ) / ((2 : ℕ) ^ i) := by
    mkOpaque
    rw [sum_legendre_8fact_raw_def, legendre_b_8_def]
    rw [subprob_Ico_1_4_is_123_proof] <;> simp_all <;> norm_num <;> linarith
  have subprob_sum_legendre_8fact_expanded_proof : (∑ i ∈ ({(1 : ℕ), (2 : ℕ), (3 : ℕ)} : Finset ℕ), (8 : ℕ) / ((2 : ℕ) ^ i)) = (8 : ℕ) / ((2 : ℕ) ^ 1) + (8 : ℕ) / ((2 : ℕ) ^ 2) + (8 : ℕ) / ((2 : ℕ) ^ 3) := by
    mkOpaque
    have h : Finset.Ico (1 : ℕ) (4 : ℕ) = ({1, 2, 3} : Finset ℕ) := by apply subprob_Ico_1_4_is_123_proof
    simp [h, Finset.sum_Ico_succ_top, Nat.div_eq_of_lt] <;> norm_num
  have subprob_term1_8_div_2p1_proof : (8 : ℕ) / (2 : ℕ) ^ 1 = (4 : ℕ) := by
    mkOpaque
    norm_num <;> decide <;> norm_num <;> decide
  have subprob_term2_8_div_2p2_proof : (8 : ℕ) / (2 : ℕ) ^ 2 = (2 : ℕ) := by
    mkOpaque
    norm_num <;> simp_all <;> norm_num <;> linarith
  have subprob_term3_8_div_2p3_proof : (8 : ℕ) / (2 : ℕ) ^ 3 = (1 : ℕ) := by
    mkOpaque
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt] <;> rfl <;> linarith
  have subprob_4_plus_2_plus_1_eq_7_proof : (4 : ℕ) + (2 : ℕ) + (1 : ℕ) = (7 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> norm_num <;> rfl <;> norm_num <;> rfl
  have subprob_sum_legendre_8fact_calc_proof : sum_legendre_8fact_raw = (7 : ℕ) := by
    mkOpaque
    rw [subprob_sum_legendre_8fact_set_rewrite_proof]
    simp [Finset.sum_insert, Finset.sum_singleton, subprob_term1_8_div_2p1_proof, subprob_term2_8_div_2p2_proof, subprob_term3_8_div_2p3_proof] <;> norm_num
  have subprob_val_8fact_2_eq_7_proof : val_8fact_2 = (7 : ℕ) := by
    mkOpaque
    simp_all only [val_8fact_2_def, subprob_padicValNat_2_8fact_legendre_proof, subprob_sum_legendre_8fact_calc_proof] <;> norm_num <;> rfl
  have subprob_Nat_log_2_9_proof : Nat.log (2 : ℕ) (9 : ℕ) = (3 : ℕ) := by
    mkOpaque
    rw [Nat.log_eq_iff] <;> norm_num <;> decide
  letI legendre_b_9 := (4 : ℕ)
  retro' legendre_b_9_def : legendre_b_9 = (4 : ℕ) := by funext; rfl
  have subprob_legendre_cond_9_proof : Nat.log (2 : ℕ) (9 : ℕ) < legendre_b_9 := by
    mkOpaque
    have h₀ : Nat.log (2 : ℕ) (9 : ℕ) = (3 : ℕ) := subprob_Nat_log_2_9_proof
    have h₁ : legendre_b_9 = (4 : ℕ) := legendre_b_9_def
    rw [h₀, h₁]
    norm_num
  letI sum_legendre_9fact_raw := ∑ i ∈ Finset.Ico (1 : ℕ) legendre_b_9, (9 : ℕ) / ((2 : ℕ) ^ i)
  retro' sum_legendre_9fact_raw_def : sum_legendre_9fact_raw = ∑ i ∈ Finset.Ico (1 : ℕ) legendre_b_9, (9 : ℕ) / (2 : ℕ) ^ i := by funext; rfl
  have subprob_padicValNat_2_9fact_legendre_proof : padicValNat (2 : ℕ) (Nat.factorial (9 : ℕ)) = sum_legendre_9fact_raw := by
    mkOpaque
    have h_legendre := padicValNat_factorial (p := 2) (n := 9) (b := legendre_b_9) subprob_legendre_cond_9_proof
    rw [h_legendre]
    rw [sum_legendre_9fact_raw_def]
  have subprob_sum_legendre_9fact_set_rewrite_proof : sum_legendre_9fact_raw = ∑ i ∈ ({(1 : ℕ), (2 : ℕ), (3 : ℕ)} : Finset ℕ), (9 : ℕ) / ((2 : ℕ) ^ i) := by
    mkOpaque
    rw [sum_legendre_9fact_raw_def]
    simp [Finset.Ico, legendre_b_9_def] <;> rfl
  have subprob_sum_legendre_9fact_expanded_proof : (∑ i ∈ ({(1 : ℕ), (2 : ℕ), (3 : ℕ)} : Finset ℕ), (9 : ℕ) / ((2 : ℕ) ^ i)) = (9 : ℕ) / ((2 : ℕ) ^ 1) + (9 : ℕ) / ((2 : ℕ) ^ 2) + (9 : ℕ) / ((2 : ℕ) ^ 3) := by
    mkOpaque
    simp [Finset.sum_insert, Finset.sum_singleton, Nat.div_eq_of_lt] <;> norm_num <;> linarith
  have subprob_term1_9_div_2p1_proof : (9 : ℕ) / (2 : ℕ) ^ 1 = (4 : ℕ) := by
    mkOpaque
    simpa [Nat.pow_one] using subprob_term1_9_div_2p1_proof
  have subprob_term2_9_div_2p2_proof : (9 : ℕ) / (2 : ℕ) ^ 2 = (2 : ℕ) := by
    mkOpaque
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt] <;> rfl <;> linarith <;> norm_num <;> rfl
  have subprob_term3_9_div_2p3_proof : (9 : ℕ) / (2 : ℕ) ^ 3 = (1 : ℕ) := by
    mkOpaque
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt] <;> decide <;> norm_num <;> decide <;> norm_num <;> decide
  have subprob_sum_legendre_9fact_calc_proof : sum_legendre_9fact_raw = (7 : ℕ) := by
    mkOpaque
    simp_all only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton, Finset.mem_insert, Nat.div_eq_of_lt, Nat.div_eq_of_lt] <;> norm_num <;> linarith
  have subprob_val_9fact_2_eq_7_proof : val_9fact_2 = (7 : ℕ) := by
    mkOpaque
    rw [val_9fact_2_def]
    rw [subprob_padicValNat_2_9fact_legendre_proof]
    rw [subprob_sum_legendre_9fact_calc_proof]
  have subprob_sum_padicValNat_2_jfact_expanded_proof : sum_padicValNat_2_jfact = val_1fact_2 + val_2fact_2 + val_3fact_2 + val_4fact_2 + val_5fact_2 + val_6fact_2 + val_7fact_2 + val_8fact_2 + val_9fact_2 := by
    mkOpaque
    rw [sum_padicValNat_2_jfact_def]
    rw [val_1fact_2_def, val_2fact_2_def, val_3fact_2_def, val_4fact_2_def, val_5fact_2_def, val_6fact_2_def, val_7fact_2_def, val_8fact_2_def, val_9fact_2_def]
    let f := fun j => padicValNat (2 : ℕ) (j !)
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 9) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 8) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 7) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 6) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 5) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 4) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 3) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2) f]
    rw [Finset.Icc_self (1 : ℕ)]
    rw [Finset.sum_singleton]
  have subprob_sum_padicValNat_2_jfact_evaluated_proof : sum_padicValNat_2_jfact = (0 : ℕ) + (1 : ℕ) + (1 : ℕ) + (3 : ℕ) + (3 : ℕ) + (4 : ℕ) + (4 : ℕ) + (7 : ℕ) + (7 : ℕ) := by
    mkOpaque
    simp [subprob_val_1fact_2_eq_0_proof, subprob_val_2fact_2_eq_1_proof, subprob_val_3fact_2_eq_1_proof, subprob_val_4fact_2_eq_3_proof, subprob_val_5fact_2_eq_3_proof, subprob_val_6fact_2_eq_4_proof, subprob_val_7fact_2_eq_4_proof, subprob_val_8fact_2_eq_7_proof, subprob_val_9fact_2_eq_7_proof, subprob_sum_padicValNat_2_jfact_expanded_proof]
  have subprob_arith_sum_2_eq_30_proof : (0 : ℕ) + (1 : ℕ) + (1 : ℕ) + (3 : ℕ) + (3 : ℕ) + (4 : ℕ) + (4 : ℕ) + (7 : ℕ) + (7 : ℕ) = (30 : ℕ) := by
    mkOpaque
    norm_num <;> decide <;> decide <;> decide <;> decide
  have subprob_exp_P_2_proof : exponent_p_P_val (2 : ℕ) = (30 : ℕ) := by
    mkOpaque
    simp_all only [exponent_p_P_val_def', subprob_sum_padicValNat_2_jfact_expanded_proof, subprob_sum_padicValNat_2_jfact_evaluated_proof, subprob_arith_sum_2_eq_30_proof] <;> rfl
  have subprob_exp_P_3_proof : exponent_p_P_val (3 : ℕ) = (13 : ℕ) := by
    mkOpaque
    rw [subprob_relation_exponent_P_val_to_factorials_proof 3 Nat.prime_three]
    rw [Finset.sum_congr rfl (fun j _ => subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof 3 j Nat.prime_three)]
    have val_1fact_3_eq : padicValNat (3 : ℕ) (1 : ℕ)! = (0 : ℕ) := by simp [Nat.factorial_one, padicValNat.one]
    have val_2fact_3_eq : padicValNat (3 : ℕ) (2 : ℕ)! = (0 : ℕ) := by
      rw [Nat.factorial_two]
      apply padicValNat.eq_zero_of_not_dvd
      norm_num
    have val_3fact_3_eq : padicValNat (3 : ℕ) (3 : ℕ)! = (1 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (3 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (3 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 3) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_4fact_3_eq : padicValNat (3 : ℕ) (4 : ℕ)! = (1 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (4 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (4 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 4) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_5fact_3_eq : padicValNat (3 : ℕ) (5 : ℕ)! = (1 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (5 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (5 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 5) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_6fact_3_eq : padicValNat (3 : ℕ) (6 : ℕ)! = (2 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (6 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (6 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 6) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_7fact_3_eq : padicValNat (3 : ℕ) (7 : ℕ)! = (2 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (7 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (7 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 7) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_8fact_3_eq : padicValNat (3 : ℕ) (8 : ℕ)! = (2 : ℕ) :=
      by
      have log_val : Nat.log (3 : ℕ) (8 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (8 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 8) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_9fact_3_eq : padicValNat (3 : ℕ) (9 : ℕ)! = (4 : ℕ) :=
      by
      have log_eq_2 : Nat.log (3 : ℕ) (9 : ℕ) = (2 : ℕ) := by
        rw [show (9 : ℕ) = (3 : ℕ) ^ (2 : ℕ) by norm_num]
        rw [Nat.log_pow (by decide : 1 < 3) (2 : ℕ)]
      have log_cond : Nat.log (3 : ℕ) (9 : ℕ) < (3 : ℕ) := by
        rw [log_eq_2]
        decide
      rw [padicValNat_factorial (p := 3) (n := 9) (b := 3) log_cond]
      rw [show Finset.Ico (1 : ℕ) (3 : ℕ) = ({1, 2} : Finset ℕ) by decide]
      rw [Finset.sum_insert (by decide : 1 ∉ {2})]
      rw [Finset.sum_singleton]
      norm_num
    have sum_Icc_1_9_eq : ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (3 : ℕ) j ! = padicValNat (3 : ℕ) 1! + padicValNat (3 : ℕ) 2! + padicValNat (3 : ℕ) 3! + padicValNat (3 : ℕ) 4! + padicValNat (3 : ℕ) 5! + padicValNat (3 : ℕ) 6! + padicValNat (3 : ℕ) 7! + padicValNat (3 : ℕ) 8! + padicValNat (3 : ℕ) 9! := by
      have list_eq : Finset.Icc (1 : ℕ) (9 : ℕ) = ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) := by decide
      rw [list_eq]
      rw [Finset.sum_insert (by decide : 1 ∉ {2, 3, 4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 2 ∉ {3, 4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 3 ∉ {4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 4 ∉ {5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 5 ∉ {6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 6 ∉ {7, 8, 9})]
      rw [Finset.sum_insert (by decide : 7 ∉ {8, 9})]
      rw [Finset.sum_insert (by decide : 8 ∉ {9})]
      rw [Finset.sum_singleton]
      ring
    rw [sum_Icc_1_9_eq]
    rw [val_1fact_3_eq, val_2fact_3_eq, val_3fact_3_eq, val_4fact_3_eq, val_5fact_3_eq, val_6fact_3_eq, val_7fact_3_eq, val_8fact_3_eq, val_9fact_3_eq]
  have subprob_prime_5_proof : Nat.Prime (5 : ℕ) := by
    mkOpaque
    decide <;> decide <;> decide <;> decide
  letI sum_factorization_jfact_5_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (5 : ℕ))
  retro' sum_factorization_jfact_5_Icc_1_9_def : sum_factorization_jfact_5_Icc_1_9 = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization j !) (5 : ℕ) := by funext; rfl
  have subprob_exp_P_5_eq_sum_factorization_jfact_5_proof : exponent_p_P_val (5 : ℕ) = sum_factorization_jfact_5_Icc_1_9 := by
    mkOpaque
    rw [subprob_relation_exponent_P_val_to_factorials_proof 5 subprob_prime_5_proof]
    simp [sum_factorization_jfact_5_Icc_1_9_def] <;> simp_all [Finset.sum_congr] <;> norm_num <;> linarith
  have subprob_factorization_eq_padicValNat_proof : ∀ (n p : ℕ), Nat.Prime p → (Nat.factorization n p) = padicValNat p n := by
    mkOpaque
    intro n p hp
    rw [Nat.factorization_def] <;> simp [hp, Nat.Prime.ne_zero] <;> norm_num <;> omega
  letI sum_padicValNat_5_jfact_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (5 : ℕ) (Nat.factorial j)
  retro' sum_padicValNat_5_jfact_Icc_1_9_def : sum_padicValNat_5_jfact_Icc_1_9 = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (5 : ℕ) j ! := by funext; rfl
  have subprob_sum_factorization_eq_sum_padicValNat_proof : sum_factorization_jfact_5_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_9 := by
    mkOpaque
    rw [sum_factorization_jfact_5_Icc_1_9_def]
    rw [sum_padicValNat_5_jfact_Icc_1_9_def]
    apply Finset.sum_congr rfl
    intro j hj
    apply subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof 5 j subprob_prime_5_proof
  have subprob_exp_P_5_eq_sum_padicValNat_5_proof : exponent_p_P_val (5 : ℕ) = sum_padicValNat_5_jfact_Icc_1_9 := by
    mkOpaque
    rw [subprob_exp_P_5_eq_sum_factorization_jfact_5_proof]
    rw [subprob_sum_factorization_eq_sum_padicValNat_proof] <;> simp_all <;> linarith
  have subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9_proof : Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (4 : ℕ) ∪ Finset.Icc (5 : ℕ) (9 : ℕ) := by
    mkOpaque
    ext x
    constructor <;> simp (config := { contextual := true }) [Finset.mem_Icc, Nat.le_succ_iff] <;> omega <;> omega
  have subprob_Icc_1_4_disjoint_Icc_5_9_proof : Disjoint (Finset.Icc (1 : ℕ) (4 : ℕ)) (Finset.Icc (5 : ℕ) (9 : ℕ)) := by
    mkOpaque
    apply Finset.disjoint_left.2
    intro x hx1 hx2
    rcases Finset.mem_Icc.mp hx1 with ⟨h1, h2⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨h3, h4⟩
    linarith
  letI sum_padicValNat_5_jfact_Icc_1_4 := ∑ j ∈ Finset.Icc (1 : ℕ) (4 : ℕ), padicValNat (5 : ℕ) (Nat.factorial j)
  retro' sum_padicValNat_5_jfact_Icc_1_4_def : sum_padicValNat_5_jfact_Icc_1_4 = ∑ j ∈ Finset.Icc (1 : ℕ) (4 : ℕ), padicValNat (5 : ℕ) j ! := by funext; rfl
  letI sum_padicValNat_5_jfact_Icc_5_9 := ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), padicValNat (5 : ℕ) (Nat.factorial j)
  retro' sum_padicValNat_5_jfact_Icc_5_9_def : sum_padicValNat_5_jfact_Icc_5_9 = ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), padicValNat (5 : ℕ) j ! := by funext; rfl
  have subprob_sum_padicValNat_5_jfact_Icc_1_9_split_proof : sum_padicValNat_5_jfact_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9 := by
    mkOpaque
    rw [sum_padicValNat_5_jfact_Icc_1_9_def, sum_padicValNat_5_jfact_Icc_1_4_def, sum_padicValNat_5_jfact_Icc_5_9_def]
    rw [subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9_proof]
    rw [Finset.sum_union subprob_Icc_1_4_disjoint_Icc_5_9_proof]
  have subprob_j_in_Icc_1_4_implies_j_lt_5_proof : ∀ (j : ℕ), j ∈ Finset.Icc (1 : ℕ) (4 : ℕ) → j < (5 : ℕ) := by
    mkOpaque
    intro j hj
    rw [Finset.mem_Icc] at hj
    linarith
  have subprob_padicValNat_5_jfact_eq_0_when_j_lt_5_proof : ∀ (j : ℕ), j < (5 : ℕ) → Nat.Prime (5 : ℕ) → padicValNat (5 : ℕ) (Nat.factorial j) = (0 : ℕ) := by
    mkOpaque
    intro j hj_lt_5 hp_prime_5
    have h_fact_zero : (Nat.factorization j !) (5 : ℕ) = (0 : ℕ) := by
      apply Nat.factorization_factorial_eq_zero_of_lt
      exact hj_lt_5
    have h_fact_eq_padicVal : (Nat.factorization j !) (5 : ℕ) = padicValNat (5 : ℕ) (Nat.factorial j) := by exact subprob_factorization_eq_padicValNat_proof (Nat.factorial j) (5 : ℕ) hp_prime_5
    rw [← h_fact_eq_padicVal]
    exact h_fact_zero
  have subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof : sum_padicValNat_5_jfact_Icc_1_4 = (0 : ℕ) := by
    mkOpaque
    have h₁ : sum_padicValNat_5_jfact_Icc_1_4 = 0 := by
      rw [sum_padicValNat_5_jfact_Icc_1_4_def]
      apply Finset.sum_eq_zero
      intro j hj
      have h₂ : j < 5 := by
        rw [Finset.mem_Icc] at hj
        linarith
      have h₃ : padicValNat 5 j ! = 0 := subprob_padicValNat_5_jfact_eq_0_when_j_lt_5_proof j h₂ subprob_prime_5_proof
      simp [h₃]
    exact h₁
  have subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25_proof : ∀ (j : ℕ), j ∈ Finset.Icc (5 : ℕ) (9 : ℕ) → (5 : ℕ) ≤ j ∧ j < (5 : ℕ) ^ 2 := by
    mkOpaque
    intro j hj
    simp only [Finset.mem_Icc] at hj
    constructor
    linarith
    linarith
  have subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9_proof : ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5 : ℕ) (9 : ℕ)), padicValNat (5 : ℕ) (Nat.factorial j) = j / (5 : ℕ) := by
    mkOpaque
    intro j hj
    have h_log_lt_b : Nat.log (5 : ℕ) j < Nat.log (5 : ℕ) j + 1 := Nat.lt_succ_self (Nat.log (5 : ℕ) j)
    have h_legendre : padicValNat (5 : ℕ) (Nat.factorial j) = ∑ i ∈ Finset.Ico (1 : ℕ) (Nat.log (5 : ℕ) j + 1), j / (5 : ℕ) ^ i := @padicValNat_factorial (5 : ℕ) j (Nat.log (5 : ℕ) j + 1) (Fact.mk subprob_prime_5_proof) h_log_lt_b
    rw [h_legendre]
    have hj_bounds := subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25_proof j hj
    have h_log_val : Nat.log (5 : ℕ) j = (1 : ℕ) := by
      apply (Nat.log_eq_iff (by simp)).mpr
      simp
      exact hj_bounds
    rw [h_log_val]
    simp
  have subprob_helper_5_gt_0_proof : (5 : ℕ) > 0 := by
    mkOpaque
    decide
  have subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10_proof : ∀ (j : ℕ), j ∈ Finset.Icc (5 : ℕ) (9 : ℕ) → (5 : ℕ) ≤ j ∧ j < 2 * (5 : ℕ) := by
    mkOpaque
    intro j hj
    simp only [Finset.mem_Icc, Nat.mul_succ] at hj ⊢
    constructor <;> omega
  have subprob_j_div_5_eq_1_when_j_in_Icc_5_9_proof : ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5 : ℕ) (9 : ℕ)), j / (5 : ℕ) = (1 : ℕ) := by
    mkOpaque
    intro j hj
    have h₁ : j ∈ Finset.Icc (5 : ℕ) (9 : ℕ) := hj
    have h₂ : 5 ≤ j := Finset.mem_Icc.mp h₁ |>.1
    have h₃ : j ≤ 9 := Finset.mem_Icc.mp h₁ |>.2
    interval_cases j <;> norm_num
  have subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9_proof : ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5 : ℕ) (9 : ℕ)), padicValNat (5 : ℕ) (Nat.factorial j) = (1 : ℕ) := by
    mkOpaque
    intro j hj
    have h₁ := subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9_proof j hj
    have h₂ := subprob_j_div_5_eq_1_when_j_in_Icc_5_9_proof j hj
    rw [h₂] at h₁
    exact h₁
  have subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof : sum_padicValNat_5_jfact_Icc_5_9 = ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), (1 : ℕ) := by
    mkOpaque
    rw [sum_padicValNat_5_jfact_Icc_5_9_def]
    apply Finset.sum_congr rfl
    intro j hj
    rw [subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9_proof j hj] <;> simp
  have subprob_card_Icc_5_9_proof : (Finset.Icc (5 : ℕ) (9 : ℕ)).card = (5 : ℕ) := by
    mkOpaque
    decide <;> simp [Finset.Icc, Finset.card] <;> norm_num <;> decide
  have subprob_sum_1_Icc_5_9_eq_card_proof : ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), (1 : ℕ) = (Finset.Icc (5 : ℕ) (9 : ℕ)).card := by
    mkOpaque
    rw [Finset.sum_const]
    norm_num <;> simp <;> rfl
  have subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof : sum_padicValNat_5_jfact_Icc_5_9 = (5 : ℕ) := by
    mkOpaque
    simpa [sum_padicValNat_5_jfact_Icc_5_9_def, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof, subprob_card_Icc_5_9_proof, subprob_sum_1_Icc_5_9_eq_card_proof] using subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof
  have subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value_proof : sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9 = (0 : ℕ) + (5 : ℕ) := by
    mkOpaque
    simp [subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof] <;> rfl
  have subprob_0_plus_5_eq_5_proof : (0 : ℕ) + (5 : ℕ) = (5 : ℕ) := by
    mkOpaque
    simp [Nat.add_zero]
  have subprob_exp_P_5_proof : exponent_p_P_val (5 : ℕ) = (5 : ℕ) := by
    mkOpaque
    simpa [subprob_sum_padicValNat_5_jfact_Icc_1_9_split_proof, subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof, subprob_0_plus_5_eq_5_proof] using subprob_exp_P_5_eq_sum_padicValNat_5_proof
  have subprob_prime_7_proof : Nat.Prime (7 : ℕ) := by
    mkOpaque
    decide <;> decide <;> decide <;> decide
  letI exp_j_fact_7 := fun (j : ℕ) => (Nat.factorization (Nat.factorial j) (7 : ℕ))
  retro' exp_j_fact_7_def : exp_j_fact_7 = fun (j : ℕ) => (Nat.factorization j !) (7 : ℕ) := by funext; rfl
  retro' exp_j_fact_7_def' : ∀ (j : ℕ), exp_j_fact_7 j = (Nat.factorization j !) (7 : ℕ) := by intros; rfl
  letI sum_exp_factorials_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), exp_j_fact_7 j
  retro' sum_exp_factorials_7_def : sum_exp_factorials_7 = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), exp_j_fact_7 j := by funext; rfl
  have subprob_exp_P_7_eq_sum_exp_factorials_7_proof : exponent_p_P_val (7 : ℕ) = sum_exp_factorials_7 := by
    mkOpaque
    rw [sum_exp_factorials_7_def]
    rw [exp_j_fact_7_def]
    simp
    exact subprob_relation_exponent_P_val_to_factorials_proof (7 : ℕ) subprob_prime_7_proof
  have subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9_proof : Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (6 : ℕ) ∪ Finset.Icc (7 : ℕ) (9 : ℕ) := by
    mkOpaque
    apply Finset.ext
    intro x
    constructor <;> simp (config := { contextual := true }) [Finset.mem_Icc, Finset.mem_union] <;> omega <;> omega <;> omega <;> omega
  have subprob_Icc_1_6_disjoint_Icc_7_9_proof : Disjoint (Finset.Icc (1 : ℕ) (6 : ℕ)) (Finset.Icc (7 : ℕ) (9 : ℕ)) := by
    mkOpaque
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    rw [Finset.mem_Icc] at hx₁ hx₂
    omega
  letI sum_1_to_6_val_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j
  retro' sum_1_to_6_val_7_def : sum_1_to_6_val_7 = ∑ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j := by funext; rfl
  letI sum_7_to_9_val_7 := ∑ j ∈ Finset.Icc (7 : ℕ) (9 : ℕ), exp_j_fact_7 j
  retro' sum_7_to_9_val_7_def : sum_7_to_9_val_7 = ∑ j ∈ Finset.Icc (7 : ℕ) (9 : ℕ), exp_j_fact_7 j := by funext; rfl
  have subprob_sum_exp_factorials_7_split_proof : sum_exp_factorials_7 = sum_1_to_6_val_7 + sum_7_to_9_val_7 := by
    mkOpaque
    rw [sum_exp_factorials_7_def, subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9_proof]
    rw [Finset.sum_union subprob_Icc_1_6_disjoint_Icc_7_9_proof]
    rw [sum_1_to_6_val_7_def, sum_7_to_9_val_7_def]
  have subprob_j_in_Icc_1_6_implies_j_lt_7_proof : ∀ (j : ℕ), j ∈ Finset.Icc (1 : ℕ) (6 : ℕ) → j < (7 : ℕ) := by
    mkOpaque
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨h1, h2⟩
    linarith
  have subprob_exp_j_fact_7_when_j_lt_7_proof : ∀ (j : ℕ), j < (7 : ℕ) → exp_j_fact_7 j = (0 : ℕ) := by
    mkOpaque
    intro j h_j_lt_7
    rw [exp_j_fact_7_def']
    exact Nat.factorization_factorial_eq_zero_of_lt h_j_lt_7
  have subprob_sum_1_to_6_val_7_eq_0_proof : sum_1_to_6_val_7 = (0 : ℕ) := by
    mkOpaque
    simp only [sum_1_to_6_val_7_def]
    have h₁ : ∀ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j = 0 := by
      intro j hj
      apply subprob_exp_j_fact_7_when_j_lt_7_proof
      apply subprob_j_in_Icc_1_6_implies_j_lt_7_proof
      exact hj
    simp [Finset.sum_eq_zero h₁]
  have subprob_exp_7_fact_7_eq_padicValNat_7_fact_7_proof : exp_j_fact_7 (7 : ℕ) = padicValNat (7 : ℕ) (Nat.factorial (7 : ℕ)) := by
    mkOpaque
    rw [exp_j_fact_7_def', subprob_factorization_eq_padicValNat_proof (Nat.factorial 7) 7 subprob_prime_7_proof] <;> simp [padicValNat.factorial] <;> norm_num
  have subprob_padicValNat_7_7fact_legendre_proof : padicValNat (7 : ℕ) (Nat.factorial (7 : ℕ)) = ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (7 : ℕ) + (1 : ℕ)), (7 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    have h_prime_7 : Fact (Nat.Prime (7 : ℕ)) := Fact.mk subprob_prime_7_proof
    apply padicValNat_factorial
    norm_num
  have subprob_Nat_log_7_7_eq_1_proof : Nat.log (7 : ℕ) (7 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [Nat.log_eq_one_iff] <;> norm_num <;> norm_num <;> norm_num
  letI sum_legendre_7_7fact := ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (7 : ℕ) + (1 : ℕ)), (7 : ℕ) / ((7 : ℕ) ^ i)
  retro' sum_legendre_7_7fact_def : sum_legendre_7_7fact = ∑ i ∈ Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (7 : ℕ) + (1 : ℕ)), (7 : ℕ) / (7 : ℕ) ^ i := by funext; rfl
  have subprob_sum_legendre_7_7fact_rewritten_log_proof : sum_legendre_7_7fact = ∑ i in Finset.Ico (1 : ℕ) ((1 : ℕ) + (1 : ℕ)), (7 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    simp [sum_legendre_7_7fact_def, subprob_Nat_log_7_7_eq_1_proof] <;> norm_num <;> rfl
  have subprob_one_plus_one_eq_two_proof : (1 : ℕ) + (1 : ℕ) = (2 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> norm_num <;> rfl <;> norm_num <;> rfl
  have subprob_sum_legendre_7_7fact_ico_1_2_proof : sum_legendre_7_7fact = ∑ i in Finset.Ico (1 : ℕ) (2 : ℕ), (7 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    rw [subprob_sum_legendre_7_7fact_rewritten_log_proof] <;> simp [subprob_one_plus_one_eq_two_proof] <;> norm_num <;> rfl
  have subprob_Finset_Ico_1_2_eq_singleton_1_proof : Finset.Ico (1 : ℕ) (2 : ℕ) = ({(1 : ℕ)} : Finset ℕ) := by
    mkOpaque
    ext x
    simp [Finset.mem_Ico, Finset.mem_singleton] <;> decide
  have subprob_sum_legendre_7_7fact_is_7_div_7_pow_1_proof : sum_legendre_7_7fact = (7 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) := by
    mkOpaque
    simp [sum_legendre_7_7fact_def, Finset.Ico, Nat.log, Nat.div_eq_of_lt] <;> decide <;> rfl
  have subprob_7_pow_1_eq_7_proof : ((7 : ℕ) : ℕ) ^ (1 : ℕ) = (7 : ℕ) := by
    mkOpaque
    rw [Nat.pow_one] <;> rfl
  have subprob_7_div_7_eq_1_proof : (7 : ℕ) / (7 : ℕ) = (1 : ℕ) := by
    mkOpaque
    norm_num <;> rfl
  have subprob_sum_legendre_7_7fact_eval_to_1_proof : (7 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    simp [Nat.pow_one] <;> apply Nat.div_self <;> decide <;> linarith
  have subprob_padicValNat_7_of_7fact_eq_1_proof : padicValNat (7 : ℕ) (Nat.factorial (7 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    rw [subprob_padicValNat_7_7fact_legendre_proof]
    simp [subprob_Nat_log_7_7_eq_1_proof, subprob_7_div_7_eq_1_proof] <;> norm_num <;> rfl
  have subprob_exp_7_fact_7_eq_1_proof : exp_j_fact_7 (7 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [subprob_exp_7_fact_7_eq_padicValNat_7_fact_7_proof]
    rw [subprob_padicValNat_7_of_7fact_eq_1_proof]
  have subprob_exp_8_fact_7_eq_padicValNat_7_fact_8_proof : exp_j_fact_7 (8 : ℕ) = padicValNat (7 : ℕ) (Nat.factorial (8 : ℕ)) := by
    mkOpaque
    rw [exp_j_fact_7_def']
    simp [padicValNat, Nat.factorial, Nat.factorization] <;> norm_num <;> rfl
  have subprob_padicValNat_7_8fact_legendre_proof : padicValNat (7 : ℕ) (Nat.factorial (8 : ℕ)) = ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (8 : ℕ) + (1 : ℕ)), (8 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    have : Fact (Nat.Prime (7 : ℕ)) := ⟨subprob_prime_7_proof⟩
    apply padicValNat_factorial (Nat.lt_succ_self (Nat.log (7 : ℕ) (8 : ℕ)))
  have subprob_Nat_log_7_8_eq_1_proof : Nat.log (7 : ℕ) (8 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [Nat.log_eq_iff] <;> norm_num <;> linarith [Nat.pow_pos (by norm_num : (0 : ℕ) < 7) 1, Nat.pow_pos (by norm_num : (0 : ℕ) < 7) 2]
  letI sum_legendre_7_8fact := ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (8 : ℕ) + (1 : ℕ)), (8 : ℕ) / ((7 : ℕ) ^ i)
  retro' sum_legendre_7_8fact_def : sum_legendre_7_8fact = ∑ i ∈ Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (8 : ℕ) + (1 : ℕ)), (8 : ℕ) / (7 : ℕ) ^ i := by funext; rfl
  have subprob_sum_legendre_7_8fact_rewritten_log_proof : sum_legendre_7_8fact = ∑ i in Finset.Ico (1 : ℕ) ((1 : ℕ) + (1 : ℕ)), (8 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    rw [sum_legendre_7_8fact_def]
    simp [Finset.Ico, Finset.sum_range_succ, Nat.log, Nat.pow_succ, Nat.div_eq_of_lt] <;> norm_num
  have subprob_sum_legendre_7_8fact_ico_1_2_proof : sum_legendre_7_8fact = ∑ i in Finset.Ico (1 : ℕ) (2 : ℕ), (8 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    rw [sum_legendre_7_8fact_def]
    simp [Finset.Ico, Nat.log, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one] <;> norm_num <;> rfl
  have subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof : sum_legendre_7_8fact = (8 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) := by
    mkOpaque
    rw [subprob_sum_legendre_7_8fact_ico_1_2_proof]
    simp [Finset.sum_Ico_succ_top] <;> norm_num <;> rfl
  have subprob_8_div_7_eq_1_proof : (8 : ℕ) / (7 : ℕ) = (1 : ℕ) := by
    mkOpaque
    norm_num <;> decide <;> norm_num <;> decide
  have subprob_sum_legendre_7_8fact_eval_to_1_proof : (8 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    simp [Nat.pow_one] <;> norm_num <;> linarith
  have subprob_padicValNat_7_of_8fact_eq_1_proof : padicValNat (7 : ℕ) (Nat.factorial (8 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    rw [subprob_padicValNat_7_8fact_legendre_proof]
    simp [subprob_Nat_log_7_8_eq_1_proof, sum_legendre_7_8fact_def, subprob_sum_legendre_7_8fact_rewritten_log_proof, subprob_sum_legendre_7_8fact_ico_1_2_proof, subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof, subprob_8_div_7_eq_1_proof, subprob_sum_legendre_7_8fact_eval_to_1_proof]
  have subprob_exp_8_fact_7_eq_1_proof : exp_j_fact_7 (8 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [subprob_exp_8_fact_7_eq_padicValNat_7_fact_8_proof]
    rw [subprob_padicValNat_7_8fact_legendre_proof]
    rw [subprob_Nat_log_7_8_eq_1_proof]
    simp [sum_legendre_7_8fact_def, subprob_sum_legendre_7_8fact_rewritten_log_proof, subprob_sum_legendre_7_8fact_ico_1_2_proof, subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof, subprob_8_div_7_eq_1_proof, subprob_sum_legendre_7_8fact_eval_to_1_proof]
  have subprob_exp_9_fact_7_eq_padicValNat_7_fact_9_proof : exp_j_fact_7 (9 : ℕ) = padicValNat (7 : ℕ) (Nat.factorial (9 : ℕ)) := by
    mkOpaque
    rw [exp_j_fact_7_def' (9 : ℕ)]
    apply subprob_factorization_eq_padicValNat_proof (9!) (7 : ℕ) subprob_prime_7_proof
  have subprob_padicValNat_7_9fact_legendre_proof : padicValNat (7 : ℕ) (Nat.factorial (9 : ℕ)) = ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ)), (9 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    have h_b_cond : Nat.log (7 : ℕ) (9 : ℕ) < Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ) := by apply Nat.lt_succ_self (Nat.log (7 : ℕ) (9 : ℕ))
    apply (@padicValNat_factorial (7 : ℕ) (9 : ℕ) (Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ)) (Fact.mk subprob_prime_7_proof) h_b_cond)
  have subprob_Nat_log_7_9_eq_1_proof : Nat.log (7 : ℕ) (9 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [Nat.log]
    norm_num <;> decide <;> norm_num <;> decide
  letI sum_legendre_7_9fact := ∑ i in Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ)), (9 : ℕ) / ((7 : ℕ) ^ i)
  retro' sum_legendre_7_9fact_def : sum_legendre_7_9fact = ∑ i ∈ Finset.Ico (1 : ℕ) (Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ)), (9 : ℕ) / (7 : ℕ) ^ i := by funext; rfl
  have subprob_sum_legendre_7_9fact_rewritten_log_proof : sum_legendre_7_9fact = ∑ i in Finset.Ico (1 : ℕ) ((1 : ℕ) + (1 : ℕ)), (9 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    simp [sum_legendre_7_9fact_def, subprob_Nat_log_7_9_eq_1_proof] <;> norm_num <;> ring <;> omega
  have subprob_sum_legendre_7_9fact_ico_1_2_proof : sum_legendre_7_9fact = ∑ i in Finset.Ico (1 : ℕ) (2 : ℕ), (9 : ℕ) / ((7 : ℕ) ^ i) := by
    mkOpaque
    have h₀ : Nat.log (7 : ℕ) (9 : ℕ) = (1 : ℕ) := subprob_Nat_log_7_9_eq_1_proof
    simp [sum_legendre_7_9fact_def, h₀, Finset.Ico, Nat.div_eq_of_lt] <;> norm_num <;> rfl
  have subprob_sum_legendre_7_9fact_is_9_div_7_pow_1_proof : sum_legendre_7_9fact = (9 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) := by
    mkOpaque
    simp only [sum_legendre_7_9fact_def]
    norm_num <;> rfl
  have subprob_9_div_7_eq_1_proof : (9 : ℕ) / (7 : ℕ) = (1 : ℕ) := by
    mkOpaque
    norm_num <;> linarith <;> omega <;> decide
  have subprob_sum_legendre_7_9fact_eval_to_1_proof : (9 : ℕ) / ((7 : ℕ) ^ (1 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    simp [Nat.pow_succ, Nat.pow_zero] <;> decide <;> rfl <;> decide <;> rfl
  have subprob_padicValNat_7_of_9fact_eq_1_proof : padicValNat (7 : ℕ) (Nat.factorial (9 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    rw [subprob_padicValNat_7_9fact_legendre_proof]
    rw [← sum_legendre_7_9fact_def]
    rw [subprob_sum_legendre_7_9fact_is_9_div_7_pow_1_proof]
    exact subprob_sum_legendre_7_9fact_eval_to_1_proof
  have subprob_exp_9_fact_7_eq_1_proof : exp_j_fact_7 (9 : ℕ) = (1 : ℕ) := by
    mkOpaque
    rw [exp_j_fact_7_def']
    have h_prime_7 : Nat.Prime (7 : ℕ) := subprob_prime_7_proof
    rw [subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof (7 : ℕ) (9 : ℕ) h_prime_7]
    exact subprob_padicValNat_7_of_9fact_eq_1_proof
  have subprob_Icc_7_9_eq_7_8_9_proof : Finset.Icc (7 : ℕ) (9 : ℕ) = ({(7 : ℕ), (8 : ℕ), (9 : ℕ)} : Finset ℕ) := by
    mkOpaque
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have subprob_sum_7_to_9_val_7_expanded_proof : sum_7_to_9_val_7 = exp_j_fact_7 (7 : ℕ) + exp_j_fact_7 (8 : ℕ) + exp_j_fact_7 (9 : ℕ) := by
    mkOpaque
    rw [sum_7_to_9_val_7_def]
    rw [subprob_Icc_7_9_eq_7_8_9_proof]
    simp
    ring
  have subprob_sum_7_to_9_val_7_calc_values_proof : exp_j_fact_7 (7 : ℕ) + exp_j_fact_7 (8 : ℕ) + exp_j_fact_7 (9 : ℕ) = (1 : ℕ) + (1 : ℕ) + (1 : ℕ) := by
    mkOpaque
    rw [subprob_exp_7_fact_7_eq_1_proof, subprob_exp_8_fact_7_eq_1_proof, subprob_exp_9_fact_7_eq_1_proof] <;> simp
  have subprob_1_plus_1_plus_1_eq_3_proof : (1 : ℕ) + (1 : ℕ) + (1 : ℕ) = (3 : ℕ) := by
    mkOpaque
    norm_num <;> rfl <;> norm_num <;> rfl <;> norm_num <;> rfl
  have subprob_sum_7_to_9_val_7_eq_3_proof : sum_7_to_9_val_7 = (3 : ℕ) := by
    mkOpaque
    rw [subprob_sum_7_to_9_val_7_expanded_proof]
    rw [subprob_sum_7_to_9_val_7_calc_values_proof]
  have subprob_sum_exp_factorials_7_calc_value_proof : sum_1_to_6_val_7 + sum_7_to_9_val_7 = (0 : ℕ) + (3 : ℕ) := by
    mkOpaque
    rw [subprob_sum_1_to_6_val_7_eq_0_proof, subprob_sum_7_to_9_val_7_eq_3_proof] <;> simp <;> rfl
  have subprob_0_plus_3_eq_3_proof : (0 : ℕ) + (3 : ℕ) = (3 : ℕ) := by
    mkOpaque
    norm_num <;> simp_all <;> norm_num <;> linarith
  have subprob_sum_exp_factorials_7_eq_3_proof : sum_exp_factorials_7 = (3 : ℕ) := by
    mkOpaque
    rw [subprob_sum_exp_factorials_7_split_proof]
    rw [subprob_sum_exp_factorials_7_calc_value_proof]
  have subprob_exp_P_7_proof : exponent_p_P_val (7 : ℕ) = (3 : ℕ) := by
    mkOpaque
    rw [subprob_exp_P_7_eq_sum_exp_factorials_7_proof]
    exact subprob_sum_exp_factorials_7_eq_3_proof
  have subprob_exp_P_other_proof : ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_gt_7 : p > (7 : ℕ)), exponent_p_P_val p = (0 : ℕ) := by
    mkOpaque
    intro p hp h_p_gt_7
    rw [subprob_relation_exponent_P_val_to_factorials_proof p hp]
    apply Finset.sum_eq_zero
    intro j hj
    rw [subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof p j hp]
    rw [padicValNat.eq_zero_iff]
    right
    right
    have h_j_bounds : 1 ≤ j ∧ j ≤ 9 := Finset.mem_Icc.mp hj
    have h_p_ge_11 : p ≥ 11 := by
      by_contra h_p_lt_11_contra
      have h_p_lt_11 : p < 11 := (lt_iff_not_le.mpr h_p_lt_11_contra)
      have h_p_le_10 : p ≤ 10 := le_of_lt_succ h_p_lt_11
      have h_p_ge_8 : p ≥ 8 := Order.succ_le_of_lt h_p_gt_7
      interval_cases p
      . have h_8_not_prime : ¬Nat.Prime 8 := Nat.not_prime_mul (a := 2) (b := 4) (by norm_num) (by norm_num)
        contradiction
      . have h_9_not_prime : ¬Nat.Prime 9 := Nat.not_prime_mul (a := 3) (b := 3) (by norm_num) (by norm_num)
        contradiction
      . have h_10_not_prime : ¬Nat.Prime 10 := Nat.not_prime_mul (a := 2) (b := 5) (by norm_num) (by norm_num)
        contradiction
    have h_j_lt_p : j < p := by linarith [h_j_bounds.2, h_p_ge_11]
    by_contra h_dvd_contra
    have h_p_le_j : p ≤ j := (Nat.Prime.dvd_factorial hp).mp h_dvd_contra
    linarith [h_p_le_j, h_j_lt_p]
  have subprob_P_val_factorization_support_proof : (Nat.factorization P_val).support = ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ) := by
    mkOpaque
    ext p
    rw [Nat.support_factorization P_val]
    rw [Nat.mem_primeFactors_of_ne_zero (ne_zero_of_lt subprob_P_val_pos_proof)]
    apply Iff.intro
    . intro h_prime_and_dvd
      cases h_prime_and_dvd with
      |
        intro h_prime h_dvd =>
        have h_exp_nonzero : (Nat.factorization P_val) p ≠ 0 := by
          apply Nat.one_le_iff_ne_zero.mp
          exact (Nat.Prime.dvd_iff_one_le_factorization h_prime (ne_zero_of_lt subprob_P_val_pos_proof)).mp h_dvd
        rw [← exponent_p_P_val_def' p] at h_exp_nonzero
        have h_if_gt_7_exp_zero : p > 7 → exponent_p_P_val p = 0 := subprob_exp_P_other_proof p h_prime
        have h_exp_nonzero_implies_not_gt_7 : exponent_p_P_val p ≠ 0 → ¬(p > 7) := mt h_if_gt_7_exp_zero
        have h_not_gt_7 : ¬(p > 7) := h_exp_nonzero_implies_not_gt_7 h_exp_nonzero
        have h_p_le_7 : p ≤ 7 := by simp at h_not_gt_7; exact h_not_gt_7
        have h_p_ge_2 : p ≥ 2 := Nat.Prime.two_le h_prime
        interval_cases p using h_p_ge_2, h_p_le_7
        . simp
        . simp
        . have h_not_prime_4 : ¬(4 : ℕ).Prime := by decide
          exact False.elim (h_not_prime_4 h_prime)
        . simp
        . have h_not_prime_6 : ¬(6 : ℕ).Prime := by decide
          exact False.elim (h_not_prime_6 h_prime)
        . simp
        done
    . intro h_p_in_set
      simp [Finset.mem_insert, Finset.mem_singleton] at h_p_in_set
      cases h_p_in_set with
      | inl h_p_eq =>
        subst h_p_eq
        apply And.intro
        . exact subprob_prime_2_proof
        . rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_2_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
          rw [← exponent_p_P_val_def' 2]
          rw [subprob_exp_P_2_proof]
          norm_num
      | inr h_p_in_set_357 =>
        cases h_p_in_set_357 with
        | inl h_p_eq =>
          subst h_p_eq
          apply And.intro
          . norm_num
          . rw [Nat.Prime.dvd_iff_one_le_factorization (by norm_num) (ne_zero_of_lt subprob_P_val_pos_proof)]
            rw [← exponent_p_P_val_def' 3]
            rw [subprob_exp_P_3_proof]
            norm_num
        | inr h_p_in_set_57 =>
          cases h_p_in_set_57 with
          | inl h_p_eq =>
            subst h_p_eq
            apply And.intro
            . exact subprob_prime_5_proof
            . rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_5_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
              rw [← exponent_p_P_val_def' 5]
              rw [subprob_exp_P_5_proof]
              norm_num
          | inr h_p_eq =>
            subst h_p_eq
            apply And.intro
            . exact subprob_prime_7_proof
            . rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_7_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
              rw [← exponent_p_P_val_def' 7]
              rw [subprob_exp_P_7_proof]
              norm_num
  letI M_val := ∏ p ∈ (Nat.factorization P_val).support, p ^ (exponent_p_P_val p / (2 : ℕ))
  retro' M_val_def : M_val = ∏ p ∈ Finsupp.support (Nat.factorization P_val), p ^ (exponent_p_P_val p / (2 : ℕ)) := by funext; rfl
  have subprob_M_val_eq_product_proof : M_val = (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) * (7 : ℕ) ^ (1 : ℕ) := by
    mkOpaque
    rw [M_val_def]
    rw [subprob_P_val_factorization_support_proof]
    simp
    rw [subprob_exp_P_2_proof]
    rw [subprob_exp_P_3_proof]
    rw [subprob_exp_P_5_proof]
    rw [subprob_exp_P_7_proof]
    have h_div_2 : (30 : ℕ) / (2 : ℕ) = (15 : ℕ) := by norm_num
    have h_div_3 : (13 : ℕ) / (2 : ℕ) = (6 : ℕ) := by norm_num
    have h_div_5 : (5 : ℕ) / (2 : ℕ) = (2 : ℕ) := by norm_num
    have h_div_7 : (3 : ℕ) / (2 : ℕ) = (1 : ℕ) := by norm_num
    rw [h_div_2]
    rw [h_div_3]
    rw [h_div_5]
    rw [h_div_7]
    rfl
  have subprob_M_val_pos_proof : M_val > (0 : ℕ) := by
    mkOpaque
    rw [subprob_M_val_eq_product_proof]
    norm_num
  have subprob_S_equiv_divisors_of_M_proof : ∀ (k : ℕ), k ∈ S ↔ ((0 : ℕ) < k ∧ k ∣ M_val) := by
    mkOpaque
    intro k
    rw [h₀]
    rw [← P_val_def]
    have h_P_ne_zero : P_val ≠ 0 := Nat.ne_of_gt subprob_P_val_pos_proof
    have h_M_ne_zero : M_val ≠ 0 := Nat.ne_of_gt subprob_M_val_pos_proof
    cases k with
    | zero =>
      simp only [Nat.not_lt_zero, mul_zero, zero_dvd_iff]
      simp only [false_and_iff]
    | succ k' =>
      simp only [Nat.succ_pos']
      simp only [true_and_iff]
      have h_k_plus_1_ne_zero : k' + 1 ≠ 0 := Nat.ne_of_gt (Nat.succ_pos k')
      have h_k_plus_1_sq_ne_zero : (k' + 1) * (k' + 1) ≠ 0 := Nat.mul_ne_zero h_k_plus_1_ne_zero h_k_plus_1_ne_zero
      have prime_of_mem_support_P : ∀ {p : ℕ}, p ∈ Finsupp.support (Nat.factorization P_val) → Nat.Prime p := by
        intro p hp_mem
        rw [subprob_P_val_factorization_support_proof] at hp_mem
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp_mem
        rcases hp_mem with rfl | rfl | rfl | rfl
        . exact subprob_prime_2_proof
        . exact Nat.prime_three
        . exact subprob_prime_5_proof
        . exact subprob_prime_7_proof
      have h_M_factorization_p : ∀ q : ℕ, Nat.Prime q → Nat.factorization M_val q = Nat.factorization P_val q / (2 : ℕ) := by
        intro q hq_prime
        rw [M_val_def]
        have h_prod_nonzero : ∀ p ∈ Finsupp.support (Nat.factorization P_val), p ^ (exponent_p_P_val p / (2 : ℕ)) ≠ 0 := by
          intro p hp_mem_supp
          rw [Nat.support_factorization P_val] at hp_mem_supp
          have h_p_is_prime_factor : p ∈ (P_val).primeFactors := hp_mem_supp
          have h_prime_and_dvd := (Nat.mem_primeFactors_of_ne_zero (Nat.ne_of_gt subprob_P_val_pos_proof)).mp h_p_is_prime_factor
          have hp_prime : Nat.Prime p := h_prime_and_dvd.left
          have hp_ne_zero : p ≠ 0 := hp_prime.ne_zero
          apply pow_ne_zero (exponent_p_P_val p / (2 : ℕ))
          exact hp_ne_zero
        rw [Nat.factorization_prod h_prod_nonzero]
        rw [Finsupp.finset_sum_apply]
        simp_rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        rw [subprob_P_val_factorization_support_proof]
        by_cases hq_in_support : q ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ)
        . rw [Finset.sum_eq_single_of_mem q hq_in_support
              (by
                intro p hp_mem_supp h_p_ne_q
                rw [← subprob_P_val_factorization_support_proof] at hp_mem_supp
                have hp_prime := prime_of_mem_support_P hp_mem_supp
                have h_q_ne_p : q ≠ p := Ne.symm h_p_ne_q
                have h_not_dvd_q_p : ¬q ∣ p := mt (Iff.mp (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime)) h_q_ne_p
                have h_fact_p_q_zero : Nat.factorization p q = 0 := Nat.factorization_eq_zero_of_not_dvd h_not_dvd_q_p
                rw [h_fact_p_q_zero]
                rw [mul_zero])]
          rw [Nat.Prime.factorization_self hq_prime]
          rw [mul_one]
          rw [exponent_p_P_val_def' q]
        . have h_sum_zero : ∑ p ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ), (exponent_p_P_val p / (2 : ℕ)) * (Nat.factorization p q) = 0 := by
            apply Finset.sum_eq_zero
            intro p hp_mem_supp
            have h_p_ne_q : p ≠ q := by
              intro h_p_eq_q
              subst h_p_eq_q
              exact hq_in_support hp_mem_supp
            rw [← subprob_P_val_factorization_support_proof] at hp_mem_supp
            have hp_prime := prime_of_mem_support_P hp_mem_supp
            have h_q_ne_p : q ≠ p := Ne.symm h_p_ne_q
            have h_not_dvd_q_p : ¬q ∣ p := mt (Iff.mp (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime)) h_q_ne_p
            have h_fact_p_q_zero : Nat.factorization p q = 0 := Nat.factorization_eq_zero_of_not_dvd h_not_dvd_q_p
            rw [h_fact_p_q_zero]
            rw [mul_zero]
          have h_fact_P_q_zero : (Nat.factorization P_val) q = 0 := by
            rw [← subprob_P_val_factorization_support_proof] at hq_in_support
            rw [Finsupp.not_mem_support_iff] at hq_in_support
            exact hq_in_support
          rw [h_sum_zero, h_fact_P_q_zero]
      constructor
      . intro h_k_plus_1_sq_dvd_P
        have h_fact_k_plus_1_sq_le_fact_P : ∀ p : ℕ, Nat.Prime p → (Nat.factorization ((k' + 1) * (k' + 1))) p ≤ (Nat.factorization P_val) p := (Nat.factorization_prime_le_iff_dvd h_k_plus_1_sq_ne_zero h_P_ne_zero).mpr h_k_plus_1_sq_dvd_P
        rw [← Nat.factorization_prime_le_iff_dvd h_k_plus_1_ne_zero h_M_ne_zero]
        intro p hp_prime
        have h_fact_k_plus_1_sq_p : Nat.factorization ((k' + 1) * (k' + 1)) p = (2 : ℕ) * Nat.factorization (k' + 1) p := by
          rw [← Nat.pow_two (k' + 1)]
          rw [Nat.factorization_pow (k' + 1) 2, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        have H_lhs_ineq_p := h_fact_k_plus_1_sq_le_fact_P p hp_prime
        rw [h_fact_k_plus_1_sq_p] at H_lhs_ineq_p
        rw [h_M_factorization_p p hp_prime]
        rw [Nat.mul_comm (2 : ℕ) (Nat.factorization (k' + 1) p)] at H_lhs_ineq_p
        exact Nat.le_div_iff_mul_le' (by norm_num) |>.mpr H_lhs_ineq_p
      . intro h_k_plus_1_dvd_M
        have h_fact_k_plus_1_le_fact_M : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (k' + 1)) p ≤ (Nat.factorization M_val) p := (Nat.factorization_prime_le_iff_dvd h_k_plus_1_ne_zero h_M_ne_zero).mpr h_k_plus_1_dvd_M
        rw [← Nat.factorization_prime_le_iff_dvd h_k_plus_1_sq_ne_zero h_P_ne_zero]
        intro p hp_prime
        have h_fact_k_plus_1_sq_p : Nat.factorization ((k' + 1) * (k' + 1)) p = (2 : ℕ) * Nat.factorization (k' + 1) p := by
          rw [← Nat.pow_two (k' + 1)]
          rw [Nat.factorization_pow (k' + 1) 2, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        rw [h_fact_k_plus_1_sq_p]
        have H_rhs_ineq_p := h_fact_k_plus_1_le_fact_M p hp_prime
        rw [h_M_factorization_p p hp_prime] at H_rhs_ineq_p
        have h_mul_le_goal : Nat.factorization (k' + 1) p * (2 : ℕ) ≤ Nat.factorization P_val p := Nat.mul_le_of_le_div (2 : ℕ) (Nat.factorization (k' + 1) p) (Nat.factorization P_val p) H_rhs_ineq_p
        rw [Nat.mul_comm (Nat.factorization (k' + 1) p) (2 : ℕ)] at h_mul_le_goal
        exact h_mul_le_goal
  have subprob_card_S_eq_num_divisors_M_proof : S.card = (Nat.divisors M_val).card := by
    mkOpaque
    have h_eq : S = Nat.divisors M_val := by
      apply Finset.ext
      intro k
      rw [subprob_S_equiv_divisors_of_M_proof]
      rw [Nat.mem_divisors]
      constructor
      . intro h_and
        constructor
        . exact h_and.right
        . apply pos_iff_ne_zero.mp subprob_M_val_pos_proof
      . intro h_and
        constructor
        . apply pos_of_dvd_of_pos h_and.left subprob_M_val_pos_proof
        . exact h_and.left
    rw [h_eq]
  have subprob_card_divisors_M_formula_proof : (Nat.divisors M_val).card = ∏ p ∈ (Nat.factorization M_val).support, ((Nat.factorization M_val p) + (1 : ℕ)) := by
    mkOpaque
    apply ArithmeticFunction.card_divisors M_val
    exact Nat.pos_iff_ne_zero.mp subprob_M_val_pos_proof
  have subprob_factorization_M_val_support_proof : (Nat.factorization M_val).support = ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ) := by
    mkOpaque
    have h_prime_3 : Nat.Prime (3 : ℕ) := Nat.prime_three
    have h_2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
    have h_3_ne_zero : (3 : ℕ) ≠ 0 := by norm_num
    have h_5_ne_zero : (5 : ℕ) ≠ 0 := by norm_num
    have h_7_ne_zero : (7 : ℕ) ≠ 0 := by norm_num
    have h_2_pow_15_ne_zero : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := pow_ne_zero 15 h_2_ne_zero
    have h_3_pow_6_ne_zero : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := pow_ne_zero 6 h_3_ne_zero
    have h_5_pow_2_ne_zero : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 h_5_ne_zero
    have h_7_pow_1_ne_zero : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := pow_ne_zero 1 h_7_ne_zero
    have h_ab_ne_zero : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := by
      apply mul_ne_zero
      exact h_2_pow_15_ne_zero
      exact h_3_pow_6_ne_zero
    have h_abc_ne_zero : ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := by
      apply mul_ne_zero
      exact h_ab_ne_zero
      exact h_5_pow_2_ne_zero
    have h_factorization_M_val : Nat.factorization ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) * (7 : ℕ) ^ (1 : ℕ)) = Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) + Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) + Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) + Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) := by
      rw [Nat.factorization_mul h_abc_ne_zero h_7_pow_1_ne_zero]
      rw [Nat.factorization_mul h_ab_ne_zero h_5_pow_2_ne_zero]
      rw [Nat.factorization_mul h_2_pow_15_ne_zero h_3_pow_6_ne_zero]
    rw [subprob_M_val_eq_product_proof, h_factorization_M_val]
    have h_15_ne_zero : (15 : ℕ) ≠ 0 := by norm_num
    have h_6_ne_zero : (6 : ℕ) ≠ 0 := by norm_num
    have h_exp_5_pow_2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
    have h_exp_7_pow_1_ne_zero : (1 : ℕ) ≠ 0 := by norm_num
    have fact_2_15 : Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) = Finsupp.single (2 : ℕ) (15 : ℕ) := Nat.Prime.factorization_pow subprob_prime_2_proof
    have fact_3_6 : Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) = Finsupp.single (3 : ℕ) (6 : ℕ) := Nat.Prime.factorization_pow h_prime_3
    have fact_5_2 : Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) = Finsupp.single (5 : ℕ) (2 : ℕ) := Nat.Prime.factorization_pow subprob_prime_5_proof
    have fact_7_1 : Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) = Finsupp.single (7 : ℕ) (1 : ℕ) := Nat.Prime.factorization_pow subprob_prime_7_proof
    rw [fact_2_15, fact_3_6, fact_5_2, fact_7_1]
    have s2 : (Finsupp.single (2 : ℕ) (15 : ℕ)).support = {(2 : ℕ)} := Finsupp.support_single_ne_zero (2 : ℕ) h_15_ne_zero
    have s3 : (Finsupp.single (3 : ℕ) (6 : ℕ)).support = {(3 : ℕ)} := Finsupp.support_single_ne_zero (3 : ℕ) h_6_ne_zero
    have s5 : (Finsupp.single (5 : ℕ) (2 : ℕ)).support = {(5 : ℕ)} := Finsupp.support_single_ne_zero (5 : ℕ) h_exp_5_pow_2_ne_zero
    have s7 : (Finsupp.single (7 : ℕ) (1 : ℕ)).support = {(7 : ℕ)} := Finsupp.support_single_ne_zero (7 : ℕ) h_exp_7_pow_1_ne_zero
    have h_disj_f1_f2 : Disjoint (Finsupp.support (Finsupp.single (2 : ℕ) (15 : ℕ))) (Finsupp.support (Finsupp.single (3 : ℕ) (6 : ℕ))) := by simp [s2, s3]
    have h_supp_f1_f2_union : (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ)).support = (Finsupp.single (2 : ℕ) (15 : ℕ)).support ∪ (Finsupp.single (3 : ℕ) (6 : ℕ)).support := Finsupp.support_add_eq h_disj_f1_f2
    have h_disj_f12_f3 : Disjoint (Finsupp.support (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ))) (Finsupp.support (Finsupp.single (5 : ℕ) (2 : ℕ))) := by
      rw [h_supp_f1_f2_union]
      simp [s2, s3, s5]
    have s123 : (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ) + Finsupp.single (5 : ℕ) (2 : ℕ)).support = ({(2 : ℕ), (3 : ℕ), (5 : ℕ)} : Finset ℕ) := by
      rw [Finsupp.support_add_eq h_disj_f12_f3]
      rw [Finsupp.support_add_eq h_disj_f1_f2]
      rw [s2, s3, s5]
      ext x
      simp
    have h_disjoint_f123_f4 : Disjoint (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ) + Finsupp.single (5 : ℕ) (2 : ℕ)).support (Finsupp.single (7 : ℕ) (1 : ℕ)).support := by
      rw [s123, s7]
      simp
    simp only [Finsupp.support_add_eq h_disjoint_f123_f4]
    rw [s123, s7]
    ext x
    simp
  have subprob_exp_M_2_proof : (Nat.factorization M_val (2 : ℕ)) = (15 : ℕ) := by
    mkOpaque
    rw [subprob_M_val_eq_product_proof]
    have nz2 : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := by norm_num
    have nz3 : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := by norm_num
    have nz5 : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := by norm_num
    have nz7 : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := by norm_num
    have nz23 : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.mul_ne_zero nz2 nz3
    have nz235 : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.mul_ne_zero nz23 nz5
    rw [Nat.factorization_mul nz235 nz7, Finsupp.add_apply]
    rw [Nat.factorization_mul nz23 nz5, Finsupp.add_apply]
    rw [Nat.factorization_mul nz2 nz3, Finsupp.add_apply]
    have h_fact_2_pow_15_at_2 : (Nat.factorization ((2 : ℕ) ^ (15 : ℕ))) (2 : ℕ) = 15 := by
      rw [Nat.Prime.factorization_pow subprob_prime_2_proof]
      simp
    rw [h_fact_2_pow_15_at_2]
    have h_3_ne_2 : (3 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_3_pow_6_at_2 : (Nat.factorization ((3 : ℕ) ^ (6 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_three]
      simp
    rw [h_fact_3_pow_6_at_2]
    have h_5_ne_2 : (5 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_5_pow_2_at_2 : (Nat.factorization ((5 : ℕ) ^ (2 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_five]
      simp
    rw [h_fact_5_pow_2_at_2]
    have h_7_ne_2 : (7 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_7_pow_1_at_2 : (Nat.factorization ((7 : ℕ) ^ (1 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow subprob_prime_7_proof]
      simp
    rw [h_fact_7_pow_1_at_2]
  have subprob_exp_M_3_proof : (Nat.factorization M_val (3 : ℕ)) = (6 : ℕ) := by
    mkOpaque
    rw [subprob_M_val_eq_product_proof]
    have h2_prime : Nat.Prime 2 := by decide
    have h3_prime : Nat.Prime 3 := by decide
    have h5_prime : Nat.Prime 5 := by decide
    have h7_prime : Nat.Prime 7 := by decide
    have pos_2_15 : (2 : ℕ) ^ (15 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_3_6 : (3 : ℕ) ^ (6 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_5_2 : (5 : ℕ) ^ (2 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_7_1 : (7 : ℕ) ^ (1 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have ne_zero_2_15 : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_2_15
    have ne_zero_3_6 : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_3_6
    have ne_zero_5_2 : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_5_2
    have ne_zero_7_1 : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_7_1
    have ne_zero_left_prod : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos pos_2_15 pos_3_6) pos_5_2)
    rw [Nat.factorization_mul ne_zero_left_prod ne_zero_7_1]
    rw [Finsupp.add_apply]
    have h_fact_7_1_3 : Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h7_prime]
      have h_ne : (3 : ℕ) ≠ (7 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_7_1_3]
    simp only [add_zero]
    have ne_zero_inner_prod : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos pos_2_15 pos_3_6)
    rw [Nat.factorization_mul ne_zero_inner_prod ne_zero_5_2]
    rw [Finsupp.add_apply]
    have h_fact_5_2_3 : Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h5_prime]
      have h_ne : (3 : ℕ) ≠ (5 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_5_2_3]
    simp only [add_zero]
    rw [Nat.factorization_mul ne_zero_2_15 ne_zero_3_6]
    rw [Finsupp.add_apply]
    have h_fact_2_15_3 : Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h2_prime]
      have h_ne : (3 : ℕ) ≠ (2 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_2_15_3]
    simp only [zero_add]
    have h_fact_3_6_3 : Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) (3 : ℕ) = 6 := by
      rw [Nat.Prime.factorization_pow h3_prime]
      simp
    rw [h_fact_3_6_3]
  have subprob_exp_M_5_proof : (Nat.factorization M_val (5 : ℕ)) = (2 : ℕ) := by
    mkOpaque
    rw [M_val_def]
    rw [subprob_P_val_factorization_support_proof]
    have h_prod_nonzero : ∀ p ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ), p ^ (exponent_p_P_val p / (2 : ℕ)) ≠ 0 := by
      intro p hp
      have h_p_pos : p > 0 := by
        simp at hp
        rcases hp with rfl | rfl | rfl | rfl
        . norm_num
        . norm_num
        . norm_num
        . norm_num
      exact pow_ne_zero (exponent_p_P_val p / 2) (Nat.pos_iff_ne_zero.mp h_p_pos)
    rw [Nat.factorization_prod h_prod_nonzero]
    rw [Finsupp.coe_finset_sum]
    have h_prime_3 : Nat.Prime 3 := by norm_num
    have h_prime_7 : Nat.Prime 7 := by norm_num
    simp [Nat.Prime.factorization_pow, subprob_prime_2_proof, h_prime_3, subprob_prime_5_proof, h_prime_7]
    rw [subprob_exp_P_5_proof]
  have subprob_exp_M_7_proof : (Nat.factorization M_val (7 : ℕ)) = (1 : ℕ) := by
    mkOpaque
    rw [Nat.factorization_def]
    rw [subprob_M_val_eq_product_proof]
    have h_7_prime : Nat.Prime (7 : ℕ) := by decide
    have h_2_pow_15_ne_zero : (2 : ℕ) ^ (15 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_3_pow_6_ne_zero : (3 : ℕ) ^ (6 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_5_pow_2_ne_zero : (5 : ℕ) ^ (2 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_7_pow_1_ne_zero : (7 : ℕ) ^ (1 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_23_ne_zero : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ (0 : ℕ) := by apply mul_ne_zero h_2_pow_15_ne_zero h_3_pow_6_ne_zero
    have h_235_ne_zero : ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ) ≠ (0 : ℕ) := by apply mul_ne_zero h_23_ne_zero h_5_pow_2_ne_zero
    rw [@padicValNat.mul (7 : ℕ) (((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ)) ((7 : ℕ) ^ (1 : ℕ)) (Fact.mk h_7_prime) h_235_ne_zero h_7_pow_1_ne_zero]
    rw [@padicValNat.mul (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) ((5 : ℕ) ^ (2 : ℕ)) (Fact.mk h_7_prime) h_23_ne_zero h_5_pow_2_ne_zero]
    rw [@padicValNat.mul (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ)) ((3 : ℕ) ^ (6 : ℕ)) (Fact.mk h_7_prime) h_2_pow_15_ne_zero h_3_pow_6_ne_zero]
    have h_2_ne_zero : (2 : ℕ) ≠ (0 : ℕ) := by decide
    have h_3_ne_zero : (3 : ℕ) ≠ (0 : ℕ) := by decide
    have h_5_ne_zero : (5 : ℕ) ≠ (0 : ℕ) := by decide
    have h_7_ne_zero : (7 : ℕ) ≠ (0 : ℕ) := by decide
    have h_val_2_pow_15 : padicValNat (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ)) = (15 : ℕ) * padicValNat (7 : ℕ) (2 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (2 : ℕ) (Fact.mk h_7_prime) (15 : ℕ) ?_
      exact h_2_ne_zero
    rw [h_val_2_pow_15]
    have h_val_3_pow_6 : padicValNat (7 : ℕ) ((3 : ℕ) ^ (6 : ℕ)) = (6 : ℕ) * padicValNat (7 : ℕ) (3 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (3 : ℕ) (Fact.mk h_7_prime) (6 : ℕ) ?_
      exact h_3_ne_zero
    rw [h_val_3_pow_6]
    have h_val_5_pow_2 : padicValNat (7 : ℕ) ((5 : ℕ) ^ (2 : ℕ)) = (2 : ℕ) * padicValNat (7 : ℕ) (5 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (5 : ℕ) (Fact.mk h_7_prime) (2 : ℕ) ?_
      exact h_5_ne_zero
    rw [h_val_5_pow_2]
    have h_val_7_pow_1 : padicValNat (7 : ℕ) ((7 : ℕ) ^ (1 : ℕ)) = (1 : ℕ) * padicValNat (7 : ℕ) (7 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (7 : ℕ) (Fact.mk h_7_prime) (1 : ℕ) ?_
      exact h_7_ne_zero
    rw [h_val_7_pow_1]
    have h_7_not_dvd_2 : ¬(7 : ℕ) ∣ (2 : ℕ) := by decide
    have h_term1 : (15 : ℕ) * padicValNat (7 : ℕ) (2 : ℕ) = (15 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_2
    rw [h_term1]
    have h_7_not_dvd_3 : ¬(7 : ℕ) ∣ (3 : ℕ) := by decide
    have h_term2 : (6 : ℕ) * padicValNat (7 : ℕ) (3 : ℕ) = (6 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_3
    rw [h_term2]
    have h_7_not_dvd_5 : ¬(7 : ℕ) ∣ (5 : ℕ) := by decide
    have h_term3 : (2 : ℕ) * padicValNat (7 : ℕ) (5 : ℕ) = (2 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_5
    rw [h_term3]
    have h_val_7_7_eq_1 : padicValNat (7 : ℕ) (7 : ℕ) = 1 := by exact @padicValNat_self (7 : ℕ) (Fact.mk h_7_prime)
    rw [h_val_7_7_eq_1]
    norm_num
  have subprob_card_S_product_form_proof : S.card = ((15 : ℕ) + (1 : ℕ)) * ((6 : ℕ) + (1 : ℕ)) * ((2 : ℕ) + (1 : ℕ)) * ((1 : ℕ) + (1 : ℕ)) := by
    mkOpaque
    rw [subprob_card_S_eq_num_divisors_M_proof]
    rw [subprob_card_divisors_M_formula_proof]
    rw [subprob_factorization_M_val_support_proof]
    simp
    rw [subprob_exp_M_2_proof]
    rw [subprob_exp_M_3_proof]
    rw [subprob_exp_M_5_proof]
    rw [subprob_exp_M_7_proof]
    rfl
  have subprob_calculation_proof : ((15 : ℕ) + (1 : ℕ)) * ((6 : ℕ) + (1 : ℕ)) * ((2 : ℕ) + (1 : ℕ)) * ((1 : ℕ) + (1 : ℕ)) = (672 : ℕ) := by
    mkOpaque
    simp [Nat.mul, Nat.add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] <;> decide
  have subprob_final_goal_proof : S.card = (672 : ℕ) := by
    mkOpaque
    rw [subprob_card_S_product_form_proof]
  exact
    show Finset.card S = (672 : ℕ) by
      mkOpaque
      exact subprob_final_goal_proof

#print axioms amc12a_2003_p23

/- Sketch
variable (S: Finset ℕ) (h₀: ∀ (k : ℕ), k ∈ S ↔ (0 : ℕ) < k ∧ k * k ∣ ∏ i ∈ Finset.Icc (1 : ℕ) (9 : ℕ), i !)
play
  P_val := (∏ i in (Finset.Icc (1 : ℕ) (9 : ℕ)), Nat.factorial i)
  subprob_P_val_pos :≡ P_val > (0 : ℕ)
  subprob_P_val_pos_proof ⇐ show subprob_P_val_pos by sorry
  exponent_p_P_val := fun (p : ℕ) => (Nat.factorization P_val) p
  subprob_relation_exponent_P_val_to_factorials :≡ ∀ (p : ℕ) (hp : Nat.Prime p), exponent_p_P_val p = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) p)
  subprob_relation_exponent_P_val_to_factorials_proof ⇐ show subprob_relation_exponent_P_val_to_factorials by sorry

  -- Start of new detailed subproblems for subprob_exp_P_2
  subprob_prime_2 :≡ Nat.Prime (2:ℕ)
  subprob_prime_2_proof ⇐ show subprob_prime_2 by sorry

  subprob_exp_P_2_eq_sum_factorization :≡ exponent_p_P_val (2:ℕ) = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2:ℕ))
  subprob_exp_P_2_eq_sum_factorization_proof ⇐ show subprob_exp_P_2_eq_sum_factorization by sorry

  subprob_factorization_jfact_p_eq_padicValNat_jfact_p :≡ ∀ (p j : ℕ), Nat.Prime p → (Nat.factorization (Nat.factorial j) p) = padicValNat p (Nat.factorial j)
  subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof ⇐ show subprob_factorization_jfact_p_eq_padicValNat_jfact_p by sorry

  sum_factorization_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2:ℕ))
  sum_padicValNat_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (2:ℕ) (Nat.factorial j)

  subprob_sum_factorization_eq_sum_padicValNat_for_2 :≡ sum_factorization_2_jfact = sum_padicValNat_2_jfact
  subprob_sum_factorization_eq_sum_padicValNat_for_2_proof ⇐ show subprob_sum_factorization_eq_sum_padicValNat_for_2 by sorry

  subprob_exp_P_2_eq_sum_padicValNat :≡ exponent_p_P_val (2:ℕ) = sum_padicValNat_2_jfact
  subprob_exp_P_2_eq_sum_padicValNat_proof ⇐ show subprob_exp_P_2_eq_sum_padicValNat by sorry

  -- Definitions for padicValNat 2 (j!)
  val_1fact_2 := padicValNat (2:ℕ) (Nat.factorial (1:ℕ))
  val_2fact_2 := padicValNat (2:ℕ) (Nat.factorial (2:ℕ))
  val_3fact_2 := padicValNat (2:ℕ) (Nat.factorial (3:ℕ))
  val_4fact_2 := padicValNat (2:ℕ) (Nat.factorial (4:ℕ))
  val_5fact_2 := padicValNat (2:ℕ) (Nat.factorial (5:ℕ))
  val_6fact_2 := padicValNat (2:ℕ) (Nat.factorial (6:ℕ))
  val_7fact_2 := padicValNat (2:ℕ) (Nat.factorial (7:ℕ))
  val_8fact_2 := padicValNat (2:ℕ) (Nat.factorial (8:ℕ))
  val_9fact_2 := padicValNat (2:ℕ) (Nat.factorial (9:ℕ))

  -- Calculate val_1fact_2
  subprob_1_fact_val :≡ Nat.factorial (1:ℕ) = (1:ℕ)
  subprob_1_fact_val_proof ⇐ show subprob_1_fact_val by sorry
  subprob_padicValNat_2_1_is_0 :≡ padicValNat (2:ℕ) (1:ℕ) = (0:ℕ)
  subprob_padicValNat_2_1_is_0_proof ⇐ show subprob_padicValNat_2_1_is_0 by sorry
  subprob_val_1fact_2_eq_0 :≡ val_1fact_2 = (0:ℕ)
  subprob_val_1fact_2_eq_0_proof ⇐ show subprob_val_1fact_2_eq_0 by sorry

  -- Calculate val_2fact_2
  subprob_2_fact_val :≡ Nat.factorial (2:ℕ) = (2:ℕ)
  subprob_2_fact_val_proof ⇐ show subprob_2_fact_val by sorry
  subprob_padicValNat_2_2_is_1 :≡ padicValNat (2:ℕ) (2:ℕ) = (1:ℕ)
  subprob_padicValNat_2_2_is_1_proof ⇐ show subprob_padicValNat_2_2_is_1 by sorry
  subprob_val_2fact_2_eq_1 :≡ val_2fact_2 = (1:ℕ)
  subprob_val_2fact_2_eq_1_proof ⇐ show subprob_val_2fact_2_eq_1 by sorry

  -- Calculate val_3fact_2
  subprob_3_fact_val :≡ Nat.factorial (3:ℕ) = (6:ℕ)
  subprob_3_fact_val_proof ⇐ show subprob_3_fact_val by sorry
  subprob_6_eq_2_mul_3 :≡ (6:ℕ) = (2:ℕ) * (3:ℕ)
  subprob_6_eq_2_mul_3_proof ⇐ show subprob_6_eq_2_mul_3 by sorry
  subprob_2_ne_zero :≡ (2:ℕ) ≠ (0:ℕ)
  subprob_2_ne_zero_proof ⇐ show subprob_2_ne_zero by sorry
  subprob_3_ne_zero :≡ (3:ℕ) ≠ (0:ℕ)
  subprob_3_ne_zero_proof ⇐ show subprob_3_ne_zero by sorry
  subprob_padicValNat_2_6_mul :≡ padicValNat (2:ℕ) ((2:ℕ)*(3:ℕ)) = padicValNat (2:ℕ) (2:ℕ) + padicValNat (2:ℕ) (3:ℕ)
  subprob_padicValNat_2_6_mul_proof ⇐ show subprob_padicValNat_2_6_mul by sorry
  subprob_padicValNat_2_3_is_0 :≡ padicValNat (2:ℕ) (3:ℕ) = (0:ℕ)
  subprob_padicValNat_2_3_is_0_proof ⇐ show subprob_padicValNat_2_3_is_0 by sorry
  subprob_1_plus_0_eq_1 :≡ (1:ℕ) + (0:ℕ) = (1:ℕ)
  subprob_1_plus_0_eq_1_proof ⇐ show subprob_1_plus_0_eq_1 by sorry
  subprob_padicValNat_2_6_is_1 :≡ padicValNat (2:ℕ) (6:ℕ) = (1:ℕ)
  subprob_padicValNat_2_6_is_1_proof ⇐ show subprob_padicValNat_2_6_is_1 by sorry
  subprob_val_3fact_2_eq_1 :≡ val_3fact_2 = (1:ℕ)
  subprob_val_3fact_2_eq_1_proof ⇐ show subprob_val_3fact_2_eq_1 by sorry

  -- Calculate val_4fact_2
  subprob_4_fact_val :≡ Nat.factorial (4:ℕ) = (24:ℕ)
  subprob_4_fact_val_proof ⇐ show subprob_4_fact_val by sorry
  subprob_24_eq_2p3_mul_3 :≡ (24:ℕ) = (2:ℕ)^3 * (3:ℕ)
  subprob_24_eq_2p3_mul_3_proof ⇐ show subprob_24_eq_2p3_mul_3 by sorry
  subprob_2p3_ne_zero :≡ (2:ℕ)^3 ≠ (0:ℕ)
  subprob_2p3_ne_zero_proof ⇐ show subprob_2p3_ne_zero by sorry
  subprob_padicValNat_2_24_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^3*(3:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^3) + padicValNat (2:ℕ) (3:ℕ)
  subprob_padicValNat_2_24_mul_proof ⇐ show subprob_padicValNat_2_24_mul by sorry
  subprob_padicValNat_2_2p3_is_3 :≡ padicValNat (2:ℕ) ((2:ℕ)^3) = (3:ℕ)
  subprob_padicValNat_2_2p3_is_3_proof ⇐ show subprob_padicValNat_2_2p3_is_3 by sorry
  subprob_3_plus_0_eq_3 :≡ (3:ℕ) + (0:ℕ) = (3:ℕ)
  subprob_3_plus_0_eq_3_proof ⇐ show subprob_3_plus_0_eq_3 by sorry
  subprob_padicValNat_2_24_is_3 :≡ padicValNat (2:ℕ) (24:ℕ) = (3:ℕ)
  subprob_padicValNat_2_24_is_3_proof ⇐ show subprob_padicValNat_2_24_is_3 by sorry
  subprob_val_4fact_2_eq_3 :≡ val_4fact_2 = (3:ℕ)
  subprob_val_4fact_2_eq_3_proof ⇐ show subprob_val_4fact_2_eq_3 by sorry

  -- Calculate val_5fact_2
  subprob_5_fact_val :≡ Nat.factorial (5:ℕ) = (120:ℕ)
  subprob_5_fact_val_proof ⇐ show subprob_5_fact_val by sorry
  subprob_120_eq_2p3_mul_15 :≡ (120:ℕ) = (2:ℕ)^3 * (15:ℕ)
  subprob_120_eq_2p3_mul_15_proof ⇐ show subprob_120_eq_2p3_mul_15 by sorry
  subprob_15_ne_zero :≡ (15:ℕ) ≠ (0:ℕ)
  subprob_15_ne_zero_proof ⇐ show subprob_15_ne_zero by sorry
  subprob_padicValNat_2_120_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^3*(15:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^3) + padicValNat (2:ℕ) (15:ℕ)
  subprob_padicValNat_2_120_mul_proof ⇐ show subprob_padicValNat_2_120_mul by sorry
  subprob_padicValNat_2_15_is_0 :≡ padicValNat (2:ℕ) (15:ℕ) = (0:ℕ)
  subprob_padicValNat_2_15_is_0_proof ⇐ show subprob_padicValNat_2_15_is_0 by sorry
  subprob_padicValNat_2_120_is_3 :≡ padicValNat (2:ℕ) (120:ℕ) = (3:ℕ)
  subprob_padicValNat_2_120_is_3_proof ⇐ show subprob_padicValNat_2_120_is_3 by sorry
  subprob_val_5fact_2_eq_3 :≡ val_5fact_2 = (3:ℕ)
  subprob_val_5fact_2_eq_3_proof ⇐ show subprob_val_5fact_2_eq_3 by sorry

  -- Calculate val_6fact_2
  subprob_6_fact_val :≡ Nat.factorial (6:ℕ) = (720:ℕ)
  subprob_6_fact_val_proof ⇐ show subprob_6_fact_val by sorry
  subprob_720_eq_2p4_mul_45 :≡ (720:ℕ) = (2:ℕ)^4 * (45:ℕ)
  subprob_720_eq_2p4_mul_45_proof ⇐ show subprob_720_eq_2p4_mul_45 by sorry
  subprob_2p4_ne_zero :≡ (2:ℕ)^4 ≠ (0:ℕ)
  subprob_2p4_ne_zero_proof ⇐ show subprob_2p4_ne_zero by sorry
  subprob_45_ne_zero :≡ (45:ℕ) ≠ (0:ℕ)
  subprob_45_ne_zero_proof ⇐ show subprob_45_ne_zero by sorry
  subprob_padicValNat_2_720_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^4*(45:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^4) + padicValNat (2:ℕ) (45:ℕ)
  subprob_padicValNat_2_720_mul_proof ⇐ show subprob_padicValNat_2_720_mul by sorry
  subprob_padicValNat_2_2p4_is_4 :≡ padicValNat (2:ℕ) ((2:ℕ)^4) = (4:ℕ)
  subprob_padicValNat_2_2p4_is_4_proof ⇐ show subprob_padicValNat_2_2p4_is_4 by sorry
  subprob_padicValNat_2_45_is_0 :≡ padicValNat (2:ℕ) (45:ℕ) = (0:ℕ)
  subprob_padicValNat_2_45_is_0_proof ⇐ show subprob_padicValNat_2_45_is_0 by sorry
  subprob_4_plus_0_eq_4 :≡ (4:ℕ) + (0:ℕ) = (4:ℕ)
  subprob_4_plus_0_eq_4_proof ⇐ show subprob_4_plus_0_eq_4 by sorry
  subprob_padicValNat_2_720_is_4 :≡ padicValNat (2:ℕ) (720:ℕ) = (4:ℕ)
  subprob_padicValNat_2_720_is_4_proof ⇐ show subprob_padicValNat_2_720_is_4 by sorry
  subprob_val_6fact_2_eq_4 :≡ val_6fact_2 = (4:ℕ)
  subprob_val_6fact_2_eq_4_proof ⇐ show subprob_val_6fact_2_eq_4 by sorry

  -- Calculate val_7fact_2
  subprob_7_fact_val :≡ Nat.factorial (7:ℕ) = (5040:ℕ)
  subprob_7_fact_val_proof ⇐ show subprob_7_fact_val by sorry
  subprob_5040_eq_2p4_mul_315 :≡ (5040:ℕ) = (2:ℕ)^4 * (315:ℕ)
  subprob_5040_eq_2p4_mul_315_proof ⇐ show subprob_5040_eq_2p4_mul_315 by sorry
  subprob_315_ne_zero :≡ (315:ℕ) ≠ (0:ℕ)
  subprob_315_ne_zero_proof ⇐ show subprob_315_ne_zero by sorry
  subprob_padicValNat_2_5040_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^4*(315:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^4) + padicValNat (2:ℕ) (315:ℕ)
  subprob_padicValNat_2_5040_mul_proof ⇐ show subprob_padicValNat_2_5040_mul by sorry
  subprob_padicValNat_2_315_is_0 :≡ padicValNat (2:ℕ) (315:ℕ) = (0:ℕ)
  subprob_padicValNat_2_315_is_0_proof ⇐ show subprob_padicValNat_2_315_is_0 by sorry
  subprob_padicValNat_2_5040_is_4 :≡ padicValNat (2:ℕ) (5040:ℕ) = (4:ℕ)
  subprob_padicValNat_2_5040_is_4_proof ⇐ show subprob_padicValNat_2_5040_is_4 by sorry
  subprob_val_7fact_2_eq_4 :≡ val_7fact_2 = (4:ℕ)
  subprob_val_7fact_2_eq_4_proof ⇐ show subprob_val_7fact_2_eq_4 by sorry

  -- Calculate val_8fact_2 (using Legendre's formula)
  subprob_Nat_log_2_8 :≡ Nat.log (2:ℕ) (8:ℕ) = (3:ℕ)
  subprob_Nat_log_2_8_proof ⇐ show subprob_Nat_log_2_8 by sorry
  legendre_b_8 := (4:ℕ)
  subprob_legendre_cond_8 :≡ Nat.log (2:ℕ) (8:ℕ) < legendre_b_8
  subprob_legendre_cond_8_proof ⇐ show subprob_legendre_cond_8 by sorry
  sum_legendre_8fact_raw := ∑ i ∈ Finset.Ico (1:ℕ) legendre_b_8, (8:ℕ) / ((2:ℕ)^i)
  subprob_padicValNat_2_8fact_legendre :≡ padicValNat (2:ℕ) (Nat.factorial (8:ℕ)) = sum_legendre_8fact_raw
  subprob_padicValNat_2_8fact_legendre_proof ⇐ show subprob_padicValNat_2_8fact_legendre by sorry
  subprob_Ico_1_4_is_123 :≡ Finset.Ico (1:ℕ) (4:ℕ) = ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ)
  subprob_Ico_1_4_is_123_proof ⇐ show subprob_Ico_1_4_is_123 by sorry
  subprob_sum_legendre_8fact_set_rewrite :≡ sum_legendre_8fact_raw = ∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (8:ℕ) / ((2:ℕ)^i)
  subprob_sum_legendre_8fact_set_rewrite_proof ⇐ show subprob_sum_legendre_8fact_set_rewrite by sorry
  subprob_sum_legendre_8fact_expanded :≡ (∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (8:ℕ) / ((2:ℕ)^i)) = (8:ℕ)/((2:ℕ)^1) + (8:ℕ)/((2:ℕ)^2) + (8:ℕ)/((2:ℕ)^3)
  subprob_sum_legendre_8fact_expanded_proof ⇐ show subprob_sum_legendre_8fact_expanded by sorry
  subprob_term1_8_div_2p1 :≡ (8:ℕ) / (2:ℕ)^1 = (4:ℕ)
  subprob_term1_8_div_2p1_proof ⇐ show subprob_term1_8_div_2p1 by sorry
  subprob_term2_8_div_2p2 :≡ (8:ℕ) / (2:ℕ)^2 = (2:ℕ)
  subprob_term2_8_div_2p2_proof ⇐ show subprob_term2_8_div_2p2 by sorry
  subprob_term3_8_div_2p3 :≡ (8:ℕ) / (2:ℕ)^3 = (1:ℕ)
  subprob_term3_8_div_2p3_proof ⇐ show subprob_term3_8_div_2p3 by sorry
  subprob_4_plus_2_plus_1_eq_7 :≡ (4:ℕ) + (2:ℕ) + (1:ℕ) = (7:ℕ)
  subprob_4_plus_2_plus_1_eq_7_proof ⇐ show subprob_4_plus_2_plus_1_eq_7 by sorry
  subprob_sum_legendre_8fact_calc :≡ sum_legendre_8fact_raw = (7:ℕ)
  subprob_sum_legendre_8fact_calc_proof ⇐ show subprob_sum_legendre_8fact_calc by sorry
  subprob_val_8fact_2_eq_7 :≡ val_8fact_2 = (7:ℕ)
  subprob_val_8fact_2_eq_7_proof ⇐ show subprob_val_8fact_2_eq_7 by sorry

  -- Calculate val_9fact_2 (using Legendre's formula)
  subprob_Nat_log_2_9 :≡ Nat.log (2:ℕ) (9:ℕ) = (3:ℕ)
  subprob_Nat_log_2_9_proof ⇐ show subprob_Nat_log_2_9 by sorry
  legendre_b_9 := (4:ℕ)
  subprob_legendre_cond_9 :≡ Nat.log (2:ℕ) (9:ℕ) < legendre_b_9
  subprob_legendre_cond_9_proof ⇐ show subprob_legendre_cond_9 by sorry
  sum_legendre_9fact_raw := ∑ i ∈ Finset.Ico (1:ℕ) legendre_b_9, (9:ℕ) / ((2:ℕ)^i)
  subprob_padicValNat_2_9fact_legendre :≡ padicValNat (2:ℕ) (Nat.factorial (9:ℕ)) = sum_legendre_9fact_raw
  subprob_padicValNat_2_9fact_legendre_proof ⇐ show subprob_padicValNat_2_9fact_legendre by sorry
  subprob_sum_legendre_9fact_set_rewrite :≡ sum_legendre_9fact_raw = ∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (9:ℕ) / ((2:ℕ)^i)
  subprob_sum_legendre_9fact_set_rewrite_proof ⇐ show subprob_sum_legendre_9fact_set_rewrite by sorry
  subprob_sum_legendre_9fact_expanded :≡ (∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (9:ℕ) / ((2:ℕ)^i)) = (9:ℕ)/((2:ℕ)^1) + (9:ℕ)/((2:ℕ)^2) + (9:ℕ)/((2:ℕ)^3)
  subprob_sum_legendre_9fact_expanded_proof ⇐ show subprob_sum_legendre_9fact_expanded by sorry
  subprob_term1_9_div_2p1 :≡ (9:ℕ) / (2:ℕ)^1 = (4:ℕ)
  subprob_term1_9_div_2p1_proof ⇐ show subprob_term1_9_div_2p1 by sorry
  subprob_term2_9_div_2p2 :≡ (9:ℕ) / (2:ℕ)^2 = (2:ℕ)
  subprob_term2_9_div_2p2_proof ⇐ show subprob_term2_9_div_2p2 by sorry
  subprob_term3_9_div_2p3 :≡ (9:ℕ) / (2:ℕ)^3 = (1:ℕ)
  subprob_term3_9_div_2p3_proof ⇐ show subprob_term3_9_div_2p3 by sorry
  subprob_sum_legendre_9fact_calc :≡ sum_legendre_9fact_raw = (7:ℕ)
  subprob_sum_legendre_9fact_calc_proof ⇐ show subprob_sum_legendre_9fact_calc by sorry
  subprob_val_9fact_2_eq_7 :≡ val_9fact_2 = (7:ℕ)
  subprob_val_9fact_2_eq_7_proof ⇐ show subprob_val_9fact_2_eq_7 by sorry

  -- Summing up all padicValNats for prime 2
  subprob_sum_padicValNat_2_jfact_expanded :≡ sum_padicValNat_2_jfact = val_1fact_2 + val_2fact_2 + val_3fact_2 + val_4fact_2 + val_5fact_2 + val_6fact_2 + val_7fact_2 + val_8fact_2 + val_9fact_2
  subprob_sum_padicValNat_2_jfact_expanded_proof ⇐ show subprob_sum_padicValNat_2_jfact_expanded by sorry

  subprob_sum_padicValNat_2_jfact_evaluated :≡ sum_padicValNat_2_jfact = (0:ℕ) + (1:ℕ) + (1:ℕ) + (3:ℕ) + (3:ℕ) + (4:ℕ) + (4:ℕ) + (7:ℕ) + (7:ℕ)
  subprob_sum_padicValNat_2_jfact_evaluated_proof ⇐ show subprob_sum_padicValNat_2_jfact_evaluated by sorry

  subprob_arith_sum_2_eq_30 :≡ (0:ℕ) + (1:ℕ) + (1:ℕ) + (3:ℕ) + (3:ℕ) + (4:ℕ) + (4:ℕ) + (7:ℕ) + (7:ℕ) = (30:ℕ)
  subprob_arith_sum_2_eq_30_proof ⇐ show subprob_arith_sum_2_eq_30 by sorry

  subprob_exp_P_2 :≡ exponent_p_P_val (2:ℕ) = (30:ℕ)
  subprob_exp_P_2_proof ⇐ show subprob_exp_P_2 by sorry
  -- End of new detailed subproblems for subprob_exp_P_2

  subprob_exp_P_3 :≡ exponent_p_P_val (3:ℕ) = (13:ℕ)
  subprob_exp_P_3_proof ⇐ show subprob_exp_P_3 by sorry
  subprob_prime_5 :≡ Nat.Prime (5:ℕ)
  subprob_prime_5_proof ⇐ show subprob_prime_5 by sorry
  sum_factorization_jfact_5_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (5:ℕ))
  subprob_exp_P_5_eq_sum_factorization_jfact_5 :≡ exponent_p_P_val (5:ℕ) = sum_factorization_jfact_5_Icc_1_9
  subprob_exp_P_5_eq_sum_factorization_jfact_5_proof ⇐ show subprob_exp_P_5_eq_sum_factorization_jfact_5 by sorry
  subprob_factorization_eq_padicValNat :≡ ∀ (n p : ℕ), Nat.Prime p → (Nat.factorization n p) = padicValNat p n
  subprob_factorization_eq_padicValNat_proof ⇐ show subprob_factorization_eq_padicValNat by sorry
  sum_padicValNat_5_jfact_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  subprob_sum_factorization_eq_sum_padicValNat :≡ sum_factorization_jfact_5_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_9
  subprob_sum_factorization_eq_sum_padicValNat_proof ⇐ show subprob_sum_factorization_eq_sum_padicValNat by sorry
  subprob_exp_P_5_eq_sum_padicValNat_5 :≡ exponent_p_P_val (5:ℕ) = sum_padicValNat_5_jfact_Icc_1_9
  subprob_exp_P_5_eq_sum_padicValNat_5_proof ⇐ show subprob_exp_P_5_eq_sum_padicValNat_5 by sorry
  subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9 :≡ Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (4 : ℕ) ∪ Finset.Icc (5 : ℕ) (9 : ℕ)
  subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9_proof ⇐ show subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9 by sorry
  subprob_Icc_1_4_disjoint_Icc_5_9 :≡ Disjoint (Finset.Icc (1 : ℕ) (4 : ℕ)) (Finset.Icc (5 : ℕ) (9 : ℕ))
  subprob_Icc_1_4_disjoint_Icc_5_9_proof ⇐ show subprob_Icc_1_4_disjoint_Icc_5_9 by sorry
  sum_padicValNat_5_jfact_Icc_1_4 := ∑ j ∈ Finset.Icc (1 : ℕ) (4 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  sum_padicValNat_5_jfact_Icc_5_9 := ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  subprob_sum_padicValNat_5_jfact_Icc_1_9_split :≡ sum_padicValNat_5_jfact_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9
  subprob_sum_padicValNat_5_jfact_Icc_1_9_split_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_9_split by sorry
  subprob_j_in_Icc_1_4_implies_j_lt_5 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (1:ℕ) (4:ℕ) → j < (5:ℕ)
  subprob_j_in_Icc_1_4_implies_j_lt_5_proof ⇐ show subprob_j_in_Icc_1_4_implies_j_lt_5 by sorry
  subprob_padicValNat_5_jfact_eq_0_when_j_lt_5 :≡ ∀ (j : ℕ), j < (5:ℕ) → Nat.Prime (5:ℕ) → padicValNat (5:ℕ) (Nat.factorial j) = (0:ℕ)
  subprob_padicValNat_5_jfact_eq_0_when_j_lt_5_proof ⇐ show subprob_padicValNat_5_jfact_eq_0_when_j_lt_5 by sorry
  subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0 :≡ sum_padicValNat_5_jfact_Icc_1_4 = (0:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0 by sorry
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (5:ℕ) (9:ℕ) → (5:ℕ) ≤ j ∧ j < (5:ℕ)^2
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25_proof ⇐ show subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25 by sorry
  subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), padicValNat (5:ℕ) (Nat.factorial j) = j / (5:ℕ)
  subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9_proof ⇐ show subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9 by sorry
  subprob_helper_5_gt_0 :≡ (5:ℕ) > 0
  subprob_helper_5_gt_0_proof ⇐ show subprob_helper_5_gt_0 by sorry
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (5:ℕ) (9:ℕ) → (5:ℕ) ≤ j ∧ j < 2 * (5:ℕ)
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10_proof ⇐ show subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10 by sorry
  subprob_j_div_5_eq_1_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), j / (5:ℕ) = (1:ℕ)
  subprob_j_div_5_eq_1_when_j_in_Icc_5_9_proof ⇐ show subprob_j_div_5_eq_1_when_j_in_Icc_5_9 by sorry
  subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), padicValNat (5:ℕ) (Nat.factorial j) = (1:ℕ)
  subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9_proof ⇐ show subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9 by sorry
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1 :≡ sum_padicValNat_5_jfact_Icc_5_9 = ∑ j ∈ Finset.Icc (5:ℕ) (9:ℕ), (1:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1 by sorry
  subprob_card_Icc_5_9 :≡ (Finset.Icc (5:ℕ) (9:ℕ)).card = (5:ℕ)
  subprob_card_Icc_5_9_proof ⇐ show subprob_card_Icc_5_9 by sorry
  subprob_sum_1_Icc_5_9_eq_card :≡ ∑ j ∈ Finset.Icc (5:ℕ) (9:ℕ), (1:ℕ) = (Finset.Icc (5:ℕ) (9:ℕ)).card
  subprob_sum_1_Icc_5_9_eq_card_proof ⇐ show subprob_sum_1_Icc_5_9_eq_card by sorry
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5 :≡ sum_padicValNat_5_jfact_Icc_5_9 = (5:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5 by sorry
  subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value :≡ sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9 = (0:ℕ) + (5:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value by sorry
  subprob_0_plus_5_eq_5 :≡ (0:ℕ) + (5:ℕ) = (5:ℕ)
  subprob_0_plus_5_eq_5_proof ⇐ show subprob_0_plus_5_eq_5 by sorry
  subprob_exp_P_5 :≡ exponent_p_P_val (5:ℕ) = (5:ℕ)
  subprob_exp_P_5_proof ⇐ show subprob_exp_P_5 by sorry
  subprob_prime_7 :≡ Nat.Prime (7:ℕ)
  subprob_prime_7_proof ⇐ show subprob_prime_7 by sorry
  exp_j_fact_7 := fun (j : ℕ) => (Nat.factorization (Nat.factorial j) (7:ℕ))
  sum_exp_factorials_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), exp_j_fact_7 j
  subprob_exp_P_7_eq_sum_exp_factorials_7 :≡ exponent_p_P_val (7:ℕ) = sum_exp_factorials_7
  subprob_exp_P_7_eq_sum_exp_factorials_7_proof ⇐ show subprob_exp_P_7_eq_sum_exp_factorials_7 by sorry
  subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9 :≡ Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (6 : ℕ) ∪ Finset.Icc (7 : ℕ) (9 : ℕ)
  subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9_proof ⇐ show subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9 by sorry
  subprob_Icc_1_6_disjoint_Icc_7_9 :≡ Disjoint (Finset.Icc (1 : ℕ) (6 : ℕ)) (Finset.Icc (7 : ℕ) (9 : ℕ))
  subprob_Icc_1_6_disjoint_Icc_7_9_proof ⇐ show subprob_Icc_1_6_disjoint_Icc_7_9 by sorry
  sum_1_to_6_val_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j
  sum_7_to_9_val_7 := ∑ j ∈ Finset.Icc (7 : ℕ) (9 : ℕ), exp_j_fact_7 j
  subprob_sum_exp_factorials_7_split :≡ sum_exp_factorials_7 = sum_1_to_6_val_7 + sum_7_to_9_val_7
  subprob_sum_exp_factorials_7_split_proof ⇐ show subprob_sum_exp_factorials_7_split by sorry
  subprob_j_in_Icc_1_6_implies_j_lt_7 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (1:ℕ) (6:ℕ) → j < (7:ℕ)
  subprob_j_in_Icc_1_6_implies_j_lt_7_proof ⇐ show subprob_j_in_Icc_1_6_implies_j_lt_7 by sorry
  subprob_exp_j_fact_7_when_j_lt_7 :≡ ∀ (j : ℕ), j < (7:ℕ) → exp_j_fact_7 j = (0:ℕ)
  subprob_exp_j_fact_7_when_j_lt_7_proof ⇐ show subprob_exp_j_fact_7_when_j_lt_7 by sorry
  subprob_sum_1_to_6_val_7_eq_0 :≡ sum_1_to_6_val_7 = (0:ℕ)
  subprob_sum_1_to_6_val_7_eq_0_proof ⇐ show subprob_sum_1_to_6_val_7_eq_0 by sorry
  subprob_exp_7_fact_7_eq_padicValNat_7_fact_7 :≡ exp_j_fact_7 (7:ℕ) = padicValNat (7:ℕ) (Nat.factorial (7:ℕ))
  subprob_exp_7_fact_7_eq_padicValNat_7_fact_7_proof ⇐ show subprob_exp_7_fact_7_eq_padicValNat_7_fact_7 by sorry
  subprob_padicValNat_7_7fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (7:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (7:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_7fact_legendre_proof ⇐ show subprob_padicValNat_7_7fact_legendre by sorry
  subprob_Nat_log_7_7_eq_1 :≡ Nat.log (7:ℕ) (7:ℕ) = (1:ℕ)
  subprob_Nat_log_7_7_eq_1_proof ⇐ show subprob_Nat_log_7_7_eq_1 by sorry
  sum_legendre_7_7fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (7:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_rewritten_log :≡ sum_legendre_7_7fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_7fact_rewritten_log by sorry
  subprob_one_plus_one_eq_two :≡ (1:ℕ) + (1:ℕ) = (2:ℕ)
  subprob_one_plus_one_eq_two_proof ⇐ show subprob_one_plus_one_eq_two by sorry
  subprob_sum_legendre_7_7fact_ico_1_2 :≡ sum_legendre_7_7fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_7fact_ico_1_2 by sorry
  subprob_Finset_Ico_1_2_eq_singleton_1 :≡ Finset.Ico (1:ℕ) (2:ℕ) = ({(1:ℕ)} : Finset ℕ)
  subprob_Finset_Ico_1_2_eq_singleton_1_proof ⇐ show subprob_Finset_Ico_1_2_eq_singleton_1 by sorry
  subprob_sum_legendre_7_7fact_is_7_div_7_pow_1 :≡ sum_legendre_7_7fact = (7:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_7fact_is_7_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_7fact_is_7_div_7_pow_1 by sorry
  subprob_7_pow_1_eq_7 :≡ ((7:ℕ):ℕ)^(1:ℕ) = (7:ℕ)
  subprob_7_pow_1_eq_7_proof ⇐ show subprob_7_pow_1_eq_7 by sorry
  subprob_7_div_7_eq_1 :≡ (7:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_7_div_7_eq_1_proof ⇐ show subprob_7_div_7_eq_1 by sorry
  subprob_sum_legendre_7_7fact_eval_to_1 :≡ (7:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_7fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_7fact_eval_to_1 by sorry
  subprob_padicValNat_7_of_7fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (7:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_7fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_7fact_eq_1 by sorry
  subprob_exp_7_fact_7_eq_1 :≡ exp_j_fact_7 (7:ℕ) = (1:ℕ)
  subprob_exp_7_fact_7_eq_1_proof ⇐ show subprob_exp_7_fact_7_eq_1 by sorry
  subprob_exp_8_fact_7_eq_padicValNat_7_fact_8 :≡ exp_j_fact_7 (8:ℕ) = padicValNat (7:ℕ) (Nat.factorial (8:ℕ))
  subprob_exp_8_fact_7_eq_padicValNat_7_fact_8_proof ⇐ show subprob_exp_8_fact_7_eq_padicValNat_7_fact_8 by sorry
  subprob_padicValNat_7_8fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (8:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (8:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_8fact_legendre_proof ⇐ show subprob_padicValNat_7_8fact_legendre by sorry
  subprob_Nat_log_7_8_eq_1 :≡ Nat.log (7:ℕ) (8:ℕ) = (1:ℕ)
  subprob_Nat_log_7_8_eq_1_proof ⇐ show subprob_Nat_log_7_8_eq_1 by sorry
  sum_legendre_7_8fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (8:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_rewritten_log :≡ sum_legendre_7_8fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_8fact_rewritten_log by sorry
  subprob_sum_legendre_7_8fact_ico_1_2 :≡ sum_legendre_7_8fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_8fact_ico_1_2 by sorry
  subprob_sum_legendre_7_8fact_is_8_div_7_pow_1 :≡ sum_legendre_7_8fact = (8:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_8fact_is_8_div_7_pow_1 by sorry
  subprob_8_div_7_eq_1 :≡ (8:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_8_div_7_eq_1_proof ⇐ show subprob_8_div_7_eq_1 by sorry
  subprob_sum_legendre_7_8fact_eval_to_1 :≡ (8:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_8fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_8fact_eval_to_1 by sorry
  subprob_padicValNat_7_of_8fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (8:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_8fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_8fact_eq_1 by sorry
  subprob_exp_8_fact_7_eq_1 :≡ exp_j_fact_7 (8:ℕ) = (1:ℕ)
  subprob_exp_8_fact_7_eq_1_proof ⇐ show subprob_exp_8_fact_7_eq_1 by sorry
  subprob_exp_9_fact_7_eq_padicValNat_7_fact_9 :≡ exp_j_fact_7 (9:ℕ) = padicValNat (7:ℕ) (Nat.factorial (9:ℕ))
  subprob_exp_9_fact_7_eq_padicValNat_7_fact_9_proof ⇐ show subprob_exp_9_fact_7_eq_padicValNat_7_fact_9 by sorry
  subprob_padicValNat_7_9fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (9:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (9:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_9fact_legendre_proof ⇐ show subprob_padicValNat_7_9fact_legendre by sorry
  subprob_Nat_log_7_9_eq_1 :≡ Nat.log (7:ℕ) (9:ℕ) = (1:ℕ)
  subprob_Nat_log_7_9_eq_1_proof ⇐ show subprob_Nat_log_7_9_eq_1 by sorry
  sum_legendre_7_9fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (9:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_rewritten_log :≡ sum_legendre_7_9fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_9fact_rewritten_log by sorry
  subprob_sum_legendre_7_9fact_ico_1_2 :≡ sum_legendre_7_9fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_9fact_ico_1_2 by sorry
  subprob_sum_legendre_7_9fact_is_9_div_7_pow_1 :≡ sum_legendre_7_9fact = (9:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_9fact_is_9_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_9fact_is_9_div_7_pow_1 by sorry
  subprob_9_div_7_eq_1 :≡ (9:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_9_div_7_eq_1_proof ⇐ show subprob_9_div_7_eq_1 by sorry
  subprob_sum_legendre_7_9fact_eval_to_1 :≡ (9:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_9fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_9fact_eval_to_1 by sorry
  subprob_padicValNat_7_of_9fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (9:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_9fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_9fact_eq_1 by sorry
  subprob_exp_9_fact_7_eq_1 :≡ exp_j_fact_7 (9:ℕ) = (1:ℕ)
  subprob_exp_9_fact_7_eq_1_proof ⇐ show subprob_exp_9_fact_7_eq_1 by sorry
  subprob_Icc_7_9_eq_7_8_9 :≡ Finset.Icc (7 : ℕ) (9 : ℕ) = ({(7:ℕ), (8:ℕ), (9:ℕ)} : Finset ℕ)
  subprob_Icc_7_9_eq_7_8_9_proof ⇐ show subprob_Icc_7_9_eq_7_8_9 by sorry
  subprob_sum_7_to_9_val_7_expanded :≡ sum_7_to_9_val_7 = exp_j_fact_7 (7:ℕ) + exp_j_fact_7 (8:ℕ) + exp_j_fact_7 (9:ℕ)
  subprob_sum_7_to_9_val_7_expanded_proof ⇐ show subprob_sum_7_to_9_val_7_expanded by sorry
  subprob_sum_7_to_9_val_7_calc_values :≡ exp_j_fact_7 (7:ℕ) + exp_j_fact_7 (8:ℕ) + exp_j_fact_7 (9:ℕ) = (1:ℕ) + (1:ℕ) + (1:ℕ)
  subprob_sum_7_to_9_val_7_calc_values_proof ⇐ show subprob_sum_7_to_9_val_7_calc_values by sorry
  subprob_1_plus_1_plus_1_eq_3 :≡ (1:ℕ) + (1:ℕ) + (1:ℕ) = (3:ℕ)
  subprob_1_plus_1_plus_1_eq_3_proof ⇐ show subprob_1_plus_1_plus_1_eq_3 by sorry
  subprob_sum_7_to_9_val_7_eq_3 :≡ sum_7_to_9_val_7 = (3:ℕ)
  subprob_sum_7_to_9_val_7_eq_3_proof ⇐ show subprob_sum_7_to_9_val_7_eq_3 by sorry
  subprob_sum_exp_factorials_7_calc_value :≡ sum_1_to_6_val_7 + sum_7_to_9_val_7 = (0:ℕ) + (3:ℕ)
  subprob_sum_exp_factorials_7_calc_value_proof ⇐ show subprob_sum_exp_factorials_7_calc_value by sorry
  subprob_0_plus_3_eq_3 :≡ (0:ℕ) + (3:ℕ) = (3:ℕ)
  subprob_0_plus_3_eq_3_proof ⇐ show subprob_0_plus_3_eq_3 by sorry
  subprob_sum_exp_factorials_7_eq_3 :≡ sum_exp_factorials_7 = (3:ℕ)
  subprob_sum_exp_factorials_7_eq_3_proof ⇐ show subprob_sum_exp_factorials_7_eq_3 by sorry
  subprob_exp_P_7 :≡ exponent_p_P_val (7:ℕ) = (3:ℕ)
  subprob_exp_P_7_proof ⇐ show subprob_exp_P_7 by sorry
  subprob_exp_P_other :≡ ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_gt_7 : p > (7:ℕ)), exponent_p_P_val p = (0:ℕ)
  subprob_exp_P_other_proof ⇐ show subprob_exp_P_other by sorry
  subprob_P_val_factorization_support :≡ (Nat.factorization P_val).support = ({(2:ℕ),(3:ℕ),(5:ℕ),(7:ℕ)} : Finset ℕ)
  subprob_P_val_factorization_support_proof ⇐ show subprob_P_val_factorization_support by sorry
  M_val := ∏ p ∈ (Nat.factorization P_val).support, p ^ (exponent_p_P_val p / (2:ℕ))
  subprob_M_val_eq_product :≡ M_val = (2:ℕ)^(15:ℕ) * (3:ℕ)^(6:ℕ) * (5:ℕ)^(2:ℕ) * (7:ℕ)^(1:ℕ)
  subprob_M_val_eq_product_proof ⇐ show subprob_M_val_eq_product by sorry
  subprob_M_val_pos :≡ M_val > (0:ℕ)
  subprob_M_val_pos_proof ⇐ show subprob_M_val_pos by sorry
  subprob_S_equiv_divisors_of_M :≡ ∀ (k : ℕ), k ∈ S ↔ ((0:ℕ) < k ∧ k ∣ M_val)
  subprob_S_equiv_divisors_of_M_proof ⇐ show subprob_S_equiv_divisors_of_M by sorry
  subprob_card_S_eq_num_divisors_M :≡ S.card = (Nat.divisors M_val).card
  subprob_card_S_eq_num_divisors_M_proof ⇐ show subprob_card_S_eq_num_divisors_M by sorry
  subprob_card_divisors_M_formula :≡ (Nat.divisors M_val).card = ∏ p ∈ (Nat.factorization M_val).support, ((Nat.factorization M_val p) + (1:ℕ))
  subprob_card_divisors_M_formula_proof ⇐ show subprob_card_divisors_M_formula by sorry
  subprob_factorization_M_val_support :≡ (Nat.factorization M_val).support = ({(2:ℕ),(3:ℕ),(5:ℕ),(7:ℕ)} : Finset ℕ)
  subprob_factorization_M_val_support_proof ⇐ show subprob_factorization_M_val_support by sorry
  subprob_exp_M_2 :≡ (Nat.factorization M_val (2:ℕ)) = (15:ℕ)
  subprob_exp_M_2_proof ⇐ show subprob_exp_M_2 by sorry
  subprob_exp_M_3 :≡ (Nat.factorization M_val (3:ℕ)) = (6:ℕ)
  subprob_exp_M_3_proof ⇐ show subprob_exp_M_3 by sorry
  subprob_exp_M_5 :≡ (Nat.factorization M_val (5:ℕ)) = (2:ℕ)
  subprob_exp_M_5_proof ⇐ show subprob_exp_M_5 by sorry
  subprob_exp_M_7 :≡ (Nat.factorization M_val (7:ℕ)) = (1:ℕ)
  subprob_exp_M_7_proof ⇐ show subprob_exp_M_7 by sorry
  subprob_card_S_product_form :≡ S.card = ((15:ℕ)+(1:ℕ))*((6:ℕ)+(1:ℕ))*((2:ℕ)+(1:ℕ))*((1:ℕ)+(1:ℕ))
  subprob_card_S_product_form_proof ⇐ show subprob_card_S_product_form by sorry
  subprob_calculation :≡ ((15:ℕ)+(1:ℕ))*((6:ℕ)+(1:ℕ))*((2:ℕ)+(1:ℕ))*((1:ℕ)+(1:ℕ)) = (672:ℕ)
  subprob_calculation_proof ⇐ show subprob_calculation by sorry
  subprob_final_goal :≡ S.card = (672:ℕ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketch with proof
variable (S: Finset ℕ) (h₀: ∀ (k : ℕ), k ∈ S ↔ (0 : ℕ) < k ∧ k * k ∣ ∏ i ∈ Finset.Icc (1 : ℕ) (9 : ℕ), i !)
play
  P_val := (∏ i in (Finset.Icc (1 : ℕ) (9 : ℕ)), Nat.factorial i)
  subprob_P_val_pos :≡ P_val > (0 : ℕ)
  subprob_P_val_pos_proof ⇐ show subprob_P_val_pos by
    rw [P_val_def]
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp [Finset.mem_Icc] at hi
    norm_num
    <;> simp [Nat.factorial_ne_zero]
  exponent_p_P_val := fun (p : ℕ) => (Nat.factorization P_val) p
  subprob_relation_exponent_P_val_to_factorials :≡ ∀ (p : ℕ) (hp : Nat.Prime p), exponent_p_P_val p = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) p)
  subprob_relation_exponent_P_val_to_factorials_proof ⇐ show subprob_relation_exponent_P_val_to_factorials by
    intro p hp
    rw [exponent_p_P_val_def' p]
    rw [P_val_def]
    have h_nonzero : ∀ (x : ℕ), x ∈ Finset.Icc 1 9 → Nat.factorial x ≠ 0 := by
      intro x hx
      apply Nat.factorial_ne_zero
    have h_map_equality : (Finset.prod (Finset.Icc 1 9) Nat.factorial).factorization = ∑ x ∈ Finset.Icc 1 9, (Nat.factorial x).factorization :=
      Nat.factorization_prod h_nonzero
    rw [h_map_equality]
    rfl
  subprob_prime_2 :≡ Nat.Prime (2:ℕ)
  subprob_prime_2_proof ⇐ show subprob_prime_2 by
    apply Nat.prime_two
  subprob_exp_P_2_eq_sum_factorization :≡ exponent_p_P_val (2:ℕ) = ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2:ℕ))
  subprob_exp_P_2_eq_sum_factorization_proof ⇐ show subprob_exp_P_2_eq_sum_factorization by
    rw [subprob_relation_exponent_P_val_to_factorials_proof 2 subprob_prime_2_proof]
    <;> simp [exponent_p_P_val_def']
    <;> norm_num
    <;> linarith
  subprob_factorization_jfact_p_eq_padicValNat_jfact_p :≡ ∀ (p j : ℕ), Nat.Prime p → (Nat.factorization (Nat.factorial j) p) = padicValNat p (Nat.factorial j)
  subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof ⇐ show subprob_factorization_jfact_p_eq_padicValNat_jfact_p by
    intro p j hp
    simp [padicValNat, Nat.factorization, hp]
    <;> rfl
  sum_factorization_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (2:ℕ))
  sum_padicValNat_2_jfact := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (2:ℕ) (Nat.factorial j)
  subprob_sum_factorization_eq_sum_padicValNat_for_2 :≡ sum_factorization_2_jfact = sum_padicValNat_2_jfact
  subprob_sum_factorization_eq_sum_padicValNat_for_2_proof ⇐ show subprob_sum_factorization_eq_sum_padicValNat_for_2 by
    have h₁ : ∀ j : ℕ, (Nat.factorization j !) 2 = padicValNat 2 j ! := by
      intro j
      apply subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof
      exact subprob_prime_2_proof
    simp_all [Finset.sum_congr]
  subprob_exp_P_2_eq_sum_padicValNat :≡ exponent_p_P_val (2:ℕ) = sum_padicValNat_2_jfact
  subprob_exp_P_2_eq_sum_padicValNat_proof ⇐ show subprob_exp_P_2_eq_sum_padicValNat by
    have h₀ := subprob_sum_factorization_eq_sum_padicValNat_for_2_proof
    simp_all
  val_1fact_2 := padicValNat (2:ℕ) (Nat.factorial (1:ℕ))
  val_2fact_2 := padicValNat (2:ℕ) (Nat.factorial (2:ℕ))
  val_3fact_2 := padicValNat (2:ℕ) (Nat.factorial (3:ℕ))
  val_4fact_2 := padicValNat (2:ℕ) (Nat.factorial (4:ℕ))
  val_5fact_2 := padicValNat (2:ℕ) (Nat.factorial (5:ℕ))
  val_6fact_2 := padicValNat (2:ℕ) (Nat.factorial (6:ℕ))
  val_7fact_2 := padicValNat (2:ℕ) (Nat.factorial (7:ℕ))
  val_8fact_2 := padicValNat (2:ℕ) (Nat.factorial (8:ℕ))
  val_9fact_2 := padicValNat (2:ℕ) (Nat.factorial (9:ℕ))
  subprob_1_fact_val :≡ Nat.factorial (1:ℕ) = (1:ℕ)
  subprob_1_fact_val_proof ⇐ show subprob_1_fact_val by
    simp [Nat.factorial]
    <;> simp
    <;> simp
    <;> simp
  subprob_padicValNat_2_1_is_0 :≡ padicValNat (2:ℕ) (1:ℕ) = (0:ℕ)
  subprob_padicValNat_2_1_is_0_proof ⇐ show subprob_padicValNat_2_1_is_0 by
    simp [val_1fact_2_def, subprob_1_fact_val_proof, padicValNat.one]
  subprob_val_1fact_2_eq_0 :≡ val_1fact_2 = (0:ℕ)
  subprob_val_1fact_2_eq_0_proof ⇐ show subprob_val_1fact_2_eq_0 by
    rw [val_1fact_2_def, subprob_1_fact_val_proof]
    exact subprob_padicValNat_2_1_is_0_proof
  subprob_2_fact_val :≡ Nat.factorial (2:ℕ) = (2:ℕ)
  subprob_2_fact_val_proof ⇐ show subprob_2_fact_val by
    norm_num
    <;> rfl
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_padicValNat_2_2_is_1 :≡ padicValNat (2:ℕ) (2:ℕ) = (1:ℕ)
  subprob_padicValNat_2_2_is_1_proof ⇐ show subprob_padicValNat_2_2_is_1 by
    simp [padicValNat, subprob_2_fact_val_proof]
    <;> omega
  subprob_val_2fact_2_eq_1 :≡ val_2fact_2 = (1:ℕ)
  subprob_val_2fact_2_eq_1_proof ⇐ show subprob_val_2fact_2_eq_1 by
    simp [val_2fact_2_def, subprob_padicValNat_2_2_is_1_proof]
  subprob_3_fact_val :≡ Nat.factorial (3:ℕ) = (6:ℕ)
  subprob_3_fact_val_proof ⇐ show subprob_3_fact_val by
    norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  subprob_6_eq_2_mul_3 :≡ (6:ℕ) = (2:ℕ) * (3:ℕ)
  subprob_6_eq_2_mul_3_proof ⇐ show subprob_6_eq_2_mul_3 by
    have h : (3 : ℕ)! = (6 : ℕ) := subprob_3_fact_val_proof
    simp [Nat.factorial, Nat.mul_succ, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    <;> omega
  subprob_2_ne_zero :≡ (2:ℕ) ≠ (0:ℕ)
  subprob_2_ne_zero_proof ⇐ show subprob_2_ne_zero by
    decide
  subprob_3_ne_zero :≡ (3:ℕ) ≠ (0:ℕ)
  subprob_3_ne_zero_proof ⇐ show subprob_3_ne_zero by
    decide
  subprob_padicValNat_2_6_mul :≡ padicValNat (2:ℕ) ((2:ℕ)*(3:ℕ)) = padicValNat (2:ℕ) (2:ℕ) + padicValNat (2:ℕ) (3:ℕ)
  subprob_padicValNat_2_6_mul_proof ⇐ show subprob_padicValNat_2_6_mul by
    rw [padicValNat.mul]
    <;> simp [Nat.prime_two]
    <;> rw [padicValNat.self]
    <;> norm_num
    <;> simp [Nat.Prime.dvd_iff_not_coprime]
    <;> norm_num
  subprob_padicValNat_2_3_is_0 :≡ padicValNat (2:ℕ) (3:ℕ) = (0:ℕ)
  subprob_padicValNat_2_3_is_0_proof ⇐ show subprob_padicValNat_2_3_is_0 by
    rw [padicValNat.eq_zero_of_not_dvd]
    norm_num
    <;> decide
  subprob_1_plus_0_eq_1 :≡ (1:ℕ) + (0:ℕ) = (1:ℕ)
  subprob_1_plus_0_eq_1_proof ⇐ show subprob_1_plus_0_eq_1 by
    rw [Nat.add_zero]
  subprob_padicValNat_2_6_is_1 :≡ padicValNat (2:ℕ) (6:ℕ) = (1:ℕ)
  subprob_padicValNat_2_6_is_1_proof ⇐ show subprob_padicValNat_2_6_is_1 by
    simp_all [padicValNat.mul, Nat.Prime.ne_zero, Nat.Prime.ne_one]
    <;> decide
  subprob_val_3fact_2_eq_1 :≡ val_3fact_2 = (1:ℕ)
  subprob_val_3fact_2_eq_1_proof ⇐ show subprob_val_3fact_2_eq_1 by
    simp_all [val_3fact_2_def, subprob_padicValNat_2_6_is_1_proof]
    <;> decide
  subprob_4_fact_val :≡ Nat.factorial (4:ℕ) = (24:ℕ)
  subprob_4_fact_val_proof ⇐ show subprob_4_fact_val by
    norm_num
    <;> rfl
  subprob_24_eq_2p3_mul_3 :≡ (24:ℕ) = (2:ℕ)^3 * (3:ℕ)
  subprob_24_eq_2p3_mul_3_proof ⇐ show subprob_24_eq_2p3_mul_3 by
    norm_num [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> rfl
  subprob_2p3_ne_zero :≡ (2:ℕ)^3 ≠ (0:ℕ)
  subprob_2p3_ne_zero_proof ⇐ show subprob_2p3_ne_zero by
    norm_num
    <;> decide
    <;> norm_num
    <;> decide
  subprob_padicValNat_2_24_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^3*(3:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^3) + padicValNat (2:ℕ) (3:ℕ)
  subprob_padicValNat_2_24_mul_proof ⇐ show subprob_padicValNat_2_24_mul by
    rw [padicValNat.mul]
    <;> norm_num
    <;> simp
    <;> norm_num
    <;> simp
    <;> norm_num
  subprob_padicValNat_2_2p3_is_3 :≡ padicValNat (2:ℕ) ((2:ℕ)^3) = (3:ℕ)
  subprob_padicValNat_2_2p3_is_3_proof ⇐ show subprob_padicValNat_2_2p3_is_3 by
    rw [padicValNat.pow]
    <;> simp [Nat.Prime.ne_zero]
    <;> norm_num
    <;> rfl
  subprob_3_plus_0_eq_3 :≡ (3:ℕ) + (0:ℕ) = (3:ℕ)
  subprob_3_plus_0_eq_3_proof ⇐ show subprob_3_plus_0_eq_3 by
    apply add_zero
    <;> simp
    <;> linarith
  subprob_padicValNat_2_24_is_3 :≡ padicValNat (2:ℕ) (24:ℕ) = (3:ℕ)
  subprob_padicValNat_2_24_is_3_proof ⇐ show subprob_padicValNat_2_24_is_3 by
    rw [subprob_24_eq_2p3_mul_3_proof]
    rw [subprob_padicValNat_2_24_mul_proof]
    rw [subprob_padicValNat_2_2p3_is_3_proof]
    simp [subprob_3_plus_0_eq_3_proof]
  subprob_val_4fact_2_eq_3 :≡ val_4fact_2 = (3:ℕ)
  subprob_val_4fact_2_eq_3_proof ⇐ show subprob_val_4fact_2_eq_3 by
    rw [val_4fact_2_def]
    rw [subprob_4_fact_val_proof]
    rw [subprob_padicValNat_2_24_is_3_proof]
    <;> simp
  subprob_5_fact_val :≡ Nat.factorial (5:ℕ) = (120:ℕ)
  subprob_5_fact_val_proof ⇐ show subprob_5_fact_val by
    norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  subprob_120_eq_2p3_mul_15 :≡ (120:ℕ) = (2:ℕ)^3 * (15:ℕ)
  subprob_120_eq_2p3_mul_15_proof ⇐ show subprob_120_eq_2p3_mul_15 by
    norm_num [Nat.factorial, Nat.pow_succ, Nat.factorial, Nat.pow_succ]
    <;> decide
  subprob_15_ne_zero :≡ (15:ℕ) ≠ (0:ℕ)
  subprob_15_ne_zero_proof ⇐ show subprob_15_ne_zero by
    norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_padicValNat_2_120_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^3*(15:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^3) + padicValNat (2:ℕ) (15:ℕ)
  subprob_padicValNat_2_120_mul_proof ⇐ show subprob_padicValNat_2_120_mul by
    rw [padicValNat.mul]
    <;> simp [subprob_15_ne_zero_proof]
    <;> norm_num
    <;> simp [padicValNat.pow]
    <;> norm_num
  subprob_padicValNat_2_15_is_0 :≡ padicValNat (2:ℕ) (15:ℕ) = (0:ℕ)
  subprob_padicValNat_2_15_is_0_proof ⇐ show subprob_padicValNat_2_15_is_0 by
    apply padicValNat.eq_zero_of_not_dvd
    norm_num
    <;> decide
  subprob_padicValNat_2_120_is_3 :≡ padicValNat (2:ℕ) (120:ℕ) = (3:ℕ)
  subprob_padicValNat_2_120_is_3_proof ⇐ show subprob_padicValNat_2_120_is_3 by
    have h₁ := subprob_padicValNat_2_15_is_0_proof
    have h₂ := subprob_padicValNat_2_2p3_is_3_proof
    have h₃ := subprob_padicValNat_2_2_is_1_proof
    have h₄ := subprob_padicValNat_2_3_is_0_proof
    simp_all [padicValNat.mul, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  subprob_val_5fact_2_eq_3 :≡ val_5fact_2 = (3:ℕ)
  subprob_val_5fact_2_eq_3_proof ⇐ show subprob_val_5fact_2_eq_3 by
    rw [val_5fact_2_def]
    apply subprob_padicValNat_2_120_is_3_proof
  subprob_6_fact_val :≡ Nat.factorial (6:ℕ) = (720:ℕ)
  subprob_6_fact_val_proof ⇐ show subprob_6_fact_val by
    norm_num [Nat.factorial]
  subprob_720_eq_2p4_mul_45 :≡ (720:ℕ) = (2:ℕ)^4 * (45:ℕ)
  subprob_720_eq_2p4_mul_45_proof ⇐ show subprob_720_eq_2p4_mul_45 by
    have h₀ : (6 : ℕ)! = (720 : ℕ) := subprob_6_fact_val_proof
    simp [h₀, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> decide
  subprob_2p4_ne_zero :≡ (2:ℕ)^4 ≠ (0:ℕ)
  subprob_2p4_ne_zero_proof ⇐ show subprob_2p4_ne_zero by
    norm_num
    <;> decide
  subprob_45_ne_zero :≡ (45:ℕ) ≠ (0:ℕ)
  subprob_45_ne_zero_proof ⇐ show subprob_45_ne_zero by
    norm_num
  subprob_padicValNat_2_720_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^4*(45:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^4) + padicValNat (2:ℕ) (45:ℕ)
  subprob_padicValNat_2_720_mul_proof ⇐ show subprob_padicValNat_2_720_mul by
    rw [padicValNat.mul]
    <;> simp [Nat.prime_two]
    <;> norm_num
    <;> assumption
    <;> ring
  subprob_padicValNat_2_2p4_is_4 :≡ padicValNat (2:ℕ) ((2:ℕ)^4) = (4:ℕ)
  subprob_padicValNat_2_2p4_is_4_proof ⇐ show subprob_padicValNat_2_2p4_is_4 by
    rw [padicValNat.pow]
    <;> simp [Nat.Prime.ne_zero]
    <;> norm_num
    <;> linarith
  subprob_padicValNat_2_45_is_0 :≡ padicValNat (2:ℕ) (45:ℕ) = (0:ℕ)
  subprob_padicValNat_2_45_is_0_proof ⇐ show subprob_padicValNat_2_45_is_0 by
    rw [show 45 = 15 * 3 by norm_num]
    rw [padicValNat.mul] <;> simp [subprob_padicValNat_2_15_is_0_proof]
    <;> norm_num
  subprob_4_plus_0_eq_4 :≡ (4:ℕ) + (0:ℕ) = (4:ℕ)
  subprob_4_plus_0_eq_4_proof ⇐ show subprob_4_plus_0_eq_4 by
    norm_num
    <;> decide
    <;> decide
    <;> decide
    <;> decide
  subprob_padicValNat_2_720_is_4 :≡ padicValNat (2:ℕ) (720:ℕ) = (4:ℕ)
  subprob_padicValNat_2_720_is_4_proof ⇐ show subprob_padicValNat_2_720_is_4 by
    rw [subprob_720_eq_2p4_mul_45_proof]
    rw [subprob_padicValNat_2_720_mul_proof]
    rw [subprob_padicValNat_2_2p4_is_4_proof, subprob_padicValNat_2_45_is_0_proof]
  subprob_val_6fact_2_eq_4 :≡ val_6fact_2 = (4:ℕ)
  subprob_val_6fact_2_eq_4_proof ⇐ show subprob_val_6fact_2_eq_4 by
    simp_all only [val_6fact_2_def, subprob_padicValNat_2_720_is_4_proof]
    <;> rfl
  subprob_7_fact_val :≡ Nat.factorial (7:ℕ) = (5040:ℕ)
  subprob_7_fact_val_proof ⇐ show subprob_7_fact_val by
    rw [Nat.factorial]
    <;> norm_num
    <;> rfl
  subprob_5040_eq_2p4_mul_315 :≡ (5040:ℕ) = (2:ℕ)^4 * (315:ℕ)
  subprob_5040_eq_2p4_mul_315_proof ⇐ show subprob_5040_eq_2p4_mul_315 by
    norm_num [Nat.factorial]
    <;> norm_num
    <;> ring
    <;> linarith
  subprob_315_ne_zero :≡ (315:ℕ) ≠ (0:ℕ)
  subprob_315_ne_zero_proof ⇐ show subprob_315_ne_zero by
    decide
  subprob_padicValNat_2_5040_mul :≡ padicValNat (2:ℕ) ((2:ℕ)^4*(315:ℕ)) = padicValNat (2:ℕ) ((2:ℕ)^4) + padicValNat (2:ℕ) (315:ℕ)
  subprob_padicValNat_2_5040_mul_proof ⇐ show subprob_padicValNat_2_5040_mul by
    rw [padicValNat.mul]
    <;> norm_num
    <;> assumption
    <;> ring
    <;> norm_num
    <;> assumption
  subprob_padicValNat_2_315_is_0 :≡ padicValNat (2:ℕ) (315:ℕ) = (0:ℕ)
  subprob_padicValNat_2_315_is_0_proof ⇐ show subprob_padicValNat_2_315_is_0 by
    rw [padicValNat.eq_zero_of_not_dvd]
    norm_num
    <;> decide
  subprob_padicValNat_2_5040_is_4 :≡ padicValNat (2:ℕ) (5040:ℕ) = (4:ℕ)
  subprob_padicValNat_2_5040_is_4_proof ⇐ show subprob_padicValNat_2_5040_is_4 by
    rw [subprob_5040_eq_2p4_mul_315_proof]
    rw [subprob_padicValNat_2_5040_mul_proof]
    rw [subprob_padicValNat_2_2p4_is_4_proof]
    rw [subprob_padicValNat_2_315_is_0_proof]
    <;> simp
  subprob_val_7fact_2_eq_4 :≡ val_7fact_2 = (4:ℕ)
  subprob_val_7fact_2_eq_4_proof ⇐ show subprob_val_7fact_2_eq_4 by
    rw [val_7fact_2_def]
    apply subprob_padicValNat_2_5040_is_4_proof
  subprob_Nat_log_2_8 :≡ Nat.log (2:ℕ) (8:ℕ) = (3:ℕ)
  subprob_Nat_log_2_8_proof ⇐ show subprob_Nat_log_2_8 by
    rw [Nat.log_eq_iff]
    <;> norm_num
    <;> linarith [Nat.pow_succ 2 3]
    <;> apply Nat.log_eq_iff
    <;> norm_num
    <;> linarith [Nat.pow_succ 2 3]
  legendre_b_8 := (4:ℕ)
  subprob_legendre_cond_8 :≡ Nat.log (2:ℕ) (8:ℕ) < legendre_b_8
  subprob_legendre_cond_8_proof ⇐ show subprob_legendre_cond_8 by
    rw [subprob_Nat_log_2_8_proof]
    rw [legendre_b_8_def]
    linarith
  sum_legendre_8fact_raw := ∑ i ∈ Finset.Ico (1:ℕ) legendre_b_8, (8:ℕ) / ((2:ℕ)^i)
  subprob_padicValNat_2_8fact_legendre :≡ padicValNat (2:ℕ) (Nat.factorial (8:ℕ)) = sum_legendre_8fact_raw
  subprob_padicValNat_2_8fact_legendre_proof ⇐ show subprob_padicValNat_2_8fact_legendre by
    have h_prime_2 : (2 : ℕ).Prime := subprob_prime_2_proof
    haveI : Fact (2 : ℕ).Prime := ⟨h_prime_2⟩
    rw [padicValNat_factorial (p := (2 : ℕ)) (n := (8 : ℕ)) (b := legendre_b_8) subprob_legendre_cond_8_proof]
    rw [sum_legendre_8fact_raw_def]
  subprob_Ico_1_4_is_123 :≡ Finset.Ico (1:ℕ) (4:ℕ) = ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ)
  subprob_Ico_1_4_is_123_proof ⇐ show subprob_Ico_1_4_is_123 by
    ext x
    simp [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  subprob_sum_legendre_8fact_set_rewrite :≡ sum_legendre_8fact_raw = ∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (8:ℕ) / ((2:ℕ)^i)
  subprob_sum_legendre_8fact_set_rewrite_proof ⇐ show subprob_sum_legendre_8fact_set_rewrite by
    rw [sum_legendre_8fact_raw_def, legendre_b_8_def]
    rw [subprob_Ico_1_4_is_123_proof]
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_sum_legendre_8fact_expanded :≡ (∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (8:ℕ) / ((2:ℕ)^i)) = (8:ℕ)/((2:ℕ)^1) + (8:ℕ)/((2:ℕ)^2) + (8:ℕ)/((2:ℕ)^3)
  subprob_sum_legendre_8fact_expanded_proof ⇐ show subprob_sum_legendre_8fact_expanded by
    have h : Finset.Ico (1 : ℕ) (4 : ℕ) = ({1, 2, 3} : Finset ℕ) := by
      apply subprob_Ico_1_4_is_123_proof
    simp [h, Finset.sum_Ico_succ_top, Nat.div_eq_of_lt]
    <;> norm_num
  subprob_term1_8_div_2p1 :≡ (8:ℕ) / (2:ℕ)^1 = (4:ℕ)
  subprob_term1_8_div_2p1_proof ⇐ show subprob_term1_8_div_2p1 by
    norm_num
    <;> decide
    <;> norm_num
    <;> decide
  subprob_term2_8_div_2p2 :≡ (8:ℕ) / (2:ℕ)^2 = (2:ℕ)
  subprob_term2_8_div_2p2_proof ⇐ show subprob_term2_8_div_2p2 by
    norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_term3_8_div_2p3 :≡ (8:ℕ) / (2:ℕ)^3 = (1:ℕ)
  subprob_term3_8_div_2p3_proof ⇐ show subprob_term3_8_div_2p3 by
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt]
    <;> rfl
    <;> linarith
  subprob_4_plus_2_plus_1_eq_7 :≡ (4:ℕ) + (2:ℕ) + (1:ℕ) = (7:ℕ)
  subprob_4_plus_2_plus_1_eq_7_proof ⇐ show subprob_4_plus_2_plus_1_eq_7 by
    norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  subprob_sum_legendre_8fact_calc :≡ sum_legendre_8fact_raw = (7:ℕ)
  subprob_sum_legendre_8fact_calc_proof ⇐ show subprob_sum_legendre_8fact_calc by
    rw [subprob_sum_legendre_8fact_set_rewrite_proof]
    simp [Finset.sum_insert, Finset.sum_singleton, subprob_term1_8_div_2p1_proof,
      subprob_term2_8_div_2p2_proof, subprob_term3_8_div_2p3_proof]
    <;> norm_num
  subprob_val_8fact_2_eq_7 :≡ val_8fact_2 = (7:ℕ)
  subprob_val_8fact_2_eq_7_proof ⇐ show subprob_val_8fact_2_eq_7 by
    simp_all only [val_8fact_2_def, subprob_padicValNat_2_8fact_legendre_proof, subprob_sum_legendre_8fact_calc_proof]
    <;> norm_num
    <;> rfl
  subprob_Nat_log_2_9 :≡ Nat.log (2:ℕ) (9:ℕ) = (3:ℕ)
  subprob_Nat_log_2_9_proof ⇐ show subprob_Nat_log_2_9 by
    rw [Nat.log_eq_iff]
    <;> norm_num
    <;> decide
  legendre_b_9 := (4:ℕ)
  subprob_legendre_cond_9 :≡ Nat.log (2:ℕ) (9:ℕ) < legendre_b_9
  subprob_legendre_cond_9_proof ⇐ show subprob_legendre_cond_9 by
    have h₀ : Nat.log (2 : ℕ) (9 : ℕ) = (3 : ℕ) := subprob_Nat_log_2_9_proof
    have h₁ : legendre_b_9 = (4 : ℕ) := legendre_b_9_def
    rw [h₀, h₁]
    norm_num
  sum_legendre_9fact_raw := ∑ i ∈ Finset.Ico (1:ℕ) legendre_b_9, (9:ℕ) / ((2:ℕ)^i)
  subprob_padicValNat_2_9fact_legendre :≡ padicValNat (2:ℕ) (Nat.factorial (9:ℕ)) = sum_legendre_9fact_raw
  subprob_padicValNat_2_9fact_legendre_proof ⇐ show subprob_padicValNat_2_9fact_legendre by
    have h_legendre := padicValNat_factorial (p := 2) (n := 9) (b := legendre_b_9) subprob_legendre_cond_9_proof
    rw [h_legendre]
    rw [sum_legendre_9fact_raw_def]
  subprob_sum_legendre_9fact_set_rewrite :≡ sum_legendre_9fact_raw = ∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (9:ℕ) / ((2:ℕ)^i)
  subprob_sum_legendre_9fact_set_rewrite_proof ⇐ show subprob_sum_legendre_9fact_set_rewrite by
    rw [sum_legendre_9fact_raw_def]
    simp [Finset.Ico, legendre_b_9_def]
    <;> rfl
  subprob_sum_legendre_9fact_expanded :≡ (∑ i ∈ ({(1:ℕ), (2:ℕ), (3:ℕ)} : Finset ℕ), (9:ℕ) / ((2:ℕ)^i)) = (9:ℕ)/((2:ℕ)^1) + (9:ℕ)/((2:ℕ)^2) + (9:ℕ)/((2:ℕ)^3)
  subprob_sum_legendre_9fact_expanded_proof ⇐ show subprob_sum_legendre_9fact_expanded by
    simp [Finset.sum_insert, Finset.sum_singleton, Nat.div_eq_of_lt]
    <;> norm_num
    <;> linarith
  subprob_term1_9_div_2p1 :≡ (9:ℕ) / (2:ℕ)^1 = (4:ℕ)
  subprob_term1_9_div_2p1_proof ⇐ show subprob_term1_9_div_2p1 by
    simpa [Nat.pow_one] using subprob_term1_9_div_2p1_proof
  subprob_term2_9_div_2p2 :≡ (9:ℕ) / (2:ℕ)^2 = (2:ℕ)
  subprob_term2_9_div_2p2_proof ⇐ show subprob_term2_9_div_2p2 by
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt]
    <;> rfl
    <;> linarith
    <;> norm_num
    <;> rfl
  subprob_term3_9_div_2p3 :≡ (9:ℕ) / (2:ℕ)^3 = (1:ℕ)
  subprob_term3_9_div_2p3_proof ⇐ show subprob_term3_9_div_2p3 by
    norm_num [Nat.pow_succ, Nat.pow_zero, Nat.div_eq_of_lt]
    <;> decide
    <;> norm_num
    <;> decide
    <;> norm_num
    <;> decide
  subprob_sum_legendre_9fact_calc :≡ sum_legendre_9fact_raw = (7:ℕ)
  subprob_sum_legendre_9fact_calc_proof ⇐ show subprob_sum_legendre_9fact_calc by
    simp_all only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      Finset.mem_insert, Nat.div_eq_of_lt, Nat.div_eq_of_lt]
    <;> norm_num
    <;> linarith
  subprob_val_9fact_2_eq_7 :≡ val_9fact_2 = (7:ℕ)
  subprob_val_9fact_2_eq_7_proof ⇐ show subprob_val_9fact_2_eq_7 by
    rw [val_9fact_2_def]
    rw [subprob_padicValNat_2_9fact_legendre_proof]
    rw [subprob_sum_legendre_9fact_calc_proof]
  subprob_sum_padicValNat_2_jfact_expanded :≡ sum_padicValNat_2_jfact = val_1fact_2 + val_2fact_2 + val_3fact_2 + val_4fact_2 + val_5fact_2 + val_6fact_2 + val_7fact_2 + val_8fact_2 + val_9fact_2
  subprob_sum_padicValNat_2_jfact_expanded_proof ⇐ show subprob_sum_padicValNat_2_jfact_expanded by
    rw [sum_padicValNat_2_jfact_def]
    rw [val_1fact_2_def, val_2fact_2_def, val_3fact_2_def, val_4fact_2_def, val_5fact_2_def, val_6fact_2_def, val_7fact_2_def, val_8fact_2_def, val_9fact_2_def]
    let f := fun j => padicValNat (2 : ℕ) (j !)
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 9) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 8) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 7) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 6) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 5) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 4) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 3) f]
    rw [Finset.sum_Icc_succ_top (by norm_num : 1 ≤ 2) f]
    rw [Finset.Icc_self (1 : ℕ)]
    rw [Finset.sum_singleton]
  subprob_sum_padicValNat_2_jfact_evaluated :≡ sum_padicValNat_2_jfact = (0:ℕ) + (1:ℕ) + (1:ℕ) + (3:ℕ) + (3:ℕ) + (4:ℕ) + (4:ℕ) + (7:ℕ) + (7:ℕ)
  subprob_sum_padicValNat_2_jfact_evaluated_proof ⇐ show subprob_sum_padicValNat_2_jfact_evaluated by
    simp [subprob_val_1fact_2_eq_0_proof, subprob_val_2fact_2_eq_1_proof, subprob_val_3fact_2_eq_1_proof, subprob_val_4fact_2_eq_3_proof, subprob_val_5fact_2_eq_3_proof, subprob_val_6fact_2_eq_4_proof, subprob_val_7fact_2_eq_4_proof, subprob_val_8fact_2_eq_7_proof, subprob_val_9fact_2_eq_7_proof, subprob_sum_padicValNat_2_jfact_expanded_proof]
  subprob_arith_sum_2_eq_30 :≡ (0:ℕ) + (1:ℕ) + (1:ℕ) + (3:ℕ) + (3:ℕ) + (4:ℕ) + (4:ℕ) + (7:ℕ) + (7:ℕ) = (30:ℕ)
  subprob_arith_sum_2_eq_30_proof ⇐ show subprob_arith_sum_2_eq_30 by
    norm_num
    <;> decide
    <;> decide
    <;> decide
    <;> decide
  subprob_exp_P_2 :≡ exponent_p_P_val (2:ℕ) = (30:ℕ)
  subprob_exp_P_2_proof ⇐ show subprob_exp_P_2 by
    simp_all only [exponent_p_P_val_def', subprob_sum_padicValNat_2_jfact_expanded_proof,
      subprob_sum_padicValNat_2_jfact_evaluated_proof, subprob_arith_sum_2_eq_30_proof]
    <;> rfl
  subprob_exp_P_3 :≡ exponent_p_P_val (3:ℕ) = (13:ℕ)
  subprob_exp_P_3_proof ⇐ show subprob_exp_P_3 by
    rw [subprob_relation_exponent_P_val_to_factorials_proof 3 Nat.prime_three]
    rw [Finset.sum_congr rfl (fun j _ => subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof 3 j Nat.prime_three)]
    have val_1fact_3_eq : padicValNat (3 : ℕ) (1 : ℕ)! = (0 : ℕ) := by
      simp [Nat.factorial_one, padicValNat.one]
    have val_2fact_3_eq : padicValNat (3 : ℕ) (2 : ℕ)! = (0 : ℕ) := by
      rw [Nat.factorial_two]
      apply padicValNat.eq_zero_of_not_dvd
      norm_num
    have val_3fact_3_eq : padicValNat (3 : ℕ) (3 : ℕ)! = (1 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (3 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (3 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 3) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_4fact_3_eq : padicValNat (3 : ℕ) (4 : ℕ)! = (1 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (4 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (4 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 4) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_5fact_3_eq : padicValNat (3 : ℕ) (5 : ℕ)! = (1 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (5 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (5 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 5) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_6fact_3_eq : padicValNat (3 : ℕ) (6 : ℕ)! = (2 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (6 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (6 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 6) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_7fact_3_eq : padicValNat (3 : ℕ) (7 : ℕ)! = (2 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (7 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (7 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 7) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_8fact_3_eq : padicValNat (3 : ℕ) (8 : ℕ)! = (2 : ℕ) := by
      have log_val : Nat.log (3 : ℕ) (8 : ℕ) = (1 : ℕ) := by
        apply Iff.mpr Nat.log_eq_one_iff
        constructor
        . norm_num
        . constructor
          . norm_num
          . norm_num
      have log_cond : Nat.log (3 : ℕ) (8 : ℕ) < (2 : ℕ) := by
        rw [log_val]
        decide
      rw [padicValNat_factorial (p := 3) (n := 8) (b := 2) log_cond]
      rw [show Finset.Ico (1 : ℕ) (2 : ℕ) = ({1} : Finset ℕ) by decide]
      rw [Finset.sum_singleton]
      norm_num
    have val_9fact_3_eq : padicValNat (3 : ℕ) (9 : ℕ)! = (4 : ℕ) := by
      have log_eq_2 : Nat.log (3 : ℕ) (9 : ℕ) = (2 : ℕ) := by
        rw [show (9 : ℕ) = (3 : ℕ) ^ (2 : ℕ) by norm_num]
        rw [Nat.log_pow (by decide : 1 < 3) (2 : ℕ)]
      have log_cond : Nat.log (3 : ℕ) (9 : ℕ) < (3 : ℕ) := by
        rw [log_eq_2]
        decide
      rw [padicValNat_factorial (p := 3) (n := 9) (b := 3) log_cond]
      rw [show Finset.Ico (1 : ℕ) (3 : ℕ) = ({1, 2} : Finset ℕ) by decide]
      rw [Finset.sum_insert (by decide : 1 ∉ {2})]
      rw [Finset.sum_singleton]
      norm_num
    have sum_Icc_1_9_eq : ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (3 : ℕ) j ! =
      padicValNat (3 : ℕ) 1! + padicValNat (3 : ℕ) 2! + padicValNat (3 : ℕ) 3! +
      padicValNat (3 : ℕ) 4! + padicValNat (3 : ℕ) 5! + padicValNat (3 : ℕ) 6! +
      padicValNat (3 : ℕ) 7! + padicValNat (3 : ℕ) 8! + padicValNat (3 : ℕ) 9! := by
      have list_eq : Finset.Icc (1 : ℕ) (9 : ℕ) = ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) := by decide
      rw [list_eq]
      rw [Finset.sum_insert (by decide : 1 ∉ {2, 3, 4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 2 ∉ {3, 4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 3 ∉ {4, 5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 4 ∉ {5, 6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 5 ∉ {6, 7, 8, 9})]
      rw [Finset.sum_insert (by decide : 6 ∉ {7, 8, 9})]
      rw [Finset.sum_insert (by decide : 7 ∉ {8, 9})]
      rw [Finset.sum_insert (by decide : 8 ∉ {9})]
      rw [Finset.sum_singleton]
      ring
    rw [sum_Icc_1_9_eq]
    rw [val_1fact_3_eq, val_2fact_3_eq, val_3fact_3_eq, val_4fact_3_eq,
      val_5fact_3_eq, val_6fact_3_eq, val_7fact_3_eq, val_8fact_3_eq,
      val_9fact_3_eq]
  subprob_prime_5 :≡ Nat.Prime (5:ℕ)
  subprob_prime_5_proof ⇐ show subprob_prime_5 by
    decide
    <;> decide
    <;> decide
    <;> decide
  sum_factorization_jfact_5_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), (Nat.factorization (Nat.factorial j) (5:ℕ))
  subprob_exp_P_5_eq_sum_factorization_jfact_5 :≡ exponent_p_P_val (5:ℕ) = sum_factorization_jfact_5_Icc_1_9
  subprob_exp_P_5_eq_sum_factorization_jfact_5_proof ⇐ show subprob_exp_P_5_eq_sum_factorization_jfact_5 by
    rw [subprob_relation_exponent_P_val_to_factorials_proof 5 subprob_prime_5_proof]
    simp [sum_factorization_jfact_5_Icc_1_9_def]
    <;> simp_all [Finset.sum_congr]
    <;> norm_num
    <;> linarith
  subprob_factorization_eq_padicValNat :≡ ∀ (n p : ℕ), Nat.Prime p → (Nat.factorization n p) = padicValNat p n
  subprob_factorization_eq_padicValNat_proof ⇐ show subprob_factorization_eq_padicValNat by
    intro n p hp
    rw [Nat.factorization_def]
    <;> simp [hp, Nat.Prime.ne_zero]
    <;> norm_num
    <;> omega
  sum_padicValNat_5_jfact_Icc_1_9 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  subprob_sum_factorization_eq_sum_padicValNat :≡ sum_factorization_jfact_5_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_9
  subprob_sum_factorization_eq_sum_padicValNat_proof ⇐ show subprob_sum_factorization_eq_sum_padicValNat by
    rw [sum_factorization_jfact_5_Icc_1_9_def]
    rw [sum_padicValNat_5_jfact_Icc_1_9_def]
    apply Finset.sum_congr rfl
    intro j hj
    apply subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof 5 j subprob_prime_5_proof
  subprob_exp_P_5_eq_sum_padicValNat_5 :≡ exponent_p_P_val (5:ℕ) = sum_padicValNat_5_jfact_Icc_1_9
  subprob_exp_P_5_eq_sum_padicValNat_5_proof ⇐ show subprob_exp_P_5_eq_sum_padicValNat_5 by
    rw [subprob_exp_P_5_eq_sum_factorization_jfact_5_proof]
    rw [subprob_sum_factorization_eq_sum_padicValNat_proof]
    <;> simp_all
    <;> linarith
  subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9 :≡ Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (4 : ℕ) ∪ Finset.Icc (5 : ℕ) (9 : ℕ)
  subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9_proof ⇐ show subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9 by
    ext x
    constructor <;> simp (config := { contextual := true }) [Finset.mem_Icc, Nat.le_succ_iff]
    <;> omega
    <;> omega
  subprob_Icc_1_4_disjoint_Icc_5_9 :≡ Disjoint (Finset.Icc (1 : ℕ) (4 : ℕ)) (Finset.Icc (5 : ℕ) (9 : ℕ))
  subprob_Icc_1_4_disjoint_Icc_5_9_proof ⇐ show subprob_Icc_1_4_disjoint_Icc_5_9 by
    apply Finset.disjoint_left.2
    intro x hx1 hx2
    rcases Finset.mem_Icc.mp hx1 with ⟨h1, h2⟩
    rcases Finset.mem_Icc.mp hx2 with ⟨h3, h4⟩
    linarith
  sum_padicValNat_5_jfact_Icc_1_4 := ∑ j ∈ Finset.Icc (1 : ℕ) (4 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  sum_padicValNat_5_jfact_Icc_5_9 := ∑ j ∈ Finset.Icc (5 : ℕ) (9 : ℕ), padicValNat (5:ℕ) (Nat.factorial j)
  subprob_sum_padicValNat_5_jfact_Icc_1_9_split :≡ sum_padicValNat_5_jfact_Icc_1_9 = sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9
  subprob_sum_padicValNat_5_jfact_Icc_1_9_split_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_9_split by
    rw [sum_padicValNat_5_jfact_Icc_1_9_def, sum_padicValNat_5_jfact_Icc_1_4_def, sum_padicValNat_5_jfact_Icc_5_9_def]
    rw [subprob_Icc_1_9_eq_union_Icc_1_4_Icc_5_9_proof]
    rw [Finset.sum_union subprob_Icc_1_4_disjoint_Icc_5_9_proof]
  subprob_j_in_Icc_1_4_implies_j_lt_5 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (1:ℕ) (4:ℕ) → j < (5:ℕ)
  subprob_j_in_Icc_1_4_implies_j_lt_5_proof ⇐ show subprob_j_in_Icc_1_4_implies_j_lt_5 by
    intro j hj
    rw [Finset.mem_Icc] at hj
    linarith
  subprob_padicValNat_5_jfact_eq_0_when_j_lt_5 :≡ ∀ (j : ℕ), j < (5:ℕ) → Nat.Prime (5:ℕ) → padicValNat (5:ℕ) (Nat.factorial j) = (0:ℕ)
  subprob_padicValNat_5_jfact_eq_0_when_j_lt_5_proof ⇐ show subprob_padicValNat_5_jfact_eq_0_when_j_lt_5 by
    intro j hj_lt_5 hp_prime_5
    have h_fact_zero : (Nat.factorization j !) (5 : ℕ) = (0 : ℕ) := by
      apply Nat.factorization_factorial_eq_zero_of_lt
      exact hj_lt_5
    have h_fact_eq_padicVal : (Nat.factorization j !) (5 : ℕ) = padicValNat (5 : ℕ) (Nat.factorial j) := by
      exact subprob_factorization_eq_padicValNat_proof (Nat.factorial j) (5 : ℕ) hp_prime_5
    rw [← h_fact_eq_padicVal]
    exact h_fact_zero
  subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0 :≡ sum_padicValNat_5_jfact_Icc_1_4 = (0:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0 by
    have h₁ : sum_padicValNat_5_jfact_Icc_1_4 = 0 := by
      rw [sum_padicValNat_5_jfact_Icc_1_4_def]
      apply Finset.sum_eq_zero
      intro j hj
      have h₂ : j < 5 := by
        rw [Finset.mem_Icc] at hj
        linarith
      have h₃ : padicValNat 5 j ! = 0 := subprob_padicValNat_5_jfact_eq_0_when_j_lt_5_proof j h₂ subprob_prime_5_proof
      simp [h₃]
    exact h₁
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (5:ℕ) (9:ℕ) → (5:ℕ) ≤ j ∧ j < (5:ℕ)^2
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25_proof ⇐ show subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25 by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    constructor
    linarith
    linarith
  subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), padicValNat (5:ℕ) (Nat.factorial j) = j / (5:ℕ)
  subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9_proof ⇐ show subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9 by
    intro j hj
    have h_log_lt_b : Nat.log (5 : ℕ) j < Nat.log (5 : ℕ) j + 1 := Nat.lt_succ_self (Nat.log (5 : ℕ) j)
    have h_legendre : padicValNat (5 : ℕ) (Nat.factorial j) = ∑ i ∈ Finset.Ico (1 : ℕ) (Nat.log (5 : ℕ) j + 1), j / (5 : ℕ) ^ i :=
      @padicValNat_factorial (5 : ℕ) j (Nat.log (5 : ℕ) j + 1) (Fact.mk subprob_prime_5_proof) h_log_lt_b
    rw [h_legendre]
    have hj_bounds := subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_25_proof j hj
    have h_log_val : Nat.log (5 : ℕ) j = (1 : ℕ) := by
      apply (Nat.log_eq_iff (by simp)).mpr
      simp
      exact hj_bounds
    rw [h_log_val]
    simp
  subprob_helper_5_gt_0 :≡ (5:ℕ) > 0
  subprob_helper_5_gt_0_proof ⇐ show subprob_helper_5_gt_0 by
    decide
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (5:ℕ) (9:ℕ) → (5:ℕ) ≤ j ∧ j < 2 * (5:ℕ)
  subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10_proof ⇐ show subprob_helper_j_in_Icc_5_9_implies_5_le_j_and_j_lt_10 by
    intro j hj
    simp only [Finset.mem_Icc, Nat.mul_succ] at hj ⊢
    constructor
    <;> omega
  subprob_j_div_5_eq_1_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), j / (5:ℕ) = (1:ℕ)
  subprob_j_div_5_eq_1_when_j_in_Icc_5_9_proof ⇐ show subprob_j_div_5_eq_1_when_j_in_Icc_5_9 by
    intro j hj
    have h₁ : j ∈ Finset.Icc (5 : ℕ) (9 : ℕ) := hj
    have h₂ : 5 ≤ j := Finset.mem_Icc.mp h₁ |>.1
    have h₃ : j ≤ 9 := Finset.mem_Icc.mp h₁ |>.2
    interval_cases j <;> norm_num
  subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9 :≡ ∀ (j : ℕ) (hj : j ∈ Finset.Icc (5:ℕ) (9:ℕ)), padicValNat (5:ℕ) (Nat.factorial j) = (1:ℕ)
  subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9_proof ⇐ show subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9 by
    intro j hj
    have h₁ := subprob_padicValNat_5_jfact_eq_j_div_5_when_j_in_Icc_5_9_proof j hj
    have h₂ := subprob_j_div_5_eq_1_when_j_in_Icc_5_9_proof j hj
    rw [h₂] at h₁
    exact h₁
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1 :≡ sum_padicValNat_5_jfact_Icc_5_9 = ∑ j ∈ Finset.Icc (5:ℕ) (9:ℕ), (1:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1 by
    rw [sum_padicValNat_5_jfact_Icc_5_9_def]
    apply Finset.sum_congr rfl
    intro j hj
    rw [subprob_padicValNat_5_jfact_eq_1_when_j_in_Icc_5_9_proof j hj]
    <;> simp
  subprob_card_Icc_5_9 :≡ (Finset.Icc (5:ℕ) (9:ℕ)).card = (5:ℕ)
  subprob_card_Icc_5_9_proof ⇐ show subprob_card_Icc_5_9 by
    decide
    <;> simp [Finset.Icc, Finset.card]
    <;> norm_num
    <;> decide
  subprob_sum_1_Icc_5_9_eq_card :≡ ∑ j ∈ Finset.Icc (5:ℕ) (9:ℕ), (1:ℕ) = (Finset.Icc (5:ℕ) (9:ℕ)).card
  subprob_sum_1_Icc_5_9_eq_card_proof ⇐ show subprob_sum_1_Icc_5_9_eq_card by
    rw [Finset.sum_const]
    norm_num
    <;> simp
    <;> rfl
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5 :≡ sum_padicValNat_5_jfact_Icc_5_9 = (5:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5 by
    simpa [sum_padicValNat_5_jfact_Icc_5_9_def, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof,
      subprob_card_Icc_5_9_proof, subprob_sum_1_Icc_5_9_eq_card_proof] using
      subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_sum_1_proof
  subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value :≡ sum_padicValNat_5_jfact_Icc_1_4 + sum_padicValNat_5_jfact_Icc_5_9 = (0:ℕ) + (5:ℕ)
  subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value_proof ⇐ show subprob_sum_padicValNat_5_jfact_Icc_1_9_calc_value by
    simp [subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof]
    <;> rfl
  subprob_0_plus_5_eq_5 :≡ (0:ℕ) + (5:ℕ) = (5:ℕ)
  subprob_0_plus_5_eq_5_proof ⇐ show subprob_0_plus_5_eq_5 by
    simp [Nat.add_zero]
  subprob_exp_P_5 :≡ exponent_p_P_val (5:ℕ) = (5:ℕ)
  subprob_exp_P_5_proof ⇐ show subprob_exp_P_5 by
    simpa [subprob_sum_padicValNat_5_jfact_Icc_1_9_split_proof, subprob_sum_padicValNat_5_jfact_Icc_1_4_eq_0_proof, subprob_sum_padicValNat_5_jfact_Icc_5_9_eq_5_proof, subprob_0_plus_5_eq_5_proof] using subprob_exp_P_5_eq_sum_padicValNat_5_proof
  subprob_prime_7 :≡ Nat.Prime (7:ℕ)
  subprob_prime_7_proof ⇐ show subprob_prime_7 by
    decide
    <;> decide
    <;> decide
    <;> decide
  exp_j_fact_7 := fun (j : ℕ) => (Nat.factorization (Nat.factorial j) (7:ℕ))
  sum_exp_factorials_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (9 : ℕ), exp_j_fact_7 j
  subprob_exp_P_7_eq_sum_exp_factorials_7 :≡ exponent_p_P_val (7:ℕ) = sum_exp_factorials_7
  subprob_exp_P_7_eq_sum_exp_factorials_7_proof ⇐ show subprob_exp_P_7_eq_sum_exp_factorials_7 by
    rw [sum_exp_factorials_7_def]
    rw [exp_j_fact_7_def]
    simp
    exact subprob_relation_exponent_P_val_to_factorials_proof (7 : ℕ) subprob_prime_7_proof
  subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9 :≡ Finset.Icc (1 : ℕ) (9 : ℕ) = Finset.Icc (1 : ℕ) (6 : ℕ) ∪ Finset.Icc (7 : ℕ) (9 : ℕ)
  subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9_proof ⇐ show subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9 by
    apply Finset.ext
    intro x
    constructor <;> simp (config := { contextual := true }) [Finset.mem_Icc, Finset.mem_union]
    <;> omega
    <;> omega
    <;> omega
    <;> omega
  subprob_Icc_1_6_disjoint_Icc_7_9 :≡ Disjoint (Finset.Icc (1 : ℕ) (6 : ℕ)) (Finset.Icc (7 : ℕ) (9 : ℕ))
  subprob_Icc_1_6_disjoint_Icc_7_9_proof ⇐ show subprob_Icc_1_6_disjoint_Icc_7_9 by
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    rw [Finset.mem_Icc] at hx₁ hx₂
    omega
  sum_1_to_6_val_7 := ∑ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j
  sum_7_to_9_val_7 := ∑ j ∈ Finset.Icc (7 : ℕ) (9 : ℕ), exp_j_fact_7 j
  subprob_sum_exp_factorials_7_split :≡ sum_exp_factorials_7 = sum_1_to_6_val_7 + sum_7_to_9_val_7
  subprob_sum_exp_factorials_7_split_proof ⇐ show subprob_sum_exp_factorials_7_split by
    rw [sum_exp_factorials_7_def, subprob_Icc_1_9_eq_union_Icc_1_6_Icc_7_9_proof]
    rw [Finset.sum_union subprob_Icc_1_6_disjoint_Icc_7_9_proof]
    rw [sum_1_to_6_val_7_def, sum_7_to_9_val_7_def]
  subprob_j_in_Icc_1_6_implies_j_lt_7 :≡ ∀ (j : ℕ), j ∈ Finset.Icc (1:ℕ) (6:ℕ) → j < (7:ℕ)
  subprob_j_in_Icc_1_6_implies_j_lt_7_proof ⇐ show subprob_j_in_Icc_1_6_implies_j_lt_7 by
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨h1, h2⟩
    linarith
  subprob_exp_j_fact_7_when_j_lt_7 :≡ ∀ (j : ℕ), j < (7:ℕ) → exp_j_fact_7 j = (0:ℕ)
  subprob_exp_j_fact_7_when_j_lt_7_proof ⇐ show subprob_exp_j_fact_7_when_j_lt_7 by
    intro j h_j_lt_7
    rw [exp_j_fact_7_def']
    exact Nat.factorization_factorial_eq_zero_of_lt h_j_lt_7
  subprob_sum_1_to_6_val_7_eq_0 :≡ sum_1_to_6_val_7 = (0:ℕ)
  subprob_sum_1_to_6_val_7_eq_0_proof ⇐ show subprob_sum_1_to_6_val_7_eq_0 by
    simp only [sum_1_to_6_val_7_def]
    have h₁ : ∀ j ∈ Finset.Icc (1 : ℕ) (6 : ℕ), exp_j_fact_7 j = 0 := by
      intro j hj
      apply subprob_exp_j_fact_7_when_j_lt_7_proof
      apply subprob_j_in_Icc_1_6_implies_j_lt_7_proof
      exact hj
    simp [Finset.sum_eq_zero h₁]
  subprob_exp_7_fact_7_eq_padicValNat_7_fact_7 :≡ exp_j_fact_7 (7:ℕ) = padicValNat (7:ℕ) (Nat.factorial (7:ℕ))
  subprob_exp_7_fact_7_eq_padicValNat_7_fact_7_proof ⇐ show subprob_exp_7_fact_7_eq_padicValNat_7_fact_7 by
    rw [exp_j_fact_7_def', subprob_factorization_eq_padicValNat_proof (Nat.factorial 7) 7 subprob_prime_7_proof]
    <;> simp [padicValNat.factorial]
    <;> norm_num
  subprob_padicValNat_7_7fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (7:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (7:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_7fact_legendre_proof ⇐ show subprob_padicValNat_7_7fact_legendre by
    have h_prime_7 : Fact (Nat.Prime (7 : ℕ)) := Fact.mk subprob_prime_7_proof
    apply padicValNat_factorial
    norm_num
  subprob_Nat_log_7_7_eq_1 :≡ Nat.log (7:ℕ) (7:ℕ) = (1:ℕ)
  subprob_Nat_log_7_7_eq_1_proof ⇐ show subprob_Nat_log_7_7_eq_1 by
    rw [Nat.log_eq_one_iff]
    <;> norm_num
    <;> norm_num
    <;> norm_num
  sum_legendre_7_7fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (7:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_rewritten_log :≡ sum_legendre_7_7fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_7fact_rewritten_log by
    simp [sum_legendre_7_7fact_def, subprob_Nat_log_7_7_eq_1_proof]
    <;> norm_num
    <;> rfl
  subprob_one_plus_one_eq_two :≡ (1:ℕ) + (1:ℕ) = (2:ℕ)
  subprob_one_plus_one_eq_two_proof ⇐ show subprob_one_plus_one_eq_two by
    norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  subprob_sum_legendre_7_7fact_ico_1_2 :≡ sum_legendre_7_7fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (7:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_7fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_7fact_ico_1_2 by
    rw [subprob_sum_legendre_7_7fact_rewritten_log_proof]
    <;> simp [subprob_one_plus_one_eq_two_proof]
    <;> norm_num
    <;> rfl
  subprob_Finset_Ico_1_2_eq_singleton_1 :≡ Finset.Ico (1:ℕ) (2:ℕ) = ({(1:ℕ)} : Finset ℕ)
  subprob_Finset_Ico_1_2_eq_singleton_1_proof ⇐ show subprob_Finset_Ico_1_2_eq_singleton_1 by
    ext x
    simp [Finset.mem_Ico, Finset.mem_singleton]
    <;> decide
  subprob_sum_legendre_7_7fact_is_7_div_7_pow_1 :≡ sum_legendre_7_7fact = (7:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_7fact_is_7_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_7fact_is_7_div_7_pow_1 by
    simp [sum_legendre_7_7fact_def, Finset.Ico, Nat.log, Nat.div_eq_of_lt]
    <;> decide
    <;> rfl
  subprob_7_pow_1_eq_7 :≡ ((7:ℕ):ℕ)^(1:ℕ) = (7:ℕ)
  subprob_7_pow_1_eq_7_proof ⇐ show subprob_7_pow_1_eq_7 by
    rw [Nat.pow_one]
    <;> rfl
  subprob_7_div_7_eq_1 :≡ (7:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_7_div_7_eq_1_proof ⇐ show subprob_7_div_7_eq_1 by
    norm_num
    <;> rfl
  subprob_sum_legendre_7_7fact_eval_to_1 :≡ (7:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_7fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_7fact_eval_to_1 by
    simp [Nat.pow_one]
    <;> apply Nat.div_self
    <;> decide
    <;> linarith
  subprob_padicValNat_7_of_7fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (7:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_7fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_7fact_eq_1 by
    rw [subprob_padicValNat_7_7fact_legendre_proof]
    simp [subprob_Nat_log_7_7_eq_1_proof, subprob_7_div_7_eq_1_proof]
    <;> norm_num
    <;> rfl
  subprob_exp_7_fact_7_eq_1 :≡ exp_j_fact_7 (7:ℕ) = (1:ℕ)
  subprob_exp_7_fact_7_eq_1_proof ⇐ show subprob_exp_7_fact_7_eq_1 by
    rw [subprob_exp_7_fact_7_eq_padicValNat_7_fact_7_proof]
    rw [subprob_padicValNat_7_of_7fact_eq_1_proof]
  subprob_exp_8_fact_7_eq_padicValNat_7_fact_8 :≡ exp_j_fact_7 (8:ℕ) = padicValNat (7:ℕ) (Nat.factorial (8:ℕ))
  subprob_exp_8_fact_7_eq_padicValNat_7_fact_8_proof ⇐ show subprob_exp_8_fact_7_eq_padicValNat_7_fact_8 by
    rw [exp_j_fact_7_def']
    simp [padicValNat, Nat.factorial, Nat.factorization]
    <;> norm_num
    <;> rfl
  subprob_padicValNat_7_8fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (8:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (8:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_8fact_legendre_proof ⇐ show subprob_padicValNat_7_8fact_legendre by
    have : Fact (Nat.Prime (7 : ℕ)) := ⟨subprob_prime_7_proof⟩
    apply padicValNat_factorial (Nat.lt_succ_self (Nat.log (7 : ℕ) (8 : ℕ)))
  subprob_Nat_log_7_8_eq_1 :≡ Nat.log (7:ℕ) (8:ℕ) = (1:ℕ)
  subprob_Nat_log_7_8_eq_1_proof ⇐ show subprob_Nat_log_7_8_eq_1 by
    rw [Nat.log_eq_iff] <;> norm_num <;>
    linarith [Nat.pow_pos (by norm_num : (0 : ℕ) < 7) 1, Nat.pow_pos (by norm_num : (0 : ℕ) < 7) 2]
  sum_legendre_7_8fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (8:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_rewritten_log :≡ sum_legendre_7_8fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_8fact_rewritten_log by
    rw [sum_legendre_7_8fact_def]
    simp [Finset.Ico, Finset.sum_range_succ, Nat.log, Nat.pow_succ, Nat.div_eq_of_lt]
    <;> norm_num
  subprob_sum_legendre_7_8fact_ico_1_2 :≡ sum_legendre_7_8fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (8:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_8fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_8fact_ico_1_2 by
    rw [sum_legendre_7_8fact_def]
    simp [Finset.Ico, Nat.log, Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one]
    <;> norm_num
    <;> rfl
  subprob_sum_legendre_7_8fact_is_8_div_7_pow_1 :≡ sum_legendre_7_8fact = (8:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_8fact_is_8_div_7_pow_1 by
    rw [subprob_sum_legendre_7_8fact_ico_1_2_proof]
    simp [Finset.sum_Ico_succ_top]
    <;> norm_num
    <;> rfl
  subprob_8_div_7_eq_1 :≡ (8:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_8_div_7_eq_1_proof ⇐ show subprob_8_div_7_eq_1 by
    norm_num
    <;> decide
    <;> norm_num
    <;> decide
  subprob_sum_legendre_7_8fact_eval_to_1 :≡ (8:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_8fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_8fact_eval_to_1 by
    simp [Nat.pow_one]
    <;> norm_num
    <;> linarith
  subprob_padicValNat_7_of_8fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (8:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_8fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_8fact_eq_1 by
    rw [subprob_padicValNat_7_8fact_legendre_proof]
    simp [subprob_Nat_log_7_8_eq_1_proof, sum_legendre_7_8fact_def, subprob_sum_legendre_7_8fact_rewritten_log_proof, subprob_sum_legendre_7_8fact_ico_1_2_proof, subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof, subprob_8_div_7_eq_1_proof, subprob_sum_legendre_7_8fact_eval_to_1_proof]
  subprob_exp_8_fact_7_eq_1 :≡ exp_j_fact_7 (8:ℕ) = (1:ℕ)
  subprob_exp_8_fact_7_eq_1_proof ⇐ show subprob_exp_8_fact_7_eq_1 by
    rw [subprob_exp_8_fact_7_eq_padicValNat_7_fact_8_proof]
    rw [subprob_padicValNat_7_8fact_legendre_proof]
    rw [subprob_Nat_log_7_8_eq_1_proof]
    simp [sum_legendre_7_8fact_def, subprob_sum_legendre_7_8fact_rewritten_log_proof,
      subprob_sum_legendre_7_8fact_ico_1_2_proof, subprob_sum_legendre_7_8fact_is_8_div_7_pow_1_proof,
      subprob_8_div_7_eq_1_proof, subprob_sum_legendre_7_8fact_eval_to_1_proof]
  subprob_exp_9_fact_7_eq_padicValNat_7_fact_9 :≡ exp_j_fact_7 (9:ℕ) = padicValNat (7:ℕ) (Nat.factorial (9:ℕ))
  subprob_exp_9_fact_7_eq_padicValNat_7_fact_9_proof ⇐ show subprob_exp_9_fact_7_eq_padicValNat_7_fact_9 by
    rw [exp_j_fact_7_def' (9 : ℕ)]
    apply subprob_factorization_eq_padicValNat_proof (9 !) (7 : ℕ) subprob_prime_7_proof
  subprob_padicValNat_7_9fact_legendre :≡ padicValNat (7:ℕ) (Nat.factorial (9:ℕ)) = ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (9:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_padicValNat_7_9fact_legendre_proof ⇐ show subprob_padicValNat_7_9fact_legendre by
    have h_b_cond : Nat.log (7 : ℕ) (9 : ℕ) < Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ) := by
      apply Nat.lt_succ_self (Nat.log (7 : ℕ) (9 : ℕ))
    apply (@padicValNat_factorial (7 : ℕ) (9 : ℕ) (Nat.log (7 : ℕ) (9 : ℕ) + (1 : ℕ)) (Fact.mk subprob_prime_7_proof) h_b_cond)
  subprob_Nat_log_7_9_eq_1 :≡ Nat.log (7:ℕ) (9:ℕ) = (1:ℕ)
  subprob_Nat_log_7_9_eq_1_proof ⇐ show subprob_Nat_log_7_9_eq_1 by
    rw [Nat.log]
    norm_num
    <;> decide
    <;> norm_num
    <;> decide
  sum_legendre_7_9fact := ∑ i in Finset.Ico (1:ℕ) (Nat.log (7:ℕ) (9:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_rewritten_log :≡ sum_legendre_7_9fact = ∑ i in Finset.Ico (1:ℕ) ((1:ℕ) + (1:ℕ)), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_rewritten_log_proof ⇐ show subprob_sum_legendre_7_9fact_rewritten_log by
    simp [sum_legendre_7_9fact_def, subprob_Nat_log_7_9_eq_1_proof]
    <;> norm_num
    <;> ring
    <;> omega
  subprob_sum_legendre_7_9fact_ico_1_2 :≡ sum_legendre_7_9fact = ∑ i in Finset.Ico (1:ℕ) (2:ℕ), (9:ℕ) / ((7:ℕ) ^ i)
  subprob_sum_legendre_7_9fact_ico_1_2_proof ⇐ show subprob_sum_legendre_7_9fact_ico_1_2 by
    have h₀ : Nat.log (7 : ℕ) (9 : ℕ) = (1 : ℕ) := subprob_Nat_log_7_9_eq_1_proof
    simp [sum_legendre_7_9fact_def, h₀, Finset.Ico, Nat.div_eq_of_lt]
    <;> norm_num
    <;> rfl
  subprob_sum_legendre_7_9fact_is_9_div_7_pow_1 :≡ sum_legendre_7_9fact = (9:ℕ) / ((7:ℕ)^(1:ℕ))
  subprob_sum_legendre_7_9fact_is_9_div_7_pow_1_proof ⇐ show subprob_sum_legendre_7_9fact_is_9_div_7_pow_1 by
    simp only [sum_legendre_7_9fact_def]
    norm_num
    <;> rfl
  subprob_9_div_7_eq_1 :≡ (9:ℕ) / (7:ℕ) = (1:ℕ)
  subprob_9_div_7_eq_1_proof ⇐ show subprob_9_div_7_eq_1 by
    norm_num
    <;> linarith
    <;> omega
    <;> decide
  subprob_sum_legendre_7_9fact_eval_to_1 :≡ (9:ℕ) / ((7:ℕ)^(1:ℕ)) = (1:ℕ)
  subprob_sum_legendre_7_9fact_eval_to_1_proof ⇐ show subprob_sum_legendre_7_9fact_eval_to_1 by
    simp [Nat.pow_succ, Nat.pow_zero]
    <;> decide
    <;> rfl
    <;> decide
    <;> rfl
  subprob_padicValNat_7_of_9fact_eq_1 :≡ padicValNat (7:ℕ) (Nat.factorial (9:ℕ)) = (1:ℕ)
  subprob_padicValNat_7_of_9fact_eq_1_proof ⇐ show subprob_padicValNat_7_of_9fact_eq_1 by
    rw [subprob_padicValNat_7_9fact_legendre_proof]
    rw [← sum_legendre_7_9fact_def]
    rw [subprob_sum_legendre_7_9fact_is_9_div_7_pow_1_proof]
    exact subprob_sum_legendre_7_9fact_eval_to_1_proof
  subprob_exp_9_fact_7_eq_1 :≡ exp_j_fact_7 (9:ℕ) = (1:ℕ)
  subprob_exp_9_fact_7_eq_1_proof ⇐ show subprob_exp_9_fact_7_eq_1 by
    rw [exp_j_fact_7_def']
    have h_prime_7 : Nat.Prime (7 : ℕ) := subprob_prime_7_proof
    rw [subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof (7 : ℕ) (9 : ℕ) h_prime_7]
    exact subprob_padicValNat_7_of_9fact_eq_1_proof
  subprob_Icc_7_9_eq_7_8_9 :≡ Finset.Icc (7 : ℕ) (9 : ℕ) = ({(7:ℕ), (8:ℕ), (9:ℕ)} : Finset ℕ)
  subprob_Icc_7_9_eq_7_8_9_proof ⇐ show subprob_Icc_7_9_eq_7_8_9 by
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  subprob_sum_7_to_9_val_7_expanded :≡ sum_7_to_9_val_7 = exp_j_fact_7 (7:ℕ) + exp_j_fact_7 (8:ℕ) + exp_j_fact_7 (9:ℕ)
  subprob_sum_7_to_9_val_7_expanded_proof ⇐ show subprob_sum_7_to_9_val_7_expanded by
    rw [sum_7_to_9_val_7_def]
    rw [subprob_Icc_7_9_eq_7_8_9_proof]
    simp
    ring
  subprob_sum_7_to_9_val_7_calc_values :≡ exp_j_fact_7 (7:ℕ) + exp_j_fact_7 (8:ℕ) + exp_j_fact_7 (9:ℕ) = (1:ℕ) + (1:ℕ) + (1:ℕ)
  subprob_sum_7_to_9_val_7_calc_values_proof ⇐ show subprob_sum_7_to_9_val_7_calc_values by
    rw [subprob_exp_7_fact_7_eq_1_proof, subprob_exp_8_fact_7_eq_1_proof, subprob_exp_9_fact_7_eq_1_proof]
    <;> simp
  subprob_1_plus_1_plus_1_eq_3 :≡ (1:ℕ) + (1:ℕ) + (1:ℕ) = (3:ℕ)
  subprob_1_plus_1_plus_1_eq_3_proof ⇐ show subprob_1_plus_1_plus_1_eq_3 by
    norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
    <;> norm_num
    <;> rfl
  subprob_sum_7_to_9_val_7_eq_3 :≡ sum_7_to_9_val_7 = (3:ℕ)
  subprob_sum_7_to_9_val_7_eq_3_proof ⇐ show subprob_sum_7_to_9_val_7_eq_3 by
    rw [subprob_sum_7_to_9_val_7_expanded_proof]
    rw [subprob_sum_7_to_9_val_7_calc_values_proof]
  subprob_sum_exp_factorials_7_calc_value :≡ sum_1_to_6_val_7 + sum_7_to_9_val_7 = (0:ℕ) + (3:ℕ)
  subprob_sum_exp_factorials_7_calc_value_proof ⇐ show subprob_sum_exp_factorials_7_calc_value by
    rw [subprob_sum_1_to_6_val_7_eq_0_proof, subprob_sum_7_to_9_val_7_eq_3_proof]
    <;> simp
    <;> rfl
  subprob_0_plus_3_eq_3 :≡ (0:ℕ) + (3:ℕ) = (3:ℕ)
  subprob_0_plus_3_eq_3_proof ⇐ show subprob_0_plus_3_eq_3 by
    norm_num
    <;> simp_all
    <;> norm_num
    <;> linarith
  subprob_sum_exp_factorials_7_eq_3 :≡ sum_exp_factorials_7 = (3:ℕ)
  subprob_sum_exp_factorials_7_eq_3_proof ⇐ show subprob_sum_exp_factorials_7_eq_3 by
    rw [subprob_sum_exp_factorials_7_split_proof]
    rw [subprob_sum_exp_factorials_7_calc_value_proof]
  subprob_exp_P_7 :≡ exponent_p_P_val (7:ℕ) = (3:ℕ)
  subprob_exp_P_7_proof ⇐ show subprob_exp_P_7 by
    rw [subprob_exp_P_7_eq_sum_exp_factorials_7_proof]
    exact subprob_sum_exp_factorials_7_eq_3_proof
  subprob_exp_P_other :≡ ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_gt_7 : p > (7:ℕ)), exponent_p_P_val p = (0:ℕ)
  subprob_exp_P_other_proof ⇐ show subprob_exp_P_other by
    intro p hp h_p_gt_7
    rw [subprob_relation_exponent_P_val_to_factorials_proof p hp]
    apply Finset.sum_eq_zero
    intro j hj
    rw [subprob_factorization_jfact_p_eq_padicValNat_jfact_p_proof p j hp]
    rw [padicValNat.eq_zero_iff]
    right
    right
    have h_j_bounds : 1 ≤ j ∧ j ≤ 9 := Finset.mem_Icc.mp hj
    have h_p_ge_11 : p ≥ 11 := by
      by_contra h_p_lt_11_contra
      have h_p_lt_11 : p < 11 := (lt_iff_not_le.mpr h_p_lt_11_contra)
      have h_p_le_10 : p ≤ 10 := le_of_lt_succ h_p_lt_11
      have h_p_ge_8 : p ≥ 8 := Order.succ_le_of_lt h_p_gt_7
      interval_cases p
      .
        have h_8_not_prime : ¬Nat.Prime 8 := Nat.not_prime_mul (a := 2) (b := 4) (by norm_num) (by norm_num)
        contradiction
      .
        have h_9_not_prime : ¬Nat.Prime 9 := Nat.not_prime_mul (a := 3) (b := 3) (by norm_num) (by norm_num)
        contradiction
      .
        have h_10_not_prime : ¬Nat.Prime 10 := Nat.not_prime_mul (a := 2) (b := 5) (by norm_num) (by norm_num)
        contradiction
    have h_j_lt_p : j < p := by linarith [h_j_bounds.2, h_p_ge_11]
    by_contra h_dvd_contra
    have h_p_le_j : p ≤ j := (Nat.Prime.dvd_factorial hp).mp h_dvd_contra
    linarith [h_p_le_j, h_j_lt_p]
  subprob_P_val_factorization_support :≡ (Nat.factorization P_val).support = ({(2:ℕ),(3:ℕ),(5:ℕ),(7:ℕ)} : Finset ℕ)
  subprob_P_val_factorization_support_proof ⇐ show subprob_P_val_factorization_support by
    ext p
    rw [Nat.support_factorization P_val]
    rw [Nat.mem_primeFactors_of_ne_zero (ne_zero_of_lt subprob_P_val_pos_proof)]
    apply Iff.intro
    .
      intro h_prime_and_dvd
      cases h_prime_and_dvd with
      | intro h_prime h_dvd =>
        have h_exp_nonzero : (Nat.factorization P_val) p ≠ 0 := by
          apply Nat.one_le_iff_ne_zero.mp
          exact (Nat.Prime.dvd_iff_one_le_factorization h_prime (ne_zero_of_lt subprob_P_val_pos_proof)).mp h_dvd
        rw [← exponent_p_P_val_def' p] at h_exp_nonzero
        have h_if_gt_7_exp_zero : p > 7 → exponent_p_P_val p = 0 := subprob_exp_P_other_proof p h_prime
        have h_exp_nonzero_implies_not_gt_7 : exponent_p_P_val p ≠ 0 → ¬(p > 7) := mt h_if_gt_7_exp_zero
        have h_not_gt_7 : ¬(p > 7) := h_exp_nonzero_implies_not_gt_7 h_exp_nonzero
        have h_p_le_7 : p ≤ 7 := by simp at h_not_gt_7; exact h_not_gt_7
        have h_p_ge_2 : p ≥ 2 := Nat.Prime.two_le h_prime
        interval_cases p using h_p_ge_2, h_p_le_7
        .
          simp
        .
          simp
        .
          have h_not_prime_4 : ¬(4 : ℕ).Prime := by decide
          exact False.elim (h_not_prime_4 h_prime)
        .
          simp
        .
          have h_not_prime_6 : ¬(6 : ℕ).Prime := by decide
          exact False.elim (h_not_prime_6 h_prime)
        .
          simp
        done
    .
      intro h_p_in_set
      simp [Finset.mem_insert, Finset.mem_singleton] at h_p_in_set
      cases h_p_in_set with
      | inl h_p_eq =>
        subst h_p_eq
        apply And.intro
        .
          exact subprob_prime_2_proof
        .
          rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_2_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
          rw [← exponent_p_P_val_def' 2]
          rw [subprob_exp_P_2_proof]
          norm_num
      | inr h_p_in_set_357 =>
        cases h_p_in_set_357 with
        | inl h_p_eq =>
          subst h_p_eq
          apply And.intro
          .
            norm_num
          .
            rw [Nat.Prime.dvd_iff_one_le_factorization (by norm_num) (ne_zero_of_lt subprob_P_val_pos_proof)]
            rw [← exponent_p_P_val_def' 3]
            rw [subprob_exp_P_3_proof]
            norm_num
        | inr h_p_in_set_57 =>
          cases h_p_in_set_57 with
          | inl h_p_eq =>
            subst h_p_eq
            apply And.intro
            .
              exact subprob_prime_5_proof
            .
              rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_5_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
              rw [← exponent_p_P_val_def' 5]
              rw [subprob_exp_P_5_proof]
              norm_num
          | inr h_p_eq =>
            subst h_p_eq
            apply And.intro
            .
              exact subprob_prime_7_proof
            .
              rw [Nat.Prime.dvd_iff_one_le_factorization subprob_prime_7_proof (ne_zero_of_lt subprob_P_val_pos_proof)]
              rw [← exponent_p_P_val_def' 7]
              rw [subprob_exp_P_7_proof]
              norm_num
  M_val := ∏ p ∈ (Nat.factorization P_val).support, p ^ (exponent_p_P_val p / (2:ℕ))
  subprob_M_val_eq_product :≡ M_val = (2:ℕ)^(15:ℕ) * (3:ℕ)^(6:ℕ) * (5:ℕ)^(2:ℕ) * (7:ℕ)^(1:ℕ)
  subprob_M_val_eq_product_proof ⇐ show subprob_M_val_eq_product by
    rw [M_val_def]
    rw [subprob_P_val_factorization_support_proof]
    simp
    rw [subprob_exp_P_2_proof]
    rw [subprob_exp_P_3_proof]
    rw [subprob_exp_P_5_proof]
    rw [subprob_exp_P_7_proof]
    have h_div_2 : (30 : ℕ) / (2 : ℕ) = (15 : ℕ) := by norm_num
    have h_div_3 : (13 : ℕ) / (2 : ℕ) = (6 : ℕ) := by norm_num
    have h_div_5 : (5 : ℕ) / (2 : ℕ) = (2 : ℕ) := by norm_num
    have h_div_7 : (3 : ℕ) / (2 : ℕ) = (1 : ℕ) := by norm_num
    rw [h_div_2]
    rw [h_div_3]
    rw [h_div_5]
    rw [h_div_7]
    rfl
  subprob_M_val_pos :≡ M_val > (0:ℕ)
  subprob_M_val_pos_proof ⇐ show subprob_M_val_pos by
    rw [subprob_M_val_eq_product_proof]
    norm_num
  subprob_S_equiv_divisors_of_M :≡ ∀ (k : ℕ), k ∈ S ↔ ((0:ℕ) < k ∧ k ∣ M_val)
  subprob_S_equiv_divisors_of_M_proof ⇐ show subprob_S_equiv_divisors_of_M by
    intro k
    rw [h₀]
    rw [← P_val_def]
    have h_P_ne_zero : P_val ≠ 0 := Nat.ne_of_gt subprob_P_val_pos_proof
    have h_M_ne_zero : M_val ≠ 0 := Nat.ne_of_gt subprob_M_val_pos_proof
    cases k with
    | zero =>
      simp only [Nat.not_lt_zero, mul_zero, zero_dvd_iff]
      simp only [false_and_iff]
    | succ k' =>
      simp only [Nat.succ_pos']
      simp only [true_and_iff]
      have h_k_plus_1_ne_zero : k' + 1 ≠ 0 := Nat.ne_of_gt (Nat.succ_pos k')
      have h_k_plus_1_sq_ne_zero : (k' + 1) * (k' + 1) ≠ 0 := Nat.mul_ne_zero h_k_plus_1_ne_zero h_k_plus_1_ne_zero
      have prime_of_mem_support_P : ∀ {p : ℕ}, p ∈ Finsupp.support (Nat.factorization P_val) → Nat.Prime p := by
        intro p hp_mem
        rw [subprob_P_val_factorization_support_proof] at hp_mem
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp_mem
        rcases hp_mem with rfl | rfl | rfl | rfl
        .
          exact subprob_prime_2_proof
        .
          exact Nat.prime_three
        .
          exact subprob_prime_5_proof
        .
          exact subprob_prime_7_proof
      have h_M_factorization_p : ∀ q : ℕ, Nat.Prime q → Nat.factorization M_val q = Nat.factorization P_val q / (2 : ℕ) := by
        intro q hq_prime
        rw [M_val_def]
        have h_prod_nonzero : ∀ p ∈ Finsupp.support (Nat.factorization P_val), p ^ (exponent_p_P_val p / (2 : ℕ)) ≠ 0 := by
          intro p hp_mem_supp
          rw [Nat.support_factorization P_val] at hp_mem_supp
          have h_p_is_prime_factor : p ∈ (P_val).primeFactors := hp_mem_supp
          have h_prime_and_dvd := (Nat.mem_primeFactors_of_ne_zero (Nat.ne_of_gt subprob_P_val_pos_proof)).mp h_p_is_prime_factor
          have hp_prime : Nat.Prime p := h_prime_and_dvd.left
          have hp_ne_zero : p ≠ 0 := hp_prime.ne_zero
          apply pow_ne_zero (exponent_p_P_val p / (2 : ℕ))
          exact hp_ne_zero
        rw [Nat.factorization_prod h_prod_nonzero]
        rw [Finsupp.finset_sum_apply]
        simp_rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        rw [subprob_P_val_factorization_support_proof]
        by_cases hq_in_support : q ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ)
        .
          rw [Finset.sum_eq_single_of_mem q hq_in_support (by
            intro p hp_mem_supp h_p_ne_q
            rw [← subprob_P_val_factorization_support_proof] at hp_mem_supp
            have hp_prime := prime_of_mem_support_P hp_mem_supp
            have h_q_ne_p : q ≠ p := Ne.symm h_p_ne_q
            have h_not_dvd_q_p : ¬ q ∣ p := mt (Iff.mp (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime)) h_q_ne_p
            have h_fact_p_q_zero : Nat.factorization p q = 0 := Nat.factorization_eq_zero_of_not_dvd h_not_dvd_q_p
            rw [h_fact_p_q_zero]
            rw [mul_zero]
          )]
          rw [Nat.Prime.factorization_self hq_prime]
          rw [mul_one]
          rw [exponent_p_P_val_def' q]
        .
          have h_sum_zero : ∑ p ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ), (exponent_p_P_val p / (2 : ℕ)) * (Nat.factorization p q) = 0 := by
            apply Finset.sum_eq_zero
            intro p hp_mem_supp
            have h_p_ne_q : p ≠ q := by
              intro h_p_eq_q
              subst h_p_eq_q
              exact hq_in_support hp_mem_supp
            rw [← subprob_P_val_factorization_support_proof] at hp_mem_supp
            have hp_prime := prime_of_mem_support_P hp_mem_supp
            have h_q_ne_p : q ≠ p := Ne.symm h_p_ne_q
            have h_not_dvd_q_p : ¬ q ∣ p := mt (Iff.mp (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime)) h_q_ne_p
            have h_fact_p_q_zero : Nat.factorization p q = 0 := Nat.factorization_eq_zero_of_not_dvd h_not_dvd_q_p
            rw [h_fact_p_q_zero]
            rw [mul_zero]
          have h_fact_P_q_zero : (Nat.factorization P_val) q = 0 := by
            rw [← subprob_P_val_factorization_support_proof] at hq_in_support
            rw [Finsupp.not_mem_support_iff] at hq_in_support
            exact hq_in_support
          rw [h_sum_zero, h_fact_P_q_zero]
      constructor
      .
        intro h_k_plus_1_sq_dvd_P
        have h_fact_k_plus_1_sq_le_fact_P : ∀ p : ℕ, Nat.Prime p → (Nat.factorization ((k' + 1) * (k' + 1))) p ≤ (Nat.factorization P_val) p :=
          (Nat.factorization_prime_le_iff_dvd h_k_plus_1_sq_ne_zero h_P_ne_zero).mpr h_k_plus_1_sq_dvd_P
        rw [← Nat.factorization_prime_le_iff_dvd h_k_plus_1_ne_zero h_M_ne_zero]
        intro p hp_prime
        have h_fact_k_plus_1_sq_p : Nat.factorization ((k' + 1) * (k' + 1)) p = (2 : ℕ) * Nat.factorization (k' + 1) p := by
          rw [← Nat.pow_two (k' + 1)]
          rw [Nat.factorization_pow (k' + 1) 2, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        have H_lhs_ineq_p := h_fact_k_plus_1_sq_le_fact_P p hp_prime
        rw [h_fact_k_plus_1_sq_p] at H_lhs_ineq_p
        rw [h_M_factorization_p p hp_prime]
        rw [Nat.mul_comm (2 : ℕ) (Nat.factorization (k' + 1) p)] at H_lhs_ineq_p
        exact Nat.le_div_iff_mul_le' (by norm_num) |>.mpr H_lhs_ineq_p
      .
        intro h_k_plus_1_dvd_M
        have h_fact_k_plus_1_le_fact_M : ∀ p : ℕ, Nat.Prime p → (Nat.factorization (k' + 1)) p ≤ (Nat.factorization M_val) p :=
          (Nat.factorization_prime_le_iff_dvd h_k_plus_1_ne_zero h_M_ne_zero).mpr h_k_plus_1_dvd_M
        rw [← Nat.factorization_prime_le_iff_dvd h_k_plus_1_sq_ne_zero h_P_ne_zero]
        intro p hp_prime
        have h_fact_k_plus_1_sq_p : Nat.factorization ((k' + 1) * (k' + 1)) p = (2 : ℕ) * Nat.factorization (k' + 1) p := by
          rw [← Nat.pow_two (k' + 1)]
          rw [Nat.factorization_pow (k' + 1) 2, Finsupp.smul_apply, Nat.nsmul_eq_mul]
        rw [h_fact_k_plus_1_sq_p]
        have H_rhs_ineq_p := h_fact_k_plus_1_le_fact_M p hp_prime
        rw [h_M_factorization_p p hp_prime] at H_rhs_ineq_p
        have h_mul_le_goal : Nat.factorization (k' + 1) p * (2 : ℕ) ≤ Nat.factorization P_val p := Nat.mul_le_of_le_div (2 : ℕ) (Nat.factorization (k' + 1) p) (Nat.factorization P_val p) H_rhs_ineq_p
        rw [Nat.mul_comm (Nat.factorization (k' + 1) p) (2 : ℕ)] at h_mul_le_goal
        exact h_mul_le_goal
  subprob_card_S_eq_num_divisors_M :≡ S.card = (Nat.divisors M_val).card
  subprob_card_S_eq_num_divisors_M_proof ⇐ show subprob_card_S_eq_num_divisors_M by
    have h_eq : S = Nat.divisors M_val := by
      apply Finset.ext
      intro k
      rw [subprob_S_equiv_divisors_of_M_proof]
      rw [Nat.mem_divisors]
      constructor
      .
        intro h_and
        constructor
        .
          exact h_and.right
        .
          apply pos_iff_ne_zero.mp subprob_M_val_pos_proof
      .
        intro h_and
        constructor
        .
          apply pos_of_dvd_of_pos h_and.left subprob_M_val_pos_proof
        .
          exact h_and.left
    rw [h_eq]
  subprob_card_divisors_M_formula :≡ (Nat.divisors M_val).card = ∏ p ∈ (Nat.factorization M_val).support, ((Nat.factorization M_val p) + (1:ℕ))
  subprob_card_divisors_M_formula_proof ⇐ show subprob_card_divisors_M_formula by
    apply ArithmeticFunction.card_divisors M_val
    exact Nat.pos_iff_ne_zero.mp subprob_M_val_pos_proof
  subprob_factorization_M_val_support :≡ (Nat.factorization M_val).support = ({(2:ℕ),(3:ℕ),(5:ℕ),(7:ℕ)} : Finset ℕ)
  subprob_factorization_M_val_support_proof ⇐ show subprob_factorization_M_val_support by
    have h_prime_3 : Nat.Prime (3 : ℕ) := Nat.prime_three
    have h_2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
    have h_3_ne_zero : (3 : ℕ) ≠ 0 := by norm_num
    have h_5_ne_zero : (5 : ℕ) ≠ 0 := by norm_num
    have h_7_ne_zero : (7 : ℕ) ≠ 0 := by norm_num
    have h_2_pow_15_ne_zero : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := pow_ne_zero 15 h_2_ne_zero
    have h_3_pow_6_ne_zero : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := pow_ne_zero 6 h_3_ne_zero
    have h_5_pow_2_ne_zero : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 h_5_ne_zero
    have h_7_pow_1_ne_zero : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := pow_ne_zero 1 h_7_ne_zero
    have h_ab_ne_zero : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := by
      apply mul_ne_zero
      exact h_2_pow_15_ne_zero
      exact h_3_pow_6_ne_zero
    have h_abc_ne_zero : ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := by
      apply mul_ne_zero
      exact h_ab_ne_zero
      exact h_5_pow_2_ne_zero
    have h_factorization_M_val : Nat.factorization ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) * (7 : ℕ) ^ (1 : ℕ)) = Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) + Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) + Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) + Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) := by
      rw [Nat.factorization_mul h_abc_ne_zero h_7_pow_1_ne_zero]
      rw [Nat.factorization_mul h_ab_ne_zero h_5_pow_2_ne_zero]
      rw [Nat.factorization_mul h_2_pow_15_ne_zero h_3_pow_6_ne_zero]
    rw [subprob_M_val_eq_product_proof, h_factorization_M_val]
    have h_15_ne_zero : (15 : ℕ) ≠ 0 := by norm_num
    have h_6_ne_zero : (6 : ℕ) ≠ 0 := by norm_num
    have h_exp_5_pow_2_ne_zero : (2 : ℕ) ≠ 0 := by norm_num
    have h_exp_7_pow_1_ne_zero : (1 : ℕ) ≠ 0 := by norm_num
    have fact_2_15 : Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) = Finsupp.single (2 : ℕ) (15 : ℕ) := Nat.Prime.factorization_pow subprob_prime_2_proof
    have fact_3_6 : Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) = Finsupp.single (3 : ℕ) (6 : ℕ) := Nat.Prime.factorization_pow h_prime_3
    have fact_5_2 : Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) = Finsupp.single (5 : ℕ) (2 : ℕ) := Nat.Prime.factorization_pow subprob_prime_5_proof
    have fact_7_1 : Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) = Finsupp.single (7 : ℕ) (1 : ℕ) := Nat.Prime.factorization_pow subprob_prime_7_proof
    rw [fact_2_15, fact_3_6, fact_5_2, fact_7_1]
    have s2 : (Finsupp.single (2 : ℕ) (15 : ℕ)).support = {(2 : ℕ)} := Finsupp.support_single_ne_zero (2 : ℕ) h_15_ne_zero
    have s3 : (Finsupp.single (3 : ℕ) (6 : ℕ)).support = {(3 : ℕ)} := Finsupp.support_single_ne_zero (3 : ℕ) h_6_ne_zero
    have s5 : (Finsupp.single (5 : ℕ) (2 : ℕ)).support = {(5 : ℕ)} := Finsupp.support_single_ne_zero (5 : ℕ) h_exp_5_pow_2_ne_zero
    have s7 : (Finsupp.single (7 : ℕ) (1 : ℕ)).support = {(7 : ℕ)} := Finsupp.support_single_ne_zero (7 : ℕ) h_exp_7_pow_1_ne_zero
    have h_disj_f1_f2 : Disjoint (Finsupp.support (Finsupp.single (2 : ℕ) (15 : ℕ))) (Finsupp.support (Finsupp.single (3 : ℕ) (6 : ℕ))) := by
      simp [s2, s3]
    have h_supp_f1_f2_union : (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ)).support = (Finsupp.single (2 : ℕ) (15 : ℕ)).support ∪ (Finsupp.single (3 : ℕ) (6 : ℕ)).support := Finsupp.support_add_eq h_disj_f1_f2
    have h_disj_f12_f3 : Disjoint (Finsupp.support (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ))) (Finsupp.support (Finsupp.single (5 : ℕ) (2 : ℕ))) := by
      rw [h_supp_f1_f2_union]
      simp [s2, s3, s5]
    have s123 : (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ) + Finsupp.single (5 : ℕ) (2 : ℕ)).support = ({(2 : ℕ), (3 : ℕ), (5 : ℕ)} : Finset ℕ) := by
      rw [Finsupp.support_add_eq h_disj_f12_f3]
      rw [Finsupp.support_add_eq h_disj_f1_f2]
      rw [s2, s3, s5]
      ext x
      simp
    have h_disjoint_f123_f4 : Disjoint (Finsupp.single (2 : ℕ) (15 : ℕ) + Finsupp.single (3 : ℕ) (6 : ℕ) + Finsupp.single (5 : ℕ) (2 : ℕ)).support (Finsupp.single (7 : ℕ) (1 : ℕ)).support := by
      rw [s123, s7]
      simp
    simp only [Finsupp.support_add_eq h_disjoint_f123_f4]
    rw [s123, s7]
    ext x
    simp
  subprob_exp_M_2 :≡ (Nat.factorization M_val (2:ℕ)) = (15:ℕ)
  subprob_exp_M_2_proof ⇐ show subprob_exp_M_2 by
    rw [subprob_M_val_eq_product_proof]
    have nz2 : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := by norm_num
    have nz3 : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := by norm_num
    have nz5 : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := by norm_num
    have nz7 : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := by norm_num
    have nz23 : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.mul_ne_zero nz2 nz3
    have nz235 : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.mul_ne_zero nz23 nz5
    rw [Nat.factorization_mul nz235 nz7, Finsupp.add_apply]
    rw [Nat.factorization_mul nz23 nz5, Finsupp.add_apply]
    rw [Nat.factorization_mul nz2 nz3, Finsupp.add_apply]
    have h_fact_2_pow_15_at_2 : (Nat.factorization ((2 : ℕ) ^ (15 : ℕ))) (2 : ℕ) = 15 := by
      rw [Nat.Prime.factorization_pow subprob_prime_2_proof]
      simp
    rw [h_fact_2_pow_15_at_2]
    have h_3_ne_2 : (3 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_3_pow_6_at_2 : (Nat.factorization ((3 : ℕ) ^ (6 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_three]
      simp
    rw [h_fact_3_pow_6_at_2]
    have h_5_ne_2 : (5 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_5_pow_2_at_2 : (Nat.factorization ((5 : ℕ) ^ (2 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow Nat.prime_five]
      simp
    rw [h_fact_5_pow_2_at_2]
    have h_7_ne_2 : (7 : ℕ) ≠ (2 : ℕ) := by norm_num
    have h_fact_7_pow_1_at_2 : (Nat.factorization ((7 : ℕ) ^ (1 : ℕ))) (2 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow subprob_prime_7_proof]
      simp
    rw [h_fact_7_pow_1_at_2]
  subprob_exp_M_3 :≡ (Nat.factorization M_val (3:ℕ)) = (6:ℕ)
  subprob_exp_M_3_proof ⇐ show subprob_exp_M_3 by
    rw [subprob_M_val_eq_product_proof]
    have h2_prime : Nat.Prime 2 := by decide
    have h3_prime : Nat.Prime 3 := by decide
    have h5_prime : Nat.Prime 5 := by decide
    have h7_prime : Nat.Prime 7 := by decide
    have pos_2_15 : (2 : ℕ) ^ (15 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_3_6 : (3 : ℕ) ^ (6 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_5_2 : (5 : ℕ) ^ (2 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have pos_7_1 : (7 : ℕ) ^ (1 : ℕ) > 0 := Nat.pow_pos (by norm_num)
    have ne_zero_2_15 : (2 : ℕ) ^ (15 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_2_15
    have ne_zero_3_6 : (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_3_6
    have ne_zero_5_2 : (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_5_2
    have ne_zero_7_1 : (7 : ℕ) ^ (1 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp pos_7_1
    have ne_zero_left_prod : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) * (5 : ℕ) ^ (2 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos pos_2_15 pos_3_6) pos_5_2)
    rw [Nat.factorization_mul ne_zero_left_prod ne_zero_7_1]
    rw [Finsupp.add_apply]
    have h_fact_7_1_3 : Nat.factorization ((7 : ℕ) ^ (1 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h7_prime]
      have h_ne : (3 : ℕ) ≠ (7 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_7_1_3]
    simp only [add_zero]
    have ne_zero_inner_prod : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos pos_2_15 pos_3_6)
    rw [Nat.factorization_mul ne_zero_inner_prod ne_zero_5_2]
    rw [Finsupp.add_apply]
    have h_fact_5_2_3 : Nat.factorization ((5 : ℕ) ^ (2 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h5_prime]
      have h_ne : (3 : ℕ) ≠ (5 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_5_2_3]
    simp only [add_zero]
    rw [Nat.factorization_mul ne_zero_2_15 ne_zero_3_6]
    rw [Finsupp.add_apply]
    have h_fact_2_15_3 : Nat.factorization ((2 : ℕ) ^ (15 : ℕ)) (3 : ℕ) = 0 := by
      rw [Nat.Prime.factorization_pow h2_prime]
      have h_ne : (3 : ℕ) ≠ (2 : ℕ) := by simp
      exact Finsupp.single_eq_of_ne (Ne.symm h_ne)
    rw [h_fact_2_15_3]
    simp only [zero_add]
    have h_fact_3_6_3 : Nat.factorization ((3 : ℕ) ^ (6 : ℕ)) (3 : ℕ) = 6 := by
      rw [Nat.Prime.factorization_pow h3_prime]
      simp
    rw [h_fact_3_6_3]
  subprob_exp_M_5 :≡ (Nat.factorization M_val (5:ℕ)) = (2:ℕ)
  subprob_exp_M_5_proof ⇐ show subprob_exp_M_5 by
    rw [M_val_def]
    rw [subprob_P_val_factorization_support_proof]
    have h_prod_nonzero : ∀ p ∈ ({(2 : ℕ), (3 : ℕ), (5 : ℕ), (7 : ℕ)} : Finset ℕ), p ^ (exponent_p_P_val p / (2 : ℕ)) ≠ 0 := by
      intro p hp
      have h_p_pos : p > 0 := by
        simp at hp
        rcases hp with rfl | rfl | rfl | rfl
        . norm_num
        . norm_num
        . norm_num
        . norm_num
      exact pow_ne_zero (exponent_p_P_val p / 2) (Nat.pos_iff_ne_zero.mp h_p_pos)
    rw [Nat.factorization_prod h_prod_nonzero]
    rw [Finsupp.coe_finset_sum]
    have h_prime_3 : Nat.Prime 3 := by norm_num
    have h_prime_7 : Nat.Prime 7 := by norm_num
    simp [
      Nat.Prime.factorization_pow,
      subprob_prime_2_proof,
      h_prime_3,
      subprob_prime_5_proof,
      h_prime_7
    ]
    rw [subprob_exp_P_5_proof]
  subprob_exp_M_7 :≡ (Nat.factorization M_val (7:ℕ)) = (1:ℕ)
  subprob_exp_M_7_proof ⇐ show subprob_exp_M_7 by
    rw [Nat.factorization_def]
    rw [subprob_M_val_eq_product_proof]
    have h_7_prime : Nat.Prime (7 : ℕ) := by decide
    have h_2_pow_15_ne_zero : (2 : ℕ) ^ (15 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_3_pow_6_ne_zero : (3 : ℕ) ^ (6 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_5_pow_2_ne_zero : (5 : ℕ) ^ (2 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_7_pow_1_ne_zero : (7 : ℕ) ^ (1 : ℕ) ≠ (0 : ℕ) := by apply pow_ne_zero; decide
    have h_23_ne_zero : (2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ) ≠ (0 : ℕ) := by
      apply mul_ne_zero h_2_pow_15_ne_zero h_3_pow_6_ne_zero
    have h_235_ne_zero : ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ) ≠ (0 : ℕ) := by
      apply mul_ne_zero h_23_ne_zero h_5_pow_2_ne_zero
    rw [@padicValNat.mul (7 : ℕ) (((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) * (5 : ℕ) ^ (2 : ℕ)) ((7 : ℕ) ^ (1 : ℕ)) (Fact.mk h_7_prime) h_235_ne_zero h_7_pow_1_ne_zero]
    rw [@padicValNat.mul (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ) * (3 : ℕ) ^ (6 : ℕ)) ((5 : ℕ) ^ (2 : ℕ)) (Fact.mk h_7_prime) h_23_ne_zero h_5_pow_2_ne_zero]
    rw [@padicValNat.mul (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ)) ((3 : ℕ) ^ (6 : ℕ)) (Fact.mk h_7_prime) h_2_pow_15_ne_zero h_3_pow_6_ne_zero]
    have h_2_ne_zero : (2 : ℕ) ≠ (0 : ℕ) := by decide
    have h_3_ne_zero : (3 : ℕ) ≠ (0 : ℕ) := by decide
    have h_5_ne_zero : (5 : ℕ) ≠ (0 : ℕ) := by decide
    have h_7_ne_zero : (7 : ℕ) ≠ (0 : ℕ) := by decide
    have h_val_2_pow_15 : padicValNat (7 : ℕ) ((2 : ℕ) ^ (15 : ℕ)) = (15 : ℕ) * padicValNat (7 : ℕ) (2 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (2 : ℕ) (Fact.mk h_7_prime) (15 : ℕ) ?_
      exact h_2_ne_zero
    rw [h_val_2_pow_15]
    have h_val_3_pow_6 : padicValNat (7 : ℕ) ((3 : ℕ) ^ (6 : ℕ)) = (6 : ℕ) * padicValNat (7 : ℕ) (3 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (3 : ℕ) (Fact.mk h_7_prime) (6 : ℕ) ?_
      exact h_3_ne_zero
    rw [h_val_3_pow_6]
    have h_val_5_pow_2 : padicValNat (7 : ℕ) ((5 : ℕ) ^ (2 : ℕ)) = (2 : ℕ) * padicValNat (7 : ℕ) (5 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (5 : ℕ) (Fact.mk h_7_prime) (2 : ℕ) ?_
      exact h_5_ne_zero
    rw [h_val_5_pow_2]
    have h_val_7_pow_1 : padicValNat (7 : ℕ) ((7 : ℕ) ^ (1 : ℕ)) = (1 : ℕ) * padicValNat (7 : ℕ) (7 : ℕ) := by
      refine @padicValNat.pow (7 : ℕ) (7 : ℕ) (Fact.mk h_7_prime) (1 : ℕ) ?_
      exact h_7_ne_zero
    rw [h_val_7_pow_1]
    have h_7_not_dvd_2 : ¬(7 : ℕ) ∣ (2 : ℕ) := by decide
    have h_term1 : (15 : ℕ) * padicValNat (7 : ℕ) (2 : ℕ) = (15 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_2
    rw [h_term1]
    have h_7_not_dvd_3 : ¬(7 : ℕ) ∣ (3 : ℕ) := by decide
    have h_term2 : (6 : ℕ) * padicValNat (7 : ℕ) (3 : ℕ) = (6 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_3
    rw [h_term2]
    have h_7_not_dvd_5 : ¬(7 : ℕ) ∣ (5 : ℕ) := by decide
    have h_term3 : (2 : ℕ) * padicValNat (7 : ℕ) (5 : ℕ) = (2 : ℕ) * (0 : ℕ) := by
      congr
      exact padicValNat.eq_zero_of_not_dvd h_7_not_dvd_5
    rw [h_term3]
    have h_val_7_7_eq_1 : padicValNat (7 : ℕ) (7 : ℕ) = 1 := by
      exact @padicValNat_self (7 : ℕ) (Fact.mk h_7_prime)
    rw [h_val_7_7_eq_1]
    norm_num
  subprob_card_S_product_form :≡ S.card = ((15:ℕ)+(1:ℕ))*((6:ℕ)+(1:ℕ))*((2:ℕ)+(1:ℕ))*((1:ℕ)+(1:ℕ))
  subprob_card_S_product_form_proof ⇐ show subprob_card_S_product_form by
    rw [subprob_card_S_eq_num_divisors_M_proof]
    rw [subprob_card_divisors_M_formula_proof]
    rw [subprob_factorization_M_val_support_proof]
    simp
    rw [subprob_exp_M_2_proof]
    rw [subprob_exp_M_3_proof]
    rw [subprob_exp_M_5_proof]
    rw [subprob_exp_M_7_proof]
    rfl
  subprob_calculation :≡ ((15:ℕ)+(1:ℕ))*((6:ℕ)+(1:ℕ))*((2:ℕ)+(1:ℕ))*((1:ℕ)+(1:ℕ)) = (672:ℕ)
  subprob_calculation_proof ⇐ show subprob_calculation by
    simp [Nat.mul, Nat.add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> decide
  subprob_final_goal :≡ S.card = (672:ℕ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    rw [subprob_card_S_product_form_proof]
  original_target :≡ Finset.card S = (672 : ℕ)
  original_target_proof ⇐ show original_target by
    exact subprob_final_goal_proof
-/
