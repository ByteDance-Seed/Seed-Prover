import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem mathd_numbertheory_618 (n : ℕ) (h_pos: n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1))) : 41 ≤ n  := by
  have subprob_pn1_eval_proof : p (n + 1) = n ^ 2 + n + 41 := by
    mkOpaque
    have h₂ : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41 := h₀ (n + 1)
    simp [Nat.pow_succ, Nat.mul_succ] at h₂
    linarith
  have subprob_pn1_ge_pn_proof : p n ≤ p (n + 1) := by
    mkOpaque
    simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    omega
  have subprob_pn1_minus_pn_proof : p (n + 1) - p n = 2 * n := by
    mkOpaque
    rw [Nat.sub_eq_iff_eq_add subprob_pn1_ge_pn_proof]
    rw [subprob_pn1_eval_proof, h₀ n]
    rw [Nat.two_mul]
    rw [Nat.add_comm (n + n) (n ^ 2 - n + 41)]
    rw [← Nat.add_assoc (n ^ 2 - n + 41) n n]
    have h_n_le_nsq : n ≤ n ^ 2 := by
      cases n with
      | zero => contradiction
      | succ n' => simp [Nat.pow_two]
    have h_rearrange_term : (n ^ 2 - n + 41) + n = (n ^ 2 - n) + (41 + n) := by exact Nat.add_assoc (n ^ 2 - n) 41 n
    rw [h_rearrange_term]
    rw [Nat.add_comm 41 n]
    rw [← Nat.add_assoc (n ^ 2 - n) n 41]
    rw [Nat.sub_add_cancel h_n_le_nsq]
    have add_add_swap (a b c : ℕ) : (a + b) + c = (a + c) + b := by rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]
    rw [add_add_swap (n ^ 2) n 41]
  have subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof : Nat.gcd (p (n + 1)) (p n) = Nat.gcd (2 * n) (p n) := by
    mkOpaque
    rw [<- Nat.gcd_sub_self_left subprob_pn1_ge_pn_proof]
    rw [subprob_pn1_minus_pn_proof]
  have subprob_n_sq_minus_n_is_even_proof : (n ^ 2 - n) % 2 = 0 := by
    mkOpaque
    have h_ge_one : 1 ≤ n := Nat.one_le_of_lt h_pos
    have h_eq : n ^ 2 - n = n * (n - 1) := by
      have h_distrib : n * (n - 1) = n * n - n * 1 := Nat.mul_sub n n 1
      have h_mul_one : n * n - n * 1 = n * n - n := by rw [Nat.mul_one]
      have h_pow_two : n * n - n = n ^ 2 - n := by rw [pow_two]
      have h_chain1 : n * (n - 1) = n * n - n := Eq.trans h_distrib h_mul_one
      have h_chain2 : n * (n - 1) = n ^ 2 - n := Eq.trans h_chain1 h_pow_two
      exact Eq.symm h_chain2
    rw [h_eq]
    have h_even_prod : Even (n * (n - 1)) := by
      have h_temp : Even ((n - 1) * ((n - 1) + 1)) := Nat.even_mul_succ_self (n - 1)
      have h_add_one_cancel : (n - 1) + 1 = n := Nat.sub_add_cancel h_ge_one
      rw [h_add_one_cancel] at h_temp
      rw [Nat.mul_comm (n - 1) n] at h_temp
      exact h_temp
    rw [← Nat.even_iff]
    exact h_even_prod
  have subprob_pn_is_odd_proof : (p n) % 2 = 1 := by
    mkOpaque
    simp_all only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    omega
  have subprob_coprime_2_pn_proof : Nat.Coprime 2 (p n) := by
    mkOpaque
    rw [Nat.Coprime]
    rw [← Nat.mod_add_div (p n) 2]
    simp [subprob_pn_is_odd_proof]
  have subprob_gcd_2n_pn_eq_gcd_n_pn_proof : Nat.gcd (2 * n) (p n) = Nat.gcd n (p n) := by
    mkOpaque
    apply subprob_coprime_2_pn_proof.gcd_mul_left_cancel
  have subprob_gcd_n_pn_eq_gcd_n_41_proof : Nat.gcd n (p n) = Nat.gcd n 41 := by
    mkOpaque
    rw [h₀ n]
    have h_ge_one : 1 ≤ n := Nat.succ_le_of_lt h_pos
    rw [Nat.pow_two n]
    rw [← Nat.mul_sub_one n]
    rw [add_comm (n * (n - 1)) 41]
    rw [Nat.gcd_add_mul_left_right n 41 (n - 1)]
  have subprob_gcd_pnp1_pn_is_gcd_n_41_proof : Nat.gcd (p (n + 1)) (p n) = Nat.gcd n 41 := by
    mkOpaque
    rw [subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof]
    rw [subprob_gcd_2n_pn_eq_gcd_n_pn_proof]
    rw [subprob_gcd_n_pn_eq_gcd_n_41_proof]
  have subprob_1_lt_gcd_n_41_proof : 1 < Nat.gcd n 41 := by
    mkOpaque
    simp_all [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_mul_left, Nat.gcd_mul_right] <;> omega
  have subprob_41_is_prime_proof : Nat.Prime 41 := by
    mkOpaque
    have h₂ := subprob_gcd_pnp1_pn_is_gcd_n_41_proof
    have h₃ := subprob_1_lt_gcd_n_41_proof
    have h₄ := subprob_gcd_n_pn_eq_gcd_n_41_proof
    have h₅ := subprob_gcd_2n_pn_eq_gcd_n_pn_proof
    have h₆ := subprob_coprime_2_pn_proof
    have h₇ := subprob_pn_is_odd_proof
    have h₈ := subprob_n_sq_minus_n_is_even_proof
    have h₉ := subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof
    have h₁₀ := subprob_pn1_minus_pn_proof
    have h₁₁ := subprob_pn1_ge_pn_proof
    have h₁₂ := subprob_pn1_eval_proof
    have h₁₃ := h₀
    norm_num [Nat.Prime, Nat.gcd_eq_right] at h₃ ⊢ <;> omega
  have subprob_gcd_n_41_is_1_or_41_proof : Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41 := by
    mkOpaque
    have h_prime_41 : Nat.Prime 41 := subprob_41_is_prime_proof
    have h_gcd_dvd_41 : Nat.gcd n 41 ∣ 41 := Nat.gcd_dvd_right n 41
    have h_gcd_eq_1_or_41 : Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41 := h_prime_41.eq_one_or_self_of_dvd (Nat.gcd n 41) h_gcd_dvd_41
    exact h_gcd_eq_1_or_41
  have subprob_gcd_n_41_is_41_proof : Nat.gcd n 41 = 41 := by
    mkOpaque
    have h_gcd : Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41 := subprob_gcd_n_41_is_1_or_41_proof
    have h_1_lt_gcd : 1 < Nat.gcd n 41 := subprob_1_lt_gcd_n_41_proof
    cases h_gcd with
    | inl h_gcd_eq_1 => linarith
    | inr h_gcd_eq_41 => exact h_gcd_eq_41
  have subprob_41_dvd_n_proof : 41 ∣ n := by
    mkOpaque
    have h₂ : Nat.gcd (p (n + 1)) (p n) = Nat.gcd n 41 := by rw [subprob_gcd_pnp1_pn_is_gcd_n_41_proof]
    have h₃ : Nat.gcd n 41 = 41 := by rw [subprob_gcd_n_41_is_41_proof]
    have h₄ : 41 ∣ n := by
      rw [← h₃]
      apply Nat.gcd_dvd_left
    exact h₄
  have subprob_final_goal_proof : 41 ≤ n := by
    mkOpaque
    have h₂ : 41 ≤ n := by
      apply Nat.le_of_dvd h_pos
      apply subprob_41_dvd_n_proof
    exact h₂
  exact
    show (41 : ℕ) ≤ n by
      mkOpaque
      have h₀ := subprob_41_dvd_n_proof
      have h₁ := subprob_final_goal_proof
      omega

#print axioms mathd_numbertheory_618

/- Sketch
variable (n : ℕ) (h_pos: n > 0) (p : ℕ → ℕ) (h₀ : ∀ x, p x = x ^ 2 - x + 41)
    (h₁ : 1 < Nat.gcd (p n) (p (n + 1)))
play
  -- Step 1: Evaluate p(n+1)
  subprob_pn1_eval :≡ p (n + 1) = n ^ 2 + n + 41
  subprob_pn1_eval_proof ⇐ show subprob_pn1_eval by sorry

  -- Step 2: Simplify gcd(p(n+1), p(n)) = gcd(2n, p(n))
  -- First, show p(n+1) - p(n) = 2n. Requires p(n+1) >= p(n) for Nat subtraction.
  -- (n^2+n+41) - (n^2-n+41) = 2n. Since n > 0, 2n > 0, so p(n+1) > p(n).
  subprob_pn1_ge_pn :≡ p n ≤ p (n+1)
  subprob_pn1_ge_pn_proof ⇐ show subprob_pn1_ge_pn by sorry
  subprob_pn1_minus_pn :≡ p (n + 1) - p n = 2 * n
  subprob_pn1_minus_pn_proof ⇐ show subprob_pn1_minus_pn by sorry
  -- Then, gcd(p(n+1), p(n)) = gcd(p(n+1) - p(n), p(n)) by Nat.gcd_sub_self_left (requires p n <= p (n+1))
  -- Using h₀ for p n on the RHS.
  subprob_gcd_pnp1_pn_eq_gcd_2n_pn :≡ Nat.gcd (p (n + 1)) (p n) = Nat.gcd (2 * n) (p n)
  subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof ⇐ show subprob_gcd_pnp1_pn_eq_gcd_2n_pn by sorry

  -- Step 3: Simplify gcd(2n, p(n)) = gcd(n, p(n))
  -- First, show p(n) is odd. p(n) = n^2 - n + 41.
  -- n^2 - n = n(n-1) is even.
  subprob_n_sq_minus_n_is_even :≡ (n ^ 2 - n) % 2 = 0
  subprob_n_sq_minus_n_is_even_proof ⇐ show subprob_n_sq_minus_n_is_even by sorry
  -- Then p(n) = (n^2 - n) + 41 is even + odd = odd.
  subprob_pn_is_odd :≡ (p n) % 2 = 1
  subprob_pn_is_odd_proof ⇐ show subprob_pn_is_odd by sorry
  -- If p(n) is odd, then Coprime(2, p(n)).
  subprob_coprime_2_pn :≡ Nat.Coprime 2 (p n)
  subprob_coprime_2_pn_proof ⇐ show subprob_coprime_2_pn by sorry
  -- Then gcd(2n, p(n)) = gcd(n, p(n)) by Nat.gcd_mul_left_cancel_of_coprime.
  subprob_gcd_2n_pn_eq_gcd_n_pn :≡ Nat.gcd (2 * n) (p n) = Nat.gcd n (p n)
  subprob_gcd_2n_pn_eq_gcd_n_pn_proof ⇐ show subprob_gcd_2n_pn_eq_gcd_n_pn by sorry

  -- Step 4: Simplify gcd(n, p(n)) = gcd(n, 41)
  -- p(n) = n^2 - n + 41. n^2 - n = (n-1)n.
  -- gcd(n, p(n)) = gcd(n, n^2 - n + 41) by h₀.
  -- gcd(n, (n-1)n + 41) = gcd(n, 41) by Nat.gcd_add_mul_self_right (requires n-1 >= 0, true by h_pos).
  subprob_gcd_n_pn_eq_gcd_n_41 :≡ Nat.gcd n (p n) = Nat.gcd n 41
  subprob_gcd_n_pn_eq_gcd_n_41_proof ⇐ show subprob_gcd_n_pn_eq_gcd_n_41 by sorry

  -- Step 5: Combine results: gcd(p(n+1), p(n)) = gcd(n, 41)
  subprob_gcd_pnp1_pn_is_gcd_n_41 :≡ Nat.gcd (p (n + 1)) (p n) = Nat.gcd n 41
  subprob_gcd_pnp1_pn_is_gcd_n_41_proof ⇐ show subprob_gcd_pnp1_pn_is_gcd_n_41 by sorry
  -- Use hypothesis h₁: 1 < gcd(p(n+1), p(n))
  subprob_1_lt_gcd_n_41 :≡ 1 < Nat.gcd n 41
  subprob_1_lt_gcd_n_41_proof ⇐ show subprob_1_lt_gcd_n_41 by sorry

  -- Step 6: Use primality of 41
  subprob_41_is_prime :≡ Nat.Prime 41
  subprob_41_is_prime_proof ⇐ show subprob_41_is_prime by sorry
  -- For a prime k, gcd(n, k) is 1 or k.
  subprob_gcd_n_41_is_1_or_41 :≡ Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41
  subprob_gcd_n_41_is_1_or_41_proof ⇐ show subprob_gcd_n_41_is_1_or_41 by sorry
  -- Since 1 < gcd(n, 41), it must be gcd(n, 41) = 41.
  subprob_gcd_n_41_is_41 :≡ Nat.gcd n 41 = 41
  subprob_gcd_n_41_is_41_proof ⇐ show subprob_gcd_n_41_is_41 by sorry

  -- Step 7: Conclude 41 ≤ n
  -- gcd(n, 41) = 41 implies 41 ∣ n. (Nat.dvd_of_gcd_eq_right)
  subprob_41_dvd_n :≡ 41 ∣ n
  subprob_41_dvd_n_proof ⇐ show subprob_41_dvd_n by sorry
  -- Since 41 ∣ n and n > 0 (h_pos), then 41 ≤ n. (Nat.le_of_dvd)
  subprob_final_goal :≡ 41 ≤ n
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketh with proof
variable (n: ℕ) (h_pos: n > (0 : ℕ)) (p: ℕ → ℕ) (h₀: ∀ (x : ℕ), p x = x ^ (2 : ℕ) - x + (41 : ℕ)) (h₁: (1 : ℕ) < Nat.gcd (p n) (p (n + (1 : ℕ))))
play
  subprob_pn1_eval :≡ p (n + 1) = n ^ 2 + n + 41
  subprob_pn1_eval_proof ⇐ show subprob_pn1_eval by
    have h₂ : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41 := h₀ (n + 1)
    simp [Nat.pow_succ, Nat.mul_succ] at h₂
    linarith
  subprob_pn1_ge_pn :≡ p n ≤ p (n+1)
  subprob_pn1_ge_pn_proof ⇐ show subprob_pn1_ge_pn by
    simp_all [Nat.gcd_eq_right, Nat.gcd_eq_left]
    omega
  subprob_pn1_minus_pn :≡ p (n + 1) - p n = 2 * n
  subprob_pn1_minus_pn_proof ⇐ show subprob_pn1_minus_pn by
    rw [Nat.sub_eq_iff_eq_add subprob_pn1_ge_pn_proof]
    rw [subprob_pn1_eval_proof, h₀ n]
    rw [Nat.two_mul]
    rw [Nat.add_comm (n + n) (n^2 - n + 41)]
    rw [← Nat.add_assoc (n^2 - n + 41) n n]
    have h_n_le_nsq : n ≤ n ^ 2 := by
      cases n with
      | zero => contradiction
      | succ n' =>
        simp [Nat.pow_two]
    have h_rearrange_term : (n^2 - n + 41) + n = (n^2 - n) + (41 + n) := by
      exact Nat.add_assoc (n^2 - n) 41 n
    rw [h_rearrange_term]
    rw [Nat.add_comm 41 n]
    rw [← Nat.add_assoc (n^2 - n) n 41]
    rw [Nat.sub_add_cancel h_n_le_nsq]
    have add_add_swap (a b c : ℕ) : (a + b) + c = (a + c) + b := by rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]
    rw [add_add_swap (n^2) n 41]
  subprob_gcd_pnp1_pn_eq_gcd_2n_pn :≡ Nat.gcd (p (n + 1)) (p n) = Nat.gcd (2 * n) (p n)
  subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof ⇐ show subprob_gcd_pnp1_pn_eq_gcd_2n_pn by
    rw [<- Nat.gcd_sub_self_left subprob_pn1_ge_pn_proof]
    rw [subprob_pn1_minus_pn_proof]
  subprob_n_sq_minus_n_is_even :≡ (n ^ 2 - n) % 2 = 0
  subprob_n_sq_minus_n_is_even_proof ⇐ show subprob_n_sq_minus_n_is_even by
    have h_ge_one : 1 ≤ n := Nat.one_le_of_lt h_pos
    have h_eq : n ^ 2 - n = n * (n - 1) := by
      have h_distrib : n * (n - 1) = n * n - n * 1 := Nat.mul_sub n n 1
      have h_mul_one : n * n - n * 1 = n * n - n := by
        rw [Nat.mul_one]
      have h_pow_two : n * n - n = n ^ 2 - n := by
        rw [pow_two]
      have h_chain1 : n * (n - 1) = n * n - n := Eq.trans h_distrib h_mul_one
      have h_chain2 : n * (n - 1) = n ^ 2 - n := Eq.trans h_chain1 h_pow_two
      exact Eq.symm h_chain2
    rw [h_eq]
    have h_even_prod : Even (n * (n - 1)) := by
      have h_temp : Even ((n - 1) * ((n - 1) + 1)) := Nat.even_mul_succ_self (n - 1)
      have h_add_one_cancel : (n - 1) + 1 = n := Nat.sub_add_cancel h_ge_one
      rw [h_add_one_cancel] at h_temp
      rw [Nat.mul_comm (n - 1) n] at h_temp
      exact h_temp
    rw [← Nat.even_iff]
    exact h_even_prod
  subprob_pn_is_odd :≡ (p n) % 2 = 1
  subprob_pn_is_odd_proof ⇐ show subprob_pn_is_odd by
    simp_all only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    omega
  subprob_coprime_2_pn :≡ Nat.Coprime 2 (p n)
  subprob_coprime_2_pn_proof ⇐ show subprob_coprime_2_pn by
    rw [Nat.Coprime]
    rw [← Nat.mod_add_div (p n) 2]
    simp [subprob_pn_is_odd_proof]
  subprob_gcd_2n_pn_eq_gcd_n_pn :≡ Nat.gcd (2 * n) (p n) = Nat.gcd n (p n)
  subprob_gcd_2n_pn_eq_gcd_n_pn_proof ⇐ show subprob_gcd_2n_pn_eq_gcd_n_pn by
    apply subprob_coprime_2_pn_proof.gcd_mul_left_cancel
  subprob_gcd_n_pn_eq_gcd_n_41 :≡ Nat.gcd n (p n) = Nat.gcd n 41
  subprob_gcd_n_pn_eq_gcd_n_41_proof ⇐ show subprob_gcd_n_pn_eq_gcd_n_41 by
    rw [h₀ n]
    have h_ge_one : 1 ≤ n := Nat.succ_le_of_lt h_pos
    rw [Nat.pow_two n]
    rw [← Nat.mul_sub_one n]
    rw [add_comm (n * (n - 1)) 41]
    rw [Nat.gcd_add_mul_left_right n 41 (n - 1)]
  subprob_gcd_pnp1_pn_is_gcd_n_41 :≡ Nat.gcd (p (n + 1)) (p n) = Nat.gcd n 41
  subprob_gcd_pnp1_pn_is_gcd_n_41_proof ⇐ show subprob_gcd_pnp1_pn_is_gcd_n_41 by
    rw [subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof]
    rw [subprob_gcd_2n_pn_eq_gcd_n_pn_proof]
    rw [subprob_gcd_n_pn_eq_gcd_n_41_proof]
  subprob_1_lt_gcd_n_41 :≡ 1 < Nat.gcd n 41
  subprob_1_lt_gcd_n_41_proof ⇐ show subprob_1_lt_gcd_n_41 by
    simp_all [Nat.gcd_comm, Nat.gcd_assoc, Nat.gcd_mul_left, Nat.gcd_mul_right]
    <;> omega
  subprob_41_is_prime :≡ Nat.Prime 41
  subprob_41_is_prime_proof ⇐ show subprob_41_is_prime by
    have h₂ := subprob_gcd_pnp1_pn_is_gcd_n_41_proof
    have h₃ := subprob_1_lt_gcd_n_41_proof
    have h₄ := subprob_gcd_n_pn_eq_gcd_n_41_proof
    have h₅ := subprob_gcd_2n_pn_eq_gcd_n_pn_proof
    have h₆ := subprob_coprime_2_pn_proof
    have h₇ := subprob_pn_is_odd_proof
    have h₈ := subprob_n_sq_minus_n_is_even_proof
    have h₉ := subprob_gcd_pnp1_pn_eq_gcd_2n_pn_proof
    have h₁₀ := subprob_pn1_minus_pn_proof
    have h₁₁ := subprob_pn1_ge_pn_proof
    have h₁₂ := subprob_pn1_eval_proof
    have h₁₃ := h₀
    norm_num [Nat.Prime, Nat.gcd_eq_right] at h₃ ⊢
    <;> omega
  subprob_gcd_n_41_is_1_or_41 :≡ Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41
  subprob_gcd_n_41_is_1_or_41_proof ⇐ show subprob_gcd_n_41_is_1_or_41 by
    have h_prime_41 : Nat.Prime 41 := subprob_41_is_prime_proof
    have h_gcd_dvd_41 : Nat.gcd n 41 ∣ 41 := Nat.gcd_dvd_right n 41
    have h_gcd_eq_1_or_41 : Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41 :=
      h_prime_41.eq_one_or_self_of_dvd (Nat.gcd n 41) h_gcd_dvd_41
    exact h_gcd_eq_1_or_41
  subprob_gcd_n_41_is_41 :≡ Nat.gcd n 41 = 41
  subprob_gcd_n_41_is_41_proof ⇐ show subprob_gcd_n_41_is_41 by
    have h_gcd : Nat.gcd n 41 = 1 ∨ Nat.gcd n 41 = 41 := subprob_gcd_n_41_is_1_or_41_proof
    have h_1_lt_gcd : 1 < Nat.gcd n 41 := subprob_1_lt_gcd_n_41_proof
    cases h_gcd with
    | inl h_gcd_eq_1 =>
      linarith
    | inr h_gcd_eq_41 =>
      exact h_gcd_eq_41
  subprob_41_dvd_n :≡ 41 ∣ n
  subprob_41_dvd_n_proof ⇐ show subprob_41_dvd_n by
    have h₂ : Nat.gcd (p (n + 1)) (p n) = Nat.gcd n 41 := by
      rw [subprob_gcd_pnp1_pn_is_gcd_n_41_proof]
    have h₃ : Nat.gcd n 41 = 41 := by
      rw [subprob_gcd_n_41_is_41_proof]
    have h₄ : 41 ∣ n := by
      rw [← h₃]
      apply Nat.gcd_dvd_left
    exact h₄
  subprob_final_goal :≡ 41 ≤ n
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    have h₂ : 41 ≤ n := by
      apply Nat.le_of_dvd h_pos
      apply subprob_41_dvd_n_proof
    exact h₂
  original_target :≡ (41 : ℕ) ≤ n
  original_target_proof ⇐ show original_target by
    have h₀ := subprob_41_dvd_n_proof
    have h₁ := subprob_final_goal_proof
    omega
-/
