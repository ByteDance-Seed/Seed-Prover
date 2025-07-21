import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem numbertheory_2pownm1prime_nprime
  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : Nat.Prime (2^n - 1)) :
  Nat.Prime n := by 
 
  -- We prove the theorem by contradiction. Assume n is not prime.
  by_contra hn
  -- Since n is a natural number > 0 (by h₀), if it's not prime (by hn), it must be 1 or composite.
  -- We use the standard classification of natural numbers greater than 0.
  -- `0 < n` implies `n` is either 1 or `n > 1`.
  have n_eq_1_or_gt_1 : n = 1 ∨ n > 1 := by
    -- We know `0 < n` from `h₀`. This is equivalent to `n ≠ 0`.
    have hn_ne_zero : n ≠ 0 := Nat.pos_iff_ne_zero.mp h₀
    -- `n ≠ 0` implies `1 ≤ n` for natural numbers.
    have hn_ge_1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne_zero
    -- `1 ≤ n` is equivalent to `1 = n ∨ 1 < n`.
    have h_temp : (1 : ℕ) = n ∨ (1 : ℕ) < n := (le_iff_eq_or_lt).mp hn_ge_1
    -- The goal is `n = 1 ∨ n > 1`. We need to rearrange the hypothesis.
    rw [eq_comm] at h_temp
    -- `1 < n` is equivalent to `n > 1` by `gt_iff_lt`. We use the reverse direction `gt_iff_lt.symm.mp`.
    -- We apply this transformation to the second disjunct of `h_temp` using `Or.imp_right`.
    exact (Or.imp_right gt_iff_lt.symm.mp h_temp)
  -- Now we case on whether n is 1 or greater than 1.
  cases n_eq_1_or_gt_1 with
  | inl h_eq_one => -- Case 1: n = 1
    -- The goal is False.
    -- We have h₁ : Nat.Prime (2^n - 1).
    -- Substitute n = 1 into h₁.
    rw [h_eq_one] at h₁ -- h₁ becomes `Nat.Prime (2^1 - 1)`
    have : 2^1 - 1 = 1 := by norm_num
    rw [this] at h₁ -- h₁ becomes `Nat.Prime 1`
    -- We have h₁ : Nat.Prime 1.
    -- We also have hn : ¬Nat.Prime n, and n = 1, so hn : ¬Nat.Prime 1.
    -- `Nat.Prime 1` is false by definition (or by `Nat.not_prime_one`).
    -- We have `h₁ : Nat.Prime 1` and `hn : ¬Nat.Prime 1`.
    -- This is a contradiction.
    -- The type of `hn` in the context is `¬Nat.Prime n`. To apply it to `h₁ : Nat.Prime 1`,
    -- we need to rewrite `n` to `1` in the type of `hn`.
    rw [h_eq_one] at hn -- hn becomes `¬Nat.Prime 1`
    exact hn h₁ -- Apply the negation to the positive statement to get False.
  | inr h_gt_one => -- Case 2: n > 1
    -- The goal is False.
    -- Since n > 1 (by h_gt_one) and n is not prime (by hn), n is composite.
    -- n > 1 is equivalent to 2 ≤ n for natural numbers.
    have h_ge_2 : 2 ≤ n := Nat.succ_le_iff.mpr h_gt_one
    -- By the theorem `Nat.not_prime_iff_exists_dvd_lt`, since n ≥ 2 and n is not prime, there exists a divisor d such that 2 ≤ d ∧ d < n.
    have hexists_proper_divisor_of_n : ∃ d, d ∣ n ∧ 2 ≤ d ∧ d < n := (Nat.not_prime_iff_exists_dvd_lt h_ge_2).mp hn
    -- Destructure the existential statement to get the divisor d.
    rcases hexists_proper_divisor_of_n with ⟨d, hd_dvd_n, hd_ge_2, hdn⟩
    -- Since d ∣ n, there exists a k such that n = d * k.
    rcases exists_eq_mul_right_of_dvd hd_dvd_n with ⟨k, hk⟩
    -- We have n = d * k, d ≥ 2, d < n.
    -- We need to show k ≥ 2.
    -- From d < n and n = d * k, we have d < d * k.
    -- Since d ≥ 2, d is positive.
    have hd_pos : d > 0 := Nat.lt_trans (by norm_num) hd_ge_2 -- Prove d > 0 from d ≥ 2 using transitivity with 0 < 2.
    -- Using `Nat.lt_mul_iff_one_lt_right` (or equivalent), d < d * k and d > 0 implies 1 < k.
    -- 1 < k is equivalent to 2 ≤ k.
    have hk_ge_2 : 2 ≤ k := Nat.lt_iff_add_one_le.mp ((Nat.lt_mul_iff_one_lt_right hd_pos).mp (hk.symm ▸ hdn))
    -- We now have factors d and k such that n = d * k, d ≥ 2, k ≥ 2.
    -- Rename d to a and k to b to match the original proof's variable names.
    let a := d
    let b := k
    have hab : n = a * b := hk
    have ha_ge_2 : a ≥ 2 := hd_ge_2
    have hb_ge_2 : b ≥ 2 := hk_ge_2
    -- Derive a > 1 and b > 1 from a ≥ 2 and b ≥ 2 as used later in the proof.
    have ha1 : a > 1 := Nat.lt_of_succ_le ha_ge_2
    have hb1 : b > 1 := Nat.lt_of_succ_le hb_ge_2
    -- Prove 1 ≤ 2^a. Needed for Nat.cast_sub and Nat.one_le_pow.
    -- We know a ≥ 2 (ha_ge_2).
    -- Use Nat.one_le_pow exponent base (0 < base) where exponent is a, base is 2. We need 0 < 2.
    have h1_le_2a_nat : 1 ≤ 2^a := by
        apply Nat.one_le_pow a 2
        norm_num -- Prove 0 < 2
    -- Prove a * b ≥ 4.
    -- Use Nat.mul_le_mul applied to the inequalities a ≥ 2 and b ≥ 2.
    -- `Nat.mul_le_mul (h_le₁ : a ≤ b) (h_le₂ : c ≤ d)` proves `a * c ≤ b * d`.
    -- We use it with a=2, b=a, c=2, d=b. The proofs are ha_ge_2 (2 ≤ a) and hb_ge_2 (2 ≤ b).
    -- This yields 2 * 2 ≤ a * b.
    have hab_ge_4 : a * b ≥ 4 := Nat.mul_le_mul ha_ge_2 hb_ge_2
    -- Prove 2 ≤ a * b.
    have h2_le_ab : 2 ≤ a * b := Nat.le_trans (by norm_num : 2 ≤ 4) hab_ge_4
    -- Prove 2^2 ≤ 2^(a*b).
    have h_2_pow_2_le_2_pow_ab : 2 ^ 2 ≤ 2 ^ (a * b) := Nat.pow_le_pow_of_le_right (by norm_num : 0 < 2) h2_le_ab
    -- Prove 1 ≤ (2^a)^b. Needed for Nat.cast_sub later.
    have h1_le_pow_pow : 1 ≤ (2^a)^b := by
      -- We prove 1 ≤ 2^(a*b) and then use the equality 2^(a*b) = (2^a)^b.
      -- Prove 1 ≤ 2^2 first.
      have h1_le_2_pow_2 : 1 ≤ 2^2 := by norm_num
      -- Prove 1 ≤ 2^(a*b) using transitivity.
      have h1_le_2_pow_ab : 1 ≤ 2 ^ (a * b) := Nat.le_trans h1_le_2_pow_2 h_2_pow_2_le_2_pow_ab
      -- Use the equality 2^(a*b) = (2^a)^b provided by pow_mul.
      have hab_eq_pow_pow : 2 ^ (a * b) = (2 ^ a) ^ b := pow_mul (2 : ℕ) a b
      -- Rewrite the inequality using the equality.
      rw [hab_eq_pow_pow] at h1_le_2_pow_ab
      -- The goal is now proven by the modified hypothesis.
      exact h1_le_2_pow_ab
    -- Define k1 = 2^a - 1 as a natural number.
    -- Since a ≥ 2, 2^a ≥ 2^2 = 4. So 2^a - 1 ≥ 3. This subtraction is valid for natural numbers.
    -- We need to ensure 1 ≤ 2^a for the subtraction `2^a - 1` to be valid in Nat.
    -- We already have h1_le_2a_nat : 1 ≤ 2^a.
    let k1 : ℕ := 2^a - 1
    -- Prove k1 > 1.
    have hk1_gt_1 : k1 > 1 := by
      -- Goal: k1 > 1 which is 1 < 2^a - 1.
      -- This is equivalent to 2 ≤ 2^a - 1.
      -- We know a ≥ 2 (ha_ge_2).
      -- 2 ≤ a implies 2^2 ≤ 2^a.
      have h_2_pow_2_le_2_pow_a : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_of_le_right (by norm_num : 0 < 2) ha_ge_2
      -- 2^2 is definitionally 4. So h_2_pow_2_le_2_pow_a is definitionally 4 ≤ 2^a.
      -- We can just use h_2_pow_2_le_2_pow_a directly to state 4 ≤ 2^a.
      have h4_le_2a : 4 ≤ 2^a := h_2_pow_2_le_2_pow_a
      -- We have 4 ≤ 2^a. We need to show 2 ≤ 2^a - 1.
      -- 3 ≤ 4 ≤ 2^a, so 3 ≤ 2^a.
      have h3_le_2a : 3 ≤ 2^a := Nat.le_trans (by norm_num : 3 ≤ 4) h4_le_2a
      -- Subtract 1 from both sides (valid because 1 ≤ 3 and 1 ≤ 2^a, both are true).
      have h_subtracted : 3 - 1 ≤ 2^a - 1 := tsub_le_tsub_right h3_le_2a 1
      -- Simplify 3 - 1.
      have h3_minus_1_eq_2 : 3 - 1 = 2 := by norm_num
      -- Rewrite the inequality using the simplified left side.
      rw [h3_minus_1_eq_2] at h_subtracted
      -- h_subtracted is now 2 ≤ 2^a - 1, which is 2 ≤ k1.
      -- Apply Nat.lt_of_succ_le to get 1 < k1.
      exact Nat.lt_of_succ_le h_subtracted
    -- Define k2 = ∑ i in Finset.range b, (2^a) ^ i as a natural number.
    let k2 : ℕ := ∑ i in Finset.range b, (2^a) ^ i
    -- Prove k2 > 1.
    have hk2_gt_1 : k2 > 1 := by
      dsimp [k2]
      -- Goal: ∑ i in Finset.range b, (2^a) ^ i > 1
      -- We know b ≥ 2 (hb_ge_2). So Finset.range b contains 0 and 1.
      have h0_lt_b : 0 < b := Nat.lt_trans (by norm_num) hb_ge_2
      have h0_mem_range_b : 0 ∈ Finset.range b := Finset.mem_range.mpr h0_lt_b
      -- Split the sum into terms for i=0 and the rest using Finset.sum_eq_sum_diff_singleton_add.
      rw [Finset.sum_eq_sum_diff_singleton_add h0_mem_range_b]
      -- The sum is over Finset.range b \ {0}. The term at 0 is (2^a)^0.
      -- Goal: (∑ i in Finset.range b \ {0}, (2^a) ^ i) + (2^a) ^ 0 > 1
      -- Rewrite (2^a)^0 to 1 using pow_zero.
      rw [pow_zero (2^a)]
      -- Goal: (∑ i in Finset.range b \ {0}, (2^a) ^ i) + 1 > 1
      -- Let S = ∑ i in Finset.range b \ {0}, (2^a) ^ i. Goal: S + 1 > 1.
      -- This is equivalent to 1 < S + 1.
      rw [gt_iff_lt]
      -- Goal: 1 < S + 1
      -- Rewrite 1 to succ 0.
      rw [Nat.one_eq_succ_zero]
      -- Goal: succ 0 < S + 1
      -- Rewrite S + 1 to succ S using Nat.succ_eq_add_one.
      rw [Nat.succ_eq_add_one]
      -- Goal: succ 0 < succ (∑ i ∈ Finset.range b \ {0}, ((2 : ℕ) ^ a) ^ i)
      -- Now the goal matches the pattern for Nat.succ_lt_succ_iff.
      rw [Nat.succ_lt_succ_iff] -- Rewrite succ 0 < succ S to 0 < S.
      -- Goal: 0 < S
      -- Goal: 0 < ∑ i in Finset.range b \ {0}, (2^a) ^ i
      -- The remaining sum is over the set {1, 2, ..., b-1}, since b ≥ 2 implies Finset.range b \ {0} = {1, ..., b-1}.
      -- Since b ≥ 2, this set is non-empty (it contains 1).
      -- The terms being summed are (2^a)^i. Since a ≥ 2, 2^a ≥ 4.
      -- For i ∈ {1, ..., b-1}, i ≥ 1, so (2^a)^i ≥ 4^i.
      -- For i ≥ 1, 4^i ≥ 4, which is positive.
      -- Use `Finset.sum_pos`. We need the set to be nonempty and all terms positive.
      -- We need proof that `1 ∈ Finset.range b \ {0}`.
      have h1_mem : 1 ∈ Finset.range b \ {0} := by
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        -- Need 1 < b and 1 ≠ 0.
        constructor
        . -- Prove 1 < b. We have b ≥ 2 (hb_ge_2).
          exact Nat.lt_of_succ_le hb_ge_2 -- 2 ≤ b implies 1 < b.
        . -- Prove 1 ≠ 0.
          decide
      -- Now apply Finset.sum_pos.
      apply Finset.sum_pos
      . -- Prove all terms are positive.
        intro i hi
        -- i ∈ Finset.range b \ {0} means i ∈ Finset.range b and i ≠ 0.
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
        have hi_ne_0 : i ≠ 0 := hi.right
        -- Since i ∈ ℕ and i ≠ 0, i ≥ 1.
        have hi_ge_1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi_ne_0
        -- We need to show 0 < (2^a)^i.
        -- We know a ≥ 2 (ha_ge_2). This implies 1 ≤ 2^a (h1_le_2a_nat).
        -- Since 1 ≤ 2^a, and for any natural number exponent i, we have 1 ≤ (2^a)^i.
        -- Use `one_le_pow_of_one_le'` which proves `1 ≤ base ^ exponent` given `1 ≤ base`.
        -- We apply this with base = 2^a and exponent = i, using hypothesis `h1_le_2a_nat : 1 ≤ 2^a`.
        have h1_le_pow : 1 ≤ (2^a)^i := one_le_pow_of_one_le' h1_le_2a_nat i
        -- 1 ≤ (2^a)^i implies 0 < (2^a)^i.
        exact Nat.lt_of_succ_le h1_le_pow
      . -- Prove the set is non-empty. We use the element 1, which we proved is in the set (h1_mem).
        refine ⟨1, h1_mem⟩
    -- We need to prove 2^n - 1 = k1 * k2.
    -- Substitute n = a * b, k1 = 2^a - 1, k2 = ∑ i in Finset.range b, (2^a) ^ i.
    -- We need to prove 2^(a*b) - 1 = (2^a - 1) * ∑ i in Finset.range b, (2^a) ^ i.
    -- Using pow_mul, this is (2^a)^b - 1 = (2^a - 1) * ∑ i in Finset.range b, (2^a) ^ i.
    -- We prove this identity by casting to ℤ, where it's a known geometric series formula.
    let x_nat := 2^a
    let x_int : ℤ := x_nat
    -- Prove the identity in ℤ: (x_int - 1) * (∑ i in Finset.range b, x_int ^ i) = x_int ^ b - 1.
    -- Use mul_geom_sum theorem, which applies to Rings like ℤ.
    have h_geom_sum_int : (x_int - 1) * (∑ i in Finset.range b, x_int ^ i) = x_int ^ b - 1 := mul_geom_sum x_int b
    -- We need to relate this back to the desired equality in ℕ: (x_nat)^b - 1 = (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i.
    -- We use the injectivity of Nat.cast (from ℕ to ℤ) for non-negative numbers.
    -- We need to show that the terms involved in subtractions in the ℕ equality are non-negative for casting.
    -- x_nat = 2^a. Since a ≥ 2, 2^a ≥ 4. So x_nat ≥ 4.
    have hx_nat_ge_4 : x_nat ≥ 4 := by
      show 4 ≤ 2^a
      rw [show 4 = 2^2 by norm_num]
      exact Nat.pow_le_pow_of_le_right (by norm_num : 0 < 2) ha_ge_2
    -- 1 ≤ x_nat, required for Nat.cast_sub (x_nat - 1).
    have h1_le_x_nat : 1 ≤ x_nat := Nat.le_trans (by norm_num) hx_nat_ge_4
    -- x_nat^b: Since x_nat ≥ 4 and b ≥ 2, x_nat^b ≥ 4^2 = 16.
    have hx_nat_pow_b_ge_16 : x_nat^b ≥ 16 := by
      rw [show 16 = 4^2 by norm_num]
      show 4^2 ≤ x_nat^b
      -- Use the version from OrderedSemiring: pow_le_pow_left (ha : 0 ≤ a) (hle : a ≤ b) (n : ℕ) : a^n ≤ b^n
      -- The arguments are (0 ≤ 4), (4 ≤ x_nat), and the exponent 2.
      have h_4_pow_2_le_x_nat_pow_2 : 4^2 ≤ x_nat^2 := pow_le_pow_left (by norm_num : 0 ≤ 4) hx_nat_ge_4 2
      -- Prove x_nat^2 ≤ x_nat^b from 2 ≤ b using Nat.pow_le_pow_right (fixed base, changing exponent).
      -- This theorem requires the base to be >= 1 (x_nat >= 1). We have h1_le_x_nat : 1 ≤ x_nat.
      have h_x_nat_pow_2_le_x_nat_pow_b : x_nat^2 ≤ x_nat^b := Nat.pow_le_pow_right h1_le_x_nat hb_ge_2
      exact Nat.le_trans h_4_pow_2_le_x_nat_pow_2 h_x_nat_pow_2_le_x_nat_pow_b
    -- 1 ≤ x_nat^b, required for Nat.cast_sub (x_nat^b - 1).
    -- We already proved x_nat^b ≥ 16, which implies 1 ≤ x_nat^b.
    have h1_le_x_nat_pow_b : 1 ≤ x_nat^b := Nat.le_trans (by norm_num) hx_nat_pow_b_ge_16
    -- Cast LHS of the ℕ equality: Nat.cast (x_nat^b - 1).
    have h_cast_lhs_eq : Nat.cast (x_nat^b - 1) = (x_int^b - 1 : ℤ) := by
      -- Use Nat.cast_sub, which requires the subtrahend <= minuend in ℕ. We know 1 <= x_nat^b.
      rw [Nat.cast_sub h1_le_x_nat_pow_b]
      -- Cast of power is power of cast, Cast of 1 is 1.
      rw [Nat.cast_pow x_nat b, Nat.cast_one]
      done
    -- Cast RHS factor 1: Nat.cast (x_nat - 1).
    have h_cast_rhs_factor1_eq : Nat.cast (x_nat - 1) = (x_int - 1 : ℤ) := by
      -- Use Nat.cast_sub, which requires 1 <= x_nat.
      rw [Nat.cast_sub h1_le_x_nat]
      -- Cast of 1 is 1.
      rw [Nat.cast_one]
      done
    -- Cast RHS factor 2: Nat.cast (∑ i in Finset.range b, x_nat ^ i).
    have h_cast_rhs_factor2_eq : Nat.cast (∑ i in Finset.range b, x_nat ^ i) = ∑ i in Finset.range b, (x_int) ^ i := by
      -- Cast of sum is sum of cast.
      rw [Nat.cast_sum]
      -- Cast of power is power of cast, and x_int is Nat.cast x_nat.
      -- Apply Nat.cast_pow and simplify using definition of x_int.
      simp_rw [Nat.cast_pow]
    -- Put RHS cast together: Nat.cast ((x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i).
    have h_cast_rhs_eq : Nat.cast ((x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i) = ((x_int - 1) * ∑ i in Finset.range b, x_int ^ i : ℤ) := by
      -- Cast of multiplication is multiplication of casts.
      -- The following rewrites simplify the left side of the equality by applying cast properties.
      rw [Nat.cast_mul, h_cast_rhs_factor1_eq, h_cast_rhs_factor2_eq]

    -- The equality holds in ℤ.
    -- We need to prove 2^n - 1 = k1 * k2 by lifting the ℤ identity using Nat.cast_inj.
    -- First, show the casted versions are equal in ℤ.
    have h_cast_eq_int : (Nat.cast (x_nat^b - 1) : ℤ) = (Nat.cast ((x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i) : ℤ) := by
      -- Use the casting equalities to move to ℤ
      rw [h_cast_lhs_eq, h_cast_rhs_eq]
      -- Use the geometric sum identity in ℤ
      rw [h_geom_sum_int.symm]

    -- Use the injectivity of Nat.cast to conclude the ℕ equality.
    -- Nat.cast_inj applies directly if both terms are ℕ.
    -- h_cast_eq_int is an equality between two ℤ values, where each value is the cast of a ℕ value.
    -- We need to apply Nat.cast_inj to this equality.
    have h_prod_nat' : (x_nat^b - 1) = ((x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i) := Nat.cast_inj.mp h_cast_eq_int

    -- We need to prove k1 * k2 = 2^n - 1.
    -- Substitute n = a * b, k1 = 2^a - 1, k2 = ∑ i in Finset.range b, (2^a) ^ i.
    -- We need to prove (2^a - 1) * ∑ i in Finset.range b, (2^a) ^ i = 2^(a*b) - 1.
    -- Let x_nat = 2^a. The equality becomes (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i = x_nat^b - 1.
    -- We prove the equality k1 * k2 = (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i first.
    have h_k1_k2_eq_expr : k1 * k2 = (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i := by
      -- Use the definitions of k1, k2, and x_nat
      dsimp [k1, k2, x_nat]
      -- The goal is definitionally true after unfolding definitions.
      -- Removed the redundant `rfl` tactic as the goal is already solved.

    -- We also prove the equality 2^n - 1 = x_nat^b - 1.
    have h_2n1_eq_xnat_pow_b_minus_1 : 2^n - 1 = x_nat^b - 1 := by
      -- Rewrite n using hab
      rw [hab]
      -- Rewrite 2^(a*b) using pow_mul
      rw [pow_mul (2 : ℕ) a b]
      -- The goal `(2^a)^b - 1 = x_nat^b - 1` is definitionally true since x_nat is defined as 2^a.
      done

    -- Now we prove k1 * k2 = 2^n - 1 by showing they are both equal to (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i and x_nat^b - 1 respectively, which are equal in ℕ by h_prod_nat'.
    have h_k1_k2_eq_2n1 : k1 * k2 = 2^n - 1 := by
      -- Rewrite LHS using h_k1_k2_eq_expr
      rw [h_k1_k2_eq_expr]
      -- Rewrite RHS using h_2n1_eq_xnat_pow_b_minus_1
      rw [h_2n1_eq_xnat_pow_b_minus_1]
      -- The goal is now (x_nat - 1) * ∑ i in Finset.range b, x_nat ^ i = x_nat^b - 1
      -- This is exactly h_prod_nat'.symm.
      exact h_prod_nat'.symm

    -- Now we have the equality k1 * k2 = 2^n - 1. This implies k1 divides 2^n - 1.
    -- Use the theorem `Dvd.intro c h` which proves `a ∣ b` given `h : a * c = b`.
    -- Here, `a` is `k1`, `b` is `2^n - 1`, and `c` is `k2`. The equality `h_k1_k2_eq_2n1` is exactly `h : k1 * k2 = 2^n - 1`.
    have hk1_dvd : k1 ∣ 2^n - 1 := Dvd.intro k2 h_k1_k2_eq_2n1
    -- Apply the prime definition to 2^n - 1.
    -- h₁ : Nat.Prime (2^n - 1)
    -- Prime definition: p > 1 and for all m, m | p implies m = 1 or m = p.
    -- We know 2^n - 1 > 1 from h₁ (prime numbers are > 1 by definition).
    have h2n1_gt_1 := (Nat.prime_def_lt''.mp h₁).left
    -- Use the second part of the prime definition for m = k1.
    have h_prime_prop := (Nat.prime_def_lt''.mp h₁).right -- ∀ (m : ℕ), m ∣ (2^n - 1) → m = 1 ∨ m = (2^n - 1)
    -- Apply h_prime_prop with m = k1 and hk1_dvd.
    have h_k1_cases : k1 = 1 ∨ k1 = 2^n - 1 := h_prime_prop k1 hk1_dvd
    -- We have k1 > 1 (hk1_gt_1), which implies k1 ≠ 1.
    have hk1_ne_1 : k1 ≠ 1 := Nat.ne_of_gt hk1_gt_1
    -- From `k1 = 1 ∨ k1 = 2^n - 1` and `k1 ≠ 1`, conclude `k1 = 2^n - 1`.
    have h_k1_is_2n1 : k1 = 2^n - 1 := Or.resolve_left h_k1_cases hk1_ne_1

    -- We have the equality k1 * k2 = 2^n - 1 (h_k1_k2_eq_2n1).
    -- Substitute k1 using h_k1_is_2n1. This changes h_k1_k2_eq_2n1 to (2^n - 1) * k2 = 2^n - 1.
    rw [h_k1_is_2n1] at h_k1_k2_eq_2n1

    -- We have (2^n - 1) * k2 = 2^n - 1 (from h_k1_k2_eq_2n1).
    -- We know 0 < 2^n - 1 from h₁ (prime numbers are > 1 by definition).
    have h2n1_pos : 0 < 2^n - 1 := Nat.lt_trans (by norm_num) h2n1_gt_1
    -- We use Nat.mul_left_eq_self_iff which states 0 < b → (a * b = b ↔ a = 1).
    -- Let a = k2 and b = 2^n - 1.
    -- We need the hypothesis 0 < b, which is h2n1_pos.
    -- The theorem gives (k2 * (2^n - 1) = 2^n - 1 ↔ k2 = 1).
    -- Our hypothesis is (2^n - 1) * k2 = 2^n - 1. We need to commute the multiplication to match the theorem's left side.
    have h_prod_comm : k2 * (2^n - 1) = 2^n - 1 := by
      rw [mul_comm k2 (2^n - 1)]
      -- The goal is now (2^n - 1) * k2 = 2^n - 1, which matches the current h_k1_k2_eq_2n1.
      exact h_k1_k2_eq_2n1

    -- Now apply the forward implication (mp) of the equivalence theorem.
    have h_k2_eq_1 : k2 = 1 := (Nat.mul_left_eq_self_iff h2n1_pos).mp h_prod_comm

    -- Contradiction: We have k2 = 1 (h_k2_eq_1) and k2 > 1 (hk2_gt_1).
    have h_k2_not_eq_1 : k2 ≠ 1 := Nat.ne_of_gt hk2_gt_1
    exact h_k2_not_eq_1 h_k2_eq_1


#print axioms numbertheory_2pownm1prime_nprime