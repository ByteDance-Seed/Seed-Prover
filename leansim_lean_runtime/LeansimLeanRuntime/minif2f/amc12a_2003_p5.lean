import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2003_p5
  (A M C : ℕ)
  (h₀ : A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9)
  (h₁ : Nat.ofDigits 10 [0,1,C,M,A] + Nat.ofDigits 10 [2,1,C,M,A] = 123422) :
  A + M + C = 14 := by

  -- The problem involves natural numbers A, M, C which are single digits (<= 9).
  -- The equation involves Nat.ofDigits, which represents a number from a list of digits (least significant first).

  -- Destructure the hypothesis h₀
  rcases h₀ with ⟨hA_le_9, hM_le_9, hC_le_9⟩

  -- Expand the Nat.ofDigits terms in h₁
  -- Nat.ofDigits 10 [d0, d1, d2, d3, d4] = d0 + 10*d1 + 100*d2 + 1000*d3 + 10000*d4
  -- First term: Nat.ofDigits 10 [0,1,C,M,A] = 0 + 10*1 + 100*C + 1000*M + 10000*A = 10 + 100*C + 1000*M + 10000*A
  have h_e1 : Nat.ofDigits 10 [0,1,C,M,A] = 10 + 100 * C + 1000 * M + 10000 * A := by
    simp [Nat.ofDigits_cons, Nat.ofDigits_nil]
    ring

  -- Second term: Nat.ofDigits 10 [2,1,C,M,A] = 2 + 10*1 + 100*C + 1000*M + 10000*A = 12 + 100*C + 1000*M + 10000*A
  have h_e2 : Nat.ofDigits 10 [2,1,C,M,A] = 12 + 100 * C + 1000 * M + 10000 * A := by
    simp [Nat.ofDigits_cons, Nat.ofDigits_nil]
    ring

  -- Substitute the expanded terms into h₁
  rw [h_e1, h_e2] at h₁

  -- The equation is now: (10 + 100*C + 1000*M + 10000*A) + (12 + 100*C + 1000*M + 10000*A) = 123422
  -- Simplify the equation
  have h_eq_simplified : 22 + 200 * C + 2000 * M + 20000 * A = 123422 := by
    -- The previous `ring [h₁]` tactic failed.
    -- We explicitly prove that the left side of the goal is equal to the left side of the hypothesis h₁,
    -- then use this equality to rewrite h₁.
    have h_sides_eq : (10 + 100 * C + 1000 * M + 10000 * A) + (12 + 100 * C + 1000 * M + 10000 * A) = 22 + 200 * C + 2000 * M + 20000 * A := by ring
    -- The goal is 22 + ... = 123422. The hypothesis h₁ is (10 + ...) + (12 + ...) = 123422.
    -- We have shown h_sides_eq : (10 + ...) + (12 + ...) = 22 + ....
    -- To get the goal from h₁, we need to replace the left side of h₁ ((10 + ...) + (12 + ...))
    -- with the right side of h_sides_eq (22 + ...).
    -- This is a forward rewrite using h_sides_eq on h₁.
    -- The previous line `rw [← h_sides_eq] at h₁` attempted a backward rewrite, which was incorrect.
    rw [h_sides_eq] at h₁
    exact h₁

  -- Rearrange the equation: 20000*A + 2000*M + 200*C = 123422 - 22
  have h_eq_sub : 20000 * A + 2000 * M + 200 * C = 123400 := by
    linarith [h_eq_simplified]
    -- The goal after linarith [h_eq_simplified] is `123422 - 22 = 123400`. linarith solves the equation directly.
    -- The `norm_num` tactic is not needed here as linarith closes the goal.
    -- -- The tactic `norm_num` was redundant as `linarith` closed the goal.
    -- norm_num

  -- Divide by 200: 100*A + 10*M + C = 123400 / 200 = 617
  have h_factor_200 : 200 * (100 * A + 10 * M + C) = 20000 * A + 2000 * M + 200 * C := by ring
  -- We need to show that 200 divides 123400. Nat.eq_div_of_mul_eq_left requires the divisor is non-zero and the dividend is a multiple of the divisor.
  -- Prove 200 ≠ 0 explicitly before applying Nat.eq_div_of_mul_eq_left.
  have h_200_ne_0 : (200 : ℕ) ≠ 0 := by norm_num
  have h_eq_final : 100 * A + 10 * M + C = 617 := by
    rw [← h_factor_200] at h_eq_sub
    -- (Eq.symm h_eq_sub) provides the equality 123400 = 200 * (100 * A + 10 * M + C).
    -- Now apply the theorem using the explicit proof of 200 ≠ 0.
    -- Nat.eq_div_of_mul_eq_left expects the multiplication to be in the form a * c = b.
    -- We have 10 * (100 * A + 10 * M + C) * 20 = 123400.
    -- Let's rewrite 200 * (100 * A + 10 * M + C) using mul_comm to (100 * A + 10 * M + C) * 200.
    rw [mul_comm] at h_eq_sub
    -- We have (100 * A + 10 * M + C) * 200 = 123400. Use Nat.eq_div_of_mul_eq_left because the divisor 200 is on the right side.
    exact Nat.eq_div_of_mul_eq_left h_200_ne_0 h_eq_sub
    -- The goal after exact is 123400 / 200 = 617, which norm_num solves.
    -- -- The tactic `norm_num` was redundant as `exact Nat.eq_div_of_mul_eq_left ...` closed the goal by reducing the division.
    -- norm_num

  -- We have 100*A + 10*M + C = 617 and A, M, C are single digits (0-9).
  -- We can deduce A, M, C using base 10 representation uniqueness.

  -- Deduce C using modulo 10
  -- (100*A + 10*M + C) % 10 = 617 % 10
  have h_mod_eq : (100 * A + 10 * M + C) % 10 = C % 10 := by
    -- We want to show that (100*A + 10*M + C) % 10 is equal to C % 10.
    -- We will derive this using standard modulo properties.
    -- First, prove 10 divides 100*A + 10*M.
    have h_div_100A_10M : 10 ∣ 100 * A + 10 * M := by
      apply dvd_add -- Apply the property n ∣ a + b if n ∣ a and n ∣ b
      -- Prove 10 ∣ 100 * A. 100 * A = (10 * 10) * A = 10 * (10 * A). Use theorem a ∣ a * b.
      -- The previous line `apply dvd_mul_right 10 (10 * A)` failed.
      -- We need to explicitly rewrite 100 as 10 * 10 and then use associativity.
      have h_100_eq : 100 = 10 * 10 := by norm_num
      rw [h_100_eq] -- Goal is now 10 ∣ (10 * 10) * A
      rw [mul_assoc] -- Goal is now 10 ∣ 10 * (10 * A)
      -- Now the goal is in the form a ∣ a * b where a = 10 and b = 10 * A.
      -- apply dvd_mul_right 10 (10 * A) -- This also failed before. Let's try applying without arguments.
      apply dvd_mul_right -- Apply the theorem

      -- Prove 10 ∣ 10 * M. Use theorem a ∣ a * b.
      apply dvd_mul_right 10 M

    -- We have 10 ∣ 100*A + 10*M. This means (100*A + 10*M) % 10 = 0.
    have h_mod_zero : (100 * A + 10 * M) % 10 = 0 := by
      exact Nat.mod_eq_zero_of_dvd h_div_100A_10M

    -- Now use Nat.add_mod which states (a + b) % n = ((a % n) + (b % n)) % n
    -- Here a is (100*A + 10*M), b is C, and n is 10.
    rw [Nat.add_mod (100 * A + 10 * M) C 10]

    -- Substitute h_mod_zero
    rw [h_mod_zero]

    -- Simplify (0 + C % 10) % 10
    rw [zero_add] -- 0 + x = x
    rw [Nat.mod_mod] -- (x % n) % n = x % n

    -- The goal is now C % 10 = C % 10, which is true by rfl.
    -- -- Redundant tactic removed as per "no goals to be solved" message.
    -- The goal is already C % 10 = C % 10 at this point, which is definitionally true,
    -- so the final `rfl` is unnecessary.

  have hC_mod_10 : C % 10 = 617 % 10 := by
    rw [← h_mod_eq, h_eq_final]
    -- The goal C % 10 = 617 % 10 is proved by rewriting using h_mod_eq and h_eq_final.
    -- The `norm_num` tactic is not needed here as the goal is already closed by the rewrites.
    -- -- The tactic `norm_num` was redundant as the rewrites closed the goal.
    -- norm_num

  -- C % 10 = 7 is proved by norm_num
  have h_617_mod_10 : 617 % 10 = 7 := by norm_num
  rw [h_617_mod_10] at hC_mod_10


  -- Since C ≤ 9, C % 10 = C
  have hC_lt_10 : C < 10 := by exact Nat.lt_succ_of_le hC_le_9
  have hC_mod_id : C % 10 = C := by apply Nat.mod_eq_of_lt hC_lt_10

  -- Therefore C = 7
  have hC : C = 7 := by rwa [← hC_mod_id]

  -- Deduce M using modulo 10 after subtracting C and dividing by 10
  -- 100*A + 10*M = 617 - C
  have h_eq_sub_C : 100 * A + 10 * M = 610 := by
    linarith [h_eq_final, hC]
    -- The goal after linarith is 617 - 7 = 610. linarith solves the equation directly.
    -- The `norm_num` tactic is not needed here as linarith closes the goal.
    -- -- The tactic `norm_num` was redundant as `linarith` closed the goal.
    -- norm_num

  -- Divide by 10: 10*A + M = 610 / 10 = 61
  have h_factor_10 : 10 * (10 * A + M) = 100 * A + 10 * M := by ring
  -- Prove 10 ≠ 0 explicitly for division
  have h_10_ne_0 : (10 : ℕ) ≠ 0 := by norm_num
  have h_eq_div_10 : 10 * A + M = 61 := by
    rw [← h_factor_10] at h_eq_sub_C
    -- Need to show 10 divides 610.
    -- (Eq.symm h_eq_sub_C) provides the equality 610 = 10 * (10 * A + M).
    -- Now apply the theorem using the explicit proof of 10 ≠ 0.
    -- Nat.eq_div_of_mul_eq_left expects the multiplication to be in the form a * c = b.
    -- We have 10 * (10 * A + M) = 610.
    -- We need to rewrite this to (10 * A + M) * 10 = 610 using mul_comm.
    rw [mul_comm] at h_eq_sub_C
    -- We have (10 * A + M) * 10 = 610. Use Nat.eq_div_of_mul_eq_left because the divisor 10 is on the right side.
    exact Nat.eq_div_of_mul_eq_left h_10_ne_0 h_eq_sub_C
    -- The goal after exact is 610 / 10 = 61, which norm_num solves.
    -- -- The tactic `norm_num` was redundant as `exact Nat.eq_div_of_mul_eq_left ...` closed the goal by reducing the division.
    -- norm_num

  -- (10*A + M) % 10 = M % 10
  have h_mod_eq' : (10 * A + M) % 10 = M % 10 := by
    -- We want to show that (10*A + M) % 10 is equal to M % 10.
    -- We will derive this using standard modulo properties, similar to the previous case.
    -- First, prove 10 divides 10*A.
    -- We need to show 10 ∣ 10 * A. We use the theorem `dvd_mul_right a b : a ∣ a * b`.
    -- Applying `dvd_mul_right` should unify a=10 and b=A.
    -- The previous line `apply dvd_mul_right 10 A` failed. Let's try without arguments.
    have h_div_10A : 10 ∣ 10 * A := by apply dvd_mul_right

    -- We have 10 ∣ 10*A. This means (10*A) % 10 = 0.
    have h_mod_zero' : (10 * A) % 10 = 0 := by
      exact Nat.mod_eq_zero_of_dvd h_div_10A

    -- Now use Nat.add_mod which states (a + b) % n = ((a % n) + (b % n)) % n
    -- Here a is (10*A), b is M, and n is 10.
    rw [Nat.add_mod (10 * A) M 10]

    -- Substitute h_mod_zero'
    rw [h_mod_zero']

    -- Simplify (0 + M % 10) % 10
    rw [zero_add] -- 0 + x = x
    rw [Nat.mod_mod] -- (x % n) % n = x % n

    -- The goal is now M % 10 = M % 10, which is true by rfl.
    -- -- Redundant tactic removed as per "no goals to be solved" message.
    -- The goal is already M % 10 = M % 10 at this point, which is definitionally true,
    -- so the final `rfl` is unnecessary.

  have hM_mod_10 : M % 10 = 61 % 10 := by
    rw [← h_mod_eq', h_eq_div_10]
    -- The goal M % 10 = 61 % 10 is proved by rewriting using h_mod_eq' and h_eq_div_10.
    -- The `norm_num` tactic is not needed here as the goal is already closed by the rewrites.
    -- -- The tactic `norm_num` was redundant as the rewrites closed the goal.
    -- norm_num

  -- M % 10 = 1 is proved by norm_num
  have h_61_mod_10 : 61 % 10 = 1 := by norm_num
  rw [h_61_mod_10] at hM_mod_10

  -- Since M ≤ 9, M % 10 = M
  have hM_lt_10 : M < 10 := by exact Nat.lt_succ_of_le hM_le_9
  have hM_mod_id : M % 10 = M := by apply Nat.mod_eq_of_lt hM_lt_10

  -- Therefore M = 1
  have hM : M = 1 := by rwa [← hM_mod_id]

  -- Deduce A
  -- 10*A = 61 - M
  have h_eq_sub_M : 10 * A = 60 := by
    linarith [h_eq_div_10, hM]
    -- The goal after linarith is 61 - 1 = 60. linarith solves the equation directly.
    -- The `norm_num` tactic is not needed here as linarith closes the goal.
    -- -- The tactic `norm_num` was redundant as `linarith` closed the goal.
    -- norm_num

  -- A = 60 / 10 = 6
  have hA : A = 6 := by
    -- Need to show 10 divides 60.
    -- (Eq.symm h_eq_sub_M) provides the equality 60 = 10 * A.
    -- Now apply the theorem using the explicit proof of 10 ≠ 0.
    -- Nat.eq_div_of_mul_eq_left expects the multiplication to be in the form a * c = b.
    -- We have 10 * A = 60.
    -- We need to rewrite this to A * 10 = 60 using mul_comm.
    rw [mul_comm] at h_eq_sub_M
    -- We have A * 10 = 60. Use Nat.eq_div_of_mul_eq_left because the divisor 10 is on the right side.
    exact Nat.eq_div_of_mul_eq_left h_10_ne_0 h_eq_sub_M
    -- The goal after exact is 60 / 10 = 6, which norm_num solves.
    -- -- The tactic `norm_num` was redundant as `exact Nat.eq_div_of_mul_eq_left ...` closed the goal by reducing the division.
    -- norm_num

  -- Check if the values satisfy the original bounds (already used indirectly in modulo steps)
  -- hA_le_9 : A ≤ 9 -> 6 ≤ 9 (True)
  -- hM_le_9 : M ≤ 9 -> 1 ≤ 9 (True)
  -- hC_le_9 : C ≤ 9 -> 7 ≤ 9 (True)

  -- The goal is A + M + C = 14
  -- Substitute the values of A, M, C
  rw [hA, hM, hC]
  -- The goal becomes 6 + 1 + 7 = 14.
  -- This is definitionally equal to 14 = 14, which is true and closes the goal automatically.


#print axioms amc12a_2003_p5
