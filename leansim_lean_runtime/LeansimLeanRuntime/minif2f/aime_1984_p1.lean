import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k in Finset.range 98, u k.succ = 137) :
  ∑ k in Finset.range 49, u (2 * k.succ) = 93 := by 

  -- Prove u n = u 0 + n by induction on n
  -- This formula is derived from the recurrence relation h₀.
  have u_formula : ∀ n : ℕ, u n = u 0 + ↑n := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      -- Goal: u 0 = u 0 + ↑0
      simp -- u 0 = u 0 + 0 is true by arithmetic.
    | succ n ih =>
      -- Inductive step: Assume u n = u 0 + ↑n, prove u (n + 1) = u 0 + ↑(n + 1)
      -- Goal: u (n.succ) = u 0 + ↑(n.succ)
      -- Use the recurrence relation h₀ to expand the left side.
      rw [h₀ n]
      -- Goal: u n + 1 = u 0 + ↑(n.succ)
      -- Use the inductive hypothesis ih: u n = u 0 + ↑n
      rw [ih]
      -- Goal: (u 0 + ↑n) + 1 = u 0 + ↑(n.succ)
      -- Use Nat.cast_succ to expand ↑(n.succ)
      rw [Nat.cast_succ n]
      -- Goal: (u 0 + ↑n) + 1 = u 0 + (↑n + 1 : ℚ)
      -- This is an equality of rational numbers. Use ring to prove it.
      ring

  -- Expand the terms in h₁ using the formula u n = u 0 + n and Nat.cast_succ,
  -- then split the sum using sum_add_distrib.
  -- The original hypothesis is h₁ : ∑ k in Finset.range 98, u k.succ = 137
  -- We want to derive the equation: (∑ k in Finset.range 98, u 0) + (∑ k in Finset.range 98, (↑k + 1 : ℚ)) = 137
  have sum_eq_137 : (∑ k in Finset.range 98, u 0) + (∑ k in Finset.range 98, (↑k + 1 : ℚ)) = 137 := by
    -- Start with h₁
    have eq := h₁
    -- Rewrite the term u k.succ using u_formula and Nat.cast_succ.
    -- u k.succ = u (k + 1) = u 0 + ↑(k + 1) = u 0 + (↑k + 1 : ℚ)
    have rewrite_term : ∀ k ∈ Finset.range 98, u k.succ = (u 0 + (↑k + 1) : ℚ) := by
      intro k hk
      rw [u_formula k.succ, Nat.cast_succ]
    -- Apply sum_congr to the LHS of the equation `eq` to rewrite the terms inside the sum.
    rw [Finset.sum_congr rfl rewrite_term] at eq
    -- The equation `eq` is now ∑ k in Finset.range 98, (u 0 + ↑k + 1 : ℚ) = 137.
    -- Apply sum_add_distrib to the LHS of the equation `eq`.
    -- ∑ k in range 98, (u 0 + (↑k + 1)) = ∑ k in range 98, u 0 + ∑ k in range 98, (↑k + 1)
    rw [Finset.sum_add_distrib] at eq
    -- The equation `eq` is now (∑ k in Finset.range 98, u 0) + (∑ k in Finset.range 98, (↑k + 1 : ℚ)) = 137.
    -- This matches the goal of this 'have' block.
    exact eq

  -- Calculate the first part of the sum: ∑ k in Finset.range 98, u 0
  -- This is summing a constant u 0 for 98 terms, so it's 98 * u 0
  have sum_u0 : ∑ k in Finset.range 98, u 0 = (98 : ℚ) * u 0 := by
    -- The sum of a constant `c` over a finset `s` is `s.card • c`.
    -- `(Finset.range 98).card` is `98`. So the sum is `98 • u 0`.
    -- The equality (n : ℕ) • q = (n : ℚ) * q for q : ℚ is provable by simp.
    simp

  -- Calculate the second part of the sum: ∑ k in Finset.range 98, (k + 1 : ℚ)
  -- This is ∑ k in {0, ..., 97}, (k + 1)
  have sum_k_plus_1 : ∑ k in Finset.range 98, (↑k + 1 : ℚ) = 4851 := by
    -- Split the sum ∑ (↑k + 1) = ∑ ↑k + ∑ 1
    rw [Finset.sum_add_distrib]
    -- Calculate the first part: ∑ ↑k
    -- ∑ k in range n, ↑k = ↑(∑ k in range n, k)
    -- Use the theorem `Nat.cast_sum` to pull the natural number casting out of the sum.
    conv =>
      lhs -- Target the left-hand side of the equality
      arg 1 -- Target the first term of the sum on the LHS: ∑ k ∈ Finset.range 98, (↑k : ℚ)
      -- Apply the rewrite rule `↑(∑ k ∈ s, f x) = ∑ k ∈ s, ↑(f x)` backwards with f = fun k => k
      rw [← Nat.cast_sum (Finset.range 98) (fun k => k)]
    -- Goal after conv: ↑(∑ k ∈ Finset.range 98, k) + ∑ k ∈ Finset.range (98 : ℕ), (1 : ℚ) = (4851 : ℚ)

    -- Use the formula for the sum of the first n natural numbers: ∑ i in range n, i = n * (n-1) / 2
    rw [Finset.sum_range_id] -- Applies to the inner sum ∑ k ∈ Finset.range 98, k
    -- Goal: (↑(98 * (98 - 1) / 2) : ℚ) + ∑ k ∈ Finset.range (98 : ℕ), (1 : ℚ) = (4851 : ℚ)

    -- Use norm_num to evaluate the casted arithmetic expression and the constant sum.
    norm_num -- This evaluates ↑(98 * 97 / 2) + 98 * 1

  -- Substitute the calculated sums back into the equation sum_eq_137.
  -- (98 * u 0) + 4851 = 137
  have u0_linear_eq : (98 : ℚ) * u 0 + 4851 = 137 := by
    have eq1 := sum_eq_137
    rw [sum_u0] at eq1
    rw [sum_k_plus_1] at eq1
    exact eq1


  -- From 98 * u 0 + 4851 = 137, we solve for 49 * u 0
  -- (98 * u 0) / 2 = (137 - 4851) / 2
  -- 49 * u 0 = -4714 / 2 = -2357
  have forty_nine_u0 : 49 * u 0 = -2357 := by
    -- Get the linear equation for u 0: 98 * u 0 + 4851 = 137
    have eq1 := u0_linear_eq
    -- Subtract 4851 from both sides using linarith
    have eq2 : (98 : ℚ) * u (0 : ℕ) = (137 : ℚ) - (4851 : ℚ) := by linarith [eq1]
    -- Calculate 137 - 4851
    have sub_val : (137 : ℚ) - (4851 : ℚ) = -4714 := by norm_num
    rw [sub_val] at eq2 -- (98 : ℚ) * u (0 : ℕ) = (-4714 : ℚ)
    -- Rewrite 98 as 2 * 49
    have ninety_eight_eq : (98 : ℚ) = 2 * 49 := by norm_num
    rw [ninety_eight_eq] at eq2 -- (2 * 49 : ℚ) * u (0 : ℕ) = (-4714 : ℚ)
    -- Rearrange: (2 : ℚ) * ((49 : ℚ) * u (0 : ℕ)) = (-4714 : ℚ)
    rw [mul_assoc] at eq2
    -- Rewrite -4714 as 2 * -2357
    have minus_4714_eq : (-4714 : ℚ) = 2 * (-2357) := by norm_num
    rw [minus_4714_eq] at eq2 -- (2 : ℚ) * ((49 : ℚ) * u (0 : ℕ)) = (2 : ℚ) * (-2357 : ℚ)
    -- Use mul_left_cancel₀ to cancel 2
    have two_ne_zero : (2 : ℚ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ two_ne_zero eq2


  -- Now consider the target sum: ∑ k in Finset.range 49, u (2 * k.succ)
  -- This is ∑ k in {0, ..., 48}, u (2 * (k + 1)) = ∑ k in {0, ..., 48}, u (2k + 2)
  -- Use the formula u_n = u_0 + n
  -- u (2k+2) = u 0 + (2k+2)
  -- Expand the term u (2 * k.succ) using u_formula and Nat.cast_succ.
  -- u (2 * k.succ) = u (2 * (k+1)) = u (2k + 2) = u 0 + ↑(2k + 2) = u 0 + (↑(2k) + ↑2) = u 0 + (2*↑k + 2)
  -- The target sum is equal to ∑ k in Finset.range 49, (u 0 + (2 * ↑k + 2) : ℚ)
  have target_expanded : ∑ k in Finset.range 49, u (2 * k.succ) = ∑ k in Finset.range 49, (u 0 + (2 * ↑k + 2) : ℚ) := by
    -- Prove the equality of the terms inside the sum.
    have term_eq : ∀ k ∈ Finset.range 49, u (2 * k.succ) = (u 0 + (2 * ↑k + 2) : ℚ) := by
      intro k hk
      -- Expand LHS: u (2 * k.succ) = u 0 + ↑(2 * k.succ) using u_formula
      rw [u_formula (2 * k.succ)]
      -- We need to show ↑(2 * k.succ) = (2 * ↑k + 2 : ℚ).
      have nat_cast_eq : ↑(2 * k.succ) = (2 * ↑k + 2 : ℚ) := by
        -- Goal: ↑(2 * k.succ) = (2 * ↑k + 2 : ℚ)
        -- Apply Nat.cast_mul to the left side: ↑(2 * k.succ) = ↑2 * ↑(k.succ)
        rw [Nat.cast_mul]
        -- Goal: (↑2 * ↑(k.succ) : ℚ) = (2 * ↑k + 2 : ℚ)
        -- Apply Nat.cast_succ to the subterm ↑(k.succ): ↑(k.succ) = ↑k + 1
        rw [Nat.cast_succ k]
        -- Goal: (↑2 * (↑k + 1) : ℚ) = (2 * ↑k + 2 : ℚ)
        -- The remaining equality is an algebraic identity in ℚ. Use ring.
        ring
      -- Now that we have proven nat_cast_eq, apply it to the main goal of term_eq.
      rw [nat_cast_eq]
    -- Apply Finset.sum_congr with rfl for the finset equality and term_eq for the term equality.
    rw [Finset.sum_congr rfl term_eq]


  -- Split the expanded target sum using sum_add_distrib.
  -- ∑ k in range 49, (u 0 + (2*↑k + 2)) = ∑ k in range 49, u 0 + ∑ k in range 49, (2*↑k + 2)
  have target_split : ∑ k in Finset.range 49, (u 0 + (2 * ↑k + 2) : ℚ) = (∑ k in Finset.range 49, u 0) + (∑ k in Finset.range 49, (2 * ↑k + 2 : ℚ)) := by
    -- Apply sum_add_distrib to the sum on the left side. The terms (u 0 + (2 * ↑k + 2) : ℚ) are in ℚ, which is an AddCommMonoid.
    rw [Finset.sum_add_distrib]

  -- Combine target_expanded and target_split to express the target sum as the sum of two separate sums.
  have target_sum_split : ∑ k in Finset.range 49, u (2 * k.succ) = (∑ k in Finset.range 49, u 0) + (∑ k in Finset.range 49, (2 * ↑k + 2 : ℚ)) := by
    rw [target_expanded, target_split]

  -- Calculate the first part of the target sum: ∑ k in Finset.range 49, u 0
  -- This is summing a constant u 0 for 49 terms, so it's 49 * u 0
  have target_sum_u0 : ∑ k in Finset.range 49, u 0 = (49 : ℚ) * u 0 := by
    -- The sum of a constant `c` over a finset `s` is `s.card • c`.
    -- `(Finset.range 49).card` is `49`. So the sum is `49 • u 0`.
    -- The equality (n : ℕ) • q = (n : ℚ) * q for q : ℚ is provable by simp.
    simp

  -- Calculate the second part of the target sum: ∑ k in Finset.range 49, (2 * ↑k + 2 : ℚ)
  -- This is ∑ k in {0, ..., 48}, (2*k + 2) as rational numbers.
  have target_sum_2k_plus_2 : ∑ k in Finset.range 49, (2 * ↑k + 2 : ℚ) = 2450 := by
    -- Split the sum ∑ (2*↑k + 2) = ∑ 2*↑k + ∑ 2 using sum_add_distrib.
    -- Then factor out the constant 2 from the first sum using mul_sum.
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    -- The expression is now (2 : ℚ) * ∑ k ∈ Finset.range 49, (↑k : ℚ) + ∑ k ∈ Finset.range 49, (2 : ℚ).
    -- Calculate the sum of ↑k over range 49: ∑ k in range 49, ↑k = ↑(∑ k in range 49, k)
    conv =>
      lhs -- Target the left-hand side of the equality
      arg 1 -- Target the first term: (2 : ℚ) * ∑ k ∈ Finset.range 49, (↑k : ℚ)
      arg 2 -- Target the sum: ∑ k ∈ Finset.range 49, (↑k : ℚ)
      -- Apply the rewrite rule `↑(∑ k ∈ s, f x) = ∑ k ∈ s, ↑(f x)` backwards with f = fun k => k
      rw [← Nat.cast_sum (Finset.range 49) (fun k => k)]
    -- The inner sum ∑ k in range 49, k is the sum of the first 49 natural numbers (0 to 48).
    -- Use the formula for the sum of the first n-1 natural numbers: ∑ i in range n, i = n * (n-1) / 2
    rw [Finset.sum_range_id] -- Applies to the inner sum ∑ k ∈ Finset.range 49, k
    -- The expression is now (2 : ℚ) * (↑(49 * (49 - 1) / 2) : ℚ) + ∑ k ∈ Finset.range 49, (2 : ℚ).
    -- Calculate the second sum: ∑ k in range 49, 2 = 49 * 2
    -- The previous line `rw [Finset.sum_const, Finset.card_range]` was redundant because norm_num can evaluate the constant sum directly.
    -- -- Removed redundant rewrite rule applications as norm_num can evaluate the constant sum directly.
    -- rw [Finset.sum_const, Finset.card_range]
    -- Evaluate the numerical expression. This includes (2 : ℚ) * ↑(49 * 48 / 2) and ∑ k ∈ range 49, (2 : ℚ).
    norm_num

  -- Substitute the calculated sums target_sum_u0 and target_sum_2k_plus_2 into the equation target_sum_split.
  -- (49 * u 0) + 2450 = ∑ k in Finset.range 49, u (2 * k.succ)
  have final_sum_expr : (49 : ℚ) * u 0 + 2450 = ∑ k in Finset.range 49, u (2 * k.succ) := by
    have eq := target_sum_split
    rw [target_sum_u0] at eq
    rw [target_sum_2k_plus_2] at eq
    -- The derived equation `eq` is ∑ k... = (49 * u0) + 2450.
    -- The goal is (49 * u0) + 2450 = ∑ k....
    -- We need to use the symmetric version of `eq` to match the goal type.
    exact eq.symm -- Use .symm to flip the equality.


  -- We found earlier that 49 * u 0 = -2357. Substitute this value into the equation final_sum_expr.
  -- -2357 + 2450 = ∑ k in Finset.range 49, u (2 * k.succ)
  have final_calc : -2357 + 2450 = ∑ k in Finset.range 49, u (2 * k.succ) := by
    -- Replace (49 : ℚ) * u 0 with its calculated value (-2357 : ℚ) using the hypothesis 'forty_nine_u0'.
    rw [forty_nine_u0] at final_sum_expr
    exact final_sum_expr

  -- Calculate the final arithmetic expression -2357 + 2450.
  have final_result : (-2357 : ℚ) + (2450 : ℚ) = 93 := by
    -- Use norm_num to evaluate the addition.
    norm_num

  -- Substitute the final result (93) into the equation final_calc.
  -- 93 = ∑ k in Finset.range 49, u (2 * k.succ)
  rw [final_result] at final_calc
  -- The goal is ∑ k in Finset.range 49, u (2 * k.succ) = 93.
  -- The equation `final_calc` is 93 = Target Sum. Flip the equality to match the goal using symm.
  exact final_calc.symm


#print axioms aime_1984_p1