import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem induction_prod1p1onk3le3m1onn
  (n : ℕ)
  (h₀ : 0 < n) :
  (∏ k in Finset.Icc 1 n, (1 + (1:ℝ) / k^3)) ≤ (3:ℝ) - 1 / ↑n := by

  -- We prove the theorem by induction on n.
  -- Let P(n) be the proposition: 0 < n → ∏ k in Finset.Icc 1 n, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n
  -- We prove P(n) for all n : ℕ by induction on n.
  -- The base case is n = 0 (proving P(0)). The inductive step assumes P(n_ind) and proves P(succ n_ind).
  -- Note: The induction is over n, but the hypothesis h₀ : 0 < n means the theorem only applies for n ≥ 1.
  -- The standard `induction n` tactic will start at n=0. The P(0) case is `0 < 0 → ...` which is trivially true.
  -- This is fine, but the base case for the *statement* is n=1, which corresponds to the n_ind=0 case in the `succ n_ind` step.
  induction n with -- Use standard induction on n.
  | zero =>
    -- Goal: P(0) which is 0 < 0 → ∏ k in Finset.Icc 1 0, ... ≤ (3:ℝ) - 1 / ↑0
    -- h₀ : 0 < 0 is in the context. This is false, so the implication is true.
    contradiction
  | succ n_ind ih => -- Rename induction variable to n_ind. n is succ n_ind. ih is P(n_ind).
    -- Goal: P(succ n_ind) which is 0 < succ n_ind → ∏ k in Finset.Icc 1 (succ n_ind), ... ≤ (3:ℝ) - 1 / ↑(succ n_ind)
    -- Inductive hypothesis ih : P(n_ind) which is 0 < n_ind → ∏ k in Finset.Icc 1 n_ind, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n_ind

    -- The hypothesis 0 < succ n_ind (which is h₀) is always true for n_ind : ℕ.
    -- The `induction` tactic already introduced this hypothesis and named it `h₀`.

    -- We handle the case n = succ n_ind by considering whether n_ind is 0 or not.
    by_cases h_n_ind_zero : n_ind = 0

    . -- Case 1: n_ind = 0. This means n = succ 0 = 1.
      -- Goal (under h₀ : 0 < 1): ∏ k in Finset.Icc 1 1, ... ≤ (3:ℝ) - 1 / ↑1
      -- We don't need ih in this case as it's the base case for the original theorem (n=1).
      -- h₀ is 0 < 1, which is true.
      -- The by_cases h_n_ind_zero : n_ind = 0 substitutes n_ind = 0 in the context.
      -- The goal is now effectively ∏ k in Finset.Icc 1 1, ... ≤ 3 - 1 / ↑1.
      simp [h_n_ind_zero]
      norm_num -- simplifies to 2 ≤ 2, which is true.

    . -- Case 2: n_ind ≠ 0. Since n_ind : ℕ, this implies n_ind > 0.
      -- This is the inductive step for n > 1. The current n is `succ n_ind`, where `n_ind > 0`.
      -- We are proving the goal ∏ k in Finset.Icc 1 (succ n_ind), ... ≤ (3:ℝ) - 1 / ↑(succ n_ind) under the premise 0 < succ n_ind (which is h₀).
      -- We can apply the inductive hypothesis `ih` which is for `n_ind`.
      -- `ih` is `0 < n_ind → ∏ ...`. We have `n_ind ≠ 0`, which implies `n_ind > 0`.
      -- Prove that 0 < n_ind (required by the IH).
      have h_n_ind_pos : 0 < n_ind := Nat.pos_of_ne_zero h_n_ind_zero
      -- Add the hypothesis 1 ≤ n_ind, which is needed for Finset.Icc_insert_succ.
      -- This is no longer strictly needed for Finset.prod_Icc_succ_top but doesn't hurt.
      have h_one_le_n_ind : 1 ≤ n_ind := Nat.one_le_of_lt h_n_ind_pos

      -- Apply the inductive hypothesis `ih` for `n_ind` using the proof `h_n_ind_pos`.
      have ih_applied : ∏ k in Finset.Icc 1 n_ind, (1 + (1:ℝ) / k^3) ≤ (3:ℝ) - 1 / ↑n_ind := ih h_n_ind_pos

      -- The left side of the goal for n = succ n_ind is ∏ k in Finset.Icc 1 (succ n_ind), (1 + (1:ℝ) / k^3)
      -- Split the product by extracting the last term succ n_ind.
      -- We use the theorem Finset.prod_Icc_succ_top.
      -- The theorem `Finset.prod_Icc_succ_top a b f` splits `∏ k ∈ Icc a (b+1), f k` into `(∏ k ∈ Icc a b, f k) * f (b+1)`.
      -- In our case, a=1, b=n_ind, f = fun k => 1 + 1/k^3. The condition a ≤ b+1 is 1 ≤ n_ind + 1, which is true by simp.
      rw [Finset.prod_Icc_succ_top (a := 1) (b := n_ind) (M := ℝ) (f := fun k : ℕ => 1 + (1:ℝ) / k^3) (by simp)]

      -- Now the goal is: (∏ k in Finset.Icc 1 n_ind, (1 + 1 / k ^ 3)) * (1 + 1 / ↑(succ n_ind) ^ 3) ≤ 3 - 1 / ↑(succ n_ind)

      -- Prove that the added factor is non-negative.
      have factor_nonneg : 1 + (1:ℝ) / (↑(succ n_ind))^3 ≥ 0 := by
        have h_succ_n_ind_pos : (↑(succ n_ind) : ℝ) > 0 := Nat.cast_pos.mpr (Nat.succ_pos n_ind)
        -- Prove (↑(succ n_ind))^3 > 0 using pow_pos
        have h_succ_n_ind_cubed_pos_real : (↑(succ n_ind) : ℝ) ^ 3 > 0 := by apply pow_pos h_succ_n_ind_pos 3
        -- Prove (1:ℝ) / (↑(succ n_ind))^3 > 0.
        have one_over_succ_n_ind_cubed_pos : (1:ℝ) / (↑(succ n_ind))^3 > 0 := by
          rw [gt_iff_lt]
          apply one_div_pos.mpr h_succ_n_ind_cubed_pos_real
        -- Use linarith with the proved positivity of the fraction and the fact that 1 > 0.
        -- The previous linarith call had a typeclass issue with `zero_lt_one`.
        -- We can prove the sum is non-negative by proving each term is non-negative and using `add_nonneg`.
        -- 1 is non-negative.
        have h_one_nonneg : (1:ℝ) ≥ 0 := zero_le_one
        -- The fraction is strictly positive, hence non-negative.
        have h_fraction_nonneg : (1:ℝ) / (↑(succ n_ind))^3 ≥ 0 := le_of_lt one_over_succ_n_ind_cubed_pos
        -- The sum of two non-negative numbers is non-negative.
        exact add_nonneg h_one_nonneg h_fraction_nonneg

      -- Apply the IH (`ih_applied`) and the non-negativity of the second factor (`factor_nonneg`).
      -- This step uses mul_le_mul_of_nonneg_right which requires the right multiplier to be non-negative.
      have step_le : Finset.prod (Finset.Icc 1 n_ind) (fun k : ℕ => 1 + (1:ℝ) / k^3) * (1 + (1:ℝ) / (↑(succ n_ind))^3) ≤ ((3:ℝ) - 1 / ↑n_ind) * (1 + (1:ℝ) / (↑(succ n_ind))^3) := by
        apply mul_le_mul_of_nonneg_right ih_applied factor_nonneg

      -- So it suffices to prove: ((3:ℝ) - 1 / ↑n_ind) * (1 + (1:ℝ) / (↑(succ n_ind))^3) ≤ (3:ℝ) - 1 / ↑(succ n_ind)
      have intermediate_bound_le_rhs : ((3:ℝ) - 1 / ↑n_ind) * (1 + (1:ℝ) / (↑(succ n_ind))^3) ≤ (3:ℝ) - 1 / ↑(succ n_ind) := by
        -- Simplify the expression using field_simp. This brings fractional terms to common denominators.
        field_simp

        -- Introduce aliases for the terms after field_simp to help unification with div_le_div_iff.
        -- NumLHS / DenomLHS corresponds to the LHS after field_simp
        let NumLHS := ((3 : ℝ) * (↑(n_ind) : ℝ) - (1 : ℝ)) * (((↑(n_ind) : ℝ) + (1 : ℝ)) ^ (3 : ℕ) + (1 : ℝ))
        let DenomLHS := ((↑(n_ind) : ℝ) * ((↑(n_ind) : ℝ) + (1 : ℝ)) ^ (3 : ℕ))
        -- NumRHS / DenomRHS corresponds to the RHS after field_simp
        let NumRHS := ((3 : ℝ) * ((↑(n_ind) : ℝ) + (1 : ℝ)) - (1 : ℝ))
        let DenomRHS := ((↑(n_ind) : ℝ) + (1 : ℝ))

        -- Prove DenomLHS > 0 and DenomRHS > 0, needed for div_le_div_iff.
        have h_cast_n_ind_pos : (↑n_ind : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_n_ind_zero)
        have h_cast_succ_n_ind_pos : (↑(succ n_ind) : ℝ) > (0 : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n_ind)

        have h_denom_pos' : (0 : ℝ) < DenomLHS := by
          -- DenomLHS = (↑n_ind : ℝ) * ((↑(n_ind) : ℝ) + (1 : ℝ)) ^ (3 : ℕ)
          -- Need 0 < (↑n_ind : ℝ) and 0 < ((↑(n_ind) : ℝ) + (1 : ℝ)) ^ (3 : ℕ).
          have h_term1_pos : (↑n_ind : ℝ) > 0 := h_cast_n_ind_pos
          have h_term2_base_pos : (↑(n_ind) : ℝ) + (1 : ℝ) > 0 := by
            rw [← @Nat.cast_succ ℝ _ n_ind]
            exact h_cast_succ_n_ind_pos
          have h_term2_pos : ((↑(n_ind) : ℝ) + (1 : ℝ)) ^ (3 : ℕ) > 0 := by apply pow_pos h_term2_base_pos 3
          apply mul_pos h_term1_pos h_term2_pos

        have h_denom2_pos : (0 : ℝ) < DenomRHS := by
          -- DenomRHS is defined as (↑(n_ind) : ℝ) + (1 : ℝ).
          -- Goal: (0 : ℝ) < (↑(n_ind) : ℝ) + (1 : ℝ)
          dsimp [DenomRHS]
          -- We know (↑(n_ind) : ℝ) + (1 : ℝ) = (↑(succ n_ind) : ℝ) by Nat.cast_succ.
          -- Use Nat.cast_succ to rewrite the RHS: (↑n_ind : ℝ) + (1 : ℝ) -> (↑(succ n_ind) : ℝ)
          -- -- The previous rewrite direction `rw [Nat.cast_succ n_ind]` failed because the pattern `↑(succ n_ind)` was not found in the goal term `(↑n_ind : ℝ) + (1 : ℝ)`.
          -- -- We need to rewrite the term `(↑n_ind : ℝ) + (1 : ℝ)` into `(↑(succ n_ind) : ℝ)`.
          -- -- The theorem `Nat.cast_succ n_ind` states `(↑(succ n_ind) : ℝ) = (↑(n_ind) : ℝ) + (1 : ℝ)`.
          -- -- To rewrite the right side of this equality, we need to use the reverse direction `←`.
          rw [← Nat.cast_succ n_ind]
          -- Goal is now (0 : ℝ) < (↑(succ n_ind) : ℝ).
          -- We already have h_cast_succ_n_ind_pos : (↑(succ n_ind) : ℝ) > (0 : ℝ).
          -- Use gt_iff_lt to convert it to (0 : ℝ) < (↑(succ n_ind) : ℝ).
          have h_lt_succ_n_ind_cast : (0 : ℝ) < (↑(succ n_ind) : ℝ) := gt_iff_lt.mp h_cast_succ_n_ind_pos
          -- The goal now exactly matches h_lt_succ_n_ind_cast.
          exact h_lt_succ_n_ind_cast

        -- Apply the equivalence div_le_div_iff using the proved positivity conditions.
        -- This transforms the goal NumLHS / DenomLHS ≤ NumRHS / DenomRHS into NumLHS * DenomRHS ≤ NumRHS * DenomLHS.
        apply (div_le_div_iff h_denom_pos' h_denom2_pos).mpr

        -- Goal is now NumLHS * DenomRHS ≤ NumRHS * DenomLHS.
        -- Rearrange the inequality to 0 ≤ NumRHS * DenomLHS - NumLHS * DenomRHS.
        rw [← sub_nonneg]

        -- Goal is 0 ≤ NumRHS * DenomLHS - NumLHS * DenomLHS.
        -- Let y = (↑n_ind : ℝ).
        let y := (↑(n_ind) : ℝ)

        -- Unfold the aliases in the goal to get the explicit polynomial expression in terms of y.
        -- The target expression after unfolding is: ((3 * (y + 1) - 1) * (y * (y + 1)^3)) - ((3 * y - 1) * ((y + 1)^3 + 1)) * (y + 1)
        dsimp [NumRHS, DenomLHS, NumLHS, DenomRHS]

        -- Prove the equality between the explicit polynomial expression and the target polynomial y^3 + y + 2.
        -- The previous `h_equality` had the form `((3 * y + 2) * (y * (y + 1)^3)) - ...`
        -- After `dsimp`, the goal contains `((3 * (y + 1) - 1) * (y * (y + 1)^3)) - ...`
        -- Since `3 * (y + 1) - 1 = 3y + 3 - 1 = 3y + 2`, these expressions are equal, but not syntactically identical.
        -- We define the equality with the exact expression present in the goal after `dsimp`.
        have h_equality_target_poly : ((3 * (y + 1) - 1) * (y * (y + 1)^3)) - ((3 * y - 1) * ((y + 1)^3 + 1)) * (y + 1) = y ^ 3 + y + 2 := by
          -- Use the `ring` tactic to prove this polynomial equality.
          -- This simplifies the left side algebraically.
          ring

        -- Rewrite the goal using the proved equality `h_equality_target_poly`.
        -- This replaces the complex expression with y^3 + y + 2.
        rw [h_equality_target_poly]

        -- The goal is now `0 ≤ y ^ 3 + y + 2`.
        -- We need to prove this using the fact that `y = ↑n_ind` and `n_ind ≥ 1`.
        -- Prove that `1 ≤ y`. This is derived from `h_one_le_n_ind : 1 ≤ n_ind`.
        have h_one_le_y : 1 ≤ y := Nat.one_le_cast.mpr h_one_le_n_ind

        -- Now prove 0 ≤ y^3 + y + 2 from h_one_le_y : 1 ≤ y.
        -- Since y ≥ 1, y is non-negative. We can raise inequalities to powers.
        -- Prove 1 ≤ y^3 from 1 ≤ y.
        have h_one_le_y_cubed : 1 ≤ y ^ 3 := by
          -- Goal: 1 ≤ y^3. We know 1 ≤ y.
          -- We want to use the theorem `pow_le_pow_left` which states `a ≤ b → a^n ≤ b^n` if `0 ≤ a`.
          -- Here, a = 1, b = y, n = 3. We have 0 ≤ 1 and 1 ≤ y.
          -- The theorem proves 1^3 ≤ y^3.
          -- We need to rewrite the goal 1 ≤ y^3 to 1^3 ≤ y^3 for the `apply` tactic to work directly.
          -- Use rw with `one_pow` in reverse to rewrite 1 as 1^3.
          -- -- The previous `simp only [one_pow 3]` failed because it tried to simplify using 1^3 = 1,
          -- -- which does not change the target 1 ≤ y^3.
          -- -- We need to rewrite 1 as 1^3. The lemma is `one_pow 3 : 1^3 = 1`.
          -- -- To apply it in the reverse direction (1 -> 1^3), we use `rw [← one_pow 3]`.
          rw [← one_pow 3]
          -- Goal is now 1^3 ≤ y^3.
          -- Apply the theorem `pow_le_pow_left`.
          -- It requires `0 ≤ 1` (zero_le_one) and `1 ≤ y` (h_one_le_y).
          apply pow_le_pow_left zero_le_one h_one_le_y 3

        -- We have 1 ≤ y and 1 ≤ y^3.
        -- We want to show 0 ≤ y^3 + y + 2.
        -- We know y^3 ≥ 1, y ≥ 1, and 2 ≥ 2. Summing these inequalities gives y^3 + y + 2 ≥ 1 + 1 + 2 = 4.
        -- Since 4 ≥ 0, the goal follows by transitivity.
        -- We can prove this by showing that (y^3 - 1) + (y - 1) + 4 is non-negative.
        -- We need to show y^3 - 1 ≥ 0 and y - 1 ≥ 0.
        have h_y_minus_one_nonneg : y - 1 ≥ 0 := by
          -- Goal: y - 1 ≥ 0. Have h_one_le_y : 1 ≤ y.
          -- This is definitionally equivalent to y ≥ 1. Subtracting 1 from both sides gives the goal.
          rw [← sub_nonneg] at h_one_le_y -- This rewrites 1 ≤ y to y - 1 ≥ 0
          exact h_one_le_y

        have h_y_cubed_minus_one_nonneg : y ^ 3 - 1 ≥ 0 := by
          -- Goal: y^3 - 1 ≥ 0. Have h_one_le_y_cubed : 1 ≤ y^3.
          -- This is definitionally equivalent to y^3 ≥ 1. Subtracting 1 from both sides gives the goal.
          rw [← sub_nonneg] at h_one_le_y_cubed -- This rewrites 1 ≤ y^3 to y^3 - 1 ≥ 0
          exact h_one_le_y_cubed

        -- The expression y^3 + y + 2 is equal to (y^3 - 1) + (y - 1) + 4.
        -- We prove this equality using ring.
        have h_poly_identity : y ^ 3 + y + 2 = (y ^ 3 - 1) + (y - 1) + 4 := by ring

        -- Rewrite the goal using this identity.
        rw [h_poly_identity]

        -- The goal is now 0 ≤ (y^3 - 1) + (y - 1) + 4.
        -- We know (y^3 - 1) ≥ 0 and (y - 1) ≥ 0. Their sum is also ≥ 0.
        have h_sum_diffs_nonneg : (y ^ 3 - 1) + (y - 1) ≥ 0 := by
          apply add_nonneg h_y_cubed_minus_one_nonneg h_y_minus_one_nonneg

        -- We know 4 ≥ 0.
        -- The inequality needs to be over real numbers for add_nonneg to apply correctly.
        -- The previous version inferred the type as Nat, causing a type mismatch.
        have h_four_nonneg : (4 : ℝ) ≥ (0 : ℝ) := by norm_num

        -- The goal is the sum of two non-negative terms: (y^3 - 1 + y - 1) + 4.
        -- Apply add_nonneg.
        apply add_nonneg h_sum_diffs_nonneg h_four_nonneg


      -- Apply transitivity to complete the proof of the inductive step.
      -- Goal is (∏ ...) * (...) ≤ (3 - 1/↑(succ n_ind)).
      -- `step_le` gives (∏ ...) * (...) ≤ intermediate_bound.
      -- `intermediate_bound_le_rhs` gives intermediate_bound ≤ RHS.
      -- So, LHS ≤ intermediate_bound ≤ RHS.
      exact le_trans step_le intermediate_bound_le_rhs

#print axioms induction_prod1p1onk3le3m1onn
