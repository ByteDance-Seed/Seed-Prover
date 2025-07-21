import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_amgm_sum1toneqn_prod1tonleq1
  (a : ℕ → NNReal)
  (n : ℕ)
  (h₀ : ∑ x in Finset.range n, a x = n) :
  ∏ x in Finset.range n, a x ≤ 1 := by 

  -- The proof proceeds by considering the case n = 0 and n > 0.
  -- For n > 0, we apply the AM-GM inequality for non-negative real numbers (NNReal).
  by_cases hn_zero : n = 0
  . -- Case 1: n = 0
    -- The hypothesis hn_zero : n = 0 is automatically introduced by by_cases.
    -- The tactic 'intro hn' is not needed here because 'by_cases' already introduces the hypothesis for this case.
    simp [hn_zero] -- Simplify the goal and hypothesis using n = 0
    -- Goal: ∏ x in Finset.range 0, a x ≤ 1
    -- Finset.range 0 is the empty set.
    -- The product over the empty set is 1.
    -- So the goal becomes 1 ≤ 1.
    -- The message "no goals to be solved" indicated the 'rfl' tactic was redundant and should be removed.
    -- The goal is already solved by `simp [hn_zero]`.
    -- -- Removed the redundant 'rfl' tactic as the goal was already solved by `simp [hn_zero]`.
  . -- Case 2: n ≠ 0
    -- The hypothesis for this case is ¬(n = 0), which is equivalent to n > 0 for natural numbers.
    have pos_n : 0 < n := Nat.pos_iff_ne_zero.mpr hn_zero

    -- -- The error "unknown constant 'NNReal.geom_mean_le_arith_mean'" indicates that the direct theorem for unweighted AM-GM
    -- -- for NNReal might not be available under this exact name or setup in the current Mathlib version or environment.
    -- -- We will use the weighted AM-GM inequality (NNReal.geom_mean_le_arith_mean_weighted) as a workaround.
    -- -- The unweighted version is a special case of the weighted version where all weights are equal to 1/n.

    -- Define the weight for each element in Finset.range n as 1/n.
    -- Since we are in the case n ≠ 0, (n : NNReal) is non-zero and its inverse exists, which corresponds to 1/n.
    let w := fun _ : ℕ => (n : NNReal)⁻¹

    -- Prove (n : NNReal) ≠ 0 and (n : ℝ) ≠ 0 since n ≠ 0. These will be needed later.
    have n_nnreal_ne_zero : (n : NNReal) ≠ 0 := by norm_cast
    have n_real_ne_zero : (n : ℝ) ≠ 0 := by exact_mod_cast hn_zero

    -- We need to show that the sum of weights over Finset.range n is equal to 1, as required by the weighted AM-GM theorem.
    -- ∑ i ∈ Finset.range n, w i = ∑ i ∈ Finset.range n, (n : NNReal)⁻¹
    have sum_weights_eq_one : ∑ i in Finset.range n, w i = 1 := by
      -- Step 1: Simplify the sum using `Finset.sum_const` and `Finset.card_range`.
      have h_sum_simplified : ∑ i in Finset.range n, w i = n • (n : NNReal)⁻¹ := by
        rw [Finset.sum_const, Finset.card_range n]
      -- Step 2: Prove that the simplified expression n • (↑n : NNReal)⁻¹ equals 1 in NNReal.
      have h_nnreal_eq_one : n • (↑n : NNReal)⁻¹ = 1 := by
        -- We prove the equality by lifting it to ℝ using the injectivity of NNReal.toReal.
        -- The theorem for injectivity is NNReal.coe_inj : (↑r : ℝ) = (↑s : ℝ) ↔ r = s.
        -- We need to rewrite the equality r=s into the equivalent equality (↑r : ℝ) = (↑s : ℝ).
        -- This is the reverse implication of the iff, so we use `rw [← NNReal.coe_inj]`.
        rw [← NNReal.coe_inj]
        -- Simplify the LHS in ℝ: NNReal.toReal (n • (↑n : NNReal)⁻¹)
        -- The unknown constant 'NNReal.toReal_one' should be 'NNReal.coe_one'.
        -- We also need to add `NNReal.coe_mul` and `NNReal.coe_inv` to the simp list
        -- to fully simplify the LHS `NNReal.toReal (n • (↑n : NNReal)⁻¹)` to `(↑n : ℝ) * ((↑n : ℝ))⁻¹`.
        simp only [NNReal.coe_nat_cast n, NNReal.coe_one, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_inv]
        -- Goal is now: (↑n : ℝ) * ((↑n : ℝ))⁻¹ = 1
        -- The error indicates the arguments to mul_inv_cancel were in the wrong order.
        -- mul_inv_cancel expects the proof `a ≠ 0` as the first explicit argument.
        exact mul_inv_cancel n_real_ne_zero -- Use the field property a * a⁻¹ = 1 for a ≠ 0.

      -- Step 3: Combine the simplified sum expression and the equality h_nnreal_eq_one.
      rw [h_sum_simplified] -- Rewrite the original sum as n • (n : NNReal)⁻¹.
      exact h_nnreal_eq_one -- The goal is now n • (n : NNReal)⁻¹ = 1, which is exactly h_nnreal_eq_one.

    -- Apply the weighted AM-GM inequality: NNReal.geom_mean_le_arith_mean_weighted
    -- This theorem states: ∏ i ∈ s, z i ^ NNReal.toReal (w i) ≤ ∑ i ∈ s, w i * z i, given ∑ i ∈ s, w i = 1 and z i ≥ 0 (which is true for NNReal).
    -- We use s = Finset.range n, w i = (n : NNReal)⁻¹, and z i = a i.
    -- Let's name this inequality.
    have am_gm_weighted_ineq : ∏ i in Finset.range n, a i ^ NNReal.toReal (w i) ≤ ∑ i in Finset.range n, w i * a i := NNReal.geom_mean_le_arith_mean_weighted (Finset.range n) w a sum_weights_eq_one

    -- The inequality obtained from weighted AM-GM is: ∏ i ∈ Finset.range n, a i ^ NNReal.toReal (w i) ≤ ∑ i ∈ Finset.range n, w i * a i

    -- Now, we simplify both sides of this inequality.
    -- First, simplify the left hand side (LHS): ∏ i ∈ Finset.range n, a i ^ NNReal.toReal (w i)
    -- We need to show that NNReal.toReal (w i) as a real number is equal to (1/n : ℝ).
    have wi_eq_one_div_n : ∀ i ∈ Finset.range n, NNReal.toReal (w i) = (1 : ℝ) / (↑(n) : ℝ) := by
      intros i hi
      -- Goal: NNReal.toReal (w i) = (1 : ℝ) / (↑(n) : ℝ)
      -- w i is defined as (n : NNReal)⁻¹. We need to show NNReal.toReal ((n : NNReal)⁻¹) = (1 / n : ℝ).
      change NNReal.toReal ((n : NNReal)⁻¹) = (1 : ℝ) / (↑n : ℝ)

      -- Step 1: Substitute w i = (n : NNReal)⁻¹ (already done by `change`).
      -- Step 2: Use NNReal.coe_inv to move toReal inside the inverse: NNReal.toReal (r⁻¹) = (NNReal.toReal r)⁻¹ for r ≠ 0.
      -- The theorem `NNReal.coe_inv r` states `↑r⁻¹ = (↑r)⁻¹` for r : NNReal. The coercion `↑` from NNReal to Real is `NNReal.toReal`.
      -- Thus, `NNReal.coe_inv r` proves `NNReal.toReal r⁻¹ = (NNReal.toReal r)⁻¹`.
      -- We apply `NNReal.coe_inv` to `(n : NNReal)`.
      have h_coe_inv : NNReal.toReal ((n : NNReal)⁻¹) = (NNReal.toReal (n : NNReal))⁻¹ := NNReal.coe_inv (n : NNReal) -- Corrected application of NNReal.coe_inv.
      -- Step 3: Use NNReal.coe_nat_cast to rewrite NNReal.toReal (n : NNReal) to (↑n : ℝ).
      -- The theorem `NNReal.coe_nat_eq` does not exist. The correct theorem is `NNReal.coe_nat_cast`.
      have h_coe_nat_eq : NNReal.toReal (n : NNReal) = (n : ℝ) := NNReal.coe_nat_cast n
      -- Step 4: Rewrite the base of the inverse using h_coe_nat_eq.
      have h_rewrite_inv_base : (NNReal.toReal (n : NNReal))⁻¹ = ((↑n : ℝ))⁻¹ := by rw [h_coe_nat_eq]
      -- Step 5: Use inv_eq_one_div to rewrite the inverse: x⁻¹ = 1 / x.
      -- The theorem `inv_eq_one_div` takes the element `x` as the argument, not the non-zero proof.
      have h_inv_eq_one_div : ((↑n : ℝ))⁻¹ = (1 : ℝ) / (↑n : ℝ) := inv_eq_one_div ((↑n : ℝ))
      -- Step 6: Chain the equalities to prove the goal.
      exact Eq.trans h_coe_inv (Eq.trans h_rewrite_inv_base h_inv_eq_one_div) -- Chain the steps from the second equality. The first equality was handled by `change`.


    -- Rewrite the exponent in the product on the LHS using the equality we just proved.
    -- The product becomes ∏ i ∈ Finset.range n, a i ^ (1 / n : ℝ).
    -- We can use the theorem NNReal.rpow_prod (in reverse) to move the exponent outside the product.
    -- theorem NNReal.rpow_prod {ι : Type u_1} {s : Finset ι} {f : ι → ℝ≥0} {r : ℝ} : (∏ x in s, f x) ^ r = ∏ x ∈ s, (f x) ^ r
    have h_rewrite_exponent : ∏ i in Finset.range n, a i ^ NNReal.toReal (w i) = ∏ i in Finset.range n, a i ^ (1 / n : ℝ) := by
      -- Use `Finset.prod_congr` to apply an equality element-wise inside the product.
      apply Finset.prod_congr
      . -- Prove the finset equality: Finset.range n = Finset.range n
        rfl
      . -- Prove the function equality on the finset elements: ∀ i ∈ Finset.range n, a i ^ NNReal.toReal (w i) = a i ^ (1 / ↑n : ℝ)
        intros i hi
        -- Goal: a i ^ NNReal.toReal (w i) = a i ^ (1 / n : ℝ)
        -- We know NNReal.toReal (w i) = (1 / n : ℝ) by `wi_eq_one_div_n i hi`.
        -- Use `congr_arg` to apply the function `a i ^ ·` to both sides of the exponent equality.
        apply congr_arg (a i ^ ·) -- Apply the function `a i ^ ·` to both sides of the exponent equality.
        exact wi_eq_one_div_n i hi -- The equality of the exponents is given by `wi_eq_one_div_n i hi`.


    -- Apply the theorem `NNReal.finset_prod_rpow` in the reverse direction.
    -- It allows us to write ∏ (f x) ^ r as (∏ f x) ^ r.
    -- The theorem `NNReal.finset_prod_rpow s f r` states `∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r`.
    -- The goal for `h_apply_rpow_prod_symm` is the symmetric version `∏ i ∈ Finset.range n, a i ^ (1 / n : ℝ) = (∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ)`.
    -- This matches the theorem statement exactly.
    have h_apply_rpow_prod_symm : ∏ i in Finset.range n, a i ^ (1 / n : ℝ) = (∏ i in Finset.range n, a i) ^ (1 / n : ℝ) := by
      -- The bases `a i` are NNReal, so they are non-negative as required by NNReal.finset_prod_rpow.
      -- Use the theorem `NNReal.finset_prod_rpow`.
      -- The goal is `∏ (f i)^r = (∏ f i)^r`. The theorem is `∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r`.
      -- This matches exactly. No `.symm` is needed.
      exact NNReal.finset_prod_rpow (Finset.range n) a (1/n : ℝ) -- Use the theorem directly. Remove `.symm`.

    -- Combine the equality steps using transitivity (Eq.trans).
    have lhs_eq_pooled_rpow : (∏ i in Finset.range n, a i ^ NNReal.toReal (w i)) = (∏ i in Finset.range n, a i) ^ (1 / n : ℝ) := by
      exact Eq.trans h_rewrite_exponent h_apply_rpow_prod_symm

    -- Apply the simplification of the LHS to the weighted AM-GM inequality.
    -- am_gm_weighted_ineq is (∏ i ∈ Finset.range n, a i ^ NNReal.toReal (w i)) ≤ ∑ i ∈ Finset.range n, w i * a i
    -- Rewrite the LHS using lhs_eq_pooled_rpow
    rw [lhs_eq_pooled_rpow] at am_gm_weighted_ineq

    -- Next, simplify the right hand side (RHS): ∑ i ∈ Finset.range n, w i * a i
    -- ∑ i ∈ Finset.range n, (n : NNReal)⁻¹ * a i
    -- We can factor out the constant (n : NNReal)⁻¹ from the sum.
    -- Use Finset.mul_sum: c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i.
    -- Then use the hypothesis h₀: ∑ i ∈ Finset.range n, a i = n.
    have rhs_eq_one : ∑ i in Finset.range n, w i * a i = 1 := by
      -- Step 1: Substitute the definition of w i into the sum.
      have h_subst_wi : ∑ i in Finset.range n, w i * a i = ∑ i in Finset.range n, (n : NNReal)⁻¹ * a i := by rfl

      -- Step 2: Factor out the constant (n : NNReal)⁻¹ from the sum.
      -- The theorem for factoring a constant from a sum is `Finset.mul_sum`.
      -- `Finset.mul_sum` states `c * ∑ i ∈ s, f i = ∑ i ∈ s, c * f i`.
      -- We need the equality in the reverse direction to move the constant `(n : NNReal)⁻¹` outside the sum on the left.
      -- So we apply `Finset.mul_sum.symm`.
      have h_factor_const : ∑ i in Finset.range n, (n : NNReal)⁻¹ * a i = (n : NNReal)⁻¹ * ∑ i in Finset.range n, a i := by
        exact (Finset.mul_sum (Finset.range n) a ((n : NNReal)⁻¹)).symm

      -- Step 3: Use the hypothesis h₀ which states ∑ i ∈ Finset.range n, a i = n.
      -- The hypothesis h₀ is ∑ x ∈ Finset.range n, a x = (n : ℕ). We need to cast n to NNReal.
      -- Cast the equality h₀ to NNReal.
      have h_sum_eq_nnreal_n : ∑ i ∈ Finset.range n, a i = (n : NNReal) := by exact_mod_cast h₀
      have h_use_h0 : (n : NNReal)⁻¹ * ∑ i in Finset.range n, a i = (n : NNReal)⁻¹ * (n : NNReal) := by
        rw [h_sum_eq_nnreal_n] -- Rewrite the sum using the casted hypothesis.
      -- Step 4: Simplify the multiplication (n : NNReal)⁻¹ * (n : NNReal).
      -- This product is 1 because (n : NNReal) is non-zero.
      -- We already have the non-zero proof for (n : NNReal).
      have h_simplify_mul : (n : NNReal)⁻¹ * (n : NNReal) = 1 := inv_mul_cancel n_nnreal_ne_zero -- Use the existing n_nnreal_ne_zero.

      -- Combine the equality steps using transitivity.
      exact Eq.trans h_subst_wi (Eq.trans h_factor_const (Eq.trans h_use_h0 h_simplify_mul))

    -- Apply the simplification of the RHS to the weighted AM-GM inequality.
    -- am_gm_weighted_ineq is now (∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ) ≤ ∑ i ∈ Finset.range n, w i * a i
    -- Rewrite the RHS using rhs_eq_one
    rw [rhs_eq_one] at am_gm_weighted_ineq

    -- The inequality now simplifies to:
    -- (∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ) ≤ 1
    -- This is the standard form of the unweighted AM-GM inequality.

    -- The final step is to show that if P^(1/n) ≤ 1 for P : NNReal and 1/n > 0, then P ≤ 1.
    -- Let P = ∏ i ∈ Finset.range n, a i. The inequality is P ^ (1 / n : ℝ) ≤ 1.
    -- Since n > 0, (n : ℝ) > 0. Raising both sides to the power (n : ℝ) preserves the inequality for non-negative bases.
    -- We need a proof that (n : ℝ) ≥ 0. We already have `pos_n : 0 < n`, which implies `(n : ℝ) > 0`, hence `(n : ℝ) ≥ 0`.
    have n_real_ge_zero : (n : ℝ) ≥ 0 := by exact_mod_cast pos_n.le

    -- Apply the theorem `NNReal.rpow_le_rpow`.
    -- This theorem states: x ≤ y → 0 ≤ z → x^z ≤ y^z for x y : NNReal, z : ℝ, z ≥ 0.
    -- We apply it to `am_gm_weighted_ineq : (∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ) ≤ 1`
    -- with x = (∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ), y = 1, and z = (n : ℝ).
    -- The base x is NNReal (rpow of NNReal is NNReal). The base y=1 is NNReal. The exponent z=(n:ℝ) is Real and ≥ 0.
    -- The hypothesis hxy is `am_gm_weighted_ineq`. The hypothesis hz is `n_real_ge_zero`.
    have final_inequality := NNReal.rpow_le_rpow am_gm_weighted_ineq n_real_ge_zero

    -- Simplify the LHS of the resulting inequality: ((∏ i ∈ Finset.range n, a i) ^ (1 / n : ℝ)) ^ (n : ℝ).
    have lhs_simplified : ((∏ i in Finset.range n, a i) ^ (1 / n : ℝ)) ^ (n : ℝ) = ∏ i in Finset.range n, a i := by
      -- Use `NNReal.rpow_mul`: (x^a)^b = x^(a*b) for x : NNReal, a b : ℝ.
      rw [(NNReal.rpow_mul (∏ i in Finset.range n, a i) (1/n : ℝ) (n : ℝ)).symm] -- Use the symmetric form of NNReal.rpow_mul.
      -- Need to show (1/n : ℝ) * (n : ℝ) = 1.
      -- We know (n : ℝ) ≠ 0 since n > 0. We already have `n_real_ne_zero`.
      have one_div_n_mul_n_eq_one : (1 / n : ℝ) * (n : ℝ) = 1 := by
        field_simp [n_real_ne_zero]
      -- Apply this equality in the exponent.
      rw [one_div_n_mul_n_eq_one]
      -- Need to simplify x^1 = x for x : NNReal.
      rw [NNReal.rpow_one]

    -- Simplify the RHS of the resulting inequality: 1 ^ (n : ℝ).
    have rhs_simplified : (1 : NNReal) ^ (n : ℝ) = 1 := by
      -- Use `NNReal.one_rpow`: 1^r = 1 for 1 : NNReal, r : ℝ.
      exact NNReal.one_rpow (n : ℝ)

    -- Rewrite the `final_inequality` using the simplified LHS and RHS.
    -- final_inequality is of the form LHS_complicated ≤ RHS_complicated.
    rw [lhs_simplified] at final_inequality
    rw [rhs_simplified] at final_inequality

    -- The inequality `final_inequality` is now exactly the goal `∏ i ∈ Finset.range n, a i ≤ 1`.
    exact final_inequality

#print axioms algebra_amgm_sum1toneqn_prod1tonleq1