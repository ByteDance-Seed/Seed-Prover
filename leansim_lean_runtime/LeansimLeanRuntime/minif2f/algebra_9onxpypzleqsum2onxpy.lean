import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
 
    -- Derive necessary positivity/non-negativity proofs from the hypothesis h₀
    have hx : 0 < x := h₀.1
    have hy : 0 < y := h₀.2.1
    have hz : 0 < z := h₀.2.2
    -- Use linarith to prove positivity of sums
    have hxy : 0 < x + y := by linarith [hx, hy]
    have hyz : 0 < y + z := by linarith [hy, hz]
    have hzx : 0 < z + x := by linarith [hz, hx]
    have hxyz : 0 < x + y + z := by linarith [hx, hy, hz]
    -- Derive non-negativity from positivity
    have hxy_nonneg : 0 ≤ x + y := le_of_lt hxy
    have hyz_nonneg : 0 ≤ y + z := le_of_lt hyz
    have hzx_nonneg : 0 ≤ z + x := le_of_lt hzx

    -- Define vectors u and v for applying the Cauchy-Schwarz inequality.
    -- The chosen vectors make the dot product sum and the sum of squares calculable
    -- in a way that leads to the desired inequality.
    -- We use `let` to define these vectors as local abbreviations.
    let u : Fin 3 → ℝ := ![1 / Real.sqrt (x + y), 1 / Real.sqrt (y + z), 1 / Real.sqrt (z + x)]
    let v : Fin 3 → ℝ := ![Real.sqrt (x + y), Real.sqrt (y + z), Real.sqrt (z + x)]

    -- Apply the Cauchy-Schwarz inequality to vectors u and v over Finset.univ (indices {0, 1, 2})
    -- The theorem sum_sq_le_sum_sq_mul_sum_sq states that (∑ i, u i * v i)² ≤ (∑ i, u i²) * (∑ i, v i²)
    have h_cauchy_schwarz : (∑ i : Fin 3, u i * v i) ^ 2 ≤ (∑ i : Fin 3, u i ^ 2) * (∑ i : Fin 3, v i ^ 2) := by
      -- The sum is over the finite set `Finset.univ` for `Fin 3`.
      -- The theorem `Finset.sum_mul_sq_le_sq_mul_sq` directly applies to two functions `u` and `v`
      -- from a finite set to a semi-inner-product space (ℝ is one).
      -- The theorem name 'sum_sq_le_sum_sq_mul_sum_sq' was incorrect. Replaced with the correct theorem name 'Finset.sum_mul_sq_le_sq_mul_sq'.
      -- The theorem `Finset.sum_mul_sq_le_sq_mul_sq` expects the finset as the first argument, followed by the two functions.
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v

    -- The sum is over Fin 3, which is {0, 1, 2}.
    -- Explicitly expand the sum ∑ i : Fin 3, u i * v i
    have h_sum_uv_expansion : (∑ i : Fin 3, u i * v i) = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := Fin.sum_univ_three (fun i => u i * v i)

    -- Calculate each term of the sum ∑ i : Fin 3, u i * v i
    have term0 : u 0 * v 0 = 1 := by
      -- Expand definitions of u and v at index 0 using dsimp.
      -- This makes the goal `(1 / Real.sqrt (x + y)) * Real.sqrt (x + y) = 1`.
      dsimp [u, v]
      -- Use commutativity to rearrange the multiplication to `Real.sqrt (x + y) * (1 / Real.sqrt (x + y)) = 1`.
      rw [mul_comm]
      -- To use field_simp for `a * (1/a) = 1`, we need to show `a ≠ 0`.
      -- Here `a` is `Real.sqrt (x + y)`. We need to show `Real.sqrt (x + y) ≠ 0`.
      -- The theorem `Real.sqrt_ne_zero` states `sqrt x ≠ 0 ↔ x ≠ 0` for `x ≥ 0`.
      -- We have `x + y > 0` (hxy), which implies `x + y ≠ 0` and `x + y ≥ 0` (hxy_nonneg).
      -- So, `Real.sqrt (x + y) ≠ 0` holds. We use `(Real.sqrt_ne_zero hxy_nonneg).mpr` to apply the reverse direction of the equivalence,
      -- which requires the proof `x + y ≠ 0`. `ne_of_gt hxy` provides this.
      have h_sqrt_xy_ne_zero : Real.sqrt (x + y) ≠ 0 := by
        apply (Real.sqrt_ne_zero hxy_nonneg).mpr
        exact ne_of_gt hxy
      -- Use field_simp which simplifies expressions involving division and multiplication in a field,
      -- using the non-zero proof for the denominator.
      field_simp [h_sqrt_xy_ne_zero]
    have term1 : u 1 * v 1 = 1 := by
      -- Expand definitions of u and v at index 1
      dsimp [u, v]
      -- Target: (1 : ℝ) / √(y + z) * √(y + z) = 1
      -- Use commutativity to get √(y + z) * (1 / √(y + z)) = 1
      rw [mul_comm]
      -- Need Real.sqrt (y+z) ≠ 0. This is true since y+z > 0.
      have h_sqrt_yz_ne_zero : Real.sqrt (y + z) ≠ 0 := by
        apply (Real.sqrt_ne_zero hyz_nonneg).mpr
        exact ne_of_gt hyz
      -- Use field_simp with the non-zero denominator proof
      field_simp [h_sqrt_yz_ne_zero]
    have term2 : u 2 * v 2 = 1 := by
      -- Expand definitions of u and v at index 2
      dsimp [u, v]
      -- Target: (1 : ℝ) / √(z + x) * √(z + x) = 1
      -- Use commutativity to get √(z + x) * (1 / √(z + x)) = 1
      have h_sqrt_zx_ne_zero : Real.sqrt (z + x) ≠ 0 := by
        apply (Real.sqrt_ne_zero hzx_nonneg).mpr
        exact ne_of_gt hzx
      -- Use field_simp which handles a * (1/a) = 1 when a ≠ 0
      field_simp [h_sqrt_zx_ne_zero]

    -- Calculate the value of the sum ∑ i : Fin 3, u i * v i
    have h_sum_uv_val : (∑ i : Fin 3, u i * v i) = 3 := by
      -- Use the explicit expansion of the sum proved earlier
      rw [h_sum_uv_expansion]
      -- Substitute the calculated term values (term0, term1, term2) into the expanded sum
      rw [term0, term1, term2]
      -- The goal is now `1 + 1 + 1 = 3`. `norm_num` solves this.
      norm_num

    -- Calculate the square of the sum ∑ i : Fin 3, u i * v i
    have h_sum_uv_sq : (∑ i : Fin 3, u i * v i) ^ 2 = 9 := by
      -- Use the calculated sum value `h_sum_uv_val`
      rw [h_sum_uv_val]
      -- The goal is now `3 ^ 2 = 9`. `norm_num` solves this.
      norm_num

    -- Calculate the sum ∑ i : Fin 3, u i ^ 2
    have h_sum_uu_sq : (∑ i : Fin 3, u i ^ 2) = 1 / (x + y) + 1 / (y + z) + (1 / (z + x)) := by
      -- Simplify the sum of squares of vector u components
      dsimp [u] -- Expand the definition of u within the sum
      rw [Fin.sum_univ_three] -- Expand the sum over Fin 3
      -- Goal is now ((![...]) 0)^2 + ((![...]) 1)^2 + ((![...]) 2)^2 = 1 / (x + y) + 1 / (y + z) + 1 / (z + x).
      -- The terms involve squares of reciprocals of square roots: (1/sqrt(D))^2.
      -- This simplifies to 1^2 / (sqrt(D))^2 = 1 / D, provided D >= 0.
      -- Use simp with the non-negativity proofs (hxy_nonneg, hyz_nonneg, hzx_nonneg) to apply lemmas like `div_pow`, `one_pow`, and `Real.sq_sqrt` (which is `sqrt(D)^2 = D` for D>=0).
      simp [hxy_nonneg, hyz_nonneg, hzx_nonneg]
      -- The goal is now 1 / (x + y) + 1 / (y + z) + 1 / (z + x) = 1 / (x + y) + 1 / (y + z) + 1 / (z + x).
      -- `simp` has successfully simplified the LHS to match the RHS, closing the goal.

    -- Calculate the sum ∑ i : Fin 3, v i ^ 2
    have h_sum_vv_sq : (∑ i : Fin 3, v i ^ 2) = 2 * (x + y + z) := by
      -- Apply definition of v using dsimp before expanding the sum.
      dsimp [v]
      -- Expand the sum over Fin 3
      rw [Fin.sum_univ_three]
      -- Goal is now (sqrt(x+y))^2 + (sqrt(y+z))^2 + (sqrt(z+x))^2 = 2 * (x+y+z).
      -- Use simp with the non-negativity proofs (hxy_nonneg, hyz_nonneg, hzx_nonneg)
      -- to apply `Real.sq_sqrt` (sqrt(D)^2 = D for D>=0) to each term.
      simp [hxy_nonneg, hyz_nonneg, hzx_nonneg]
      -- The goal is now (x + y) + (y + z) + (z + x) = 2 * (x + y + z).
      -- This is an algebraic identity. `ring` simplifies the LHS to `2*x + 2*y + 2*z` and matches the RHS.
      ring

    -- Substitute the calculated sums into the Cauchy-Schwarz inequality (h_cauchy_schwarz)
    -- h_cauchy_schwarz: (∑ uᵢvᵢ)² ≤ (∑ uᵢ²) * (∑ vᵢ²)
    -- Substitute values: 9 ≤ (1/(x+y) + ...) * (2*(x+y+z))
    -- The sum `(1/(x+y) + ...)` is `h_sum_uu_sq`'s RHS. By default parsing, this sum is grouped left-associatively: `((1/(x+y) + 1/(y+z)) + 1/(z+x))`.
    -- The product `(2*(x+y+z))` is grouped right-associatively by default.
    have h_cauchy_schwarz_substituted : 9 ≤ ((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * ((2 : ℝ) * (x + y + z)) := by
      -- The hypothesis is `h_cauchy_schwarz : (∑ uᵢvᵢ)² ≤ (∑ uᵢ²) * (∑ vᵢ²)`.
      -- We have calculated the values for `(∑ uᵢvᵢ)²`, `(∑ uᵢ²)`, and `(∑ vᵢ²)`.
      -- Substitute these values into `h_cauchy_schwarz`.
      rw [h_sum_uv_sq, h_sum_uu_sq, h_sum_vv_sq] at h_cauchy_schwarz
      -- The goal is now `9 ≤ (((1/(x+y) + ...) + 1/(z+x))) * (2*(x+y+z))`.
      -- This matches the modified hypothesis `h_cauchy_schwarz`.
      exact h_cauchy_schwarz

    -- Rearrange the inequality using algebraic properties to match the form needed for the next step.
    -- We have 9 ≤ A * (B * C) from h_cauchy_schwarz_substituted, where A is the sum, B=2, C=x+y+z.
    -- We want 9 ≤ (A * B) * C.
    -- This transformation is the reverse of `mul_assoc A B C : (A * B) * C = A * (B * C)`.
    -- We apply the reverse rewrite `← mul_assoc A B C` to the RHS of `h_cauchy_schwarz_substituted`.
    have h_rearranged : 9 ≤ (((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * (2 : ℝ)) * (x + y + z) := by
      -- The hypothesis h_cauchy_schwarz_substituted is `9 ≤ A * (B * C)`.
      -- We use `← mul_assoc A B C` to rewrite `A * (B * C)` to `(A * B) * C`.
      -- Here A is the sum `((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z)) + (1 : ℝ) / (z + x)`, B is 2, C is (x + y + z).
      -- The rewrite target is the RHS of `h_cauchy_schwarz_substituted`.
      -- -- The previous attempt failed because it used `mul_assoc` (forward direction) which tries to match `(A*B)*C` when the hypothesis contains `A*(B*C)`.
      -- -- We correct this by using the reverse direction `← mul_assoc`.
      rw [← mul_assoc (((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z)) + (1 : ℝ) / (z + x)) (2 : ℝ) (x + y + z)] at h_cauchy_schwarz_substituted
      -- The hypothesis now has the form `9 ≤ (A * B) * C`, which matches the goal.
      exact h_cauchy_schwarz_substituted

    -- We want to show 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x).
    -- We have 9 ≤ ((1 / (x + y) + 1 / (y + z) + (1 / (z + x))) * 2) * (x + y + z) from h_rearranged.
    -- We use the equivalence `div_le_iff` which states `a / c ≤ b ↔ a ≤ c * b` for `c > 0`.
    -- We are in the situation `a ≤ b * c` (h_rearranged, where `a=9`, `b = ((1 / (x + y) + ...) * 2)`, `c = x+y+z`), and we want to show `a / c ≤ b`.
    -- This is the forward direction (`.mp`) of the equivalence `a ≤ b * c ↔ a / c ≤ b` (or the reverse direction `.mpr` of `a / c ≤ b ↔ a ≤ c * b`). Let's use `div_le_iff` and its `.mpr`.
    have h_intermediate_ineq : (9 : ℝ) / (x + y + z) ≤ ((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * (2 : ℝ) := by
      -- Apply the equivalence `div_le_iff`. It requires a proof that the denominator `x + y + z` is positive.
      -- We have the proof `hxyz : 0 < x + y + z`.
      apply (div_le_iff hxyz).mpr
      -- The goal is now `9 ≤ (((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * (2 : ℝ)) * (x + y + z)`.
      -- This exactly matches the hypothesis `h_rearranged`.
      exact h_rearranged

    -- The target inequality is 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x).
    -- We have shown `9 / (x + y + z) ≤ ((1 / (x + y) + 1 / (y + z) + (1 / (z + x))) * 2)`.
    -- We need to show that the RHS of this inequality is equal to the RHS of the target inequality.

    -- Prove the distributive property on the RHS of the goal: 2/(x+y) + ... = 2 * (1/(x+y) + ...)
    have h_rhs_rewrite : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) = 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
      -- The goal is `∑ᵢ 2/Dᵢ = 2 * ∑ᵢ 1/Dᵢ`.
      -- We can rewrite each term `2/D` as `2 * (1/D)` using `mul_one_div a b = a / b` which holds in a field.
      -- First, prove the general property `2/D = 2 * (1/D)` for `D ≠ 0`.
      have two_div_eq_two_mul_one_div (D : ℝ) (hD_ne_zero : D ≠ 0) : 2 / D = 2 * (1 / D) := by
        -- The goal is 2 / D = 2 * (1 / D).
        -- The theorem `mul_one_div` states that a * (1/b) = a / b.
        -- Applying this rewrite rule to the RHS (2 * (1/D)) changes it to 2 / D.
        -- The goal becomes 2 / D = 2 / D, which is definitionally true.
        -- Therefore, the rewrite itself closes the goal.
        rw [mul_one_div]
        -- The previous `rfl` was redundant as the goal was closed by the `rw`.
      -- Apply this property to each term on the LHS of the goal equality.
      -- We need to show the denominators are non-zero, which is true since x+y > 0 (hxy), y+z > 0 (hyz), z+x > 0 (hzx).
      rw [two_div_eq_two_mul_one_div (x + y) (ne_of_gt hxy)]
      rw [two_div_eq_two_mul_one_div (y + z) (ne_of_gt hyz)]
      rw [two_div_eq_two_mul_one_div (z + x) (ne_of_gt hzx)]
      -- The goal is now `2 * (1/(x+y)) + 2 * (1/(y+z)) + 2 * (1/(z+x)) = 2 * (1/(x+y) + 1/(y+z) + 1/(z+x))`.
      -- This is the distributive property `2*a + 2*b + 2*c = 2*(a + b + c)`. `ring` can prove this.
      ring

    -- Show that the RHS of h_intermediate_ineq equals the RHS of the goal.
    -- RHS of h_intermediate_ineq: `((1 / (x + y) + 1 / (y + z) + (1 / (z + x))) * 2)`
    -- RHS of goal: `2 / (x + y) + 2 / (y + z) + 2 / (z + x)`
    -- We know from `h_rhs_rewrite` that `RHS_goal = 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x))`.
    -- We need to show `((1 / (x + y) + ...) * 2) = 2 * (1 / (x + y) + ...)`.
    have h_rhs_eq : ((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * (2 : ℝ) = (2 : ℝ) / (x + y) + (2 : ℝ) / (y + z) + (2 : ℝ) / (z + x) := by
      -- Rewrite the RHS of the goal using the equality from `h_rhs_rewrite`.
      rw [h_rhs_rewrite]
      -- The goal is now `((1 / (x + y) + ...) * 2) = 2 * (1 / (x + y) + ...)`.
      -- This is of the form `A * 2 = 2 * A`, which is true by commutativity of multiplication in ℝ.
      rw [mul_comm]

    -- Now use transitivity of ≤. We have A ≤ B (h_intermediate_ineq) and B = C (h_rhs_eq). We want to show A ≤ C (goal).
    -- Rewrite the goal using the equality `h_rhs_eq` to make its RHS match `h_intermediate_ineq`.
    rw [← h_rhs_eq]
    -- The goal is now `9 / (x + y + z) ≤ ((1 : ℝ) / (x + y) + (1 : ℝ) / (y + z) + (1 : ℝ) / (z + x)) * (2 : ℝ)`.
    -- This exactly matches the hypothesis `h_intermediate_ineq`.
    exact h_intermediate_ineq


#print axioms algebra_9onxpypzleqsum2onxpy
