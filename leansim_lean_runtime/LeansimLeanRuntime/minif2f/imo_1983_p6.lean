import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) := by

  -- The previous attempt to prove the expanded algebraic inequality directly using nlinarith failed.
  -- This problem is known to be solvable using a standard substitution related to triangle inequalities.
  -- Given the triangle inequalities h₁, h₂ and h₃, we can define positive numbers x, y, z such that a, b, c
  -- are formed by sums of these numbers.
  -- Define x, y, z based on the sides of the triangle.
  let x := (b + c - a) / 2
  let y := (a + c - b) / 2
  let z := (a + b - c) / 2

  -- The triangle inequalities h₁, h₂ and h₃ ensure that x, y, and z are positive.
  -- a < b + c <=> b + c - a > 0 <=> x > 0
  have h_b_c_a_pos : 0 < b + c - a := by linarith [h₃] -- Added intermediate hypothesis for clarity
  have hx : 0 < x := by
    -- Use linarith on the inequality h₃ to show the numerator is positive.
    apply div_pos
    exact h_b_c_a_pos -- Use the named hypothesis
    norm_num -- Prove 0 < 2

  -- b < a + c <=> a + c - b > 0 <=> y > 0
  have h_a_c_b_pos : 0 < a + c - b := by linarith [h₂] -- Added intermediate hypothesis for clarity
  have hy : 0 < y := by
    -- Use linarith on the inequality h₂ to show the numerator is positive.
    apply div_pos
    exact h_a_c_b_pos -- Use the named named hypothesis
    norm_num

  -- c < a + b <=> a + b - c > 0 <=> z > 0
  have h_a_b_c_pos : 0 < a + b - c := by linarith [h₁] -- Added intermediate hypothesis for clarity
  have hz : 0 < z := by
    -- Use linarith on the inequality h₁ to show the numerator is positive.
    apply div_pos
    exact h_a_b_c_pos -- Use the named hypothesis
    norm_num

  -- Express a, b, and c in terms of x, y, and z.
  -- y + z = (a + c - b)/2 + (a + b - c)/2 = (a + c - b + a + b - c)/2 = 2a/2 = a
  have ha : a = y + z := by
    -- Substitute the definitions of x, y, z and simplify using field_simp and ring.
    simp only [x, y, z]
    field_simp -- Clears denominators
    ring -- Simplifies the numerator and checks equality

  -- x + z = (b + c - a)/2 + (a + b - c)/2 = (b + c - a + a + b - c)/2 = 2b/2 = b
  have hb : b = x + z := by
    simp only [x, y, z]
    field_simp
    ring

  -- x + y = (b + c - a)/2 + (a + c - b)/2 = (b + c - a + a + c - b)/2 = 2c/2 = c
  have hc : c = x + y := by
    simp only [x, y, z]
    field_simp
    ring

  -- The intermediate lemmas ha_b, hb_c, hc_a are not strictly necessary for the proof of h_subst
  -- using `ring` after substituting a, b, c, so they are removed.
  -- Express the differences a-b, b-c, c-a in terms of x, y, and z.
  -- a - b = y - x
  -- b - c = z - y
  -- c - a = x - z

  -- Substitute a, b, c into the original inequality expression.
  -- The original expression is a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)
  -- Replace a, b, c with their expressions in terms of x, y, z.
  have h_subst : a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) =
    (y + z)^2 * (x + z) * (y - x) + (x + z)^2 * (x + y) * (z - y) + (x + y)^2 * (y + z) * (x - z) := by
    -- We only need to substitute a, b, c using ha, hb, hc. This transforms
    -- the terms like (a-b) into (y+z)-(x+z).
    rw [ha, hb, hc]
    -- The goal is now an equality of two polynomial expressions in x, y, z:
    -- (y + z)^2 * (x + z) * (y + z - (x + z)) + ... = (y + z)^2 * (x + z) * (y - x) + ...
    -- We use the `ring` tactic. `ring` automatically simplifies algebraic differences
    -- like (y + z - (x + z)) to (y - x) and then expands both sides to prove the equality.
    ring -- This part is correct and proved the substitution.

  -- Apply this substitution to the goal.
  rw [h_subst]
  -- Goal: 0 ≤ the expression in terms of x, y, z.
  -- Goal: 0 ≤ (y + z)^2 * (x + z) * (y - x) + (x + z)^2 * (x + y) * (z - y) + (x + y)^2 * (y + z) * (x - z)

  -- Prove a polynomial identity relating the substituted expression to a simpler form.
  -- The identity used previously was incorrect, causing the `ring` tactic to fail.
  -- The correct identity relates the substituted expression to 2 times the difference
  -- between the cyclic sum x y^3 + y z^3 + z x^3 and x y z (x + y + z).
  have poly_id (x_var y_var z_var : ℝ) :
    (y_var + z_var)^2 * (x_var + z_var) * (y_var - x_var) +
    (x_var + z_var)^2 * (x_var + y_var) * (z_var - y_var) +
    (x_var + y_var)^2 * (y_var + z_var) * (x_var - z_var) =
    2 * (x_var * y_var^3 + y_var * z_var^3 + z_var * x_var^3 - (x_var * y_var * z_var * (x_var + y_var + z_var))) := by
    -- `ring` can now prove this correct polynomial identity after fixing the typo.
    ring

  -- Apply this identity to the current goal using the specific values of x, y, z.
  rw [poly_id x y z]
  -- Goal: 0 ≤ 2 * (x * y^3 + y * z^3 + z * x^3 - x * y * z * (x + y + z))

  -- Since 2 is positive, the inequality 0 ≤ 2 * P is equivalent to 0 ≤ P.
  have h_two_pos : 0 < (2 : ℝ) := by norm_num
  -- The mul_nonneg_iff_left_nonneg_of_pos lemma requires the positive term to be on the right
  -- side of the multiplication. We use mul_comm to swap the order.
  rw [mul_comm (2 : ℝ) _]
  rw [mul_nonneg_iff_left_nonneg_of_pos h_two_pos]
  -- Goal: 0 ≤ x * y^3 + y * z^3 + z * x^3 - x * y * z * (x + y + z)

  -- Rearrange the inequality: 0 ≤ A - B is equivalent to B ≤ A.
  -- This rearrangement is the same as the one intended in the original code.
  have h_rearrange : 0 ≤ x * y^3 + y * z^3 + z * x^3 - (x * y * z * (x + y + z)) ↔
                     x * y * z * (x + y + z) ≤ x * y^3 + y * z^3 + z * x^3 := by -- Corrected typo from x*y^3 to z*x^3
    -- This is the standard equivalence between 0 <= B - A and A <= B.
    -- We use the le_sub_iff_add_le theorem. Let A := x*y*z*(x+y+z) and B := x*y^3 + y*z^3 + z*x^3.
    -- The theorem states c <= b - a <=> c + a <= b. Setting c = 0, we get 0 <= b - a <=> a <= b.
    -- The equivalence in h_rearrange is exactly 0 <= B - A <=> A <= B.
    simp [le_sub_iff_add_le] -- Replaced the manual Iff.intro proof with a direct application of the lemma.

  -- Apply the rearrangement to the goal.
  rw [h_rearrange]
  -- Goal: x^2 * y * z + x * y^2 * z + x * y * z ^ 2 ≤ x * y^3 + y * z^3 + z * x^3 -- Corrected typo from x*y^3 to z*x^3

  -- Expand the left side.
  have h_expand_lhs : x * y * z * (x + y + z) = x^2 * y * z + x * y^2 * z + x * y * z^2 := by ring
  rw [h_expand_lhs]
  -- Goal: x^2 * y * z + x * y^2 * z + x * y * z^2 ≤ x * y^3 + y * z^3 + z * x^3 -- Corrected typo from x*y^3 to z*x^3

  -- This inequality can be proved using the AM-GM inequality for three terms.
  -- The inequality is equivalent to x + y + z ≤ x^2/y + y^2/z + z^2/x for x, y, z > 0.
  -- We prove the equivalent form x^2/y + y^2/z + z^2/x ≥ x + y + z using AM-GM.

  -- Prove x^2/y + y ≥ 2 * x using AM-GM
  have h_amgm_x : x^2 / y + y ≥ 2 * x := by
    -- The goal x^2/y + y ≥ 2*x is equivalent to 2*x ≤ x^2/y + y.
    rw [ge_iff_le] -- Change goal P ≥ Q to Q ≤ P
    -- We prove the equivalence A ≤ B ↔ 0 ≤ B - A using le_sub_iff_add_le.symm.
    -- A = 2*x, B = x^2/y + y. The equivalence is 2*x <= x^2/y + y <=> 0 <= (x^2/y + y) - 2*x.
    have h_equiv_le_sub : (2 : ℝ) * x ≤ x ^ (2 : ℕ) / y + y ↔ 0 ≤ (x ^ (2 : ℕ) / y + y) - (2 : ℝ) * x := by
      simp [le_sub_iff_add_le.symm] -- Use le_sub_iff_add_le.symm to prove A <= B <=> 0 <= B - A.
    -- Apply this equivalence to the goal (A ≤ B becomes 0 ≤ B - A).
    rw [h_equiv_le_sub]
    -- Goal is now 0 ≤ (x ^ 2 / y + y) - 2 * x.

    -- We show that (x^2 / y + y) - 2*x is equal to (x - y)^2 / y.
    have h_algebraic_eq : (x^2 / y + y) - 2 * x = (x - y)^2 / y := by
      -- Use field_simp to handle division and then ring for polynomial simplification.
      field_simp [hy.ne'] -- Need y ≠ 0 for field_simp; hy: 0 < y implies y ≠ 0.
      ring -- Simplify the numerator and verify the equality.
    -- Substitute the algebraic equality into the goal (the right side of 0 ≤ ...).
    rw [h_algebraic_eq]
    -- The goal is now 0 ≤ (x - y)^2 / y.
    -- We know (x - y)^2 ≥ 0 (square of a real number).
    have h_sq_nonneg : 0 ≤ (x - y) ^ 2 := by apply sq_nonneg
    -- We also know y > 0 from the hypothesis hy, so y ≥ 0.
    have h_y_pos : 0 < y := hy -- Use h_y_pos from 0 < y
    -- The division of a non-negative number by a positive number is non-negative.
    apply div_nonneg h_sq_nonneg (le_of_lt h_y_pos) -- Use le_of_lt to get 0 <= y from 0 < y

  -- Prove y^2/z + z ≥ 2 * y using AM-GM (cyclic permutation)
  have h_amgm_y : y^2 / z + z ≥ 2 * y := by
    -- The goal y^2/z + z ≥ 2*y is equivalent to 2*y ≤ y^2/z + z.
    rw [ge_iff_le] -- Change goal P ≥ Q to Q ≤ P
    -- We prove the equivalence A ≤ B ↔ 0 ≤ B - A using le_sub_iff_add_le.symm.
    -- A = 2*y, B = y^2/z + z.
    have h_equiv_le_sub : (2 : ℝ) * y ≤ y ^ (2 : ℕ) / z + z ↔ 0 ≤ (y ^ (2 : ℕ) / z + z) - (2 : ℝ) * y := by
      simp [le_sub_iff_add_le.symm] -- Use le_sub_iff_add_le.symm to prove A <= B <=> 0 <= B - A.
    -- Apply this equivalence to the goal (A ≤ B becomes 0 ≤ B - A).
    rw [h_equiv_le_sub]
    -- We show that (y^2 / z + z) - 2*y is equal to (y - z)^2 / z.
    have h_algebraic_eq : (y^2 / z + z) - 2 * y = (y - z)^2 / z := by
      -- Use field_simp to handle division and then ring for polynomial simplification.
      field_simp [hz.ne'] -- Need z ≠ 0 for field_simp; hz: 0 < z implies z ≠ 0.
      ring -- Simplify the numerator and verify the equality.
    -- Substitute the algebraic equality into the goal (the right side of 0 ≤ ...).
    rw [h_algebraic_eq]
    -- The goal is now 0 ≤ (y - z)^2 / z.
    -- We know (y - z)^2 ≥ 0 (square of a real number).
    have h_sq_nonneg : 0 ≤ (y - z) ^ 2 := by apply sq_nonneg
    -- We also know z > 0 from the hypothesis hz, so z ≥ 0.
    have h_z_pos : 0 < z := hz -- Use h_z_pos from 0 < z
    -- The division of a non-negative number by a positive number is non-negative.
    apply div_nonneg h_sq_nonneg (le_of_lt h_z_pos) -- Use le_of_lt to get 0 <= z from 0 < z

  -- Prove z^2/x + x ≥ 2 * z using AM-GM (cyclic permutation)
  have h_amgm_z : z^2 / x + x ≥ 2 * z := by
    -- The goal z^2/x + x ≥ 2*z is equivalent to 2*z ≤ z^2/x + x.
    rw [ge_iff_le] -- Change goal P ≥ Q to Q ≤ P
    -- We prove the equivalence A ≤ B ↔ 0 ≤ B - A using le_sub_iff_add_le.symm.
    -- A = 2*z, B = z^2/x + x.
    have h_equiv_le_sub : (2 : ℝ) * z ≤ z ^ (2 : ℕ) / x + x ↔ 0 ≤ (z ^ (2 : ℕ) / x + x) - (2 : ℝ) * z := by
      simp [le_sub_iff_add_le.symm] -- Use le_sub_iff_add_le.symm to prove A <= B <=> 0 <= B - A.
    -- Apply this equivalence to the goal (A ≤ B becomes 0 ≤ B - A).
    rw [h_equiv_le_sub]
    -- Goal is now 0 ≤ (z ^ 2 / x + x) - 2 * z.

    -- We show that (z^2 / x + x) - 2*z is equal to (z - x)^2 / x.
    have h_algebraic_eq : (z^2 / x + x) - 2 * z = (z - x)^2 / x := by
      -- Use field_simp to handle division and then ring for polynomial simplification.
      field_simp [hx.ne'] -- Need x ≠ 0 for field_simp; hx: 0 < x implies x ≠ 0.
      ring -- Simplify the numerator and verify the equality.
    -- Substitute the algebraic equality into the goal (the right side of 0 ≤ ...).
    rw [h_algebraic_eq]
    -- The goal is now 0 ≤ (z - x)^2 / x.
    -- We know (z - x)^2 ≥ 0 (square of a real number).
    have h_sq_nonneg : 0 ≤ (z - x) ^ 2 := by apply sq_nonneg
    -- We also know x > 0 from the hypothesis hx, so x ≥ 0.
    have h_x_pos : 0 < x := hx -- Use h_x_pos from 0 < x
    -- The division of a non-negative number by a positive number is non-negative.
    apply div_nonneg h_sq_nonneg (le_of_lt h_x_pos) -- Use le_of_lt to get 0 <= x from 0 < x

  -- Sum the three AM-GM inequalities
  have h_sum_amgm : x^2 / y + y + y^2 / z + z + z^2 / x + x ≥ 2 * x + 2 * y + 2 * z := by
    linarith [h_amgm_x, h_amgm_y, h_amgm_z]

  -- Rearrange the terms on the LHS of the sum
  have h_lhs_rearrange : x^2 / y + y + y^2 / z + z + z^2 / x + x = x^2 / y + y^2 / z + z^2 / x + x + y + z := by ring
  -- Rearrange the RHS of the sum
  have h_rhs_rearrange : 2 * x + 2 * y + 2 * z = 2 * (x + y + z) := by ring

  -- Apply rearrangements to the summed inequality
  have h_sum_rearranged : x^2 / y + y^2 / z + z^2 / x + (x + y + z) ≥ 2 * (x + y + z) := by
    rw [h_lhs_rearrange, h_rhs_rearrange] at h_sum_amgm
    -- The hypothesis h_sum_amgm now has type x^2 / y + y^2 / z + z^2 / x + x + y + z ≥ 2 * (x + y + z).
    -- The goal is x^2 / y + y^2 / z + z^2 / x + (x + y + z) ≥ (2 : ℝ) * (x + y + z).
    -- The only difference is the grouping of (x + y + z) on the LHS.
    -- Although definitionally equal, `exact` requires the types to match syntactically here.
    -- We prove the equality of the two LHS forms and rewrite the hypothesis.
    have h_lhs_grouped : x^2 / y + y^2 / z + z^2 / x + x + y + z = x^2 / y + y^2 / z + z^2 / x + (x + y + z) := by ring
    rw [h_lhs_grouped] at h_sum_amgm
    -- Now `h_sum_amgm` has the exact same type as the goal.
    exact h_sum_amgm

  -- Subtract (x + y + z) from both sides
  have h_final_amgm : x^2 / y + y^2 / z + z^2 / x ≥ x + y + z := by
    linarith [h_sum_rearranged]

  -- The current goal is x^2 * y * z + x * y^2 * z + x * y * z ^ 2 ≤ x * y^3 + y * z^3 + z * x^3 -- Corrected typo from x*y^3 to z*x^3
  -- This is equivalent to x + y + z ≤ x^2/y + y^2/z + z^2/x given x, y, z > 0.

  -- Show the equivalence between the goal and the AM-GM inequality.
  have h_equiv : (x^2 * y * z + x * y^2 * z + x * y * z ^ 2 ≤ x * y^3 + y * z^3 + z * x^3) ↔ -- Corrected typo from x*y^3 to z*x^3
               (x + y + z ≤ x^2 / y + y^2 / z + z^2 / x) := by
    have h_xyz_pos : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
    have h_mul_lhs : (x + y + z) * (x * y * z) = x^2 * y * z + x * y^2 * z + x * y * z^2 := by ring
    have h_mul_rhs : (x^2 / y + y^2 / z + z^2 / x) * (x * y * z) = x * y^3 + y * z^3 + z * x^3 := by field_simp [hx.ne', hy.ne', hz.ne']; ring
    -- Rewrite the left side of the equivalence using the algebraic identities
    rw [← h_mul_lhs, ← h_mul_rhs]
    -- The goal is now of the form `(A * C ≤ B * C) ↔ (A ≤ B)` where C is positive.
    -- Use the theorem `mul_le_mul_iff_of_pos_right`.
    -- `apply mul_le_mul_iff_of_pos_right h_xyz_pos` proves the goal directly because the hypothesis `0 < c` is discharged by `h_xyz_pos`
    -- and the conclusion `a * c ≤ b * c ↔ a ≤ b` matches the current goal after rewrites.
    apply mul_le_mul_iff_of_pos_right h_xyz_pos -- This applies the equivalence A*C ≤ B*C ↔ A ≤ B given 0 < C, leaving `0 < C` as a goal.
    -- Goal: 0 < x * y * z. This is proved by h_xyz_pos.

  -- Apply the equivalence to the goal.
  rw [h_equiv]
  -- The goal is now x + y + z ≤ x^2/y + y^2/z + z^2/x
  -- This is exactly the statement of h_final_amgm with sides swapped (using ge_iff_le).
  exact ge_iff_le.mp h_final_amgm

#print axioms imo_1983_p6
