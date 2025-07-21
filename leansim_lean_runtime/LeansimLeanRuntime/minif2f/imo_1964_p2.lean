import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by 

  -- Let x = b + c - a, y = c + a - b, z = a + b - c
  let x := b + c - a
  let y := c + a - b
  let z := a + b - c

  -- Prove x, y, z are positive using the triangle inequalities
  -- The goal hx_pos : x > 0 is b + c - a > 0, which is equivalent to b + c > a.
  -- This is exactly hypothesis h₃: a < b + c.
  -- Changed linarith to direct application of sub_pos.mpr as it failed for z.
  have hx_pos : x > 0 := by exact sub_pos.mpr h₃

  -- The goal hy_pos : y > 0 is c + a - b > 0, which is equivalent to c + a > b.
  -- This is exactly hypothesis h₂: b < a + c.
  -- Changed linarith to direct application of sub_pos.mpr.
  -- The message indicates a type mismatch when directly using h₂ with sub_pos.mpr.
  -- sub_pos.mpr expects an argument of type P > Q to prove P - Q > 0.
  -- Here, we want to prove (c + a) - b > 0, so P = c + a and Q = b. We need a proof of c + a > b.
  -- We are given h₂ : b < a + c. This is equivalent to a + c > b (by gt_iff_lt) which is equivalent to c + a > b (by add_comm).
  have hy_pos : y > 0 := by
    -- The goal is y > 0, which is c + a - b > 0.
    -- The theorem sub_pos.mpr takes a proof of P > Q to show P - Q > 0.
    -- Here P = c + a and Q = b. So we need a proof of c + a > b.
    -- We are given h₂ : b < a + c.
    -- First, rewrite b < a + c to a + c > b using gt_iff_lt.mpr.
    have h_a_plus_c_gt_b : a + c > b := gt_iff_lt.mpr h₂
    -- Then, rewrite a + c > b to c + a > b using add_comm.
    have h_c_plus_a_gt_b : c + a > b := by rw [add_comm a c] at h_a_plus_c_gt_b; exact h_a_plus_c_gt_b
    -- Now we have the required proof c + a > b.
    exact sub_pos.mpr h_c_plus_a_gt_b

  -- The goal hz_pos : z > 0 is a + b - c > 0, which is equivalent to a + b > c.
  -- This is exactly hypothesis h₁: c < a + b.
  -- Linarith failed here according to the message. Using direct application of sub_pos.mpr.
  have hz_pos : z > 0 := by exact sub_pos.mpr h₁

  -- Express a, b, c in terms of x, y, z
  -- x + y = (b + c - a) + (c + a - b) = 2c
  -- x + z = (b + c - a) + (a + b - c) = 2b
  -- y + z = (c + a - b) + (a + b - c) = 2a

  -- The goal is `2 * a = y + z`. Substituting definitions of `y` and `z`,
  -- this is `2 * a = (c + a - b) + (a + b - c)`. The `ring` tactic can prove this algebraic identity directly.
  -- The `rw [y, z]` tactic was incorrect as `y` and `z` are variables, not equality proofs.
  have h_2a : 2 * a = y + z := by ring
  -- The goal is `2 * b = x + z`. Substituting definitions of `x` and `z`,
  -- this is `2 * b = (b + c - a) + (a + b - c)`. The `ring` tactic can prove this algebraic identity directly.
  -- The `rw [x, z]` tactic was incorrect as `x` and `z` are variables, not equality proofs.
  have h_2b : 2 * b = x + z := by ring
  -- The goal is `2 * c = x + y`. Substituting definitions of `x` and `y`,
  -- this is `2 * c = (b + c - a) + (c + a - b)`. The `ring` tactic can prove this algebraic identity directly.
  -- The `rw [x, y]` tactic was incorrect as `x` and `y` are variables, not equality proofs.
  have h_2c : 2 * c = x + y := by ring

  -- Divide by 2. Need 2 ≠ 0.
  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num

  -- Correcting the proofs for a, b, c in terms of x, y, z
  have h_a : a = (y + z) / 2 := by
    -- We have h_2a : 2 * a = y + z. We want to prove a = (y + z) / 2.
    -- Rewrite the right side of the goal using `h_2a`.
    rw [← h_2a]
    -- The goal is now `a = (2 * a) / 2`.
    -- This simplifies to a = a because (2 * a) / 2 = a for 2 ≠ 0 in a field.
    -- The `ring` tactic handles this simplification in a field.
    ring
  have h_b : b = (x + z) / 2 := by
    -- We have h_2b : 2 * b = x + z. We want to prove b = (x + z) / 2.
    -- Rewrite the right side of the main goal using the equality `h_2b`.
    rw [← h_2b]
    -- The goal is now `b = (2 * b) / 2`.
    -- This equality holds in a field like ℝ because (2 * b) / 2 simplifies to b, given 2 ≠ 0.
    -- The `ring` tactic can prove this simplification.
    ring

  have h_c : c = (x + y) / 2 := by
    -- We have h_2c : 2 * c = x + y. We want to prove c = (x + y) / 2.
    -- Rewrite the right side of the goal using h_2c.
    rw [← h_2c]
    -- The goal is now c = (2 * c) / 2.
    -- This simplifies to c = c because (2 * c) / 2 = c for 2 ≠ 0.
    -- The ring tactic handles this simplification in a field.
    ring

  -- The proof structure is H <= G <= F <= E <= D <= C <= B
  -- We use nested suffices: suffices G from (G -> H) { suffices F from (F -> G) { ... suffices B from (B -> C) { Proof of B } ... } }

  -- Prove H from G
  suffices a ^ 2 * x + b ^ 2 * y + c ^ 2 * z ≤ 3 * a * b * c from
    -- Goal is H (Original goal). Hypothesis is `this : G`. Prove H from G.
    -- The variables x, y, z are introduced by `let`. The original goal uses the explicit expressions
    -- like `b + c - a`. Since the let definitions are local and definitionally equal to the expressions
    -- in the goal, the goal is definitionally equal to the hypothesis `this`.
    by
    exact this

  -- Prove G from F
  suffices ((y + z) / 2) ^ 2 * x + ((x + z) / 2) ^ 2 * y + ((x + y) / 2) ^ 2 * z ≤ 3 * ((y + z) / 2) * ((x + z) / 2) * ((x + y) / 2) from
    -- Goal is G. Hypothesis is `this : F`. Prove G from F.
    by
    -- Rewrite hypothesis F using h_a, h_b, h_c.
    -- The equalities are h_a : a = (y + z) / 2, etc. We need to replace (y + z) / 2 with a in the hypothesis.
    -- This requires using the reversed rewrite arrows `←`.
    -- The previous use of `simp only` failed to make progress. `rw` is more direct here.
    rw [← h_a, ← h_b, ← h_c] at this
    -- Hypothesis is now G.
    exact this

  -- Prove F from E
  suffices 2 * (y + z)^2 * x + 2 * (x + z)^2 * y + 2 * (x + y)^2 * z ≤ 3 * (y + z) * (x + z) * (x + y) from
    -- Goal is F. Hypothesis is `this : E`. Prove G from F.
    by
    have h_eight_pos : (8 : ℝ) > 0 := by norm_num

    -- Show E_LHS = 8 * F_LHS
    have h_L3_eq_8L2 : 2 * (y + z)^2 * x + 2 * (x + z)^2 * y + 2 * (x + y)^2 * z = 8 * (((y + z) / 2) ^ 2 * x + ((x + z) / 2) ^ 2 * y + ((x + y) / 2) ^ 2 * z) := by
      simp only [mul_add, mul_assoc]
      -- The theorem `div_pow` states (a/b)^n = a^n / b^n.
      have h_sq_div : forall (u v : ℝ), v ≠ 0 → (u / v)^2 = u^2 / v^2 := by
        intro u v hv
        -- Apply the `div_pow` theorem which directly gives the desired equality.
        rw [div_pow]
      have h_two_sq : (2 : ℝ)^2 = 4 := by norm_num
      rw [h_sq_div (y+z) 2 h_two_ne_zero, h_two_sq]
      rw [h_sq_div (x+z) 2 h_two_ne_zero, h_two_sq]
      rw [h_sq_div (x+y) 2 h_two_ne_zero, h_two_sq]
      field_simp
      ring

    -- Show E_RHS = 8 * F_RHS
    have h_R3_eq_8R2 : 3 * (y + z) * (x + z) * (x + y) = 8 * (3 * ((y + z) / 2) * ((x + z) / 2) * ((x + y) / 2)) := by
      -- This is an algebraic identity in ℝ, which is a field. The `ring` tactic should handle it directly.
      -- Previous attempt used `conv` and `rw` which was overly complicated and failed due to pattern matching issues.
      ring

    -- We have `this : E_LHS ≤ E_RHS`. We want to prove `F_LHS ≤ F_RHS`.
    -- We have E_LHS = 8 * F_LHS and E_RHS = 8 * F_RHS. We want to prove F_LHS <= F_RHS from E_LHS <= E_RHS.
    -- This is equivalent to proving F_LHS <= F_RHS from 8 * F_LHS <= 8 * F_RHS.
    -- This is true since 8 > 0. We can use `le_of_mul_le_mul_left`.
    have h_8F_LHS_le_8F_RHS : 8 * (((y + z) / 2) ^ 2 * x + ((x + z) / 2) ^ 2 * y + ((x + y) / 2) ^ 2 * z) ≤ 8 * (3 * ((y + z) / 2) * ((x + z) / 2) * ((x + y) / 2)) := by
      -- Rewrite the left side of the goal (8 * F_LHS) using the equality E_LHS = 8 * F_LHS. We use the reversed equality ← h_L3_eq_8L2.
      -- The previous attempt used `rw [h_L3_eq_8L2]` which tries to replace E_LHS with 8 * F_LHS. This fails because E_LHS is not in the goal.
      rw [← h_L3_eq_8L2]
      -- Rewrite the right side of the goal (8 * F_RHS) using the equality E_RHS = 8 * F_RHS. We use the reversed equality ← h_R3_eq_8R2.
      -- The previous attempt used `rw [h_R3_eq_8R2]` which tries to replace E_RHS with 8 * F_RHS. This fails because E_RHS is not in the goal.
      rw [← h_R3_eq_8R2]
      -- The goal is now E_LHS ≤ E_RHS. We have `this : E_LHS ≤ E_RHS`.
      exact this
    -- Now prove F_LHS <= F_RHS from 8 * F_LHS <= 8 * F_RHS using 8 > 0.
    exact le_of_mul_le_mul_left h_8F_LHS_le_8F_RHS h_eight_pos

  -- Prove E from D
  -- Corrected the target expression to include the coefficient 2 for the last term.
  suffices 0 ≤ 3 * (y + z) * (x + z) * (x + y) - (2 * (y + z)^2 * x + 2 * (x + z)^2 * y + 2 * (x + y)^2 * z) from
    -- Goal is E. Hypothesis is `this : D`. Prove E from D.
    -- D is 0 ≤ E_RHS - E_LHS. This is equivalent to E : E_LHS ≤ E_RHS.
    by
    -- We use `le_of_sub_nonneg` which takes a proof of `0 ≤ b - a` and proves `a ≤ b`.
    -- In this case, we have `this : 0 ≤ (E_RHS - E_LHS)` and want to prove `E_LHS ≤ E_RHS`.
    -- So we apply `le_of_sub_nonneg` to `this`.
    exact le_of_sub_nonneg this

  -- Prove D from C
  suffices 0 ≤ x^2*y + x*y^2 + x^2*z + x*z^2 + y^2*z + y*z^2 - 6*x*y*z from
    by
    -- Goal is D. Hypothesis is `this : C`. Prove D from C.
    -- Use the algebraic identity: D_value = C_value.
    -- This algebraic identity must use the *corrected* E_LHS expression. The ring proof should reflect this.
    have h_difference_expansion : 3 * (y + z) * (x + z) * (x + y) - (2 * (y + z)^2 * x + 2 * (x + z)^2 * y + 2 * (x + y)^2 * z) = x^2*y + x*y^2 + x^2*z + x*z^2 + y^2*z + y*z^2 - 6*x*y*z := by ring -- Ensure the ring proof works with the corrected expression
    -- We want to prove `0 ≤ D_value`. We have `this : 0 ≤ C_value`.
    -- Rewrite the goal `0 ≤ D_value` using the identity `D_value = C_value`.
    rw [h_difference_expansion]
    -- The goal is now `0 ≤ C_value`. We have `this : 0 ≤ C_value`.
    exact this

  -- Prove C from B
  suffices 0 ≤ y*(x-z)^2 + x*(y-z)^2 + z*(x-y)^2 from
    by
    -- Goal is C. Hypothesis is `this : B`. Prove C from B.
    -- Use the algebraic identity: C_value = B_value.
    have h_algebraic_identity : x^2*y + x*y^2 + x^2*z + x*z^2 + y^2*z + y*z^2 - 6*x*y*z = y*(x-z)^2 + x*(y-z)^2 + z*(x-y)^2 := by ring
    -- We want to prove `0 ≤ C_value`. We have `this : 0 ≤ B_value`.
    -- Rewrite the goal `0 ≤ C_value` using the identity `C_value = B_value`.
    rw [h_algebraic_identity]
    -- The goal is now `0 ≤ B_value`. We have `this : 0 ≤ B_value`.
    exact this

  -- Proof of B: 0 ≤ y*(x-z)^2 + x*(y-z)^2 + z*(x-y)^2
  -- This is the base case of the suffices chain.
  -- We know x, y, z > 0 and squares are non-negative.
  -- y * (x-z)^2 ≥ 0
  -- x * (y-z)^2 ≥ 0
  -- z * (x-y)^2 ≥ 0
  -- The sum is non-negative.

  have h_x_minus_z_sq_nonneg : (x - z) ^ 2 ≥ 0 := by apply sq_nonneg
  have h_y_mul_x_minus_z_sq_nonneg : y * (x - z) ^ 2 ≥ 0 := by
    apply mul_nonneg
    exact le_of_lt hy_pos -- y > 0
    exact h_x_minus_z_sq_nonneg -- (x - z)^2 ≥ 0

  have h_y_minus_z_sq_nonneg : (y - z) ^ 2 ≥ 0 := by apply sq_nonneg
  have h_x_mul_y_minus_z_sq_nonneg : x * (y - z) ^ 2 ≥ 0 := by
    apply mul_nonneg
    exact le_of_lt hx_pos -- x > 0
    exact h_y_minus_z_sq_nonneg -- (y - z)^2 ≥ 0

  have h_x_minus_y_sq_nonneg : (x - y) ^ 2 ≥ 0 := by apply sq_nonneg
  have h_z_mul_x_minus_y_sq_nonneg : z * (x - y) ^ 2 ≥ 0 := by
    apply mul_nonneg
    exact le_of_lt hz_pos -- z > 0
    exact h_x_minus_y_sq_nonneg -- (x - y)^2 ≥ 0

  -- The goal is the sum of these three non-negative terms.
  -- First, prove the sum of the first two terms is non-negative
  have h_sum_first_two_nonneg : y * (x - z) ^ 2 + x * (y - z) ^ 2 ≥ 0 := by
    apply add_nonneg
    exact h_y_mul_x_minus_z_sq_nonneg
    exact h_x_mul_y_minus_z_sq_nonneg

  -- Then, prove the sum of all three terms is non-negative
  apply add_nonneg
  exact h_sum_first_two_nonneg
  exact h_z_mul_x_minus_y_sq_nonneg

#print axioms imo_1964_p2