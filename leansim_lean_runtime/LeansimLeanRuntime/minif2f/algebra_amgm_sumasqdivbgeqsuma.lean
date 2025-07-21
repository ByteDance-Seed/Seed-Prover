import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
 
  -- Destructure the hypothesis h₀ to get individual positive conditions
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- Apply the AM-GM-like inequality x^2/y + y ≥ 2x for x>0, y>0 to each cyclic term.
  -- This inequality comes from (x-y)^2 ≥ 0 => x^2 - 2xy + y^2 ≥ 0.
  -- Dividing by y (since y > 0): x^2/y - 2x + y ≥ 0 => x^2/y + y ≥ 2x.

  -- 1. a^2/b + b ≥ 2a using a > 0, b > 0
  -- The inequality a^2/b + b ≥ 2a is derived from (a - b)^2 ≥ 0.
  -- (a-b)^2 ≥ 0  => a^2 - 2ab + b^2 ≥ 0
  -- Dividing by b (which is > 0 by hb) => (a^2 - 2ab + b^2) / b ≥ 0
  -- => a^2/b - 2a + b ≥ 0 => a^2/b + b ≥ 2a
  have h_ab : a^2 / b + b ≥ 2 * a := by
    -- Prove (a - b)^2 / b ≥ 0
    have h_step1 : (a - b) ^ 2 ≥ 0 := sq_nonneg (a - b)
    -- div_nonneg requires the numerator to be non-negative and the denominator to be non-negative.
    -- h_step1 provides the non-negative numerator. hb provides the positive denominator, which implies non-negative.
    -- Corrected: div_nonneg expects 0 ≤ b, but hb is 0 < b. Use le_of_lt to convert 0 < b to 0 ≤ b.
    have h_step2 : (a - b) ^ 2 / b ≥ 0 := div_nonneg h_step1 (le_of_lt hb)
    -- Rewrite (a - b)^2 / b into a^2/b - 2a + b using field simplification and ring properties.
    -- This rewrite requires the denominator b to be non-zero, which is true because hb : b > 0.
    have h_rewrite : (a - b) ^ 2 / b = a ^ 2 / b - 2 * a + b := by field_simp [hb.ne']; ring
    -- Substitute the rewritten form back into the inequality h_step2.
    rw [h_rewrite] at h_step2
    -- The inequality is now a ^ 2 / b - 2 * a + b ≥ 0. Add 2*a to both sides using linarith.
    linarith [h_step2]

  -- 2. b^2/c + c ≥ 2b using b > 0, c > 0
  -- Derived from (b - c)^2 ≥ 0, similarly to the previous step.
  have h_bc : b^2 / c + c ≥ 2 * b := by
    have h_step1 : (b - c) ^ 2 ≥ 0 := sq_nonneg (b - c)
    -- Use hc : c > 0 for the positive denominator. Convert 0 < c to 0 ≤ c.
    have h_step2 : (b - c) ^ 2 / c ≥ 0 := div_nonneg h_step1 (le_of_lt hc)
    -- Use hc.ne' : c ≠ 0 for field_simp.
    have h_rewrite : (b - c) ^ 2 / c = b ^ 2 / c - 2 * b + c := by field_simp [hc.ne']; ring
    rw [h_rewrite] at h_step2
    linarith [h_step2]

  -- 3. c^2/d + d ≥ 2c using c > 0, d > 0
  -- Derived from (c - d)^2 ≥ 0, similarly to the previous step.
  have h_cd : c^2 / d + d ≥ 2 * c := by
    have h_step1 : (c - d) ^ 2 ≥ 0 := sq_nonneg (c - d)
    -- Use hd : d > 0 for the positive denominator. Convert 0 < d to 0 ≤ d.
    have h_step2 : (c - d) ^ 2 / d ≥ 0 := div_nonneg h_step1 (le_of_lt hd)
    -- Use hd.ne' : d ≠ 0 for field_simp.
    have h_rewrite : (c - d) ^ 2 / d = c ^ 2 / d - 2 * c + d := by field_simp [hd.ne']; ring
    rw [h_rewrite] at h_step2
    linarith [h_step2]

  -- 4. d^2/a + a ≥ 2d using d > 0, a > 0
  -- Derived from (d - a)^2 ≥ 0, similarly to the previous step.
  have h_da : d^2 / a + a ≥ 2 * d := by
    have h_step1 : (d - a) ^ 2 ≥ 0 := sq_nonneg (d - a)
    -- Use ha : a > 0 for the positive denominator. Convert 0 < a to 0 ≤ a.
    -- Corrected: Applied le_of_lt to ha to match the expected type 0 ≤ a for div_nonneg.
    have h_step2 : (d - a) ^ 2 / a ≥ 0 := div_nonneg h_step1 (le_of_lt ha)
    -- Use ha.ne' : a ≠ 0 for field_simp.
    have h_rewrite : (d - a) ^ 2 / a = d ^ 2 / a - 2 * d + a := by field_simp [ha.ne']; ring
    rw [h_rewrite] at h_step2
    linarith [h_step2]

  -- Sum the four inequalities h_ab, h_bc, h_cd, h_da using linarith
  -- The sum is (a^2/b + b) + (b^2/c + c) + (c^2/d + d) + (d^2/a + a) ≥ 2a + 2b + 2c + 2d
  -- Rearranging the left side gives: (a^2/b + b^2/c + c^2/d + d^2/a) + (a + b + c + d) ≥ 2(a + b + c + d)
  -- Subtracting (a + b + c + d) from both sides gives the goal: a^2/b + b^2/c + c^2/d + d^2/a ≥ a + b + c + d
  -- Linarith can deduce the final step from the summed inequality.
  linarith [h_ab, h_bc, h_cd, h_da] -- Use linarith to sum the four inequalities and simplify


#print axioms algebra_amgm_sumasqdivbgeqsuma
