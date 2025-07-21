import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_113
  (x : ℝ) :
  x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 := by 
  -- The goal is to prove x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3.

  -- Evaluate the constant expression on the right-hand side.
  -- 7^2 - 14 * 7 + 3 = 49 - 98 + 3 = -46.
  -- We use a `have` statement and `norm_num` to prove this equality.
  have rhs_value : (7:ℝ)^2 - (14:ℝ) * 7 + 3 = -46 := by
    norm_num -- Proves the numerical equality 49 - 98 + 3 = -46.

  -- Rewrite the goal using the evaluated right-hand side.
  -- The goal `A ≥ B` becomes `A ≥ -46`.
  rw [rhs_value]
  -- Goal: x^2 - 14 * x + 3 ≥ -46

  -- The inequality `x^2 - 14 * x + 3 ≥ -46` is equivalent to
  -- `(x^2 - 14 * x + 3) - (-46) ≥ 0`, which simplifies to `x^2 - 14 * x + 49 ≥ 0`.
  -- We will prove `x^2 - 14 * x + 49 ≥ 0` first as a separate hypothesis.
  -- -- The previous error occurred because the `rw [h_factor]` was being attempted on the main goal,
  -- -- not the simplified goal introduced by `suffices`. By proving the simplified inequality
  -- -- in a self-contained `have` block, the `rw` will operate on the correct target within that block.
  have h_simplified_nonneg : x^2 - 14 * x + 49 ≥ 0 := by
    -- Proof of the hypothesis `h_simplified_nonneg`: `x^2 - 14 * x + 49 ≥ 0`.
    -- Recognize the expression `x^2 - 14 * x + 49` as the square of `(x - 7)`.
    -- That is, `x^2 - 14 * x + 49 = (x - 7)^2`.
    -- Use a `have` statement and `ring` to prove this algebraic equality.
    have h_factor : x ^ 2 - 14 * x + 49 = (x - 7) ^ 2 := by
      ring
    -- Rewrite the current goal (which is `x^2 - 14 * x + 49 ≥ 0`) using this equality.
    -- After rewriting using `h_factor`, the goal becomes `(x - 7)^2 ≥ 0`.
    rw [h_factor]
    -- Current Goal: `(x - 7)^2 ≥ 0`

    -- The goal is now `(x - 7)^2 ≥ 0`. This is true because the square of any real number is non-negative.
    -- Use the theorem `sq_nonneg`. `sq_nonneg a` proves `a^2 ≥ 0`. We apply it to `(x - 7)`.
    exact sq_nonneg (x - 7)
  -- The proof of `h_simplified_nonneg` is now complete.
  -- We now have `h_simplified_nonneg : x^2 - 14 * x + 49 ≥ 0` available as a hypothesis.
  -- The main goal is still `x^2 - 14 * x + 3 ≥ -46`.

  -- Proof of the main goal: prove `x^2 - 14 * x + 3 ≥ -46`
  -- using the hypothesis `h_simplified_nonneg : x^2 - 14 * x + 49 ≥ 0`.
  -- These two inequalities are linearly related in terms of `x^2 - 14*x`.
  -- We can use `linarith` with the hypothesis `h_simplified_nonneg`.
  linarith [h_simplified_nonneg]
  -- The main goal is now solved using linarith.
  -- The entire proof is complete.


#print axioms mathd_algebra_113