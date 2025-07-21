import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_263
  (y : ℝ)
  (h₀ : 0 ≤ 19 + 3 * y)
  (h₁ : Real.sqrt (19 + 3 * y) = 7) :
  y = 10 := by 
  -- We are given the equation involving a square root: `Real.sqrt (19 + 3 * y) = 7`.
  -- To eliminate the square root, we can square both sides of the equation.
  -- Squaring both sides of an equality maintains the equality.
  have h₂ : (Real.sqrt (19 + 3 * y)) ^ 2 = 7 ^ 2 := by
    -- We apply the function `(·)^2` to both sides of the equality `h₁`.
    rw [h₁]

  -- Now we simplify the left side `(Real.sqrt (19 + 3 * y)) ^ 2`.
  -- We use the theorem `Real.sq_sqrt`, which states that `(Real.sqrt x)^2 = x` for `0 ≤ x`.
  -- Our hypothesis `h₀ : 0 ≤ 19 + 3 * y` provides the necessary condition for `Real.sq_sqrt`.
  rw [Real.sq_sqrt h₀] at h₂

  -- The hypothesis `h₂` is now `19 + 3 * y = 7 ^ 2`.
  -- Let's evaluate the right side `7 ^ 2`.
  norm_num at h₂

  -- The hypothesis `h₂` is now `19 + 3 * y = 49`.
  -- This is a simple linear equation in the variable `y`.
  -- We want to show that `y = 10`.
  -- The tactic `linarith` is capable of solving linear equations and inequalities by finding contradictions.
  -- We can use `linarith` with our hypothesis `h₂` to derive the goal `y = 10`.
  linarith [h₂]

#print axioms mathd_algebra_263