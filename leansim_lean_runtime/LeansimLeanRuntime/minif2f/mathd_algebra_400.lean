import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_400
  (x : ℝ)
  (h₀ : 5 + 500 / 100 * 10 = 110 / 100 * x) :
  x = 50 := by
 
  -- Simplify the numerical expressions in the hypothesis h₀ using norm_num.
  -- 5 + 500 / 100 * 10 simplifies to 55.
  -- 110 / 100 simplifies to 11 / 10.
  norm_num at h₀
  -- The hypothesis h₀ is now `55 = (11 / 10) * x`.

  -- We want to solve for x from `55 = (11 / 10) * x`. This means we need to get `x = 55 / (11 / 10)`.
  -- We need the coefficient (11 / 10) to be non-zero to divide by it.
  have h_coeff_ne_zero : (11 : ℝ) / (10 : ℝ) ≠ 0 := by
    -- norm_num can prove this inequality.
    norm_num

  -- Use the property `div_eq_iff_mul_eq` to isolate x.
  -- The theorem `div_eq_iff_mul_eq` states that `b ≠ 0 → (a / b = c ↔ c * b = a)`.
  -- Our hypothesis `h₀` is `55 = (11 / 10) * x`.
  -- To use the `mpr` part of `div_eq_iff_mul_eq`, we need the hypothesis to be in the form `c * b = a`.
  -- So we need to rewrite `h₀` to `x * (11 / 10) = 55`.

  -- Rewrite `(11 / 10) * x` to `x * (11 / 10)`.
  -- The previous code had a type mismatch because the hypothesis h₀ was `55 = (11 / 10) * x`,
  -- but `div_eq_iff_mul_eq.mpr` expects the argument to be of the form `c * b = a`.
  -- We use mul_comm to swap the terms in the multiplication on the right side.
  rw [mul_comm] at h₀
  -- h₀ is now `55 = x * ((11 : ℝ) / (10 : ℝ))`.

  -- Rewrite the equality `55 = x * (...)` to `x * (...) = 55`.
  -- We use eq_comm to swap the sides of the equality to match the form `c * b = a`.
  rw [eq_comm] at h₀
  -- h₀ is now `x * ((11 : ℝ) / (10 : ℝ)) = 55`.

  -- Now apply the `mpr` direction of `div_eq_iff_mul_eq`.
  have h_x_eq_div : 55 / ((11 : ℝ) / (10 : ℝ)) = x := by
    -- The hypothesis `h₀` is now in the correct form `c * b = a` as required by `div_eq_iff_mul_eq.mpr`.
    apply (div_eq_iff_mul_eq h_coeff_ne_zero).mpr h₀

  -- The hypothesis h_x_eq_div is now `55 / (11 / 10) = x`.
  -- We need to simplify the left side of the equation `h_x_eq_div`.
  -- 55 / (11 / 10) should simplify to 50.
  norm_num at h_x_eq_div
  -- The hypothesis h_x_eq_div is now `50 = x`.

  -- Rewrite the equation so that x is on the left side.
  rw [eq_comm] at h_x_eq_div
  -- The hypothesis h_x_eq_div is now `x = 50`.

  -- The hypothesis h_x_eq_div is exactly the goal we want to prove.
  exact h_x_eq_div

#print axioms mathd_algebra_400
