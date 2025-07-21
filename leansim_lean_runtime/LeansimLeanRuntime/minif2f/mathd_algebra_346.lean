import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_346
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = 2 * x - 3)
  (h₁ : ∀ x, g x = x + 1) :
  g (f 5 - 1) = 7 := by 
  -- We need to evaluate g(f(5) - 1).
  -- First, let's evaluate f(5) using h₀.
  have hf5 : f 5 = 2 * 5 - 3 := by
    apply h₀

  -- Now, let's calculate the value of 2 * 5 - 3.
  -- The previous step inferred the numbers as real numbers because f has type ℝ → ℝ.
  -- We need to ensure this calculation is also done with real numbers for the rewrite to work.
  have hvalf5 : (2 : ℝ) * (5 : ℝ) - (3 : ℝ) = (7 : ℝ) := by
    norm_num

  -- Combine the previous two steps to get f 5 = 7.
  rw [hvalf5] at hf5

  -- Now the goal is g (f 5 - 1) = 7.
  -- Substitute the value of f 5 (which is 7) into the goal.
  -- -- The rewrite failed previously because `f 5` was not yet simplified to 7 in the goal.
  rw [hf5]

  -- Now the goal is g (7 - 1) = 7.
  -- Calculate 7 - 1.
  -- Ensure this calculation is done with real numbers.
  have hsub : (7 : ℝ) - (1 : ℝ) = (6 : ℝ) := by
    norm_num

  -- Substitute the subtraction result into the goal.
  -- Now that the goal contains (7 : ℝ) - (1 : ℝ), this rewrite will work.
  rw [hsub]

  -- Now the goal is g 6 = 7.
  -- Use the definition of g from h₁ to evaluate g(6).
  have hg6 : g 6 = 6 + 1 := by
    apply h₁

  -- Calculate 6 + 1.
  -- Ensure this calculation is done with real numbers.
  have hvalg6 : (6 : ℝ) + (1 : ℝ) = (7 : ℝ) := by
    norm_num

  -- Combine the previous two steps to get g 6 = 7.
  rw [hvalg6] at hg6

  -- The goal is now g 6 = 7, which is exactly what we just proved.
  exact hg6


#print axioms mathd_algebra_346