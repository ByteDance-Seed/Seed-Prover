import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_algebra_143
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = x + 1)
  (h₁ : ∀ x, g x = x^2 + 3) :
  f (g 2) = 8 := by 
  -- The goal is to show f(g 2) = 8.
  -- We can evaluate f(g 2) step by step using the definitions of f and g.
  -- First, apply the definition of f using hypothesis h₀.
  -- h₀ says f x = x + 1 for all x.
  -- So, f (g 2) = g 2 + 1.
  rw [h₀]
  -- The goal is now `g 2 + 1 = 8`.
  -- Next, apply the definition of g using hypothesis h₁.
  -- h₁ says g x = x^2 + 3 for all x.
  -- So, g 2 = 2^2 + 3.
  rw [h₁]
  -- The goal is now `(2^2 + 3) + 1 = 8`.
  -- Now, simplify the numerical expression on the left side.
  -- 2^2 = 4
  -- 4 + 3 = 7
  -- 7 + 1 = 8
  -- The expression is just 8, so the goal becomes 8 = 8.
  norm_num
  -- norm_num solves the equality 8 = 8.

#print axioms mathd_algebra_143