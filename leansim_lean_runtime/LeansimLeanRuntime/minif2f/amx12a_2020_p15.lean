import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem amc12a_2020_p15
  (a b : ℂ)
  (h₀ : a^3 - 8 = 0)
  (h₁ : b^3 - 8 * b^2 - 8 * b + 64 = 0) :
  Complex.abs (a - b) ≤ 2 * Real.sqrt 21 := by sorry
