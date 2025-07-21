import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem mathd_algebra_296 :
  abs (((3491 - 60) * (3491 + 60) - 3491^2):ℤ) = 3600 := by
  -- The goal is to prove an equality involving an absolute value of an integer expression.
  -- The expression inside the absolute value is ((3491 - 60) * (3491 + 60) - 3491^2).
  -- This is of the form (a - b)(a + b) - a^2, where a = 3491 and b = 60.
  -- Using the difference of squares formula (a - b)(a + b) = a^2 - b^2,
  -- the expression simplifies to (a^2 - b^2) - a^2 = -b^2.
  -- In this case, the expression simplifies to -60^2.
  -- We use the `simp` tactic to perform this algebraic simplification and numerical evaluation.
  -- The first `simp` will simplify the expression inside the `abs`.
  simp
  -- The previous `simp` tactic was redundant as the goal was already solved by the first `simp`.
  -- The first `simp` simplified the expression `abs (((3491 - 60) * (3491 + 60) - 3491^2):ℤ)`
  -- to `abs (-3600) = 3600`, and then further simplified `abs (-3600)` to `3600`,
  -- resulting in the goal `3600 = 3600`, which was automatically closed.
  -- No further tactics are needed.


#print axioms mathd_algebra_296
