import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_others_exirrpowirrrat :
  ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a^b) := by 

  -- We consider the number sqrt(2) ^ sqrt(2).
  -- We proceed by cases on whether this number is rational or irrational.
  by_cases h_sqrt_sqrt_irrational : Irrational (Real.sqrt 2 ^ Real.sqrt 2)
  -- Case 1: sqrt(2) ^ sqrt(2) is irrational.
  . -- In this case, we choose a = sqrt(2) ^ sqrt(2) and b = sqrt(2).
    -- We need to show that a and b are irrational and a^b is not.
    use (Real.sqrt 2 ^ Real.sqrt 2), Real.sqrt 2
    -- Goal: Irrational (Real.sqrt 2 ^ Real.sqrt 2) ∧ Irrational (Real.sqrt 2) ∧ ¬Irrational ((Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2)
    constructor
    . -- Prove Irrational (Real.sqrt 2 ^ Real.sqrt 2)
      -- This is our hypothesis in this case.
      exact h_sqrt_sqrt_irrational
    . -- Prove Irrational (Real.sqrt 2) ∧ ¬Irrational ((Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2)
      constructor
      . -- Prove Irrational (Real.sqrt 2)
        -- This is a known theorem from mathlib.
        exact irrational_sqrt_two
      . -- Prove ¬Irrational ((Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2)
        -- We need to evaluate the power: ((sqrt(2)^sqrt(2))^sqrt(2)) = sqrt(2)^(sqrt(2)*sqrt(2)) = sqrt(2)^2 = 2.
        -- Then show ¬Irrational 2.
        have h_pow_eval : (Real.sqrt 2 ^ Real.sqrt 2) ^ Real.sqrt 2 = 2 := by
          -- Use the power rule (x^y)^z = x^(y*z) for real numbers.
          -- The theorem Real.rpow_mul requires the base (Real.sqrt 2) to be non-negative.
          rw [← Real.rpow_mul (Real.sqrt_nonneg 2) (Real.sqrt 2) (Real.sqrt 2)]
          -- Goal: Real.sqrt 2 ^ (Real.sqrt 2 * Real.sqrt 2) = 2
          -- Evaluate the exponent: sqrt(2) * sqrt(2) = 2.
          have h_mul_sqrt_two : Real.sqrt 2 * Real.sqrt 2 = 2 := by
            -- Goal: Real.sqrt 2 * Real.sqrt 2 = 2
            -- Use the definition of power 2 for real numbers: x * x = x^(2:ℕ) (via pow_two).
            rw [← pow_two (Real.sqrt 2)]
            -- Goal: Real.sqrt 2 ^ (2 : ℕ) = 2
            -- The theorem Real.sq_sqrt proves Real.sqrt x ^ (2 : ℕ) = x for x >= 0.
            exact Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
          -- Now substitute the evaluated exponent into the goal.
          rw [h_mul_sqrt_two]
          -- Goal: Real.sqrt 2 ^ (2 : ℝ) = 2
          -- The term Real.sqrt 2 ^ (2 : ℝ) needs to be rewritten using Real.rpow_nat_cast.
          -- Real.rpow_nat_cast applies to a base `x` raised to a natural number coerced to a real `↑n : ℝ`.
          -- We explicitly rewrite the real number `(2 : ℝ)` in the exponent to the coercion of the natural number `(↑(2 : ℕ) : ℝ)`.
          -- This is definitionally equal, but helps the rewrite tactic match the pattern expected by Real.rpow_nat_cast.
          have h_exp_coerce : (2 : ℝ) = (↑(2 : ℕ) : ℝ) := rfl
          rw [h_exp_coerce]
          -- Goal: Real.sqrt (↑(2 : ℕ) : ℝ) ^ (↑(2 : ℕ) : ℝ) = (↑(2 : ℕ) : ℝ)
          -- The base Real.sqrt 2 has been transformed to Real.sqrt (↑(2 : ℕ) : ℝ) by the previous rewrite `rw [h_exp_coerce]`.
          -- Apply Real.rpow_nat_cast to rewrite `Real.sqrt (↑(2 : ℕ) : ℝ) ^ (↑(2 : ℕ) : ℝ)` to `Real.sqrt (↑(2 : ℕ) : ℝ) ^ (2 : ℕ)`.
          -- We must use the transformed base `Real.sqrt (↑(2 : ℕ) : ℝ)` for the pattern match.
          rw [Real.rpow_nat_cast (Real.sqrt (↑(2 : ℕ) : ℝ)) 2]
          -- Goal: Real.sqrt (↑(2 : ℕ) : ℝ) ^ (2 : ℕ) = (↑(2 : ℕ) : ℝ)
          -- Apply Real.sq_sqrt which works on `^ (2 : ℕ)`.
          -- We need to prove the argument to sqrt, which is `(↑(2 : ℕ) : ℝ)`, is non-negative.
          exact Real.sq_sqrt (by norm_num : (↑(2 : ℕ) : ℝ) ≥ 0)
        -- Now substitute the evaluated power into the goal.
        rw [h_pow_eval]
        -- Goal: ¬Irrational 2
        -- A real number is not irrational if it is a rational number. Natural number 2 is rational.
        -- We use the theorem `not_irrational_ofNat` which states that natural numbers >= 2 are not irrational.
        exact not_irrational_ofNat 2

  -- Case 2: sqrt(2) ^ sqrt(2) is rational.
  . -- In this case, we choose a = sqrt(2) and b = sqrt(2).
    -- We need to show that a and b are irrational and a^b is not.
    -- Our hypothesis is ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2).
    use Real.sqrt 2, Real.sqrt 2
    -- Goal: Irrational (Real.sqrt 2) ∧ Irrational (Real.sqrt 2) ∧ ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2)
    constructor
    . -- Prove Irrational (Real.sqrt 2)
      exact irrational_sqrt_two
    . -- Prove Irrational (Real.sqrt 2) ∧ ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2)
      constructor
      . -- Prove Irrational (Real.sqrt 2)
        exact irrational_sqrt_two
      . -- Prove ¬Irrational (Real.sqrt 2 ^ Real.sqrt 2)
        -- This is our hypothesis in this case.
        exact h_sqrt_sqrt_irrational


#print axioms algebra_others_exirrpowirrrat
