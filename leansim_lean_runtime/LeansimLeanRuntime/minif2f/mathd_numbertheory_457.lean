import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem mathd_numbertheory_457
  (n  : ℕ)
  (h₀ : 0 < n)
  (h₁ : 80325∣(n !)) :
  17 ≤ n  := by 
  -- The strategy is to identify a prime factor of 80325 that is large enough.
  -- We will show that 17 is a prime factor of 80325.
  -- Given that 80325 divides n!, any prime factor of 80325 must also be a factor of n!.
  -- We then use the property that a prime p divides n! if and only if p is less than or equal to n.
  -- This will lead to the conclusion that 17 must be less than or equal to n.

  -- Step 1: Show that 17 is a prime number.
  have h_17_prime : Nat.Prime 17 := by
    -- `norm_num` can prove primality for small integers.
    norm_num

  -- Step 2: Show that 17 divides 80325.
  have h_17_dvd_80325 : 17 ∣ 80325 := by
    -- We perform the division to show the relationship.
    have h_eq : 80325 = 17 * 4725 := by norm_num
    -- From the equality `80325 = 17 * 4725`, we conclude that 17 divides 80325.
    rw [h_eq]
    -- `dvd_mul_right` is the theorem stating that `a ∣ a * b`.
    apply dvd_mul_right

  -- Step 3: Use the transitivity property of divisibility.
  -- We are given `80325 ∣ n!` (hypothesis `h₁`).
  -- We have shown `17 ∣ 80325` (hypothesis `h_17_dvd_80325`).
  -- By the transitivity of divisibility (`dvd_trans`), if `a ∣ b` and `b ∣ c`, then `a ∣ c`.
  have h_17_dvd_n_factorial : 17 ∣ n ! := by
    apply dvd_trans h_17_dvd_80325 h₁

  -- Step 4: Use the theorem `Nat.Prime.dvd_factorial`.
  -- This theorem states that for any prime number `p`, `p` divides `n!` if and only if `p` is less than or equal to `n`.
  -- The statement is `Nat.Prime p → (p ∣ n ! ↔ p ≤ n)`.
  have h_iff : Nat.Prime 17 → (17 ∣ n ! ↔ 17 ≤ n) := by
    apply Nat.Prime.dvd_factorial -- This theorem is exactly what we need.

  -- Apply the theorem using the fact that 17 is prime (hypothesis `h_17_prime`).
  have h_17_dvd_n_factorial_iff_le_n : 17 ∣ n ! ↔ 17 ≤ n := by
    apply h_iff h_17_prime

  -- Step 5: We have the equivalence `17 ∣ n! ↔ 17 ≤ n` and the fact `17 ∣ n!` (hypothesis `h_17_dvd_n_factorial`).
  -- We use the forward implication (`Iff.mp`) of the equivalence to deduce `17 ≤ n`.
  have h_17_le_n : 17 ≤ n := by
    apply Iff.mp h_17_dvd_n_factorial_iff_le_n h_17_dvd_n_factorial

  -- Step 6: The goal is `17 ≤ n`, which is precisely what we have proved in `h_17_le_n`.
  exact h_17_le_n

#print axioms mathd_numbertheory_457