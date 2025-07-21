import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem induction_pprime_pdvdapowpma
  (p a : ℕ)
  (h₀ : 0 < a)
  (h₁ : Nat.Prime p) :
  p ∣ (a^p - a) := by 

  -- We prove the result by induction on `a`.
  -- Since the hypothesis is `0 < a`, which means `a ≥ 1`, we induct starting from `a=1`.
  -- We use `Nat.le_induction` to induct on `a` for `a ≥ 1`.
  -- The base case is `a = 1`. The inductive step assumes the result for `k ≥ 1` and proves it for `k + 1`.
  -- The theorem `Nat.le_induction` proves a statement of the form `∀ n, m ≤ n → P n`.
  -- Our goal is `p ∣ a^p - a` under the assumption `0 < a`.
  -- We need the required `1 ≤ a` hypothesis from `0 < a`.
  -- For natural numbers, `0 < a` is definitionally equivalent to `1 ≤ a`.
  -- Removed the incorrect `rw [Nat.pos_iff_one_le a] at h₀` because `Nat.pos_iff_one_le` is not a defined constant, and `0 < a` is definitionally `1 ≤ a` for natural numbers.
  induction a, h₀ using Nat.le_induction with
  | base =>
  -- Base case: a = 1. The goal becomes P 1, i.e., p ∣ 1^p - 1.
    show p ∣ 1 ^ p - 1
    -- Calculate 1^p - 1.
    have h_pow_one : 1 ^ p = 1 := by rw [one_pow p]
    have h_sub : 1 - 1 = 0 := by rw [Nat.sub_self 1]
    -- The goal becomes `p ∣ 0`.
    rw [h_pow_one, h_sub]
    -- `p ∣ 0` is true for any p.
    apply dvd_zero
  | succ k h_le_k ih_k => -- k : ℕ, h_le_k : 1 ≤ k, ih_k : p ∣ k^p - k
  -- Inductive step: Assume the result holds for k (with h_le_k : 1 ≤ k and ih_k : p ∣ k^p - k), prove it for k + 1.
  -- The goal is `p ∣ (k + 1) ^ p - (k + 1)`.

    -- The inductive hypothesis `ih_k : p ∣ k^p - k` is not directly used in proving the k+1 case;
    -- the proof for k+1 relies on the properties of ZMod p and Fermat's Little Theorem.

    -- We need `k + 1 ≤ (k + 1) ^ p` to use `Nat.modEq_iff_dvd'`.
    -- Since h₁ : Nat.Prime p, we have p ≠ 0.
    have h_le_kp1p : k + 1 ≤ (k + 1) ^ p := by
      -- Use `Nat.le_self_pow {n} (hn_ne_zero : n ≠ 0) (a : ℕ) : a ≤ a ^ n`.
      -- Here, n=p, a=k+1. We need p ≠ 0.
      apply Nat.le_self_pow (Nat.Prime.ne_zero h₁) (k + 1) -- Apply the theorem correctly, passing the proof of p ≠ 0 and the base k+1.

    -- We want to prove `p ∣ (k + 1) ^ p - (k + 1)`.
    -- By `Nat.modEq_iff_dvd' h_le_kp1p` (`a ≤ b → (a ≡ b [MOD n] ↔ n ∣ b - a)`),
    -- proving `p ∣ (k+1)^p - (k+1)` can be done by proving `(k + 1) ≡ (k + 1) ^ p [MOD p]`
    -- (taking a=k+1, b=(k+1)^p, n=p). We use the forward implication `.mp`.
    -- The theorem is `(k + 1) ≡ (k + 1) ^ p [MOD p] → p ∣ (k + 1) ^ p - (k + 1)`.
    -- We apply this implication. The goal `p ∣ (k + 1)^p - (k+1)` unifies with the conclusion,
    -- and the new goal is the premise `(k + 1) ≡ (k + 1) ^ p [MOD p]`.
    -- -- The original code used `.mpr` here, which applies the reverse implication `(n ∣ b - a) → (a ≡ b [MOD n])`. This is incorrect as our goal is `n ∣ b - a`. We need the forward implication `(a ≡ b [MOD n]) → (n ∣ b - a)`, which is `.mp`.
    apply (Nat.modEq_iff_dvd' h_le_kp1p).mp
    -- The goal is now `(k + 1) ≡ (k + 1) ^ p [MOD p]`.

    -- Use symmetry to swap the sides of the modular congruence using `Nat.ModEq.symm`.
    -- The previous `rw [Nat.ModEq.symm_iff]` failed because `rw` expects an equality or iff, and while `Nat.ModEq.symm_iff` is an iff, the tactic seems to have trouble applying it directly here. `apply Nat.ModEq.symm` is the standard way to apply a `modus ponens` style implication like `a ≡ b → b ≡ a`.
    apply Nat.ModEq.symm
    -- The goal is now `(k + 1) ^ p ≡ (k + 1) [MOD p]`.

    -- This modular congruence is equivalent to the equality in `ZMod p` by `ZMod.eq_iff_modEq_nat`.
    -- `(a : ZMod n) = (b : ZMod n) ↔ a ≡ b [MOD n]`.
    -- We want to prove `a ≡ b [MOD n]`, which is the RHS. We apply the reverse implication `.mpr` of the equivalence `(↑a : ZMod n) = ↑b ↔ a ≡ b [MOD n]`. This means `rw [← ZMod.eq_iff_modEq_nat]`.
    -- This changes the goal to `((k + 1) ^ p : ZMod p) = ((k + 1) : ZMod p)`.
    rw [← ZMod.eq_iff_modEq_nat]
    -- The goal is now `(↑((k + 1) ^ p) : ZMod p) = ↑(k + 1)`.

    -- Rewrite the left side `(↑((k + 1) ^ p) : ZMod p)`, which is `Nat.cast ((k + 1) ^ p)`,
    -- using `Nat.cast_pow` (`Nat.cast (m^n) = (Nat.cast m)^n`).
    -- This changes `Nat.cast ((k + 1) ^ p)` to `(Nat.cast (k + 1)) ^ p`.
    rw [Nat.cast_pow]
    -- The goal is now `(↑(k + 1) : ZMod p) ^ p = ↑(k + 1)`.

    -- Introduce the Fact instance needed for ZMod.pow_card from the hypothesis h₁.
    -- The Fact instance for `Nat.Prime p` is needed for the `ZMod.pow_card` theorem,
    -- which is specific to prime moduli.
    -- The `haveI` creates a local instance named `inst`.
    haveI inst : Fact (Nat.Prime p) := Fact.mk h₁

    -- Apply Fermat's Little Theorem for ZMod p: `ZMod.pow_card (y : ZMod p) : y^p = y`.
    -- We rewrite the left side of the goal `(↑(k + 1) : ZMod p) ^ p` using this theorem
    -- with `y = ↑(k + 1) : ZMod p`.
    -- The previous attempt used `exact @ZMod.pow_card p inst x` after a `let x := ↑(k+1)`.
    -- This caused a "type mismatch" error possibly due to issues with `exact` and `let` or explicit arguments.
    -- Using `rw` with the casted term directly is a more robust way to apply the equality.
    -- This changes the goal to `↑(k + 1) = ↑(k + 1)`. This is a reflexivity goal.
    -- In Lean 4, `rw` often solves reflexivity goals automatically.
    rw [ZMod.pow_card (↑(k + 1) : ZMod p)]
    -- The previous line `rfl` is redundant because the `rw` tactic already closed the goal `↑(k + 1) = ↑(k + 1)`.
    -- rfl


#print axioms induction_pprime_pdvdapowpma