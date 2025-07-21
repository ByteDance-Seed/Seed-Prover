import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2021_p8
  (d : ℕ → ℕ)
  (h₀ : d 0 = 0)
  (h₁ : d 1 = 0)
  (h₂ : d 2 = 1)
  (h₃ : ∀ n≥3, d n = d (n - 1) + d (n - 3)) :
  Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023) := by 

  -- Define the parity function p(n) = d(n) % 2 locally within the proof.
  let p (n : ℕ) := d n % 2

  -- 2. Prove the base cases for the parity sequence p.
  have p0 : p 0 = 0 := by simp [p, h₀]
  have p1 : p 1 = 0 := by simp [p, h₁]
  have p2 : p 2 = 1 := by simp [p, h₂]

  -- 3. Prove that p satisfies a similar recurrence relation for n >= 3.
  -- This uses the recurrence relation for d and the property of modulo.
  have p_recurrence (n : ℕ) (hn_ge_3 : n ≥ 3) : p n = (p (n - 1) + p (n - 3)) % 2 := by
    -- Goal: d n % 2 = (d (n-1) % 2 + d (n-3) % 2) % 2
    -- Unfold the definition of p on both sides
    dsimp [p]
    -- Apply the recurrence relation h₃ for d since n >= 3
    rw [h₃ n hn_ge_3]
    -- Apply the property (a + b) % k = (a % k + b % k) % k for modulo 2
    -- This is Nat.add_mod. The goal now exactly matches the conclusion of Nat.add_mod.
    -- -- The message "no goals to be solved" on the previous `simp [Nat.add_mod]` line
    -- -- suggested that the goal was solved directly by the application of Nat.add_mod.
    -- -- Replacing `simp` with a direct `apply` of the lemma is a more explicit way
    -- -- to use the lemma and avoids the specific message reported by `simp`.
    apply Nat.add_mod


  -- Calculate the parities of the first few terms using the recurrence and base cases.
  -- This avoids recalculating them multiple times later in the periodicity proof.
  have p3 : p 3 = 1 := by
    rw [p_recurrence 3 (by norm_num), p2, p0]
    -- The goal is now (p 2 + p 0) % 2 = 1, which is (1 + 0) % 2 = 1, or 1 % 2 = 1, i.e., 1 = 1.
    -- This is definitionally true, so no further tactic is needed.
    -- -- Removed redundant `simp` based on the "no goals to be solved" message.
  have p4 : p 4 = 1 := by
    rw [p_recurrence 4 (by norm_num), p3, p1]
    -- The goal is now (p 3 + p 1) % 2 = 1, which is (1 + 0) % 2 = 1, or 1 % 2 = 1, i.e., 1 = 1.
    -- This is definitionally true, so no further tactic is needed.
    -- -- Removed redundant `simp` based on the same pattern as the previous fix.
  have p5 : p 5 = 0 := by
    rw [p_recurrence 5 (by norm_num), p4, p2]
    -- The goal is now (p 4 + p 2) % 2 = 0, which is (1 + 1) % 2 = 0, or 2 % 2 = 0, i.e., 0 = 0.
    -- This is definitionally true, so no further tactic is needed.
    -- -- Removed redundant `simp` based on the same pattern as the previous fix.
  have p6 : p 6 = 1 := by
    rw [p_recurrence 6 (by norm_num), p5, p3]
    -- The goal is now (p 5 + p 3) % 2 = 1, which is (0 + 1) % 2 = 1, or 1 % 2 = 1, i.e., 1 = 1.
    -- This is definitionally true, so no further tactic is needed.
    -- -- Removed redundant `simp` based on the same pattern as the previous fix.
  have p7 : p 7 = 0 := by
    rw [p_recurrence 7 (by norm_num), p6, p4]
    -- The goal is now (p 6 + p 4) % 2 = 0, which is (1 + 1) % 2 = 0, or 2 % 2 = 0, i.e., 0 = 0.
    -- This is definitionally true, so no further tactic is needed.
    -- -- Removed redundant `simp` based on the same pattern as the previous fix.

  -- 4. Prove p is periodic with period 7.
  -- We demonstrate that the sequence of parities repeats every 7 terms.
  -- This lemma was previously defined outside the `by` block using `lemma`,
  -- which caused the "function expected" error because `p` was not in scope there.
  -- We now define and prove it using `have` inside the `by` block.
  have p_period_7 (n : ℕ) : p (n + 7) = p n := by
    -- Use strong induction on n
    -- The goal here is `∀ (n : ℕ), p (n + 7) = p n`.
    -- The `induction` tactic handles the introduction of the variable `n`.
    induction n using Nat.strongInductionOn with
    | ind n ih => -- Inductive step: Assume P m for all m < n, prove p (n+7) = p n.
      -- Split n into cases: 0, 1, 2, and >= 3 to handle small values explicitly
      -- before relying on the recurrence relation.
      -- The error "invalid alternative name 'k'" occurred because `cases k` was used immediately after `| k ih =>`.
      -- The variable `n` is already introduced by the induction. We just need to case on `n`.
      -- -- Removed redundant `cases k` line.
      cases n -- -- Corrected from `cases n with` to use dot notation for alternatives.
      . case zero => -- Case n = 0. Prove p 7 = p 0.
        -- Use the pre-calculated values p7 and p0.
        -- The goal is p (0+7) = p 0.
        -- -- Removed redundant simp based on the error message and hint.
        rw [p7, p0] -- Use p7 : p 7 = 0 and p0 : p 0 = 0. Goal: 0 = 0.
        -- The goal is now 0 = 0, which is definitionally true.
        -- -- The previous `rfl` tactic was redundant as the goal was already solved definitionally.
      . case succ n₀ => -- Case n = succ n₀ (n > 0). Use n₀ for the predecessor.
        -- Now we have n₀ and ih is available for m < succ n₀ (i.e., m <= n₀).
        -- We need to further case split on n₀ to handle n=1, n=2, n>=3 (i.e., n₀=0, n₀=1, n₀>=2)
        cases n₀ -- -- Corrected from `cases n₀ with` to use dot notation for alternatives.
        . case zero => -- Case n₀ = 0, so n = succ 0 = 1
          -- Prove p 8 = p 1.
          -- Calculate p 8 using recurrence and pre-calculated values.
          -- Note: n = 1, so we need p(1+7) = p(8). Since 8 ≥ 3, p(8) = (p(8 - 1) + p(8 - 3)) % 2 = (p(7) + p(5)) % 2.
          -- We have p7 = 0, p5 = 0. So p(8) = (0+0)%2 = 0.
          have p8_val : p 8 = 0 := by
            rw [p_recurrence 8 (by norm_num)] -- 8 ≥ 3 is true.
            rw [p7, p5]                     -- Use pre-calculated p7=0, p5=0.
            -- After the rewrites, the goal is (0 + 0) % 2 = 0, which is 0 = 0.
            -- The goal is definitionally equal to `0 = 0`, which is solved by definitional equality.
            -- -- The previous `simp` tactic here was causing the "no goals to be solved" error. It is redundant because the goal becomes definitionally equal after the rewrites.
            -- Removed the redundant simp tactic as indicated by the error message.
            -- The message "no goals to be solved" refers to this `rfl` tactic.
            -- It is redundant because the goal (0+0)%2 = 0 is definitionally equal to 0 = 0 after the rewrites.
            -- Removed the redundant `rfl` tactic.
          -- Goal: p 8 = p 1. Replace p 8 and p 1 with their values.
          rw [p8_val, p1]
        . case succ n₁ => -- Case n₀ = succ n₁, so n = succ (succ n₁), n >= 2. Use n₁ for the predecessor of n₀.
          -- Now we have n₁ and ih is available for m < succ (succ n₁) (i.e., m <= succ n₁).
          -- We need to further case split on n₁ to handle n=2, n>=3 (i.e., n₁=0, n₁>=1)
          cases n₁ -- -- Corrected from `cases n₁ with` to use dot notation for alternatives.
          . case zero => -- Case n₁ = 0, so n₀ = 1, n = 2
            -- Prove p 9 = p 2.
            -- Calculate p 9 using recurrence and pre-calculated values.
            -- Note: n = 2, we need p(2+7) = p(9). Since 9 ≥ 3, p(9) = (p(9 - 1) + p(9 - 3)) % 2 = (p(8) + p(6)) % 2.
            -- We need p 8. Use the one from the n=1 case above (p8_val).
            have p8_val : p 8 = 0 := by -- This proof is repeated, but it's okay within `have`.
              rw [p_recurrence 8 (by norm_num), p7, p5]
              -- After the rewrites, the goal is (0 + 0) % 2 = 0, which is 0 = 0.
              -- The goal is definitionally equal to `0 = 0`, which is solved by definitional equality.
              -- Removed redundant rfl based on the "no goals to be solved" message and hint.
              -- The previous `simp` tactic here was causing the "no goals to be solved" error. It is redundant because the goal becomes definitionally equal after the rewrites.
              -- Removed the redundant simp tactic as indicated by the error message.
              -- The message "no goals to be solved" refers to this `rfl` tactic.
              -- It is redundant because the goal (0+0)%2 = 0 is definitionally equal to 0 = 0 after the rewrites.
              -- Removed the redundant `rfl` tactic.
            -- We have p 6 = 1.
            have p9_val : p 9 = 1 := by
              rw [p_recurrence 9 (by norm_num)] -- 9 ≥ 3 is true.
              rw [p8_val, p6] -- Use p8=0, p6=1.
              -- The goal is (0 + 1) % 2 = 1, which is 1 = 1.
              -- The goal is definitionally equal to `1 = 1`.
              -- The previous `simp` tactic here was causing the "no goals to be solved" error. It is redundant because the goal becomes definitionally equal after the rewrites.
              -- Removed the redundant simp tactic as indicated by the error message.
              -- The goal (0 + 1) % 2 = 1 is definitionally 1 = 1, so no tactics are needed.
              -- Removed the redundant `done` tactic.
            -- Goal: p 9 = p 2. Replace p 9 and p 2 with their values.
            rw [p9_val, p2]
          . case succ n₂ => -- Case n₁ = succ n₂, so n₀ = succ (succ n₂), n = succ (succ (succ n₂)) = n₂ + 3.
            -- Case n = n₂ + 3, so n >= 3. This is the general inductive step.
            -- Goal: p ((n₂ + 3) + 7) = p (n₂ + 3)  => p (n₂ + 10) = p (n₂ + 3)

            -- Apply the recursive definition of p using p_recurrence for both sides.
            -- n₂+10 ≥ 0+10 = 10 ≥ 3 is true.
            -- n₂+3 ≥ 0+3 = 3 ≥ 3 is true.
            have h_n₂_plus_3_ge_3 : n₂ + 3 ≥ 3 := by omega
            have h_n₂_plus_10_ge_3 : n₂ + 10 ≥ 3 := by omega
            rw [p_recurrence (n₂ + 10) h_n₂_plus_10_ge_3, p_recurrence (n₂ + 3) h_n₂_plus_3_ge_3]
            -- Goal: (p (n₂ + 10 - 1) + p (n₂ + 10 - 3)) % 2 = (p (n₂ + 3 - 1) + p (n₂ + 3 - 3)) % 2

            -- Apply the induction hypothesis (ih). ih : (m : ℕ) → m < n → p (m+7) = p m.
            -- Here n = n₂ + 3.
            -- We need ih for m = n₂ + 2 (since n₂ + 2 < n₂ + 3 is true for n₂ ≥ 0).
            have h_n₂_plus_2_lt_n : n₂ + 2 < n₂ + 3 := by omega
            have ih_n_minus_1 := ih (n₂ + 2) h_n₂_plus_2_lt_n -- Gives p ((n₂+2)+7) = p (n₂+2), i.e. p (n₂+9) = p (n₂+2).

            -- We need ih for m = n₂ (since n₂ < n₂ + 3 is true for n₂ ≥ 0).
            have h_n₂_lt_n : n₂ < n₂ + 3 := by omega
            have ih_n_minus_3 := ih n₂ h_n₂_lt_n -- Gives p (n₂+7) = p n₂.

            -- Simplify the arguments of p in the goal using arithmetic.
            -- The rewrite tactic failed because the arguments (like n₂+10-1) were not simplified
            -- to match the patterns in the hypotheses (like n₂+9).
            simp
            -- Goal is now (p (n₂ + 9) + p (n₂ + 7)) % 2 = (p (n₂ + 2) + p n₂) % 2

            -- Apply the induction hypotheses as rewrites.
            rw [ih_n_minus_1, ih_n_minus_3]
            -- Goal is now (p (n₂ + 2) + p n₂) % 2 = (p (n₂ + 2) + p n₂) % 2, which is trivial.
            -- The previous `rfl` tactic was redundant as the goal was already solved definitionally after the rewrites.


  -- 5. Prove p a = p (a % 7) for any a : ℕ using the periodicity.
  -- This lemma was also previously defined outside using `lemma`, causing an error.
  -- We now define and prove it using `have` inside the `by` block.
  have p_periodic_at (a : ℕ) : p a = p (a % 7) := by
    -- Prove p (b * 7 + r) = p r for any b r : ℕ by induction on b, the multiplier of the period 7.
    have p_add_mul_period (b r : ℕ) : p (b * 7 + r) = p r := by
      induction b with
      | zero =>
        -- Base case: b = 0. Goal: p (0 * 7 + r) = p r.
        -- Add simp to simplify 0 * 7 + r to r. The goal becomes p r = p r, which simp solves.
        simp
      | succ b ih =>
        -- Induction step: Assume p (b * 7 + r) = p r (induction hypothesis ih).
        -- Goal: p ((b + 1) * 7 + r) = p r.
        -- Rearrange ((b + 1) * 7 + r) to the form (X + 7) to use p_period_7.
        rw [Nat.add_comm b 1]
        rw [Nat.add_mul 1 b 7]
        rw [one_mul (7 : ℕ)]
        rw [Nat.add_assoc 7 (b * 7) r]
        rw [Nat.add_comm 7 (b * 7 + r)]
        -- Apply the periodicity property p_period_7: p (X + 7) = p X.
        rw [p_period_7 (b * 7 + r)] -- p ((b*7+r) + 7) = p (b*7+r)
        -- The goal is now p (b * 7 + r) = p r, which is exactly the induction hypothesis (ih).
        exact ih

    -- Use Nat.div_add_mod to relate a and (a / 7) * 7 + a % 7.
    -- This allows us to write a as quotient*7 + remainder.
    have h_eq : a = (a / 7) * 7 + a % 7 := by
      -- We want to show a = (a / 7) * 7 + a % 7.
      -- The theorem Nat.div_add_mod a 7 gives us 7 * (a / 7) + a % 7 = a.
      -- We use the theorem Nat.div_add_mod a 7 and reverse the equality using Eq.symm.
      -- -- The Nat.div_add_mod theorem gives the equality in the form RHS = LHS.
      -- -- We need it in the form LHS = RHS, so we use Eq.symm.
      have h_div_add_mod : a = 7 * (a / 7) + a % 7 := (Nat.div_add_mod a 7).symm
      -- Now rewrite the multiplication order in the first term on the RHS of h_div_add_mod.
      -- We rewrite 7 * (a / 7) to (a / 7) * 7 using the commutativity of multiplication for natural numbers.
      rw [Nat.mul_comm 7 (a / 7)] at h_div_add_mod
      -- The hypothesis h_div_add_mod is now a = (a / 7) * 7 + a % 7, which is the goal.
      exact h_div_add_mod

    -- Apply p_add_mul_period with b = a / 7 and r = a % 7.
    have h_period_applied : p ((a / 7) * 7 + a % 7) = p (a % 7) := p_add_mul_period (a / 7) (a % 7)

    -- Rewrite the left side of this equality using h_eq (rewriting from the RHS of h_eq to the LHS).
    -- The goal is p a = p (a % 7).
    -- We need to rewrite the LHS of h_period_applied, which is `(a / 7) * 7 + a % 7` to `a`.
    -- h_eq is `a = (a / 7) * 7 + a % 7`. We need to rewrite from RHS to LHS.
    rw [← h_eq] at h_period_applied -- Use ← h_eq to rewrite the RHS `(a / 7) * 7 + a % 7` to the LHS `a` in the hypothesis `h_period_applied`.

    -- The resulting hypothesis `h_period_applied` is now `p a = p (a % 7)`.
    -- This is exactly the goal.
    exact h_period_applied


  -- 6. Calculate the remainders when 2021, 2022, 2023 are divided by 7.
  -- We use norm_num to compute these simple arithmetic values.
  have rem2021 : 2021 % 7 = 5 := by norm_num
  have rem2022 : 2022 % 7 = 6 := by norm_num
  have rem2023 : 2023 % 7 = 0 := by norm_num

  -- 7. Calculate the parities of d(2021), d(2022), d(2023) using periodicity.
  have d2021_mod_2 : d 2021 % 2 = 0 := by
    -- The goal is d 2021 % 2 = 0. We use `change` to make it explicitly `p 2021 = 0`.
    change p 2021 = 0
    -- p 2021 = p (2021 % 7) (by periodicity lemma p_periodic_at)
    rw [p_periodic_at 2021]
    -- 2021 % 7 = 5 (by calculation rem2021)
    rw [rem2021]
    -- p 5 = 0 (by pre-calculation p5)
    rw [p5]

  have d2022_mod_2 : d 2022 % 2 = 1 := by
    -- The goal is d 2022 % 2 = 1. We use `change` to make it explicitly `p 2022 = 1`.
    change p 2022 = 1
    -- p 2022 = p (2022 % 7)
    rw [p_periodic_at 2022]
    -- 2022 % 7 = 6
    rw [rem2022]
    -- p 6 = 1 (by pre-calculation p6)
    rw [p6]

  have d2023_mod_2 : d 2023 % 2 = 0 := by
    -- The goal is d 2023 % 2 = 0. We use `change` to make it explicitly `p 2023 = 0`.
    change p 2023 = 0
    -- p 2023 = p (2023 % 7)
    rw [p_periodic_at 2023]
    -- 2023 % 7 = 0
    rw [rem2023]
    -- p 0 = 0 (by pre-calculation p0)
    rw [p0]

  -- 8. Combine the results to prove the final conjunction.
  -- The goal is Even (d 2021) ∧ Odd (d 2022) ∧ Even (d 2023).
  -- We use the definitions of Even and Odd in terms of modulo 2 results.

  -- Split the main goal into three parts.
  apply And.intro
  . -- Prove the first part: Even (d 2021)
    -- We know d 2021 % 2 = 0 from d2021_mod_2.
    -- We use the equivalence theorem Nat.even_iff {n} : Even n ↔ n % 2 = 0.
    rw [Nat.even_iff]
    -- The goal is now d 2021 % 2 = 0.
    -- Provide the hypothesis d 2021 % 2 = 0.
    exact d2021_mod_2
  . -- The remaining goal is Odd (d 2022) ∧ Even (d 2023). Split this conjunction.
    apply And.intro
    . -- Prove the second part: Odd (d 2022)
      -- We know d 2022 % 2 = 1 from d2022_mod_2.
      -- We use the equivalence theorem Nat.odd_iff {n} : Odd n ↔ Odd n ↔ n % 2 = 1.
      -- Apply the reverse direction (mpr) of the iff to prove `Odd (d 2022)` from `d 2022 % 2 = 1`.
      apply (Nat.odd_iff).mpr
      -- The goal is now d 2022 % 2 = 1.
      -- Provide the hypothesis d 2022 % 2 = 1.
      exact d2022_mod_2
    . -- Now the goal is the third part: Even (d 2023).
      -- We know d 2023 % 2 = 0 from d2023_mod_2.
      rw [Nat.even_iff]
      -- The goal is now d 2023 % 2 = 0.
      -- Provide the hypothesis d 2023 % 2 = 0.
      exact d2023_mod_2

#print axioms amc12a_2021_p8
