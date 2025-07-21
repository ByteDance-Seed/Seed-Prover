import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 := by 

  -- Define the sequence n_k = 84 + 5k. This was used implicitly before but needs a formal definition.
  let n_k (k : ℕ) : ℤ := 84 + 5 * k
  -- Define the property P(k) that we will prove by decreasing induction. This was used implicitly before but needs a formal definition.
  -- P(k) is (n_k k < 1000) → (if k % 2 = 0 then f (n_k k) = 997 else f (n_k k) = 998)
  let P (f : ℤ → ℤ) (k : ℕ) : Prop := (n_k k : ℤ) < 1000 → (if k % 2 = 0 then f (n_k k) = 997 else f (n_k k) = 998)

  -- Let n_k = 84 + 5k. We want to evaluate f(n_0) = f(84).
  -- The rule h₁ applies when n < 1000.
  -- The sequence 84, 89, 94, ..., eventually reaches values >= 1000.
  -- We need k such that 84 + 5k >= 1000. 5k >= 916, k >= 183.2.
  -- The maximum k such that 84 + 5k < 1000 is k = 183 (84 + 5*183 = 999).
  -- We use downward induction on k from 183 down to 0 for the expression f(84 + 5k).


  -- Define helper lemmas for the values of f at numbers around 1000 using h₀ and h₁
  have f_1000_val : f 1000 = 997 := by
    -- The condition 1000 ≤ 1000 is required for h₀.
    have h : (1000 : ℤ) ≥ 1000 := by simp
    simp [h₀ 1000 h]

  have f_1001_val : f 1001 = 998 := by
    -- The condition 1000 ≤ 1001 is required for h₀.
    have h : (1001 : ℤ) ≥ 1000 := by simp
    simp [h₀ 1001 h]

  have f_1002_val : f 1002 = 999 := by
    -- The condition 1000 ≤ 1002 is required for h₀.
    have h : (1002 : ℤ) ≥ 1000 := by simp
    simp [h₀ 1002 h]

  have f_1003_val : f 1003 = 1000 := by
    -- The condition 1000 ≤ 1003 is required for h₀.
    have h : (1003 : ℤ) ≥ 1000 := by simp
    simp [h₀ 1003 h]

  have f_1004_val : f 1004 = 1001 := by
    -- The condition 1000 ≤ 1004 is required for h₀.
    have h : (1004 : ℤ) ≥ 1000 := by simp
    simp [h₀ 1004 h]

  -- Calculate f(999) using h₁ and the values above
  have f_999_val : f 999 = 998 := by
    -- The condition 999 < 1000 is required for h₁.
    have h_999_lt_1000 : (999 : ℤ) < 1000 := by simp
    -- f(999) = f(f(999 + 5)) by h₁
    have f_999_step1 : f 999 = f (f (999 + 5)) := h₁ 999 h_999_lt_1000
    -- Simplify 999 + 5 to 1004 in the hypothesis f_999_step1
    -- Explicitly type the numbers as `ℤ` to ensure the rewrite applies to the integer addition.
    have h_add : (999 : ℤ) + (5 : ℤ) = (1004 : ℤ) := by simp
    rw [h_add] at f_999_step1 -- f 999 = f (f 1004)
    rw [f_1004_val] at f_999_step1 -- f 999 = f 1001
    rw [f_1001_val] at f_999_step1 -- f 999 = 998
    exact f_999_step1

  -- Calculate f(998) using h₁ and the values above
  have f_998_val : f 998 = 997 := by
    -- The condition 998 < 1000 is required for h₁.
    have h_998_lt_1000 : (998 : ℤ) < 1000 := by simp
    -- f(998) = f(f(998 + 5)) by h₁
    have f_998_step1 : f 998 = f (f (998 + 5)) := h₁ 998 h_998_lt_1000
    -- Simplify 998 + 5 to 1003 in the hypothesis f_998_step1
    -- Explicitly type the numbers as `ℤ` to ensure the integer addition is performed.
    have h_add : (998 : ℤ) + (5 : ℤ) = (1003 : ℤ) := by simp
    rw [h_add] at f_998_step1 -- f 998 = f (f 1003)
    rw [f_1003_val] at f_998_step1 -- f 998 = f 1000
    rw [f_1000_val] at f_998_step1 -- f 998 = 997
    exact f_998_step1

  -- Calculate f(997) using h₁ and the values above
  -- The previous lemma declaration had the wrong result (f 997 = 997 instead of 998). Correcting the declaration.
  have f_997_val : f 997 = 998 := by
    -- The condition 997 < 1000 is required for h₁.
    have h_997_lt_1000 : (997 : ℤ) < 1000 := by simp
    -- f(997) = f(f(997 + 5)) by h₁
    have f_997_step1 : f 997 = f (f (997 + 5)) := h₁ 997 h_997_lt_1000
    -- Simplify 997 + 5 to 1002 in the hypothesis f_997_step1
    -- Explicitly type the numbers as `ℤ` to ensure the integer addition is performed.
    have h_add : (997 : ℤ) + (5 : ℤ) = (1002 : ℤ) := by simp
    rw [h_add] at f_997_step1 -- f 997 = f (f 1002)
    rw [f_1002_val] at f_997_step1 -- f 997 = f 999
    rw [f_999_val] at f_997_step1 -- f 997 = 998
    exact f_997_step1

  -- Prove the base case of the downward induction: P(183)
  -- Correcting the reference to P to include f as an argument.
  have P_183_proof : P f 183 := by
    -- The goal is P f 183, which is (n_k 183 : ℤ) < 1000 → (if 183 % 2 = 0 then f (n_k 183) = 997 else f (n_k 183) = 998).
    -- We remove the `unfold P` step as it caused an error and is not strictly necessary for `intro` to work on the implication.
    -- unfold P
    -- P f 183 is n_k 183 < 1000 -> (if 183 % 2 = 0 then f (n_k 183) = 997 else f (n_k 183) = 998)
    -- We introduce the premise of the implication as a hypothesis.
    intro h_183_lt_1000
    -- The goal is (if 183 % 2 = 0 then f (n_k 183) = 997 else f (n_k 183) = 998)
    -- Calculate n_k 183 = 84 + 5 * 183 = 84 + 915 = 999.
    -- `simp [n_k]` now works because n_k is a formal definition.
    have h_nk_183_val : n_k 183 = 999 := by simp [n_k]
    rw [h_nk_183_val] -- Goal: (if 183 % 2 = 0 then f 999 = 997 else f 999 = 998)
    -- Evaluate 183 % 2. It is 1.
    -- So the goal becomes (if 1 = 0 then f 999 = 997 else f 999 = 998) which simplifies to f 999 = 998.
    -- The evaluation of the `if` condition and the branches happens automatically.
    simp
    -- Goal is f 999 = 998
    exact f_999_val

  -- Prove the inductive step for downward induction: P(k+1) → P(k) for 0 <= k < 183
  -- We define this as a separate lemma proof.
  -- The type signature is adjusted to fit Nat.decreasingInduction', which requires m ≤ k < n for the step.
  -- For Nat.decreasingInduction' {m n} {P} (step : ∀ k, k < n → m ≤ k → P (k + 1) → P k) (hle : m ≤ n) (base : P n) : P m
  -- With m=0, n=183, the step requires ∀ k, k < 183 → 0 ≤ k → P (k + 1) → P k.
  -- Since k is Nat, 0 ≤ k is automatic. Explicitly adding it to the type signature is needed for type matching with `Nat.decreasingInduction'`.
  -- Correcting the type signature of the step to use P f.
  have proof_step : ∀ (k : ℕ), k < 183 → 0 ≤ k → P f (k + 1) → P f k := by
    intros k hk_lt_n hk_ge_0 -- Inductive step for k < 183. hk_ge_0 is trivial for k : ℕ.
    intro h_kp1 -- Inductive hypothesis: P f (k+1) is assumed
    intro hk_lt_1000 -- Premise of P f k: n_k k < 1000 is assumed

    -- We need to prove the conclusion of P f k: (if k % 2 = 0 then f (n_k k) = 997 else f (n_k k) = 998)

    -- Use the assumption n_k k < 1000 (hk_lt_1000) and h₁
    -- Apply h₁ using the value of n_k k, which is an integer.
    have fnk_rule : f (n_k k) = f (f ((n_k k) + 5)) := h₁ (n_k k) hk_lt_1000

    -- Simplify n_k k + 5 to n_k (k + 1)
    -- n_k k + 5 = (84 + 5k) + 5 = 84 + 5k + 5 = 84 + 5(k + 1) = n_k (k + 1)
    -- `simp [n_k]` now works because n_k is a formal definition.
    have h_nk_add_5 : (n_k k : ℤ) + (5 : ℤ) = n_k (k + 1) := by simp [n_k]; ring
    rw [h_nk_add_5] at fnk_rule -- f (n_k k) = f (f (n_k (k + 1)))

    -- To use the inductive hypothesis h_kp1 : P f (k+1), we need to show its premise: n_k (k + 1) < 1000
    -- We have the hypothesis `hk_lt_n : k < 183` from the decreasing induction.
    -- From k < 183, we get k ≤ 182.
    have h_k_le_182 : k ≤ 182 := Nat.le_of_lt_succ hk_lt_n
    -- From k ≤ 182, adding 1 gives k + 1 ≤ 183.
    have h_k_plus_1_le_183 : k + 1 ≤ 183 := Nat.succ_le_succ h_k_le_182

    -- Show that n_k (k + 1) < 1000.
    -- Expand n_k (k + 1)
    -- `simp [n_k]` now works because n_k is a formal definition.
    have h_nk_k_plus_1_val : n_k (k + 1) = (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ) := by simp [n_k]
    have h_nk_k_plus_1_lt_1000 : (n_k (k + 1) : ℤ) < 1000 := by
      rw [h_nk_k_plus_1_val]
      -- Goal: (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ) < 1000
      -- Use h_k_plus_1_le_183 : k + 1 ≤ 183 (Nat)
      -- Cast to Int: (k + 1 : ℤ) ≤ (183 : ℤ)
      have h_k_plus_1_int_le_183_int : (↑(k + 1) : ℤ) ≤ (↑(183) : ℤ) := by exact Nat.cast_le.mpr h_k_plus_1_le_183
      -- Multiply by 5: (5 : ℤ) * (k + 1 : ℤ) ≤ (5 : ℤ) * (183 : ℤ)
      have five_pos : (5 : ℤ) ≥ 0 := by norm_num
      have h_5_mul_kp1_le : (5 : ℤ) * (↑(k + 1) : ℤ) ≤ (5 : ℤ) * (↑(183) : ℤ) := by linarith [h_k_plus_1_int_le_183_int, five_pos]

      -- Now prove the final inequality: (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ) < 1000
      -- We know (5 : ℤ) * (↑(k + 1) : ℤ) ≤ (5 : ℤ) * (↑(183) : ℤ) = 915
      -- So (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ) ≤ (84 : ℤ) + 915 = 999
      -- And 999 < 1000
      have h_84_plus_5_183_val : (84 : ℤ) + (5 : ℤ) * (↑(183) : ℤ) = 999 := by simp
      have h_999_lt_1000' : (999 : ℤ) < 1000 := by simp

      -- Use linarith to combine the inequalities: A ≤ B and B < C implies A < C.
      -- Here A = (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ)
      -- B = (84 : ℤ) + (5 : ℤ) * (↑(183) : ℤ)
      -- C = 1000
      -- We need to show A ≤ B from h_5_mul_kp1_le. Adding 84 to both sides is a linear step linarith can do.
      have h_add_84_le : (84 : ℤ) + (5 : ℤ) * (↑(k + 1) : ℤ) ≤ (84 : ℤ) + (5 : ℤ) * (↑(183) : ℤ) := by linarith [h_5_mul_kp1_le]
      -- Now use A ≤ B, B = 999, 999 < 1000 in linarith.
      linarith [h_add_84_le, h_84_plus_5_183_val, h_999_lt_1000']

    -- Apply the inductive hypothesis h_kp1 : P f (k+1), which is `n_k (k + 1) < 1000 → (if (k + 1) % 2 = 0 then f (n_k (k + 1)) = 997 else f (n_k (k + 1)) = 998)`
    -- Apply the inductive hypothesis h_kp1.
    -- We already proved the premise `h_nk_k_plus_1_lt_1000`.
    have ih_result_prop := h_kp1 h_nk_k_plus_1_lt_1000

    -- We need to show the conclusion of P f k, which depends on the parity of k.
    have k_parity := Nat.even_or_odd k

    cases k_parity with
    | inl hk_even => -- k is even (hk_even : Even k)
      -- Goal: if k % 2 = 0 then f (n_k k) = 997 else f (n_k k) = 998
      -- We know k is even (hk_even).
      have h_k_mod_2_eq_0 : k % 2 = 0 := Nat.even_iff.mp hk_even
      -- Simplify the goal using k % 2 = 0
      rw [if_pos h_k_mod_2_eq_0]
      -- Goal is now f (n_k k) = 997.

      -- Use Nat.succ_mod_two_eq_one_iff to show (k+1)%2 = 1 from k%2=0.
      have k_plus_1_mod_2_eq_1 : (k + 1) % 2 = 1 := Nat.succ_mod_two_eq_one_iff.mpr h_k_mod_2_eq_0
      -- By IH result (ih_result_prop), since (k+1)%2=1, we have f(n_k(k+1)) = 998
      -- Apply the IH result `ih_result_prop` and simplify the `if` using `k_plus_1_mod_2_eq_1`.
      -- The if condition (k + 1) % 2 = 0 is false (since it's 1=0), so the `else` branch is taken.
      have h_f_nk_k_plus_1 : f (n_k (k + 1)) = 998 := by
        simp only [k_plus_1_mod_2_eq_1] at ih_result_prop -- The if condition in ih_result_prop becomes 1 = 0, which is false.
        -- The previous line `simp only [Nat.zero_ne_one.symm]` was redundant as simp can deduce 1=0 is false without it.
        simp only [if_false] at ih_result_prop -- The if simplifies to the else branch using `if_false` because the condition `1=0` is false.
        exact ih_result_prop

      -- We have f (n_k k) = f (f (n_k (k + 1))) (fnk_rule) and h_f_nk_k_plus_1 : f (n_k (k + 1)) = 998
      -- Derive f(n_k k) = f 998
      have h_f_nk_k_eq_f_998 : f (n_k k) = f 998 := by rw [fnk_rule, h_f_nk_k_plus_1]

      -- We have h_f_nk_k_eq_f_998 : f (n_k k) = f 998 and f_998_val : f 998 = 997
      -- Derive f(n_k k) = 997
      have h_f_nk_k_eq_997 : f (n_k k) = 997 := by rw [h_f_nk_k_eq_f_998, f_998_val]

      -- The current goal is f (n_k k) = 997. We have h_f_nk_k_eq_997 proving it.
      exact h_f_nk_k_eq_997

    | inr hk_odd => -- k is odd (hk_odd : Odd k)
      -- Goal: if k % 2 = 0 then f (n_k k) = 997 else f (n_k k) = 998
      -- We know k is odd (hk_odd).
      have h_k_mod_2_eq_1 : k % 2 = 1 := Nat.odd_iff.mp hk_odd
      -- Prove ¬ (k % 2 = 0) from k % 2 = 1
      have h_k_mod_2_ne_0 : ¬ (k % 2 = 0) := by
        intro contra
        rw [h_k_mod_2_eq_1] at contra
        simp at contra

      -- Simplify the goal using ¬ (k % 2 = 0).
      rw [if_neg h_k_mod_2_ne_0]
      -- Goal is now f (n_k k) = 998.

      -- Use Nat.succ_mod_two_eq_zero_iff to show (k+1)%2 = 0 from k%2=1.
      have k_plus_1_mod_2_eq_0 : (k + 1) % 2 = 0 := Nat.succ_mod_two_eq_zero_iff.mpr h_k_mod_2_eq_1
      -- By IH result (ih_result_prop), since (k+1)%2=0, we have f(n_k(k+1)) = 997
      -- Apply the IH result `ih_result_prop` and simplify the `if` using `k_plus_1_mod_2_eq_0`.
      -- The if condition (k + 1) % 2 = 0 is true (since it's 0=0), so the `then` branch is taken.
      have h_f_nk_k_plus_1 : f (n_k (k + 1)) = 997 := by
        simp only [k_plus_1_mod_2_eq_0] at ih_result_prop -- The if condition in ih_result_prop becomes 0 = 0, which is true.
        simp only [if_true] at ih_result_prop -- The if simplifies to the then branch.
        exact ih_result_prop

      -- We have f (n_k k) = f (f (n_k (k + 1))) (fnk_rule) and h_f_nk_k_plus_1 : f (n_k (k + 1)) = 997
      -- Derive f(n_k k) = f 997
      have h_f_nk_k_eq_f_997 : f (n_k k) = f 997 := by rw [fnk_rule, h_f_nk_k_plus_1]

      -- We have h_f_nk_k_eq_f_997 : f (n_k k) = f 997 and f_997_val : f 997 = 998
      -- Derive f(n_k k) = 998
      have h_f_nk_k_eq_998 : f (n_k k) = 998 := by rw [h_f_nk_k_eq_f_997, f_997_val]
      exact h_f_nk_k_eq_998

  -- Use Nat.decreasingInduction' from n=183 down to m=0 to prove P f 0.
  -- The previous attempt using `Nat.decreasingInduction` caused a type mismatch because its step function
  -- expects a different type signature than `proof_step`.
  -- We change to `Nat.decreasingInduction'` which matches the type signature of `proof_step`.
  -- The arguments are the step (proof_step), the range condition (0 <= 183), and the base case (P f 183).
  have h_P_0 : P f 0 := Nat.decreasingInduction' (m := 0) (n := 183) (P := P f) proof_step (by norm_num) P_183_proof

  -- Now use P f 0 (h_P_0) to prove the main goal f 84 = 997.
  -- P f 0 is n_k 0 < 1000 → (if 0 % 2 = 0 then f (n_k 0) = 997 else f (n_k 0) = 998)
  -- The goal is f 84 = 997

  -- Apply P f 0 (h_P_0) to prove the conclusion of P f 0.
  -- P f 0 is an implication, so applying it means proving its premise: n_k 0 < 1000.
  -- `n_k` is now a known identifier because it was defined outside the tactic block.
  have h_concl_P0_if : (if 0 % 2 = 0 then f (n_k 0) = 997 else f (n_k 0) = 998) := by
    -- Apply the lemma h_P_0 which is P f 0
    apply h_P_0
    -- The subgoal is the premise of P f 0: n_k 0 < 1000.
    -- Expand n_k 0 using its definition.
    simp only [n_k] -- n_k 0 = 84 + 5*0 = 84
    -- Goal: (84 : ℤ) < 1000
    -- Prove the numerical inequality using norm_num.
    norm_num

  -- The condition 0 % 2 = 0 is true.
  have h_0_even : 0 % 2 = 0 := by simp

  -- Simplify the if statement based on the true condition (0 % 2 = 0).
  -- The statement becomes `f (n_k 0) = 997`.
  have h_concl_P0 : f (n_k 0) = 997 := by simp [h_0_even] at h_concl_P0_if; exact h_concl_P0_if

  -- We have h_concl_P0 : f (n_k 0) = 997.
  -- We want to prove f 84 = 997.
  -- Simplify f (n_k 0) to f 84 using the definition of n_k.
  -- Need to unfold n_k applied to 0.
  -- Using simp [n_k] should simplify n_k 0.
  simp only [n_k] at h_concl_P0 -- f (84 + 5 * 0) = 997 becomes f 84 = 997

  -- The goal is f 84 = 997. We have h_concl_P0 proving it.
  exact h_concl_P0


#print axioms aime_1984_p7