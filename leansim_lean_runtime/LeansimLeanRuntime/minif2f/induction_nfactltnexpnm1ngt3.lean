import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem induction_nfactltnexpnm1ngt3
  (n  : ℕ)
  (h₀ : 3 ≤ n) :
  (n) ! < n^(n - 1)  := by
  letI P1 := ∏ k ∈ Finset.Icc 3 n, k
  retro' P1_def : P1 = ∏ k ∈ Finset.Icc (3 : ℕ) n, k := by funext; rfl
  have subprob_nfact_eq_P1_mul_2_proof : Nat.factorial n = P1 * 2 := by
    mkOpaque
    rw [P1_def]
    have h_icc_eq_ico : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext x
      rw [Finset.mem_Icc, Finset.mem_Ico]
      constructor
      . intro h_le_n
        cases h_le_n with
        | intro h1x hxn =>
          constructor
          . exact h1x
          . exact Nat.lt_succ_of_le hxn
      . intro h_lt_succ_n
        cases h_lt_succ_n with
        | intro h1x hlt =>
          constructor
          . exact h1x
          . exact Nat.le_of_lt_succ hlt
    have h_prod_icc_eq_ico : ∏ k ∈ Finset.Icc 1 n, k = ∏ k ∈ Finset.Ico 1 (n + 1), k := by rw [h_icc_eq_ico]
    have h_prod_ico_eq_fact : ∏ k ∈ Finset.Ico 1 (n + 1), k = n.factorial := Finset.prod_Ico_id_eq_factorial n
    have h_prod_icc_eq_fact : ∏ k ∈ Finset.Icc 1 n, k = n.factorial := by rw [h_prod_icc_eq_ico, h_prod_ico_eq_fact]
    rw [h_prod_icc_eq_fact.symm]
    have h_union : Finset.Icc 1 2 ∪ Finset.Icc 3 n = Finset.Icc 1 n := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      . intro h
        cases h with
        | inl h_le_2 =>
          cases h_le_2 with
          | intro h1x hx2 =>
            constructor
            . exact h1x
            . omega
        | inr h_ge_3 =>
          cases h_ge_3 with
          | intro h3x hxn =>
            constructor
            . omega
            . exact hxn
      . intro h
        cases h with
        | intro h1x hxn =>
          by_cases hx2 : x ≤ 2
          . left
            constructor; exact h1x; exact hx2
          . right
            constructor
            . omega
            . exact hxn
    have h_disjoint : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 n) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_Icc] at hb
      cases ha; cases hb
      linarith
    have h_prod_split : ∏ k ∈ Finset.Icc 1 n, k = (∏ k ∈ Finset.Icc 1 2, k) * (∏ k ∈ Finset.Icc 3 n, k) := by
      rw [← h_union]
      exact Finset.prod_union h_disjoint
    rw [h_prod_split]
    have h_prod_1_2 : ∏ k ∈ Finset.Icc 1 2, k = 2 := by
      have h_icc_1_2_cons : Finset.Icc 1 2 = Finset.cons 1 (Finset.Ioc 1 2) (Finset.left_not_mem_Ioc (a := 1) (b := 2)) := Finset.Icc_eq_cons_Ioc (by norm_num : 1 ≤ 2)
      rw [h_icc_1_2_cons]
      have h_ioc_1_2 : Finset.Ioc 1 2 = ({2} : Finset ℕ) := by
        ext x
        rw [Finset.mem_Ioc, Finset.mem_singleton]
        constructor
        . intro h_le
          omega
        . intro h_eq
          rw [h_eq]
          norm_num
      rw [Finset.prod_cons]
      rw [h_ioc_1_2]
      rw [Finset.prod_singleton]
      simp
    rw [h_prod_1_2]
    ring
  letI prod_n_const := ∏ k ∈ Finset.Icc 3 n, n
  retro' prod_n_const_def : prod_n_const = ∏ k ∈ Finset.Icc (3 : ℕ) n, n := by funext; rfl
  have subprob_P1_le_prod_n_const_proof : P1 ≤ prod_n_const := by
    mkOpaque
    rw [P1_def, prod_n_const_def]
    apply Finset.prod_le_prod
    intro k hk
    simp_all
    intro k hk
    simp_all
  have subprob_card_Icc_3_n_proof : Finset.card (Finset.Icc 3 n) = n - 2 := by
    mkOpaque
    rw [Nat.card_Icc 3 n]
    simp
  have subprob_prod_n_const_eq_n_pow_card_proof : prod_n_const = n ^ (Finset.card (Finset.Icc 3 n)) := by
    mkOpaque
    simp_all [Finset.prod_const] <;> simp_all [Finset.card_Icc] <;> linarith
  have subprob_prod_n_const_eq_n_pow_n_minus_2_proof : prod_n_const = n ^ (n - 2) := by
    mkOpaque
    rw [subprob_prod_n_const_eq_n_pow_card_proof]
    rw [subprob_card_Icc_3_n_proof] <;> simp_all
  have subprob_k_le_n_proof : ∀ k ∈ Finset.Icc 3 n, k ≤ n := by
    mkOpaque
    intro k h₁
    exact Finset.mem_Icc.mp h₁ |>.2
  have subprob_k_ge_0_proof : ∀ k ∈ Finset.Icc 3 n, 0 ≤ k := by
    mkOpaque
    intro k hk
    have h₁ : 3 ≤ k := Finset.mem_Icc.mp hk |>.1
    linarith
  have subprob_P1_le_n_pow_n_minus_2_proof : P1 ≤ n ^ (n - 2) := by
    mkOpaque
    simp_all [Finset.prod_const, Nat.pow_succ] <;>
      induction n with
      | zero => contradiction
      | succ n ih => simp_all [Finset.prod_const, Nat.pow_succ] <;> linarith
  have subprob_nfact_le_n_pow_n_minus_2_mul_2_proof : Nat.factorial n ≤ n ^ (n - 2) * 2 := by
    mkOpaque
    induction' h₀ with n h₀
    all_goals simp_all [Nat.factorial_succ, Nat.pow_succ, Nat.mul_assoc]
    all_goals nlinarith
  have subprob_2_lt_n_proof : 2 < n := by
    mkOpaque
    linarith [h₀]
  have subprob_one_le_n_proof : 1 ≤ n := by
    mkOpaque
    linarith [h₀]
  have subprob_n_minus_2_ge_0_proof : 0 ≤ n - 2 := by
    mkOpaque
    have h₁ : 0 ≤ n - 2 := by linarith [h₀]
    exact h₁
  have subprob_n_pow_n_minus_2_ge_one_proof : 1 ≤ n ^ (n - 2) := by
    mkOpaque
    have h₁ : 1 ≤ n ^ (n - 2) := by nlinarith [pow_pos (by linarith : (0 : ℕ) < n) (n - 2)]
    linarith
  have subprob_n_pow_n_minus_2_pos_proof : 0 < n ^ (n - 2) := by
    mkOpaque
    induction' h₀ with n h₀
    norm_num
    simp_all [Nat.pow_succ, Nat.mul_succ]
    all_goals nlinarith
  have subprob_mul_lt_mul_left_proof : n ^ (n - 2) * 2 < n ^ (n - 2) * n := by
    mkOpaque
    simp_all [Nat.mul_lt_mul_of_pos_right] <;> linarith
  have subprob_n_minus_2_plus_1_eq_n_minus_1_proof : (n - 2) + 1 = n - 1 := by
    mkOpaque
    simp_all [Nat.add_sub_assoc, Nat.add_sub_cancel_left] <;> omega
  have subprob_n_pow_times_n_eq_n_pow_n_minus_1_proof : n ^ (n - 2) * n = n ^ (n - 1) := by
    mkOpaque
    rw [← pow_succ] <;> simp_all [Nat.pow_succ] <;> linarith
  have subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1_proof : n ^ (n - 2) * 2 < n ^ (n - 1) := by
    mkOpaque
    have h₁ : (2 : ℕ) < n := subprob_2_lt_n_proof
    have h₂ : n - (2 : ℕ) + (1 : ℕ) = n - (1 : ℕ) := subprob_n_minus_2_plus_1_eq_n_minus_1_proof
    have h₃ : n ^ (n - (2 : ℕ)) * n = n ^ (n - (1 : ℕ)) := subprob_n_pow_times_n_eq_n_pow_n_minus_1_proof
    have h₄ : n ^ (n - (2 : ℕ)) * (2 : ℕ) < n ^ (n - (2 : ℕ)) * n := subprob_mul_lt_mul_left_proof
    linarith
  have subprob_final_goal_proof : Nat.factorial n < n ^ (n - 1) := by
    mkOpaque
    have h₀ : n ! ≤ n ^ (n - 2) * 2 := subprob_nfact_le_n_pow_n_minus_2_mul_2_proof
    have h₁ : n ^ (n - 2) * 2 < n ^ (n - 1) := subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1_proof
    linarith
  exact
    show n ! < n ^ (n - (1 : ℕ)) by
      mkOpaque
      exact subprob_final_goal_proof

#print axioms induction_nfactltnexpnm1ngt3

/- Sketch
variable (n : ℕ) (h₀ : 3 ≤ n)
play
  -- Define P1 as the product n * (n-1) * ... * 3
  P1 := ∏ k ∈ Finset.Icc 3 n, k

  -- Step 1: Express n! in terms of P1
  -- n! = P1 * 2 for n >= 3
  subprob_nfact_eq_P1_mul_2 :≡ Nat.factorial n = P1 * 2
  subprob_nfact_eq_P1_mul_2_proof ⇐ show subprob_nfact_eq_P1_mul_2 by sorry

  -- Step 2: Bound P1 -- P1 ≤ n^(n-2)
  -- Step 2a: Calculate the number of terms in P1
  -- The number of terms in Finset.Icc 3 n is n - 3 + 1 = n - 2.
  -- This requires n >= 3 for n-2 to be a natural number resulting from subtraction.
  -- h₀ (3 <= n) ensures n-2 is well-defined and n-2 >= 1.
  subprob_card_Icc_3_n :≡ Finset.card (Finset.Icc 3 n) = n - 2
  subprob_card_Icc_3_n_proof ⇐ show subprob_card_Icc_3_n by sorry

  -- Step 2b: Show each term k in P1 is less than or equal to n.
  subprob_k_le_n :≡ ∀ k ∈ Finset.Icc 3 n, k ≤ n
  subprob_k_le_n_proof ⇐ show subprob_k_le_n by sorry

  -- Step 2c: Show each term k in P1 is non-negative (actually k >= 3).
  subprob_k_ge_0 :≡ ∀ k ∈ Finset.Icc 3 n, 0 ≤ k
  subprob_k_ge_0_proof ⇐ show subprob_k_ge_0 by sorry

  -- Step 2d: Bound P1 by \prod_{k \in Finset.Icc 3 n} n
  prod_n_const := ∏ k ∈ Finset.Icc 3 n, n
  subprob_P1_le_prod_n_const :≡ P1 ≤ prod_n_const
  subprob_P1_le_prod_n_const_proof ⇐ show subprob_P1_le_prod_n_const by sorry

  -- Step 2e: Evaluate \prod_{k \in Finset.Icc 3 n} n
  -- This product is n raised to the power of the number of terms.
  subprob_prod_n_const_eq_n_pow_card :≡ prod_n_const = n ^ (Finset.card (Finset.Icc 3 n))
  subprob_prod_n_const_eq_n_pow_card_proof ⇐ show subprob_prod_n_const_eq_n_pow_card by sorry

  -- Step 2f: Substitute card to get n^(n-2)
  subprob_prod_n_const_eq_n_pow_n_minus_2 :≡ prod_n_const = n^(n-2)
  subprob_prod_n_const_eq_n_pow_n_minus_2_proof ⇐ show subprob_prod_n_const_eq_n_pow_n_minus_2 by sorry

  -- Step 2g: Conclude P1 ≤ n^(n-2)
  subprob_P1_le_n_pow_n_minus_2 :≡ P1 ≤ n^(n-2)
  subprob_P1_le_n_pow_n_minus_2_proof ⇐ show subprob_P1_le_n_pow_n_minus_2 by sorry

  -- Step 3: Combine to get n! ≤ n^(n-2) * 2
  subprob_nfact_le_n_pow_n_minus_2_mul_2 :≡ Nat.factorial n ≤ n^(n-2) * 2
  subprob_nfact_le_n_pow_n_minus_2_mul_2_proof ⇐ show subprob_nfact_le_n_pow_n_minus_2_mul_2 by sorry

  -- Step 4: Use n ≥ 3 to show 2 < n
  subprob_2_lt_n :≡ 2 < n
  subprob_2_lt_n_proof ⇐ show subprob_2_lt_n by sorry

  -- Step 5 & 6: Show n^(n-2) * 2 < n^(n-1)
  -- Step 5a: Show n^(n-2) > 0.
  -- For n ≥ 3, n ≥ 1. Also n-2 ≥ 1. So n^(n-2) ≥ 1^(n-2) = 1 > 0.
  subprob_one_le_n :≡ 1 ≤ n
  subprob_one_le_n_proof ⇐ show subprob_one_le_n by sorry
  subprob_n_minus_2_ge_0 :≡ 0 ≤ n-2 -- Actually n-2 >= 1 since n >= 3
  subprob_n_minus_2_ge_0_proof ⇐ show subprob_n_minus_2_ge_0 by sorry
  subprob_n_pow_n_minus_2_ge_one :≡ 1 ≤ n^(n-2)
  subprob_n_pow_n_minus_2_ge_one_proof ⇐ show subprob_n_pow_n_minus_2_ge_one by sorry
  subprob_n_pow_n_minus_2_pos :≡ 0 < n^(n-2)
  subprob_n_pow_n_minus_2_pos_proof ⇐ show subprob_n_pow_n_minus_2_pos by sorry

  -- Step 5b: Show n^(n-2) * 2 < n^(n-2) * n, using 2 < n and n^(n-2) > 0.
  subprob_mul_lt_mul_left :≡ n^(n-2) * 2 < n^(n-2) * n
  subprob_mul_lt_mul_left_proof ⇐ show subprob_mul_lt_mul_left by sorry

  -- Step 6a: Show (n-2)+1 = n-1. This needs n ≥ 2. h₀ (n ≥ 3) ensures this.
  subprob_n_minus_2_plus_1_eq_n_minus_1 :≡ (n-2)+1 = n-1
  subprob_n_minus_2_plus_1_eq_n_minus_1_proof ⇐ show subprob_n_minus_2_plus_1_eq_n_minus_1 by sorry

  -- Step 6b: Show n^(n-2) * n = n^((n-2)+1) using Nat.pow_add (after Nat.pow_one for n).
  subprob_pow_add_form :≡ n^(n-2) * n = n^((n-2)+1)
  subprob_pow_add_form_proof ⇐ show subprob_pow_add_form by sorry

  -- Step 6c: Rewrite n^(n-2) * n to n^(n-1)
  subprob_n_pow_times_n_eq_n_pow_n_minus_1 :≡ n^(n-2) * n = n^(n-1)
  subprob_n_pow_times_n_eq_n_pow_n_minus_1_proof ⇐ show subprob_n_pow_times_n_eq_n_pow_n_minus_1 by sorry

  -- Step 5&6 Combined: Conclude n^(n-2) * 2 < n^(n-1)
  subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1 :≡ n^(n-2) * 2 < n^(n-1)
  subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1_proof ⇐ show subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1 by sorry

  -- Step 7: Combine inequalities to get the final result
  -- n! ≤ n^(n-2) * 2  (from subprob_nfact_le_n_pow_n_minus_2_mul_2)
  -- n^(n-2) * 2 < n^(n-1) (from subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1)
  -- So n! < n^(n-1) by transitivity.
  subprob_final_goal :≡ Nat.factorial n < n^(n-1)
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketch with proof
variable (n: ℕ) (h₀: (3 : ℕ) ≤ n)
play
  P1 := ∏ k ∈ Finset.Icc 3 n, k
  subprob_nfact_eq_P1_mul_2 :≡ Nat.factorial n = P1 * 2
  subprob_nfact_eq_P1_mul_2_proof ⇐ show subprob_nfact_eq_P1_mul_2 by
    rw [P1_def]
    have h_icc_eq_ico : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext x
      rw [Finset.mem_Icc, Finset.mem_Ico]
      constructor
      .
        intro h_le_n
        cases h_le_n with
        | intro h1x hxn =>
          constructor
          . exact h1x
          .
            exact Nat.lt_succ_of_le hxn
      .
        intro h_lt_succ_n
        cases h_lt_succ_n with
        | intro h1x hlt =>
          constructor
          . exact h1x
          .
            exact Nat.le_of_lt_succ hlt
    have h_prod_icc_eq_ico : ∏ k ∈ Finset.Icc 1 n, k = ∏ k ∈ Finset.Ico 1 (n + 1), k := by
      rw [h_icc_eq_ico]
    have h_prod_ico_eq_fact : ∏ k ∈ Finset.Ico 1 (n + 1), k = n.factorial := Finset.prod_Ico_id_eq_factorial n
    have h_prod_icc_eq_fact : ∏ k ∈ Finset.Icc 1 n, k = n.factorial := by
      rw [h_prod_icc_eq_ico, h_prod_ico_eq_fact]
    rw [h_prod_icc_eq_fact.symm]
    have h_union : Finset.Icc 1 2 ∪ Finset.Icc 3 n = Finset.Icc 1 n := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc]
      constructor
      .
        intro h
        cases h with
        | inl h_le_2 =>
          cases h_le_2 with | intro h1x hx2 =>
          constructor
          . exact h1x
          .
            omega
        | inr h_ge_3 =>
          cases h_ge_3 with | intro h3x hxn =>
          constructor
          .
            omega
          . exact hxn
      .
        intro h
        cases h with | intro h1x hxn =>
        by_cases hx2 : x ≤ 2
        .
          left
          constructor ; exact h1x ; exact hx2
        .
          right
          constructor
          .
            omega
          . exact hxn
    have h_disjoint : Disjoint (Finset.Icc 1 2) (Finset.Icc 3 n) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      rw [Finset.mem_Icc] at ha
      rw [Finset.mem_Icc] at hb
      cases ha ; cases hb
      linarith
    have h_prod_split : ∏ k ∈ Finset.Icc 1 n, k = (∏ k ∈ Finset.Icc 1 2, k) * (∏ k ∈ Finset.Icc 3 n, k) := by
      rw [← h_union]
      exact Finset.prod_union h_disjoint
    rw [h_prod_split]
    have h_prod_1_2 : ∏ k ∈ Finset.Icc 1 2, k = 2 := by
      have h_icc_1_2_cons : Finset.Icc 1 2 = Finset.cons 1 (Finset.Ioc 1 2) (Finset.left_not_mem_Ioc (a := 1) (b := 2)) :=
        Finset.Icc_eq_cons_Ioc (by norm_num : 1 ≤ 2)
      rw [h_icc_1_2_cons]
      have h_ioc_1_2 : Finset.Ioc 1 2 = ({2} : Finset ℕ) := by
        ext x
        rw [Finset.mem_Ioc, Finset.mem_singleton]
        constructor
        .
          intro h_le
          omega
        .
          intro h_eq
          rw [h_eq]
          norm_num
      rw [Finset.prod_cons]
      rw [h_ioc_1_2]
      rw [Finset.prod_singleton]
      simp
    rw [h_prod_1_2]
    ring
  subprob_card_Icc_3_n :≡ Finset.card (Finset.Icc 3 n) = n - 2
  subprob_card_Icc_3_n_proof ⇐ show subprob_card_Icc_3_n by
    rw [Nat.card_Icc 3 n]
    simp
  subprob_k_le_n :≡ ∀ k ∈ Finset.Icc 3 n, k ≤ n
  subprob_k_le_n_proof ⇐ show subprob_k_le_n by
    intro k h₁
    exact Finset.mem_Icc.mp h₁ |>.2
  subprob_k_ge_0 :≡ ∀ k ∈ Finset.Icc 3 n, 0 ≤ k
  subprob_k_ge_0_proof ⇐ show subprob_k_ge_0 by
    intro k hk
    have h₁ : 3 ≤ k := Finset.mem_Icc.mp hk |>.1
    linarith
  prod_n_const := ∏ k ∈ Finset.Icc 3 n, n
  subprob_P1_le_prod_n_const :≡ P1 ≤ prod_n_const
  subprob_P1_le_prod_n_const_proof ⇐ show subprob_P1_le_prod_n_const by
    rw [P1_def, prod_n_const_def]
    apply Finset.prod_le_prod
    intro k hk
    simp_all
    intro k hk
    simp_all
  subprob_prod_n_const_eq_n_pow_card :≡ prod_n_const = n ^ (Finset.card (Finset.Icc 3 n))
  subprob_prod_n_const_eq_n_pow_card_proof ⇐ show subprob_prod_n_const_eq_n_pow_card by
    simp_all [Finset.prod_const]
    <;> simp_all [Finset.card_Icc]
    <;> linarith
  subprob_prod_n_const_eq_n_pow_n_minus_2 :≡ prod_n_const = n^(n-2)
  subprob_prod_n_const_eq_n_pow_n_minus_2_proof ⇐ show subprob_prod_n_const_eq_n_pow_n_minus_2 by
    rw [subprob_prod_n_const_eq_n_pow_card_proof]
    rw [subprob_card_Icc_3_n_proof]
    <;> simp_all
  subprob_P1_le_n_pow_n_minus_2 :≡ P1 ≤ n^(n-2)
  subprob_P1_le_n_pow_n_minus_2_proof ⇐ show subprob_P1_le_n_pow_n_minus_2 by
    simp_all [Finset.prod_const, Nat.pow_succ]
    <;> induction n with
    | zero => contradiction
    | succ n ih =>
      simp_all [Finset.prod_const, Nat.pow_succ]
      <;> linarith
  subprob_nfact_le_n_pow_n_minus_2_mul_2 :≡ Nat.factorial n ≤ n^(n-2) * 2
  subprob_nfact_le_n_pow_n_minus_2_mul_2_proof ⇐ show subprob_nfact_le_n_pow_n_minus_2_mul_2 by
    induction' h₀ with n h₀
    all_goals simp_all [Nat.factorial_succ, Nat.pow_succ, Nat.mul_assoc]
    all_goals nlinarith
  subprob_2_lt_n :≡ 2 < n
  subprob_2_lt_n_proof ⇐ show subprob_2_lt_n by
    linarith [h₀]
  subprob_one_le_n :≡ 1 ≤ n
  subprob_one_le_n_proof ⇐ show subprob_one_le_n by
    linarith [h₀]
  subprob_n_minus_2_ge_0 :≡ 0 ≤ n-2
  subprob_n_minus_2_ge_0_proof ⇐ show subprob_n_minus_2_ge_0 by
    have h₁ : 0 ≤ n - 2 := by
      linarith [h₀]
    exact h₁
  subprob_n_pow_n_minus_2_ge_one :≡ 1 ≤ n^(n-2)
  subprob_n_pow_n_minus_2_ge_one_proof ⇐ show subprob_n_pow_n_minus_2_ge_one by
    have h₁ : 1 ≤ n ^ (n - 2) := by
      nlinarith [pow_pos (by linarith : (0 : ℕ) < n) (n - 2)]
    linarith
  subprob_n_pow_n_minus_2_pos :≡ 0 < n^(n-2)
  subprob_n_pow_n_minus_2_pos_proof ⇐ show subprob_n_pow_n_minus_2_pos by
    induction' h₀ with n h₀
    norm_num
    simp_all [Nat.pow_succ, Nat.mul_succ]
    all_goals nlinarith
  subprob_mul_lt_mul_left :≡ n^(n-2) * 2 < n^(n-2) * n
  subprob_mul_lt_mul_left_proof ⇐ show subprob_mul_lt_mul_left by
    simp_all [Nat.mul_lt_mul_of_pos_right]
    <;> linarith
  subprob_n_minus_2_plus_1_eq_n_minus_1 :≡ (n-2)+1 = n-1
  subprob_n_minus_2_plus_1_eq_n_minus_1_proof ⇐ show subprob_n_minus_2_plus_1_eq_n_minus_1 by
    simp_all [Nat.add_sub_assoc, Nat.add_sub_cancel_left]
    <;> omega
  subprob_pow_add_form :≡ n^(n-2) * n = n^((n-2)+1)
  subprob_pow_add_form_proof ⇐ show subprob_pow_add_form by
    rw [← pow_succ]
    <;> simp_all [Nat.mul_comm]
    <;> norm_num
    <;> linarith
  subprob_n_pow_times_n_eq_n_pow_n_minus_1 :≡ n^(n-2) * n = n^(n-1)
  subprob_n_pow_times_n_eq_n_pow_n_minus_1_proof ⇐ show subprob_n_pow_times_n_eq_n_pow_n_minus_1 by
    rw [← pow_succ]
    <;> simp_all [Nat.pow_succ]
    <;> linarith
  subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1 :≡ n^(n-2) * 2 < n^(n-1)
  subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1_proof ⇐ show subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1 by
    have h₁ : (2 : ℕ) < n := subprob_2_lt_n_proof
    have h₂ : n - (2 : ℕ) + (1 : ℕ) = n - (1 : ℕ) := subprob_n_minus_2_plus_1_eq_n_minus_1_proof
    have h₃ : n ^ (n - (2 : ℕ)) * n = n ^ (n - (1 : ℕ)) := subprob_n_pow_times_n_eq_n_pow_n_minus_1_proof
    have h₄ : n ^ (n - (2 : ℕ)) * (2 : ℕ) < n ^ (n - (2 : ℕ)) * n := subprob_mul_lt_mul_left_proof
    linarith
  subprob_final_goal :≡ Nat.factorial n < n^(n-1)
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    have h₀ : n ! ≤ n ^ (n - 2) * 2 := subprob_nfact_le_n_pow_n_minus_2_mul_2_proof
    have h₁ : n ^ (n - 2) * 2 < n ^ (n - 1) := subprob_n_pow_n_minus_2_mul_2_lt_n_pow_n_minus_1_proof
    linarith
  original_target :≡ n ! < n ^ (n - (1 : ℕ))
  original_target_proof ⇐ show original_target by
    exact subprob_final_goal_proof
-/
