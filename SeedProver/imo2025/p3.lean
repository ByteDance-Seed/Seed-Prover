import Mathlib
import Aesop
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial

lemma round1_h1 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h_k_le_2_plus_padic : k ≤ 2 + padicValNat 2 n.toNat):
  (2 : ℤ) ^ k ≤ (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) := by
  apply pow_le_pow_right (by norm_num) h_k_le_2_plus_padic

lemma round1_h2 (n : ℤ)
  (k : ℕ)
  (hn : n > 0):
  (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) = 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) := by
  simp [pow_add, pow_two]
  <;> ring

lemma round1_h3 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h1 : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ (2 + padicValNat 2 n.toNat))
  (h2 : (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) = 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat)):
  (2 : ℤ) ^ k ≤ 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) := by
  linarith

lemma round1_h4 (n : ℤ)
  (k : ℕ)
  (hn : n > 0):
  (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n := by
  have h4₁ : (2 : ℕ) ^ (padicValNat 2 n.toNat) ∣ n.toNat := by
    apply pow_padicValNat_dvd
  have h4₂ : (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ (n.toNat : ℤ) := by
    exact_mod_cast h4₁
  have h4₃ : (n.toNat : ℤ) = n := by
    simp [hn]
    <;> norm_num
    <;> omega
  rw [h4₃] at h4₂
  exact h4₂

lemma round1_h5 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h4 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n):
  (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n := by
  have h5₁ : (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n := h4
  have h5₂ : 0 < (2 : ℤ) ^ (padicValNat 2 n.toNat) := by positivity
  exact Int.le_of_dvd (by linarith) h5₁

lemma round1_h6 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h5 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n):
  4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ 4 * n := by
  have h6₁ : (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n := h5
  linarith

lemma round1_h7 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h3 : (2 : ℤ) ^ k ≤ 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat))
  (h6 : 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ 4 * n):
  (2 : ℤ) ^ k ≤ 4 * n := by
  linarith

lemma round1_h_main (n : ℤ)
  (f : ℤ → ℤ)
  (k : ℕ)
  (hn : n > 0)
  (hk : f n = (2 : ℤ) ^ k)
  (h7 : (2 : ℤ) ^ k ≤ 4 * n):
  f n ≤ 4 * n := by
  rw [hk]
  exact h7

lemma round1_h6' (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℕ) (hk : f n = (2 : ℤ) ^ k) (h_k_le_2_plus_padic : k ≤ 2 + padicValNat 2 n.toNat) : f n ≤ 4 * n := by

  have h1 : (2 : ℤ) ^ k ≤ (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) := by
    exact round1_h1 n k hn h_k_le_2_plus_padic
  have h2 : (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) = 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) := by
    exact round1_h2 n k hn
  have h3 : (2 : ℤ) ^ k ≤ 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) := by
    exact round1_h3 n k hn h1 h2
  have h4 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n := by
    exact round1_h4 n k hn
  have h5 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n := by
    exact round1_h5 n k hn h4
  have h6 : 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ 4 * n := by
    exact round1_h6 n k hn h5
  have h7 : (2 : ℤ) ^ k ≤ 4 * n := by
    exact round1_h7 n k hn h3 h6
  have h_main : f n ≤ 4 * n := by
    exact round1_h_main n f k hn hk h7
  exact h_main


lemma lte_2_3n_minus_1_h1 :
  ∀ k : ℕ, k > 0 → k % 2 = 1 → 3 ^ k % 4 = 3 := by
  intro k hkpos hkodd
  have h : ∀ m : ℕ, 3 ^ (2 * m + 1) % 4 = 3 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      calc
        3 ^ (2 * (m + 1) + 1) % 4 = 3 ^ (2 * m + 1 + 2) % 4 := by ring_nf
        _ = (3 ^ (2 * m + 1) * 3 ^ 2) % 4 := by ring
        _ = ((3 ^ (2 * m + 1) % 4) * (3 ^ 2 % 4)) % 4 := by simp [Nat.mul_mod]
        _ = (3 * 1) % 4 := by rw [ih]; all_goals norm_num
        _ = 3 := by norm_num
  have h2 : ∃ m, k = 2 * m + 1 := by
    refine ⟨(k - 1) / 2,?_⟩
    omega
  rcases h2 with ⟨m, rfl⟩
  have h3 := h m
  simpa using h3

lemma lte_2_3n_minus_1_h4 :
  ∀ k : ℕ, k > 0 → k % 2 = 0 → 3 ^ k % 4 = 1 := by
  intro k hkpos hkodd
  have h5 : ∃ m, k = 2 * m ∧ m > 0 := by
    refine ⟨k / 2,?_⟩
    omega
  rcases h5 with ⟨m, hmk, hmpos⟩
  have h6 : 3 ^ (2 * m) % 4 = 1 := by
    have h : ∀ n : ℕ, n > 0 → 3 ^ (2 * n) % 4 = 1 := by
      intro n hn
      induction n with
      | zero => contradiction
      | succ n ih =>
        by_cases h' : n = 0
        · subst h'
          norm_num
        · have h'' : n > 0 := by omega
          have ih' := ih h''
          calc
            3 ^ (2 * (n + 1)) % 4 = 3 ^ (2 * n + 2) % 4 := by ring_nf
            _ = (3 ^ (2 * n) * 3 ^ 2) % 4 := by ring
            _ = ((3 ^ (2 * n) % 4) * (3 ^ 2 % 4)) % 4 := by simp [Nat.mul_mod]
            _ = (1 * 1) % 4 := by rw [ih']; all_goals norm_num
            _ = 1 := by norm_num
    exact h m hmpos
  rw [hmk]
  simpa using h6

lemma lte_2_3n_minus_1_h3_pow_mod_8 :
  ∀ m : ℕ, m > 0 → m % 2 = 1 → 3 ^ m % 8 = 3 := by
  intro m hmpos hmodd
  have h : ∀ k : ℕ, 3 ^ (2 * k + 1) % 8 = 3 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        3 ^ (2 * (k + 1) + 1) % 8 = 3 ^ (2 * k + 1 + 2) % 8 := by ring_nf
        _ = (3 ^ (2 * k + 1) * 3 ^ 2) % 8 := by ring
        _ = ((3 ^ (2 * k + 1) % 8) * (3 ^ 2 % 8)) % 8 := by simp [Nat.mul_mod]
        _ = (3 * 1) % 8 := by rw [ih]; all_goals norm_num
        _ = 3 := by norm_num
  have h2 : ∃ k, m = 2 * k + 1 := by
    refine ⟨(m - 1) / 2,?_⟩
    omega
  rcases h2 with ⟨k, rfl⟩
  have h3 := h k
  simpa using h3

lemma lte_2_3n_minus_1_h_padicValNat_mul (p : ℕ) [Fact p.Prime] (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
  padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  exact padicValNat.mul ha hb

lemma lte_2_3n_minus_1_general_lemma_A (x : ℕ) (h1 : 2 ∣ x) (h2 : ¬ 4 ∣ x) : padicValNat 2 x = 1 := by
  have h3 : ∃ y, x = 2 * y := by
    obtain ⟨y, hy⟩ := h1
    refine ⟨y, by linarith⟩
  rcases h3 with ⟨y, rfl⟩
  have hy_pos : y > 0 := by
    by_contra h
    have h4 : y = 0 := by linarith
    have h5 : 2 * y = 0 := by simp [h4]
    have h6 : 4 ∣ (2 * y) := by
      norm_num [h5]
    contradiction
  have h4 : ¬ 2 ∣ y := by
    by_contra h5
    have h6 : ∃ z, y = 2 * z := by
      obtain ⟨z, hz⟩ := h5
      refine ⟨z, by linarith⟩
    rcases h6 with ⟨z, hz⟩
    have h7 : 2 * (2 * z) = 4 * z := by ring
    have h8 : 2 * y = 4 * z := by
      rw [hz]
      <;> linarith
    have h9 : 4 ∣ (2 * y) := by
      use z
      <;> linarith
    contradiction
  have h5 : padicValNat 2 (2 * y) = 1 := by
    have h6 : padicValNat 2 2 = 1 := by norm_num
    have h7 : padicValNat 2 y = 0 := by
      by_contra h7
      have h8 : padicValNat 2 y > 0 := by omega
      have h9 : 2 ∣ y := by
        have h10 : padicValNat 2 y > 0 := h8
        have h11 : 2 ^ 1 ∣ y := by
          have h12 : 2 ^ 1 ≤ 2 ^ padicValNat 2 y := by
            have h13 : 1 ≤ padicValNat 2 y := by omega
            exact Nat.pow_le_pow_of_le_right (by norm_num) h13
          have h14 : 2 ^ padicValNat 2 y ∣ y := by
            exact?
          exact dvd_trans (by
            exact Nat.pow_dvd_pow 2 (by omega)) h14
        tauto
      contradiction
    have h10 : (2 : ℕ) ≠ 0 := by norm_num
    have h11 : y ≠ 0 := by linarith
    have h12 : padicValNat 2 (2 * y) = padicValNat 2 2 + padicValNat 2 y := by
      exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 y (by norm_num) (by linarith)
    rw [h12, h6, h7]
    <;> norm_num
  simpa using h5

lemma lte_2_3n_minus_1_general_lemma_B (x : ℕ) (h1 : 4 ∣ x) (h2 : ¬ 8 ∣ x) : padicValNat 2 x = 2 := by
  have h3 : ∃ y, x = 4 * y := by
    obtain ⟨y, hy⟩ := h1
    refine ⟨y, by linarith⟩
  rcases h3 with ⟨y, rfl⟩
  have hy_pos : y > 0 := by
    by_contra h
    have h4 : y = 0 := by linarith
    have h5 : 4 * y = 0 := by simp [h4]
    have h6 : 8 ∣ (4 * y) := by
      norm_num [h5]
    contradiction
  have h4 : ¬ 2 ∣ y := by
    by_contra h5
    have h6 : ∃ z, y = 2 * z := by
      obtain ⟨z, hz⟩ := h5
      refine ⟨z, by linarith⟩
    rcases h6 with ⟨z, hz⟩
    have h7 : 4 * (2 * z) = 8 * z := by ring
    have h8 : 4 * y = 8 * z := by
      rw [hz]
      <;> linarith
    have h9 : 8 ∣ (4 * y) := by
      use z
      <;> linarith
    contradiction
  have h5 : padicValNat 2 (4 * y) = 2 := by
    have h6 : 4 * y = 2 * (2 * y) := by ring
    have h7 : padicValNat 2 (2 * (2 * y)) = padicValNat 2 2 + padicValNat 2 (2 * y) := by
      have h71 : (2 : ℕ) ≠ 0 := by norm_num
      have h72 : 2 * y ≠ 0 := by
        have h73 : y > 0 := hy_pos
        omega
      exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 (2 * y) h71 h72
    have h8 : padicValNat 2 (2 * y) = 1 := by
      have h81 : padicValNat 2 2 = 1 := by norm_num
      have h82 : padicValNat 2 y = 0 := by
        by_contra h82
        have h83 : padicValNat 2 y > 0 := by omega
        have h84 : 2 ∣ y := by
          have h841 : padicValNat 2 y > 0 := h83
          have h842 : 2 ^ 1 ∣ y := by
            have h843 : 2 ^ 1 ≤ 2 ^ padicValNat 2 y := by
              have h844 : 1 ≤ padicValNat 2 y := by omega
              exact Nat.pow_le_pow_of_le_right (by norm_num) h844
            have h845 : 2 ^ padicValNat 2 y ∣ y := by
              exact?
            exact dvd_trans (by
              exact Nat.pow_dvd_pow 2 (by omega)) h845
          tauto
        contradiction
      have h85 : (2 : ℕ) ≠ 0 := by norm_num
      have h86 : y ≠ 0 := by linarith
      have h87 : padicValNat 2 (2 * y) = padicValNat 2 2 + padicValNat 2 y := by
        exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 y h85 h86
      rw [h87, h81, h82]
      <;> norm_num
    have h9 : padicValNat 2 2 = 1 := by norm_num
    have h10 : padicValNat 2 (2 * (2 * y)) = 2 := by
      rw [h7, h9, h8]
      <;> norm_num
    have h11 : 4 * y = 2 * (2 * y) := by ring
    have h12 : padicValNat 2 (4 * y) = padicValNat 2 (2 * (2 * y)) := by
      rw [h11]
    rw [h12, h10]
    <;> rfl
  simpa using h5

lemma lte_2_3n_minus_1_lemma1 (k : ℕ) (hk_pos : k > 0) (hk_odd : k % 2 = 1) : padicValNat 2 (3 ^ k - 1) = 1 := by
  have h1 : 3 ^ k % 4 = 3 := lte_2_3n_minus_1_h1 k hk_pos hk_odd
  have h2 : 2 ∣ (3 ^ k - 1) := by
    have h3 : 3 ^ k % 4 = 3 := h1
    have h4 : ∃ q, 3 ^ k = 4 * q + 3 := by
      refine ⟨(3 ^ k) / 4,?_⟩
      omega
    rcases h4 with ⟨q, h4⟩
    have h5 : 3 ^ k - 1 = 2 * (2 * q + 1) := by
      omega
    omega
  have h3 : ¬ 4 ∣ (3 ^ k - 1) := by
    have h4 : 3 ^ k % 4 = 3 := h1
    intro h6
    have h61 : (3 ^ k - 1) % 4 = 0 := by
      omega
    have h31 : k > 0 := hk_pos
    have h32 : 3 ^ k ≥ 1 := by
      apply Nat.one_le_pow
      all_goals linarith
    have h41 : ∃ q, 3 ^ k = 4 * q + 3 := by
      refine ⟨(3 ^ k) / 4,?_⟩
      omega
    rcases h41 with ⟨q, h41⟩
    have h42 : 3 ^ k - 1 = 4 * q + 2 := by omega
    have h43 : (3 ^ k - 1) % 4 = 2 := by omega
    omega
  exact lte_2_3n_minus_1_general_lemma_A (3 ^ k - 1) h2 h3

lemma lte_2_3n_minus_1_lemma2 (k : ℕ) (hk_pos : k > 0) (hk_even : k % 2 = 0) : padicValNat 2 (3 ^ k - 1) = 2 + padicValNat 2 k := by
  have h_padicValNat_2_2 : padicValNat 2 2 = 1 := by
    have h1 : 2 ∣ 2 := by norm_num
    have h2 : ¬ 4 ∣ 2 := by norm_num
    exact lte_2_3n_minus_1_general_lemma_A 2 h1 h2
  have h_padicValNat_2_4 : padicValNat 2 4 = 2 := by
    have h1 : 4 ∣ 4 := by norm_num
    have h2 : ¬ 8 ∣ 4 := by norm_num
    exact lte_2_3n_minus_1_general_lemma_B 4 h1 h2
  have h_padicValNat_2_8 : padicValNat 2 8 = 3 := by
    have h1 : padicValNat 2 (2 * 4) = padicValNat 2 2 + padicValNat 2 4 := by
      exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 4 (by norm_num) (by norm_num)
    have h2 : 2 * 4 = 8 := by norm_num
    rw [h2] at h1
    rw [h1]
    rw [h_padicValNat_2_2, h_padicValNat_2_4]
    <;> norm_num
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k = 2
    · -- Base case: k = 2
      subst h
      norm_num at *
      <;>
      (try simp [h_padicValNat_2_8, h_padicValNat_2_2]) <;>
      (try aesop) <;>
      (try linarith)
    · -- Inductive step: k ≠ 2
      have hk_ge_4 : k ≥ 4 := by
        have h1 : k > 0 := hk_pos
        have h2 : k % 2 = 0 := hk_even
        have h3 : k ≠ 2 := h
        omega
      have h1 : ∃ m, k = 2 * m := by
        refine ⟨k / 2,?_⟩
        omega
      rcases h1 with ⟨m, rfl⟩
      have hm_pos : m > 0 := by omega
      have hm_lt_k : m < 2 * m := by nlinarith
      by_cases h2 : m % 2 = 1
      · -- Case 1: m is odd
        have h3 : m > 0 := hm_pos
        have h4 : m % 2 = 1 := h2
        have h5 : 3 ^ m % 8 = 3 := lte_2_3n_minus_1_h3_pow_mod_8 m h3 h4
        have h6 : 2 ∣ (3 ^ m - 1) := by omega
        have h7 : ¬ 4 ∣ (3 ^ m - 1) := by
          have h71 : 3 ^ m % 8 = 3 := h5
          intro h72
          have h73 : (3 ^ m - 1) % 4 = 0 := by omega
          have h31 : m > 0 := h3
          have h32 : 3 ^ m ≥ 1 := by
            apply Nat.one_le_pow
            all_goals linarith
          have h41 : 3 ^ m % 4 = 3 := by omega
          have h42 : ∃ q, 3 ^ m = 4 * q + 3 := by
            refine ⟨(3 ^ m) / 4,?_⟩
            omega
          rcases h42 with ⟨q, h42⟩
          have h44 : 3 ^ m - 1 = 4 * q + 2 := by omega
          have h45 : (3 ^ m - 1) % 4 = 2 := by omega
          omega
        have h8 : padicValNat 2 (3 ^ m - 1) = 1 := lte_2_3n_minus_1_general_lemma_A (3 ^ m - 1) h6 h7
        have h9 : 4 ∣ (3 ^ m + 1) := by omega
        have h10 : ¬ 8 ∣ (3 ^ m + 1) := by omega
        have h11 : padicValNat 2 (3 ^ m + 1) = 2 := lte_2_3n_minus_1_general_lemma_B (3 ^ m + 1) h9 h10
        have h12 : 3 ^ m - 1 > 0 := by
          have h121 : m > 0 := h3
          have h122 : 3 ^ m ≥ 3 ^ 1 := by
            exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
          omega
        have h13 : 3 ^ m + 1 > 0 := by positivity
        have h14 : 3 ^ (2 * m) - 1 = (3 ^ m - 1) * (3 ^ m + 1) := by
          have h141 : 3 ^ m ≥ 1 := by
            apply Nat.one_le_pow
            <;> omega
          have h142 : 3 ^ (2 * m) = (3 ^ m) ^ 2 := by ring
          rw [h142]
          have h143 : (3 ^ m) ^ 2 - 1 = (3 ^ m - 1) * (3 ^ m + 1) := by
            have h144 : 3 ^ m ≥ 1 := h141
            have h145 : (3 ^ m) ^ 2 = (3 ^ m) * (3 ^ m) := by ring
            rw [h145]
            cases' le_iff_exists_add.mp (by omega : 1 ≤ 3 ^ m) with x hx
            simp [hx, Nat.mul_add, Nat.add_mul, Nat.add_assoc] <;> ring_nf at * <;> omega
          exact h143
        have h15 : padicValNat 2 ((3 ^ m - 1) * (3 ^ m + 1)) = padicValNat 2 (3 ^ m - 1) + padicValNat 2 (3 ^ m + 1) := by
          have ha : (3 ^ m - 1) ≠ 0 := by linarith
          have hb : (3 ^ m + 1) ≠ 0 := by linarith
          exact lte_2_3n_minus_1_h_padicValNat_mul 2 (3 ^ m - 1) (3 ^ m + 1) ha hb
        have h16 : padicValNat 2 (3 ^ (2 * m) - 1) = padicValNat 2 (3 ^ m - 1) + padicValNat 2 (3 ^ m + 1) := by
          rw [h14] at *
          exact h15
        have h17 : padicValNat 2 (3 ^ (2 * m) - 1) = 1 + 2 := by
          rw [h16, h8, h11]
          <;> norm_num
        have h18 : padicValNat 2 (3 ^ (2 * m) - 1) = 3 := by linarith
        have h19 : 2 ∣ (2 * m) := by omega
        have h20 : ¬ 4 ∣ (2 * m) := by omega
        have h21 : padicValNat 2 (2 * m) = 1 := lte_2_3n_minus_1_general_lemma_A (2 * m) h19 h20
        have h22 : 2 + padicValNat 2 (2 * m) = 3 := by linarith
        linarith
      · -- Case 2: m is even
        have h2' : m % 2 = 0 := by omega
        have h3 : m > 0 := hm_pos
        have h4 : ∃ t, m = 2 * t := by
          refine ⟨m / 2,?_⟩
          omega
        rcases h4 with ⟨t, h4t⟩
        have ht_pos : t > 0 := by omega
        have ht_lt_m : t < m := by omega
        have hm_even : m % 2 = 0 := h2'
        have hm_pos' : m > 0 := h3
        have h5 : m < 2 * m := by nlinarith
        have ih_m : padicValNat 2 (3 ^ m - 1) = 2 + padicValNat 2 m := by
          have h51 : m < 2 * m := by nlinarith
          have h52 : m > 0 := hm_pos'
          have h53 : m % 2 = 0 := hm_even
          exact ih m (by omega) h52 h53
        have h6 : 3 ^ m % 4 = 1 := lte_2_3n_minus_1_h4 m hm_pos' hm_even
        have h7 : 2 ∣ (3 ^ m + 1) := by omega
        have h8 : ¬ 4 ∣ (3 ^ m + 1) := by omega
        have h9 : padicValNat 2 (3 ^ m + 1) = 1 := lte_2_3n_minus_1_general_lemma_A (3 ^ m + 1) h7 h8
        have h10 : 3 ^ m - 1 > 0 := by
          have h101 : m > 0 := hm_pos'
          have h102 : 3 ^ m ≥ 3 ^ 1 := by
            exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)
          omega
        have h11 : 3 ^ m + 1 > 0 := by positivity
        have h12 : 3 ^ (2 * m) - 1 = (3 ^ m - 1) * (3 ^ m + 1) := by
          have h121 : 3 ^ m ≥ 1 := by
            apply Nat.one_le_pow
            <;> omega
          have h122 : 3 ^ (2 * m) = (3 ^ m) ^ 2 := by ring
          rw [h122]
          have h123 : (3 ^ m) ^ 2 - 1 = (3 ^ m - 1) * (3 ^ m + 1) := by
            have h124 : 3 ^ m ≥ 1 := h121
            have h125 : (3 ^ m) ^ 2 = (3 ^ m) * (3 ^ m) := by ring
            rw [h125]
            cases' le_iff_exists_add.mp (by omega : 1 ≤ 3 ^ m) with x hx
            simp [hx, Nat.mul_add, Nat.add_mul, Nat.add_assoc] <;> ring_nf at * <;> omega
          exact h123
        have h13 : padicValNat 2 ((3 ^ m - 1) * (3 ^ m + 1)) = padicValNat 2 (3 ^ m - 1) + padicValNat 2 (3 ^ m + 1) := by
          have ha : (3 ^ m - 1) ≠ 0 := by linarith
          have hb : (3 ^ m + 1) ≠ 0 := by linarith
          exact lte_2_3n_minus_1_h_padicValNat_mul 2 (3 ^ m - 1) (3 ^ m + 1) ha hb
        have h14 : padicValNat 2 (3 ^ (2 * m) - 1) = padicValNat 2 (3 ^ m - 1) + padicValNat 2 (3 ^ m + 1) := by
          rw [h12] at *
          exact h13
        have h15 : padicValNat 2 (3 ^ (2 * m) - 1) = (2 + padicValNat 2 m) + 1 := by
          rw [h14, ih_m, h9]
          <;> ring
        have h16 : padicValNat 2 (3 ^ (2 * m) - 1) = 3 + padicValNat 2 m := by linarith
        have h17 : m = 2 * t := h4t
        have ht_pos' : t > 0 := ht_pos
        have h18 : padicValNat 2 m = padicValNat 2 (2 * t) := by
          rw [h17]
        have h19 : padicValNat 2 (2 * t) = 1 + padicValNat 2 t := by
          have h191 : padicValNat 2 2 = 1 := by norm_num
          have h192 : t > 0 := ht_pos'
          have h193 : padicValNat 2 (2 * t) = padicValNat 2 2 + padicValNat 2 t := by
            have h194 : (2 : ℕ) ≠ 0 := by norm_num
            have h195 : t ≠ 0 := by linarith
            exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 t h194 h195
          rw [h193, h191]
          <;> ring
        have h20 : padicValNat 2 m = 1 + padicValNat 2 t := by linarith
        have h21 : padicValNat 2 (3 ^ (2 * m) - 1) = 4 + padicValNat 2 t := by linarith
        have h22 : padicValNat 2 (2 * m) = 2 + padicValNat 2 t := by
          have h221 : padicValNat 2 (2 * m) = padicValNat 2 (2 * (2 * t)) := by
            rw [h17]
          have h222 : padicValNat 2 (2 * (2 * t)) = padicValNat 2 2 + padicValNat 2 (2 * t) := by
            have h223 : (2 : ℕ) ≠ 0 := by norm_num
            have h224 : 2 * t ≠ 0 := by
              have h225 : t > 0 := ht_pos'
              omega
            exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 (2 * t) h223 h224
          have h223 : padicValNat 2 2 = 1 := by norm_num
          have h224 : padicValNat 2 (2 * t) = 1 + padicValNat 2 t := by
            have h2241 : padicValNat 2 2 = 1 := by norm_num
            have h2242 : t > 0 := ht_pos'
            have h2243 : padicValNat 2 (2 * t) = padicValNat 2 2 + padicValNat 2 t := by
              have h2244 : (2 : ℕ) ≠ 0 := by norm_num
              have h2245 : t ≠ 0 := by linarith
              exact lte_2_3n_minus_1_h_padicValNat_mul 2 2 t h2244 h2245
            rw [h2243, h2241]
            <;> ring
          have h225 : padicValNat 2 (2 * (2 * t)) = 2 + padicValNat 2 t := by
            rw [h222, h223, h224]
            <;> ring
          have h226 : padicValNat 2 (2 * m) = 2 + padicValNat 2 t := by
            have h227 : padicValNat 2 (2 * m) = padicValNat 2 (2 * (2 * t)) := by
              rw [h17]
            linarith
          linarith
        have h23 : 2 + padicValNat 2 (2 * m) = 4 + padicValNat 2 t := by linarith
        linarith

theorem lte_2_3n_minus_1 (n : ℤ) (hn : n > 0) : padicValNat 2 (3 ^ n.toNat - 1) = if n % 2 = 1 then 1 else 2 + padicValNat 2 n.toNat := by

  have h98 : n.toNat > 0 := by
    have h99 : n > 0 := hn
    omega

  by_cases h9 : n % 2 = 1
  · -- Case 1: n % 2 = 1
    have h10 : n.toNat % 2 = 1 := by
      have h101 : (n : ℤ) > 0 := by linarith
      have h102 : (n.toNat : ℤ) = n := by
        simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ n)]
      omega
    have h11 : padicValNat 2 (3 ^ n.toNat - 1) = 1 := lte_2_3n_minus_1_lemma1 n.toNat h98 h10
    simp [h9, h11]
  · -- Case 2: n % 2 ≠ 1
    have h10 : n % 2 = 0 := by omega
    have h10' : n.toNat % 2 = 0 := by
      have h101 : (n : ℤ) > 0 := by linarith
      have h102 : (n.toNat : ℤ) = n := by
        simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ n)]
      omega
    have h12 : padicValNat 2 (3 ^ n.toNat - 1) = 2 + padicValNat 2 n.toNat := lte_2_3n_minus_1_lemma2 n.toNat h98 h10'
    simp [h10, h12]
    <;> aesop

-- axiom f_n_is_power_of_two_for_even_n (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k) :
--   ∃ k : ℕ, f n = 2 ^ k  

lemma round1_h_n_toNat_ge_one (n : ℤ)
  (hn : n > 0):
  n.toNat ≥ 1 := by
  have h₁ : n ≥ 1 := by linarith
  have h₂ : n.toNat ≥ 1 := by
    omega
  exact h₂

lemma round1_h_pow_div (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h_2_pow_k_divides : (2 : ℤ) ^ k ∣ 3 ^ n.toNat - 1)
  (h_n_toNat_ge_one : n.toNat ≥ 1):
  2 ^ k ∣ 3 ^ n.toNat - 1 := by
  have h₁ : (2 : ℤ) ^ k ∣ (3 ^ n.toNat - 1 : ℤ) := h_2_pow_k_divides
  have h₂ : (2 ^ k : ℤ) ∣ (3 ^ n.toNat - 1 : ℤ) := by simpa using h₁
  have h₃ : 3 ^ n.toNat ≥ 1 := by
    have h₄ : n.toNat ≥ 1 := h_n_toNat_ge_one
    have h₅ : 3 ^ n.toNat ≥ 3 ^ 1 := by
      exact Nat.pow_le_pow_of_le_right (by norm_num) h₄
    omega
  have h₄ : (3 ^ n.toNat - 1 : ℤ) = ((3 ^ n.toNat - 1) : ℕ) := by
    simp [h₃]
  rw [h₄] at h₂
  have h₅ : (2 ^ k : ℤ) ∣ ((3 ^ n.toNat - 1) : ℕ) := by simpa using h₂
  norm_cast at h₅ ⊢
  <;> simpa using h₅

lemma round1_h_main'' (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h_n_toNat_ge_one : n.toNat ≥ 1)
  (h_pow_div : 2 ^ k ∣ 3 ^ n.toNat - 1):
  k ≤ padicValNat 2 (3 ^ n.toNat - 1) := by
  have h₁ : 3 ^ n.toNat - 1 > 0 := by
    have h₂ : n.toNat ≥ 1 := h_n_toNat_ge_one
    have h₃ : 3 ^ n.toNat ≥ 3 ^ 1 := by
      exact Nat.pow_le_pow_of_le_right (by norm_num) h₂
    omega
  have h₃ : 2 ^ k ∣ 3 ^ n.toNat - 1 := h_pow_div
  have h₄ : 3 ^ n.toNat - 1 ≠ 0 := by linarith
  exact?

lemma round1_h_k_le_padic (n : ℤ)
  (f : ℤ → ℤ)
  (k : ℕ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_2_pow_k_divides : (2 : ℤ) ^ k ∣ 3 ^ n.toNat - 1):
  k ≤ padicValNat 2 (3 ^ n.toNat - 1) := by

  have h_n_toNat_ge_one : n.toNat ≥ 1 := by
    exact round1_h_n_toNat_ge_one n hn
  have h_pow_div : 2 ^ k ∣ 3 ^ n.toNat - 1 := by
    exact round1_h_pow_div n k hn h_2_pow_k_divides h_n_toNat_ge_one
  have h_main : k ≤ padicValNat 2 (3 ^ n.toNat - 1) := by
    exact round1_h_main'' n k hn h_n_toNat_ge_one h_pow_div
  exact h_main

lemma round1_main (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f 1 = 1 := by
  have h1 : f 1 > 0 := hpos 1 (by norm_num)
  have h2 : f 1 ∣ (1 : ℤ) ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat := by
    specialize hf 1 1 (by norm_num) (by norm_num)
    simpa using hf
  have h41 : (f 1).toNat ≥ 1 := by
    have h11 : f 1 ≥ 1 := by linarith
    have h411 : (f 1).toNat ≥ 1 := by
      omega
    linarith
  have h42 : f 1 ∣ (f 1) ^ (f 1).toNat := by
    apply dvd_pow
    · exact dvd_refl (f 1)
    · omega
  have h5 : f 1 ∣ 1 := by
    have h21 : f 1 ∣ (f 1) ^ (f 1).toNat := h42
    have h22 : f 1 ∣ (1 : ℤ) ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat := h2
    have h51 : f 1 ∣ ((1 : ℤ) ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat) + (f 1) ^ (f 1).toNat := by
      apply Int.dvd_add
      · exact h22
      · exact h21
    have h52 : ((1 : ℤ) ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat) + (f 1) ^ (f 1).toNat = 1 := by
      norm_num
      <;> ring
    rw [h52] at h51
    exact h51
  have h6 : f 1 = 1 := by
    have h53 : f 1 ∣ 1 := h5
    have h54 : f 1 > 0 := h1
    have h553 : f 1 ≤ 1 := by
      exact Int.le_of_dvd (by norm_num) h53
    omega
  exact h6

theorem imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : (∀ k : ℤ, k > 0 → f k = 1) ∨ f 1 = 1:= by

  have h6 : f 1 = 1 := round1_main f hpos hf
  right
  exact h6

lemma round1_h_subcase1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_subcase1 : ∀ k : ℤ, k > 0 → f k = k):
  f n ≤ 4 * n := by
  have h1 : f n = n := h_subcase1 n hn
  rw [h1]
  have h2 : n ≤ 4 * n := by nlinarith
  linarith


lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_int_toNat_mul (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a * b).toNat = a.toNat * b.toNat := by
  have ha1 : a = (a.toNat : ℤ) := by
    simp [ha]
  have hb1 : b = (b.toNat : ℤ) := by
    simp [hb]
  have h1 : a * b = ((a.toNat * b.toNat : ℕ) : ℤ) := by
    rw [ha1, hb1]
    simp [mul_comm]
    <;> ring
  have h2 : 0 ≤ a * b := mul_nonneg ha hb
  have h4 : ((a * b).toNat : ℤ) = a * b := by
    simp [Int.toNat_of_nonneg h2]
  have h5 : ((a * b).toNat : ℤ) = ((a.toNat * b.toNat : ℕ) : ℤ) := by linarith
  have h6 : (a * b).toNat = a.toNat * b.toNat := by
    norm_cast at h5 ⊢ <;> omega
  exact h6

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h64 (p : ℤ) (hp_nonneg : 0 ≤ p) (k : ℕ) : (p : ℤ) ^ k = ↑((p.toNat) ^ k) := by
  have hp1 : p = (p.toNat : ℤ) := by
    simp [hp_nonneg]
  rw [hp1]
  simp [pow_succ]
  <;> ring

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_p_divides_f_p_stronger (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (p : ℤ) (hp : Nat.Prime p.toNat) (hfp_ne_1 : f p ≠ 1) (hp_pos : p > 0):
  ∃ j : ℕ, j ≥ 1 ∧ f p = p ^ j := by
  have h13 : f p > 0 := hpos p (by linarith)
  have h27 := hf p p (by linarith) (by linarith)
  have h28 : f p ∣ p ^ p.toNat - (f p) ^ (f p).toNat := h27
  have h29 : (f p).toNat > 0 := by
    have h30 : f p > 0 := h13
    omega
  have h31 : f p ∣ (f p) ^ (f p).toNat := by
    apply dvd_pow
    · rfl
    · omega
  have h32 : f p ∣ p ^ p.toNat := by
    have h323 : f p ∣ (p ^ p.toNat - (f p) ^ (f p).toNat) + (f p) ^ (f p).toNat := by
      apply Int.dvd_add
      · exact h28
      · exact h31
    have h324 : (p ^ p.toNat - (f p) ^ (f p).toNat) + (f p) ^ (f p).toNat = p ^ p.toNat := by ring
    rw [h324] at h323
    exact h323
  have h322 : ∃ c : ℤ, p ^ p.toNat = f p * c := by
    obtain ⟨c, hc⟩ := h32
    refine ⟨c,?_⟩
    linarith
  rcases h322 with ⟨c, hc⟩
  have h3251 : p ^ p.toNat > 0 := by
    have h32511 : p > 0 := hp_pos
    have h32512 : p.toNat ≥ 1 := by
      have h1 : Nat.Prime p.toNat := hp
      have h2 : p.toNat ≥ 2 := Nat.Prime.two_le h1
      linarith
    have h32513 : p ^ p.toNat > 0 := by
      apply pow_pos
      linarith
    simpa using h32513
  have hc_pos : c > 0 := by
    have h1 : p ^ p.toNat = f p * c := hc
    have h2 : p ^ p.toNat > 0 := h3251
    have h3 : f p > 0 := h13
    nlinarith
  have h3261 : (p ^ p.toNat : ℤ).toNat = (f p : ℤ).toNat * (c : ℤ).toNat := by
    have h1 : p ^ p.toNat = f p * c := hc
    have h11 : f p ≥ 0 := by linarith
    have h12 : c ≥ 0 := by linarith
    have h131 : (f p * c : ℤ) ≥ 0 := mul_nonneg h11 h12
    have h14 : ((f p * c : ℤ).toNat) = (f p : ℤ).toNat * (c : ℤ).toNat := by
      exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_int_toNat_mul (f p) c h11 h12
    have h15 : (p ^ p.toNat : ℤ) ≥ 0 := by linarith
    have h16 : ((p ^ p.toNat : ℤ).toNat) = ((f p * c : ℤ).toNat) := by
      rw [h1]
      <;> rfl
    linarith
  have h3262 : (f p : ℤ).toNat ∣ (p ^ p.toNat : ℤ).toNat := by
    use (c : ℤ).toNat
    <;> linarith
  have h326 : (f p : ℤ).toNat ∣ (p ^ p.toNat : ℤ).toNat := h3262
  have h324 : ∀ (k : ℕ), (p ^ k : ℤ).toNat = (p.toNat) ^ k := by
    intro k
    have h1 : p ≥ 0 := by linarith
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h2 : p ^ k ≥ 0 := by positivity
      have h3 : (p ^ (k + 1) : ℤ) = p * (p ^ k) := by ring
      have h4 : (p ^ (k + 1) : ℤ) ≥ 0 := by positivity
      have h5 : ((p ^ (k + 1) : ℤ).toNat) = (p : ℤ).toNat * ((p ^ k : ℤ).toNat) := by
        rw [h3]
        exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_int_toNat_mul p (p ^ k) (by linarith) (by linarith)
      rw [h5]
      rw [ih]
      simp [pow_succ]
      <;> ring_nf <;> norm_cast <;> aesop
  have h3241 : (p ^ p.toNat : ℤ).toNat = (p.toNat) ^ p.toNat := by
    specialize h324 (p.toNat)
    simpa using h324
  have h323 : (f p : ℤ).toNat ∣ (p.toNat) ^ p.toNat := by
    rw [h3241] at h326
    exact h326
  have h325 : ∃ j : ℕ, j ≤ p.toNat ∧ (f p : ℤ).toNat = (p.toNat) ^ j := by
    exact?
  rcases h325 with ⟨j, hj1, hj2⟩
  have h326 : j ≥ 1 := by
    by_contra h3261
    have h3262 : j = 0 := by omega
    rw [h3262] at hj2
    have h3263 : (f p : ℤ).toNat = 1 := by simpa using hj2
    have h3264 : f p = 1 := by
      have h1 : 0 ≤ f p := by linarith
      omega
    contradiction
  refine ⟨j, h326,?_⟩
  have h3271 : (f p : ℤ).toNat = (p.toNat) ^ j := hj2
  have h2 : 0 ≤ f p := by linarith
  have h64 : ∀ (k : ℕ), (p : ℤ) ^ k = ↑((p.toNat) ^ k) := by
    intro k
    exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h64 p (by linarith) k
  have h3272 : f p = (p : ℤ) ^ j := by
    have h1 : (f p : ℤ).toNat = (p.toNat) ^ j := h3271
    have h22 : (f p) = ↑((f p : ℤ).toNat) := by
      simp [show 0 ≤ f p by linarith]
    have h23 : ((p : ℤ) ^ j) = ↑((p.toNat) ^ j) := by
      simpa using h64 j
    have h24 : ↑((f p : ℤ).toNat) = ↑((p.toNat) ^ j) := by
      rw [h1]
      <;> simp
    rw [h22, h24, h23]
    <;> simp
  simpa using h3272

lemma fermat_little_theorem_int_version (q : ℕ) (hq : Nat.Prime q) (x : ℤ) : (q : ℤ) ∣ x ^ q - x := by
  have h1 : (x : ZMod q) ^ q = (x : ZMod q) := by
    by_cases h : (x : ZMod q) = 0
    · -- Case 1: (x : ZMod q) = 0
      have h2 : (x : ZMod q) = 0 := h
      have h3 : q ≥ 2 := Nat.Prime.two_le hq
      have h4 : q ≥ 1 := by linarith
      have h5 : (0 : ZMod q) ^ q = 0 := by
        have h51 : q ≥ 1 := by linarith
        have h52 : (0 : ZMod q) ^ q = 0 := by
          have h521 : q ≥ 1 := by linarith
          have h522 : (0 : ZMod q) ^ 1 = 0 := by simp
          have h523 : ∀ (n : ℕ), n ≥ 1 → (0 : ZMod q) ^ n = 0 := by
            intro n hn
            induction n with
            | zero => contradiction
            | succ n ih =>
              by_cases h524 : n = 0
              · simp [h524]
              · have h525 : n ≥ 1 := by omega
                have ih' := ih h525
                simp [pow_succ, ih']
                <;> ring
          exact h523 q h51
        exact h52
      have h6 : (x : ZMod q) ^ q = (0 : ZMod q) ^ q := by
        rw [h2]
      rw [h6, h5, h2]
      <;> rfl
    · -- Case 2: (x : ZMod q) ≠ 0
      haveI : Fact (Nat.Prime q) := ⟨hq⟩
      have h2 : (x : ZMod q) ≠ 0 := h
      have h3 : (x : ZMod q) ^ (q - 1) = 1 := by
        apply?
      have h4 : (x : ZMod q) ^ q = (x : ZMod q) := by
        calc
          (x : ZMod q) ^ q = (x : ZMod q) ^ ((q - 1) + 1) := by
            have h41 : q ≥ 2 := Nat.Prime.two_le hq
            have h42 : (q - 1) + 1 = q := by omega
            rw [h42]
            <;> ring
          _ = (x : ZMod q) ^ (q - 1) * (x : ZMod q) := by
            rw [pow_add]
            <;> ring
          _ = 1 * (x : ZMod q) := by rw [h3]
          _ = (x : ZMod q) := by ring
      exact h4
  have h3 : ((x ^ q - x : ℤ) : ZMod q) = 0 := by
    simp_all [sub_eq_zero]
    <;> norm_cast at * <;>
    aesop
  have h4 : (q : ℤ) ∣ x ^ q - x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa using h3
  exact h4

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main_proof (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (p : ℤ) (hp : Nat.Prime p.toNat) (hfp_ne_1 : f p ≠ 1) (hp_pos : p > 0) (h_f1_eq_1 : f 1 = 1) (h_p_divides_f_p_stronger : ∃ j : ℕ, j ≥ 1 ∧ f p = p ^ j):
  ∀ b : ℤ, b > 0 → b ≡ f b [ZMOD p] := by
  have h13 : f p > 0 := hpos p (by linarith)
  have h_prime_p : Prime p := by
    have h1 : Nat.Prime p.toNat := hp
    have h2 : Prime (p.toNat : ℤ) := by exact?
    have h3 : (p.toNat : ℤ) = p := by
      simp [show 0 ≤ p by linarith]
    have h4 : Prime p := by
      rw [h3] at h2
      exact h2
    exact h4
  rcases h_p_divides_f_p_stronger with ⟨j, hj_ge1, hj_eq⟩
  intro b hb
  have h19 : f p ∣ b ^ p.toNat - (f b) ^ (f p).toNat := by
    specialize hf p b (by linarith) (by linarith)
    simpa using hf
  have h21 : p ∣ f p := by
    have h1 : f p = p ^ j := hj_eq
    have h_j_ge_1 : j ≥ 1 := hj_ge1
    have h_j_pos : 0 < j := by linarith
    have h : ∃ k : ℕ, j = k + 1 := by
      refine ⟨j - 1,?_⟩
      omega
    rcases h with ⟨k, hk⟩
    have h2 : f p = p ^ (k + 1) := by
      rw [h1, hk]
      <;> ring
    have h3 : p ∣ p ^ (k + 1) := by
      use p ^ k
      <;> ring
    rw [h2] at *
    exact h3
  have hX : p ∣ b ^ p.toNat - (f b) ^ (f p).toNat := dvd_trans h21 h19
  have h20 : p ∣ b ^ p.toNat - b := by
    have h201 : (p.toNat : ℤ) ∣ b ^ p.toNat - b := by
      exact fermat_little_theorem_int_version p.toNat hp b
    have h202 : (p.toNat : ℤ) = p := by
      simp [show 0 ≤ p by linarith]
    rw [h202] at h201
    exact h201
  have h222 : p ∣ (f b) ^ p.toNat - f b := by
    have h2221 : (p.toNat : ℤ) ∣ (f b) ^ p.toNat - f b := by
      exact fermat_little_theorem_int_version p.toNat hp (f b)
    have h2222 : (p.toNat : ℤ) = p := by
      simp [show 0 ≤ p by linarith]
    rw [h2222] at h2221
    exact h2221
  have hY : p ∣ b - b ^ p.toNat := by
    have h20' : p ∣ b ^ p.toNat - b := h20
    have h201 : p ∣ -(b ^ p.toNat - b) := dvd_neg.mpr h20'
    have h202 : -(b ^ p.toNat - b) = b - b ^ p.toNat := by ring
    rw [h202] at h201
    exact h201
  have h231 : p ∣ (b - b ^ p.toNat) + (b ^ p.toNat - (f b) ^ (f p).toNat) := by
    apply Int.dvd_add
    · exact hY
    · exact hX
  have h232 : (b - b ^ p.toNat) + (b ^ p.toNat - (f b) ^ (f p).toNat) = b - (f b) ^ (f p).toNat := by ring
  have h23 : p ∣ b - (f b) ^ (f p).toNat := by
    rw [h232] at h231
    exact h231
  have h23' : b ≡ (f b) ^ (f p).toNat [ZMOD p] := by
    simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h23
  have h_induction : ∀ (k : ℕ), k ≥ 1 → (f b) ^ ((p.toNat) ^ k) ≡ f b [ZMOD p] := by
    intro k hk
    induction k with
    | zero =>
      exfalso
      <;> omega
    | succ k ih =>
      by_cases h : k = 0
      · -- Base case: k = 0, so k + 1 = 1
        subst h
        have h22_flt : (f b) ^ p.toNat ≡ f b [ZMOD p] := by
          have h2221 : p ∣ (f b) ^ p.toNat - f b := h222
          simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h2221
        simpa using h22_flt
      · -- Inductive step: k ≠ 0, so k ≥ 1
        have h_k_ge1 : k ≥ 1 := by omega
        have ih' : (f b) ^ ((p.toNat) ^ k) ≡ f b [ZMOD p] := ih (by omega)
        have h22_flt : (f b) ^ p.toNat ≡ f b [ZMOD p] := by
          have h2221 : p ∣ (f b) ^ p.toNat - f b := h222
          simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h2221
        have h1 : ((f b) ^ ((p.toNat) ^ k)) ^ p.toNat ≡ (f b) ^ p.toNat [ZMOD p] := by
          exact Int.ModEq.pow p.toNat ih'
        have h2 : ((f b) ^ ((p.toNat) ^ k)) ^ p.toNat ≡ f b [ZMOD p] := by
          exact Int.ModEq.trans h1 h22_flt
        have h3 : (f b) ^ ((p.toNat) ^ (k + 1)) = ((f b) ^ ((p.toNat) ^ k)) ^ p.toNat := by
          have h31 : (p.toNat) ^ (k + 1) = (p.toNat) * (p.toNat) ^ k := by ring
          rw [h31]
          rw [show (f b) ^ ((p.toNat) * (p.toNat) ^ k) = ((f b) ^ ((p.toNat) ^ k)) ^ (p.toNat) by
            rw [← pow_mul]
            <;> ring]
          <;> ring
        have h4 : (f b) ^ ((p.toNat) ^ (k + 1)) ≡ f b [ZMOD p] := by
          rw [h3]
          exact h2
        simpa using h4
  have h5 : (f p).toNat = (p.toNat) ^ j := by
    have h324 : ∀ (k : ℕ), (p ^ k : ℤ).toNat = (p.toNat) ^ k := by
      intro k
      have h1 : p ≥ 0 := by linarith
      induction k with
      | zero =>
        simp
      | succ k ih =>
        have h2 : p ^ k ≥ 0 := by positivity
        have h3 : (p ^ (k + 1) : ℤ) = p * (p ^ k) := by ring
        have h4 : (p ^ (k + 1) : ℤ) ≥ 0 := by positivity
        have h5 : ((p ^ (k + 1) : ℤ).toNat) = (p : ℤ).toNat * ((p ^ k : ℤ).toNat) := by
          rw [h3]
          exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_int_toNat_mul p (p ^ k) (by linarith) (by linarith)
        rw [h5]
        rw [ih]
        simp [pow_succ]
        <;> ring_nf <;> norm_cast <;> aesop
    have h51 : f p = p ^ j := hj_eq
    have h512 : 0 ≤ f p := by linarith
    have h513 : (f p).toNat = ((p ^ j : ℤ)).toNat := by rw [h51]
    rw [h513]
    have h514 := h324 j
    simpa using h514
  have h24 : (f b) ^ ((p.toNat) ^ j) ≡ f b [ZMOD p] := h_induction j (by linarith)
  have h24' : (f b) ^ (f p).toNat ≡ f b [ZMOD p] := by
    have h6 : (f b) ^ ((p.toNat) ^ j) ≡ f b [ZMOD p] := h24
    have h7 : (f p).toNat = (p.toNat) ^ j := h5
    have h8 : (f b) ^ ((p.toNat) ^ j) = (f b) ^ (f p).toNat := by
      rw [h7]
      <;> rfl
    rw [h8] at h6
    exact h6
  have h_final : b ≡ f b [ZMOD p] := Int.ModEq.trans h23' h24'
  simpa using h_final

theorem  f_b_equiv_b_mod_p_of_f_p_ne_1 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (p : ℤ) (hp : Nat.Prime p.toNat) (hfp_ne_1 : f p ≠ 1):
  ∀ b : ℤ, b > 0 → b ≡ f b [ZMOD p]  := by


  have hp_pos : p > 0 := by
    by_contra h
    have h1 : p ≤ 0 := by linarith
    have h2 : p.toNat = 0 := by omega
    rw [h2] at hp
    norm_num at hp
    <;> contradiction

  have h_f1_eq_1 : f 1 = 1 := by
    have h11 : f 1 > 0 := hpos 1 (by norm_num)
    have h12 : f 1 ∣ 1 ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat := by
      specialize hf 1 1 (by norm_num) (by norm_num)
      simpa using hf
    have h13 : f 1 ∣ (f 1) ^ (f 1).toNat := by
      apply dvd_pow
      · rfl
      · have h11' : (f 1).toNat > 0 := by omega
        omega
    have h14 : f 1 ∣ 1 := by
      have h142 : f 1 ∣ 1 ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat := h12
      have h141 : f 1 ∣ (f 1) ^ (f 1).toNat := h13
      have h143 : f 1 ∣ (f 1) ^ (f 1).toNat + (1 ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat) := by
        apply Int.dvd_add
        · exact h141
        · simpa using h142
      have h144 : (f 1) ^ (f 1).toNat + (1 ^ (1 : ℤ).toNat - (f 1) ^ (f 1).toNat) = 1 := by ring
      rw [h144] at h143
      exact h143
    have h15 : f 1 = 1 := by
      have h151 : f 1 ∣ 1 := h14
      have h152 : f 1 > 0 := h11
      have h153 : f 1 ≤ 1 := by exact Int.le_of_dvd (by norm_num) h151
      omega
    exact h15

  have h_p_divides_f_p_stronger : ∃ j : ℕ, j ≥ 1 ∧ f p = p ^ j := by
    exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_p_divides_f_p_stronger n f hn hpos hf p hp hfp_ne_1 hp_pos

  exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main_proof n f hn hpos hf p hp hfp_ne_1 hp_pos h_f1_eq_1 h_p_divides_f_p_stronger


lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case2 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (hf_not_id : ∃ i > 0, f i ≠ i) : ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1 := by
  rcases hf_not_id with ⟨i₀, hi₀_pos, hfi₀_ne_i₀⟩
  by_cases h : ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1
  · exact h
  · push_neg at h
    have h4 : ∀ (p : ℤ), Nat.Prime p.toNat → p > k → f p ≠ 1 := h
    have h_fi₀_pos : f i₀ > 0 := hpos i₀ hi₀_pos
    have h3 : ∃ q : ℕ, Nat.Prime q ∧ q > (k : ℤ).toNat ∧ q > (i₀ : ℤ).toNat ∧ q > ((f i₀ : ℤ).toNat) := by
      set M : ℕ := max ((k : ℤ).toNat) (max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat)) with hM
      have h1 := Nat.exists_infinite_primes (M + 1)
      rcases h1 with ⟨q, hq_ge, hq_prime⟩
      have hq_gt_M : M < q := by linarith
      have h11 : (k : ℤ).toNat ≤ M := by
        simp [hM]
        <;> apply le_max_left
      have h12 : (i₀ : ℤ).toNat ≤ M := by
        have h121 : (i₀ : ℤ).toNat ≤ max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat) := by apply le_max_left
        have h122 : max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat) ≤ max ((k : ℤ).toNat) (max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat)) := by apply le_max_right
        have h123 : (i₀ : ℤ).toNat ≤ max ((k : ℤ).toNat) (max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat)) := by linarith
        rw [hM]
        exact h123
      have h13 : ((f i₀ : ℤ).toNat) ≤ M := by
        have h131 : ((f i₀ : ℤ).toNat) ≤ max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat) := by apply le_max_right
        have h132 : max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat) ≤ max ((k : ℤ).toNat) (max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat)) := by apply le_max_right
        have h133 : ((f i₀ : ℤ).toNat) ≤ max ((k : ℤ).toNat) (max ((i₀ : ℤ).toNat) ((f i₀ : ℤ).toNat)) := by linarith
        rw [hM]
        exact h133
      have h11' : (k : ℤ).toNat < q := by linarith
      have h12' : (i₀ : ℤ).toNat < q := by linarith
      have h13' : ((f i₀ : ℤ).toNat) < q := by linarith
      refine ⟨q, hq_prime, by simpa using h11', by simpa using h12', by simpa using h13'⟩
    rcases h3 with ⟨q, hq_prime, hq_gt_k, hq_gt_i₀, hq_gt_fi₀⟩
    have hq_gt_k2 : (q : ℤ) > k := by
      have hq_gt_k21 : (q : ℤ) > (k : ℤ).toNat := by exact_mod_cast hq_gt_k
      have h4 : 0 ≤ k := by linarith
      have h5 : ((k : ℤ).toNat : ℤ) = k := by
        simp [Int.toNat_of_nonneg h4]
      linarith
    have hq_gt_i₀2 : (q : ℤ) > i₀ := by
      have hq_gt_i₀21 : (q : ℤ) > (i₀ : ℤ).toNat := by exact_mod_cast hq_gt_i₀
      have h4 : 0 ≤ i₀ := by linarith
      have h5 : ((i₀ : ℤ).toNat : ℤ) = i₀ := by
        simp [Int.toNat_of_nonneg h4]
      linarith
    have hq_gt_fi₀2 : (q : ℤ) > f i₀ := by
      have hq_gt_fi₀21 : (q : ℤ) > ((f i₀ : ℤ).toNat) := by exact_mod_cast hq_gt_fi₀
      have h4 : 0 ≤ f i₀ := by linarith [h_fi₀_pos]
      have h5 : (((f i₀ : ℤ).toNat : ℤ)) = f i₀ := by
        simp [Int.toNat_of_nonneg h4]
      linarith
    have hq_pos : (q : ℤ) > 0 := by linarith
    have h5 : f (q : ℤ) ≠ 1 := h4 (q : ℤ) (by simpa using hq_prime) hq_gt_k2
    have h6 : i₀ ≡ f i₀ [ZMOD (q : ℤ)] := by
      have h61 := f_b_equiv_b_mod_p_of_f_p_ne_1 (q : ℤ) f hq_pos hpos hf (q : ℤ) (by simpa using hq_prime) h5
      specialize h61 i₀ hi₀_pos
      simpa using h61
    have h62 : (q : ℤ) ∣ i₀ - f i₀ := by simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h6
    by_cases h7 : f i₀ ≤ i₀
    · -- Case 2.1: f i₀ ≤ i₀
      have h71 : i₀ - f i₀ ≥ 0 := by linarith
      have h72 : i₀ - f i₀ > 0 := by
        by_contra h721
        have h722 : i₀ - f i₀ ≤ 0 := by linarith
        have h723 : i₀ - f i₀ = 0 := by linarith
        have h724 : f i₀ = i₀ := by linarith
        contradiction
      have h73 : i₀ - f i₀ < (q : ℤ) := by
        have h731 : i₀ - f i₀ < i₀ := by
          linarith [h_fi₀_pos]
        have h732 : i₀ < (q : ℤ) := by linarith
        linarith
      have h74 : (q : ℤ) ∣ i₀ - f i₀ := h62
      have h75 : 0 < i₀ - f i₀ := by linarith
      have h76 : (q : ℤ) ≤ i₀ - f i₀ := by exact Int.le_of_dvd (by linarith) h74
      linarith
    · -- Case 2.2: f i₀ > i₀
      have h8 : f i₀ > i₀ := by linarith
      have h9 : (q : ℤ) ∣ f i₀ - i₀ := by
        have h91 : (q : ℤ) ∣ i₀ - f i₀ := h62
        have h92 : (q : ℤ) ∣ -(i₀ - f i₀) := by exact dvd_neg.mpr h91
        have h93 : -(i₀ - f i₀) = f i₀ - i₀ := by ring
        rw [h93] at h92
        exact h92
      have h94 : f i₀ - i₀ > 0 := by linarith
      have h95 : (q : ℤ) ≤ f i₀ - i₀ := by
        exact Int.le_of_dvd (by linarith) h9
      have h96 : (q : ℤ) + i₀ ≤ f i₀ := by linarith
      linarith

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case1 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (h11 : ∀ k : ℤ, k > 0 → f k = 1) : ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1 := by
  have h111 : ∀ k : ℤ, k > 0 → f k = 1 := h11
  have h2 : ∃ q : ℕ, Nat.Prime q ∧ q > (k : ℤ).toNat := by
    have h21 := Nat.exists_infinite_primes ((k : ℤ).toNat + 1)
    rcases h21 with ⟨q, hq_ge, hq_prime⟩
    have hq_gt : (k : ℤ).toNat < q := by linarith
    refine ⟨q, hq_prime, hq_gt⟩
  rcases h2 with ⟨q, hq_prime, hq_gt⟩
  have hq_gt2 : (q : ℤ) > k := by
    have h1 : (q : ℤ) > (k : ℤ).toNat := by exact_mod_cast hq_gt
    have h2 : 0 ≤ k := by linarith
    have h3 : ((k : ℤ).toNat : ℤ) = k := by
      simp [Int.toNat_of_nonneg h2]
    linarith
  have hq_pos : (q : ℤ) > 0 := by linarith
  have h_fq_eq_1 : f (q : ℤ) = 1 := h111 (q : ℤ) (by linarith)
  have hq_prime2 : Nat.Prime ((q : ℤ).toNat) := by simpa using hq_prime
  refine ⟨(q : ℤ), hq_prime2, hq_gt2, h_fq_eq_1⟩

theorem f_is_not_identity_implies_f_p_eq_1_for_some_p_gt_k (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (hf_not_id : ∃ i > 0, f i ≠ i):
  ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1  := by

  have h1 : (∀ k : ℤ, k > 0 → f k = 1) ∨ f 1 = 1 := by
    exact imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf

  rcases h1 with h11 | h12
  · exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case1 f hpos hf k hk_pos h11
  · exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case2 f hpos hf k hk_pos hf_not_id

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h_main (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k)
  (p0 : ℤ)
  (hp0_prime : Nat.Prime p0.toNat)
  (hfp0_eq_1 : f p0 = 1)
  (h_f_not_const_1 : ∃ n, n > 0 ∧ f n ≠ 1):
  ∀ (p : ℤ), Nat.Prime p.toNat → p ≥ p0 → f p = 1 := by
  intro p hp_prime hp_ge_p0
  by_cases h : f p = 1
  · exact h
  · -- Case: f p ≠ 1
    have h_p_pos : p > 0 := by
      by_contra h_p_nonpos
      have h_p_le_zero : p ≤ 0 := by linarith
      have h1 : p.toNat = 0 := by
        omega
      have h2 : Nat.Prime p.toNat := hp_prime
      rw [h1] at h2
      norm_num at h2
      <;> contradiction
    have h_p0_pos : p0 > 0 := by
      by_contra h_p0_nonpos
      have h_p0_le_zero : p0 ≤ 0 := by linarith
      have h1 : p0.toNat = 0 := by
        omega
      have h2 : Nat.Prime p0.toNat := hp0_prime
      rw [h1] at h2
      norm_num at h2
      <;> contradiction
    have h_p0_ge_2 : p0 ≥ 2 := by
      have h1 : Nat.Prime p0.toNat := hp0_prime
      have h2 : p0.toNat ≥ 2 := Nat.Prime.two_le h1
      omega
    have h_p0_minus_1_pos : p0 - 1 > 0 := by linarith
    have h1 : ∀ b : ℤ, b > 0 → b ≡ f b [ZMOD p] := by
      exact f_b_equiv_b_mod_p_of_f_p_ne_1 n f hn hpos hf p hp_prime h
    have h2 : p0 ≡ f p0 [ZMOD p] := by
      specialize h1 p0 (by linarith)
      exact h1
    have h3 : p0 ≡ 1 [ZMOD p] := by
      rw [hfp0_eq_1] at h2
      exact h2
    have h4 : p ∣ (p0 - 1) := by
      simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h3
    have h5 : ∃ k : ℤ, p0 - 1 = p * k := by
      obtain ⟨k, hk⟩ := h4
      refine' ⟨k, _⟩
      linarith
    rcases h5 with ⟨k, hk⟩
    have h6 : k > 0 := by
      by_contra h6
      have h6' : k ≤ 0 := by linarith
      have h7 : p * k ≤ 0 := by nlinarith
      linarith
    have h7 : k ≥ 1 := by linarith
    have h8 : p0 - 1 ≥ p := by
      nlinarith
    have h9 : p < p0 := by linarith
    linarith

theorem f_is_1_on_all_primes_ge_p0_if_f_p0_eq_1_and_f_is_not_const_1 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k) {p0 : ℤ} (hp0_prime : Nat.Prime p0.toNat) (hfp0_eq_1 : f p0 = 1) (h_f_not_const_1 : ∃ n, n > 0 ∧ f n ≠ 1): ∀ p, Nat.Prime p.toNat → p ≥ p0 → f p = 1   := by

  have h_main : ∀ (p : ℤ), Nat.Prime p.toNat → p ≥ p0 → f p = 1 := by
    exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h_main n f hn hpos hf h_exists_k p0 hp0_prime hfp0_eq_1 h_f_not_const_1
  intro p hp_prime hp_ge_p0
  exact h_main p hp_prime hp_ge_p0

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat):
  (∃ n : ℤ, n > 0 ∧ f n ≠ n) → ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1 := by
  intro h_f_not_id
  intro p hp_prime hp_gt_2
  by_cases h : f p = 1
  · exact h
  · -- Case f p ≠ 1
    have hfp_ne_1 : f p ≠ 1 := h
    have h1 := imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf
    cases h1 with
    | inl h_f_const_1 =>
      have h2 : f p = 1 := h_f_const_1 p (by linarith)
      contradiction
    | inr h_f1_eq_1 =>
      have h_f1_eq_1 : f 1 = 1 := h_f1_eq_1
      have h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k := by
        rcases h_f_not_id with ⟨n, hn_pos, hfn_ne_n⟩
        by_cases h_n_gt_1 : n > 1
        · -- Case n > 1
          refine ⟨n, h_n_gt_1, hfn_ne_n⟩
        · -- Case n ≤ 1
          have h_n_le_1 : n ≤ 1 := by linarith
          have h_n_eq_1 : n = 1 := by linarith
          rw [h_n_eq_1] at hfn_ne_n
          contradiction
      have h_p_pos : p > 0 := by linarith
      have h_exists_p0 : ∃ p0 : ℤ, Nat.Prime p0.toNat ∧ p0 > p ∧ f p0 = 1 := by
        exact f_is_not_identity_implies_f_p_eq_1_for_some_p_gt_k f hpos hf p h_p_pos h_f_not_id
      rcases h_exists_p0 with ⟨p0, hp0_prime, hp0_gt_p, hfp0_eq_1⟩
      have h_p0_prime' : Nat.Prime p0.toNat := hp0_prime
      have h_p0_pos : p0 > 0 := by linarith
      have h_b_equiv : ∀ b : ℤ, b > 0 → b ≡ f b [ZMOD p] := by
        exact f_b_equiv_b_mod_p_of_f_p_ne_1 n f hn hpos hf p hp_prime hfp_ne_1
      have h11 : p0 ≡ f p0 [ZMOD p] := h_b_equiv p0 (by linarith)
      have h11' : p0 ≡ 1 [ZMOD p] := by
        rw [hfp0_eq_1] at h11
        simpa using h11
      have h_p_div_p0_sub_1 : p ∣ p0 - 1 := by
        simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h11'
      have h_f_not_const_1 : ∃ n : ℤ, n > 0 ∧ f n ≠ 1 := by
        refine ⟨p, by linarith, hfp_ne_1⟩
      have h_forall_primes_ge_p0_f_eq_1 : ∀ (q : ℤ), Nat.Prime q.toNat → q ≥ p0 → f q = 1 := by
        exact f_is_1_on_all_primes_ge_p0_if_f_p0_eq_1_and_f_is_not_const_1 n f hn hpos hf h_exists_k hp0_prime hfp0_eq_1 h_f_not_const_1
      have h_p_toNat_gt_2 : p.toNat > 2 := by
        have h_p_gt_2' : p > 2 := hp_gt_2
        norm_cast at h_p_gt_2' ⊢
        <;> omega
      have h_p_toNat_pos : 0 < p.toNat := by
        have h_p_gt_2' : p > 2 := hp_gt_2
        have h1 : (p : ℤ) > 2 := h_p_gt_2'
        have h2 : 0 < (p : ℤ) := by linarith
        have h3 : 0 < p.toNat := by
          omega
        exact_mod_cast h3
      have h_p_not_dvd_2 : ¬ (p.toNat ∣ 2) := by
        have h_p_prime' : Nat.Prime p.toNat := by exact_mod_cast hp_prime
        intro h_dvd
        have h4 : p.toNat ≤ 2 := Nat.le_of_dvd (by norm_num) h_dvd
        have h5 : p.toNat > 2 := by exact_mod_cast h_p_toNat_gt_2
        linarith
      have h2_unit : IsUnit (2 : ZMod p.toNat) := by
        haveI : Fact (Nat.Prime p.toNat) := ⟨by exact_mod_cast hp_prime⟩
        have h_p_toNat_gt_2' : p.toNat > 2 := by exact_mod_cast h_p_toNat_gt_2
        have h_p_toNat_ne_2 : p.toNat ≠ 2 := by linarith
        have h : (2 : ZMod p.toNat) ≠ 0 := by
          intro h6
          have h7 : (p.toNat : ℕ) ∣ 2 := by
            exact (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p.toNat).mp h6
          contradiction
        exact isUnit_iff_ne_zero.mpr h
      have h_p_toNat_ne_zero : p.toNat ≠ 0 := by linarith
      haveI : NeZero (p.toNat) := ⟨h_p_toNat_ne_zero⟩
      have h_exists_q : ∃ q : ℕ, q > p0.toNat ∧ Nat.Prime q ∧ (q : ZMod p.toNat) = (2 : ZMod p.toNat) := by
        have h9 := Nat.forall_exists_prime_gt_and_eq_mod h2_unit (p0.toNat)
        rcases h9 with ⟨q, hq1, hq2, hq3⟩
        refine ⟨q, ?_, hq2, hq3⟩
        exact_mod_cast hq1
      rcases h_exists_q with ⟨q, hq_gt_p0, hq_prime, hq_mod⟩
      have hq_gt_p0' : (q : ℤ) > p0 := by
        have h10 : q > p0.toNat := hq_gt_p0
        have h11 : (q : ℤ) > (p0.toNat : ℤ) := by exact_mod_cast h10
        have h12 : (p0.toNat : ℤ) = p0 := by
          have h13 : 0 ≤ p0 := by linarith
          simp [Int.toNat_of_nonneg h13]
        rw [h12] at h11
        linarith
      have hq_pos : (q : ℤ) > 0 := by linarith
      have hq_ge_p0 : (q : ℤ) ≥ p0 := by linarith
      have h14 : Nat.Prime q := hq_prime
      have h15 : f (q : ℤ) = 1 := by
        have h141 : Nat.Prime ((q : ℤ)).toNat := by
          have h151 : 0 < (q : ℤ) := by linarith
          have h161 : ((q : ℤ)).toNat = q := by
            simp [abs_of_pos h151]
          rw [h161]
          exact_mod_cast h14
        exact h_forall_primes_ge_p0_f_eq_1 (q : ℤ) h141 (by linarith)
      have h13 : (q : ℤ) ≡ f (q : ℤ) [ZMOD p] := h_b_equiv (q : ℤ) (by linarith)
      have h14' : (q : ℤ) ≡ 1 [ZMOD p] := by
        rw [h15] at h13
        simpa using h13
      have h151 : p ∣ (q : ℤ) - 1 := by
        simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h14'
      have hq_ge_2 : q ≥ 2 := by
        have h_p0_gt_2 : p0 > 2 := by linarith
        have h_p0_toNat_gt_2 : p0.toNat > 2 := by
          have h1 : p0 > 2 := by linarith
          have h2 : p0.toNat > 2 := by omega
          exact_mod_cast h2
        have hq_gt_p0 : q > p0.toNat := by linarith
        have h1 : q > p0.toNat := by linarith
        have h2 : p0.toNat > 2 := by linarith
        have h3 : q > 2 := by linarith
        omega
      have h1 : (q : ℕ) % p.toNat = 2 := by
        have h11 : (q : ZMod p.toNat) = (2 : ZMod p.toNat) := hq_mod
        have h12 : (q : ℕ) % p.toNat = (2 : ℕ) % p.toNat := by
          exact?
        have h13 : (2 : ℕ) % p.toNat = 2 := by
          apply Nat.mod_eq_of_lt
          have h14 : p.toNat > 2 := by exact_mod_cast h_p_toNat_gt_2
          omega
        rw [h13] at h12
        exact h12
      have h2 : ∃ k : ℕ, q = p.toNat * k + 2 := by
        use (q / p.toNat)
        have h15 : q % p.toNat = 2 := h1
        have h16 : q = (q / p.toNat) * p.toNat + q % p.toNat := by
          exact?
        rw [h15] at h16
        linarith
      rcases h2 with ⟨k, hk⟩
      have h4 : (q : ℕ) - 2 = p.toNat * k := by
        have h10 : q = p.toNat * k + 2 := hk
        omega
      have h5 : (p.toNat : ℕ) ∣ (q : ℕ) - 2 := by
        use k
        <;> omega
      have h6 : (p.toNat : ℤ) ∣ (q : ℤ) - 2 := by
        exact_mod_cast h5
      have h7 : (p : ℤ) = (p.toNat : ℤ) := by
        have h71 : 0 ≤ p := by linarith
        simp [Int.toNat_of_nonneg h71]
        <;> ring
      have h8 : (p : ℤ) ∣ (q : ℤ) - 2 := by
        rw [h7]
        exact h6
      have h18 : p ∣ ((q : ℤ) - 1) - ((q : ℤ) - 2) := by
        exact Int.dvd_sub h151 h8
      have h19 : ((q : ℤ) - 1) - ((q : ℤ) - 2) = 1 := by ring
      rw [h19] at h18
      have h20 : p ∣ 1 := h18
      have h21 : p ≤ 1 := by
        exact Int.le_of_dvd (by norm_num) h20
      linarith

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat):
  (∃ n : ℤ, n > 0 ∧ f n ≠ n) → ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1 := by
  exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main n f hn hpos hf

theorem f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat):
  (∃ n : ℤ, n > 0 ∧ f n ≠ n) → ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1  := by

  exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 n f hn hpos hf


lemma prime_divisor_of_fa_divides_fx_minus_x_h1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a):
  p ≥ 2 := by
  have h11 : Nat.Prime p.toNat := hp
  have h12 : p.toNat ≥ 2 := Nat.Prime.two_le h11
  by_contra h14
  have h15 : p ≤ 1 := by linarith
  have h16 : p.toNat ≤ 1 := by
    omega
  linarith

lemma prime_divisor_of_fa_divides_fx_minus_x_h2 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h1 : p ≥ 2):
  f p ≠ 1 := by
  by_contra hfp_eq_1
  have hp_pos : p > 0 := by linarith
  have h3 : f a ∣ p ^ a.toNat - (f p) ^ (f a).toNat := hf a p ha (by linarith)
  have h4 : p ∣ p ^ a.toNat - (f p) ^ (f a).toNat := by
    exact dvd_trans hdiv h3
  have ha1 : a.toNat ≥ 1 := by
    have h16 : a > 0 := ha
    have h17 : a.toNat ≥ 1 := by
      omega
    exact h17
  have h5 : p ∣ p ^ a.toNat := by
    have h51 : a.toNat ≥ 1 := ha1
    have h54 : ∃ k, a.toNat = k + 1 := ⟨a.toNat - 1, by omega⟩
    rcases h54 with ⟨k, hk⟩
    have h55 : p ^ a.toNat = p * (p ^ k) := by
      rw [hk, pow_succ]
      <;> ring
    rw [h55]
    <;> use (p ^ k) <;> ring
  have h6 : p ∣ (f p) ^ (f a).toNat := by
    have h61 : p ∣ p ^ a.toNat := h5
    have h62 : p ∣ p ^ a.toNat - (f p) ^ (f a).toNat := h4
    have h63 : p ∣ (p ^ a.toNat) - (p ^ a.toNat - (f p) ^ (f a).toNat) := by
      apply Int.dvd_sub
      · exact h61
      · exact h62
    have h64 : (p ^ a.toNat) - (p ^ a.toNat - (f p) ^ (f a).toNat) = (f p) ^ (f a).toNat := by ring
    rw [h64] at h63
    exact h63
  have h7 : (f p) ^ (f a).toNat = 1 := by
    rw [hfp_eq_1]
    simp
  rw [h7] at h6
  have h6' : p ∣ 1 := by simpa using h6
  have h100 : p ∣ 1 := h6'
  have h101 : p = 1 ∨ p = -1 := by
    have h1011 : p ∣ 1 := h100
    have h1012 : p = 1 ∨ p = -1 := by
      rw [← Int.natAbs_dvd_natAbs] at h1011 <;> norm_num at h1011 <;> omega
    exact h1012
  rcases h101 with (h101 | h101)
  · -- p = 1
    linarith
  · -- p = -1
    linarith

lemma prime_divisor_of_fa_divides_fx_minus_x_h10 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h2 : f p ≠ 1):
  ∀ (b : ℤ), b > 0 → b ≡ f b [ZMOD p] := by
  exact f_b_equiv_b_mod_p_of_f_p_ne_1 1 f (by norm_num) hpos hf p hp h2

lemma prime_divisor_of_fa_divides_fx_minus_x_h11 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h10 : ∀ (b : ℤ), b > 0 → b ≡ f b [ZMOD p]):
  x ≡ f x [ZMOD p] := by
  exact h10 x hx

lemma prime_divisor_of_fa_divides_fx_minus_x_h13 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h11 : x ≡ f x [ZMOD p]):
  p ∣ f x - x := by
  have h12 : p ∣ x - f x := by
    simpa [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero] using h11
  have h131 : f x - x = -(x - f x) := by ring
  rw [h131]
  exact dvd_neg.mpr h12

theorem prime_divisor_of_fa_divides_fx_minus_x (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (a x p : ℤ) (ha : a > 0) (hx : x > 0) (hp : Nat.Prime p.toNat) (hdiv : p ∣ f a): p ∣ f x - x  := by

  have h1 : p ≥ 2 := by
    exact prime_divisor_of_fa_divides_fx_minus_x_h1 n f hn hpos hf a x p ha hx hp hdiv
  have h2 : f p ≠ 1 := by
    exact prime_divisor_of_fa_divides_fx_minus_x_h2 n f hn hpos hf a x p ha hx hp hdiv h1
  have h10 : ∀ (b : ℤ), b > 0 → b ≡ f b [ZMOD p] := by
    exact prime_divisor_of_fa_divides_fx_minus_x_h10 n f hn hpos hf a x p ha hx hp hdiv h2
  have h11 : x ≡ f x [ZMOD p] := by
    exact prime_divisor_of_fa_divides_fx_minus_x_h11 n f hn hpos hf a x p ha hx hp hdiv h10
  have h13 : p ∣ f x - x := by
    exact prime_divisor_of_fa_divides_fx_minus_x_h13 n f hn hpos hf a x p ha hx hp hdiv h11
  exact h13

lemma f_n_is_power_of_two_for_even_n_h10 :
  ∀ (m : ℕ), m > 0 → (∀ p : ℕ, Nat.Prime p → p ∣ m → p = 2) → (∃ k : ℕ, m = 2 ^ k) := by
  intro m hm_pos h_prime
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h_m_eq_1 : m = 1
    · -- Case 1: m = 1
      refine ⟨0,?_⟩
      simp [h_m_eq_1]
      <;> aesop
    · -- Case 2: m ≠ 1
      have h_m_gt_1 : m > 1 := by
        omega
      have h_exists_prime_dvd : ∃ p : ℕ, Nat.Prime p ∧ p ∣ m := Nat.exists_prime_and_dvd (by omega)
      rcases h_exists_prime_dvd with ⟨p, hp_prime, hp_dvd_m⟩
      have hp_eq_2 : p = 2 := h_prime p hp_prime hp_dvd_m
      have h2_dvd_m : 2 ∣ m := by
        rw [hp_eq_2] at hp_dvd_m
        exact hp_dvd_m
      rcases h2_dvd_m with ⟨t, ht⟩
      have ht_eq : m = 2 * t := by linarith
      have ht_pos : t > 0 := by
        by_contra h
        have h' : t = 0 := by omega
        rw [h'] at ht_eq
        omega
      have ht_lt_m : t < m := by nlinarith
      have ht_property : ∀ (p : ℕ), Nat.Prime p → p ∣ t → p = 2 := by
        intro p hp_prime hp_dvd_t
        have h_p_dvd_m : p ∣ m := by
          rw [ht_eq]
          exact dvd_mul_of_dvd_right hp_dvd_t 2
        exact h_prime p hp_prime h_p_dvd_m
      have ih_t := ih t (by omega) (by omega) ht_property
      rcases ih_t with ⟨k, hk⟩
      refine ⟨k + 1,?_⟩
      calc
        m = 2 * t := by rw [ht_eq]
        _ = 2 * (2 ^ k) := by rw [hk]
        _ = 2 ^ (k + 1) := by ring


lemma f_n_is_power_of_two_for_even_n_h1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k):
  ∀ (q : ℤ), Nat.Prime q.toNat → q ∣ f n → q = 2 := by
  intro q hq_prime hq_divides_fn
  by_cases hq : q = 2
  · exact hq
  · -- Case 2: q ≠ 2
    have hq_pos : q > 0 := by
      by_contra h
      have h' : q ≤ 0 := by linarith
      have h11 : q.toNat = 0 := by
        omega
      rw [h11] at hq_prime
      norm_num at hq_prime <;> contradiction
    have hq_gt_2 : q > 2 := by
      by_cases hq_le_2 : q ≤ 2
      · have h12 : q = 1 ∨ q = 2 := by omega
        rcases h12 with (h12 | h12)
        · -- Case q = 1
          have h13 : q.toNat = 1 := by
            simp [h12]
            <;> omega
          rw [h13] at hq_prime
          norm_num at hq_prime <;> contradiction
        · -- Case q = 2
          contradiction
      · -- Case ¬ (q ≤ 2)
        have h14 : q > 2 := by linarith
        linarith
    have h2 : ∃ n : ℤ, n > 0 ∧ f n ≠ n := by
      rcases h_exists_k with ⟨k, hk1, hk2⟩
      refine ⟨k, by linarith, hk2⟩
    have h3 : ∀ (p : ℤ), Nat.Prime p.toNat → p > 2 → f p = 1 := by
      exact (f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 n f hn hpos hf h2)
    have h4 : f q = 1 := by
      specialize h3 q hq_prime hq_gt_2
      exact h3
    have h5 : q ∣ f q - q := by
      have h51 : q ∣ f q - q := prime_divisor_of_fa_divides_fx_minus_x n f hn hpos hf n q q hn hq_pos hq_prime hq_divides_fn
      exact h51
    have h51 : q ∣ 1 - q := by
      rw [h4] at h5
      simpa using h5
    have h52 : q ∣ (1 - q) + q := by
      have h521 : q ∣ 1 - q := h51
      have h522 : q ∣ q := by simp
      exact dvd_add h521 h522
    have h53 : (1 - q) + q = 1 := by ring
    rw [h53] at h52
    have h54 : q = 1 := by
      have h541 : q ∣ 1 := h52
      have h542 : q > 0 := hq_pos
      have h543 : q ≤ 1 := by exact Int.le_of_dvd (by norm_num) h541
      omega
    have h55 : q.toNat = 1 := by
      simp [h54]
      <;> omega
    rw [h55] at hq_prime
    norm_num at hq_prime <;> contradiction

lemma f_n_is_power_of_two_for_even_n_main (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k):
  ∃ k : ℕ, f n = 2 ^ k := by
  have h1 : ∀ (q : ℤ), Nat.Prime q.toNat → q ∣ f n → q = 2 := by
    exact f_n_is_power_of_two_for_even_n_h1 n f hn hpos hf h_exists_k
  have h6 : f n > 0 := hpos n hn
  have h61 : ∃ (m : ℕ), (m : ℤ) = f n ∧ m > 0 := by
    use (f n).toNat
    constructor
    · simp [Int.toNat_of_nonneg (by linarith : 0 ≤ f n)]
      <;> aesop
    · have h611 : 0 < f n := by linarith
      have h612 : 0 < (f n).toNat := by
        omega
      omega
  rcases h61 with ⟨m, hm1, hm2⟩
  have h7 : ∀ (p : ℕ), Nat.Prime p → p ∣ m → p = 2 := by
    intro p hp_prime hp_dvd_m
    have h71 : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hp_dvd_m
    have h72 : (p : ℤ) ∣ f n := by
      have h721 : (m : ℤ) = f n := by linarith
      rw [h721] at h71
      exact h71
    have h73 : Nat.Prime ((p : ℤ)).toNat := by
      have h101 : ((p : ℤ)).toNat = p := by
        simp
        <;> aesop
      rw [h101]
      exact hp_prime
    have h74 : (p : ℤ) = 2 := h1 (p : ℤ) h73 h72
    have h75 : p = 2 := by
      norm_cast at h74 ⊢ <;> omega
    exact h75
  have h10 : ∀ (m : ℕ), m > 0 → (∀ p : ℕ, Nat.Prime p → p ∣ m → p = 2) → (∃ k : ℕ, m = 2 ^ k) := by
    exact f_n_is_power_of_two_for_even_n_h10
  have h8 : ∃ k : ℕ, m = 2 ^ k := by
    exact h10 m hm2 h7
  rcases h8 with ⟨k, hk⟩
  refine ⟨k,?_⟩
  have h11 : (m : ℤ) = (2 ^ k : ℤ) := by exact_mod_cast hk
  have h12 : f n = (2 ^ k : ℤ) := by
    have h121 : (m : ℤ) = f n := by linarith
    linarith
  norm_cast at h12 ⊢ <;> linarith

theorem f_n_is_power_of_two_for_even_n (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k) :
  ∃ k : ℕ, f n = 2 ^ k   := by

  exact f_n_is_power_of_two_for_even_n_main n f hn hpos hf h_exists_k

lemma round1_h_main' (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f n ≤ 4 * n := by
  have h_main1 : (∀ k : ℤ, k > 0 → f k = 1) ∨ f 1 = 1 := imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf
  cases h_main1 with
  | inl h1 =>
    -- Case 1: ∀ k : ℤ, k > 0 → f k = 1
    have h2 : f n = 1 := h1 n hn
    have h3 : (1 : ℤ) ≤ 4 * n := by
      linarith
    linarith
  | inr h1 =>
    -- Case 2: f 1 = 1
    have h_f1 : f 1 = 1 := h1
    by_cases h2 : ∀ k : ℤ, k > 0 → f k = k
    · -- Subcase 2.1: ∀ k : ℤ, k > 0 → f k = k
      exact round1_h_subcase1 n f hn hpos hf h2
    · -- Subcase 2.2: ¬(∀ k : ℤ, k > 0 → f k = k)
      have h3 : ¬(∀ k : ℤ, k > 0 → f k = k) := h2
      have h4 : ∃ k : ℤ, k > 0 ∧ f k ≠ k := by
        by_contra h4
        push_neg at h4
        exact h3 (fun k hk => by tauto)
      obtain ⟨k, hk_pos, hk_ne⟩ := h4
      have h5 : k > 1 := by
        by_contra h5
        have h6 : k ≤ 1 := by linarith
        have h7 : k = 1 := by
          omega
        rw [h7] at hk_ne
        have h8 : f 1 ≠ 1 := hk_ne
        have h9 : f 1 = 1 := h_f1
        contradiction
      have h6 : ∃ k' : ℤ, k' > 1 ∧ f k' ≠ k' := ⟨k, h5, hk_ne⟩
      have h_exists : ∃ k : ℤ, k > 1 ∧ f k ≠ k := h6
      have h7 : ∃ n : ℤ, n > 0 ∧ f n ≠ n := by
        obtain ⟨k, hk1, hk2⟩ := h_exists
        refine' ⟨k, by linarith, hk2⟩
      have h8 : ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1 := by
        have h9 : (∃ n : ℤ, n > 0 ∧ f n ≠ n) := h7
        exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 n f hn hpos hf h9
      have h9 : f 3 = 1 := by
        have h10 : Nat.Prime (3 : ℤ).toNat := by decide
        have h11 : (3 : ℤ) > 2 := by norm_num
        specialize h8 3 h10 h11
        exact h8
      have h10 : f n ∣ 3 ^ n.toNat - 1 := by
        have h11 : f n ∣ (3 : ℤ) ^ n.toNat - (f 3) ^ (f n).toNat := hf n 3 hn (by norm_num)
        rw [h9] at h11
        have h12 : (1 : ℤ) ^ (f n).toNat = 1 := by simp
        simp [h12] at h11 ⊢
        <;> simpa using h11
      have h11 : ∃ k : ℕ, f n = 2 ^ k := f_n_is_power_of_two_for_even_n n f hn hpos hf h_exists
      obtain ⟨k, hk⟩ := h11
      have h12 : f n = (2 : ℤ) ^ k := hk
      have h13 : (2 : ℤ) ^ k ∣ 3 ^ n.toNat - 1 := by
        have h14 : f n = (2 : ℤ) ^ k := h12
        have h15 : f n ∣ 3 ^ n.toNat - 1 := h10
        rw [h14] at h15
        exact h15
      have h14 : k ≤ padicValNat 2 (3 ^ n.toNat - 1) := round1_h_k_le_padic n f k hn hpos hf h13
      have h15 : padicValNat 2 (3 ^ n.toNat - 1) = if n % 2 = 1 then 1 else 2 + padicValNat 2 n.toNat := lte_2_3n_minus_1 n hn
      have h16 : k ≤ 2 + padicValNat 2 n.toNat := by
        rw [h15] at h14
        split_ifs at h14 with h17
        · -- Case n % 2 = 1
          have h18 : k ≤ 1 := h14
          have h19 : (1 : ℕ) ≤ 2 + padicValNat 2 n.toNat := by
            have h20 : padicValNat 2 n.toNat ≥ 0 := by positivity
            omega
          omega
        · -- Case n % 2 ≠ 1
          have h18 : k ≤ 2 + padicValNat 2 n.toNat := h14
          exact h18
      have h17 : f n ≤ 4 * n := round1_h6' n f hn hpos hf k h12 h16
      exact h17

theorem imo2025_p3_left (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f n ≤ 4 * n  := by

  exact round1_h_main' n f hn hpos hf

#print axioms imo2025_p3_left


theorem imo2025_p3_right : ∃ (n : ℤ) (f : ℤ → ℤ), (n > 0) ∧ (∀ k : ℤ, k > 0 → f k > 0) ∧ (∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) ∧ (f n ≥ 4 * n) := by

  use 4
  use fun k => if k > 0 then (if k = 4 then 16 else (if k % 2 = 1 then 1 else 2)) else 0
  constructor
  · -- Prove n > 0
    norm_num
  constructor
  · -- Prove ∀ k : ℤ, k > 0 → f k > 0
    intro k hk
    have h1 : (if k > 0 then (if k = 4 then 16 else (if k % 2 = 1 then 1 else 2)) else 0 : ℤ) > 0 := by
      split_ifs with h1 h2 h3 <;>
      (try omega) <;>
      (try {
        have h4 : k % 2 = 1 ∨ k % 2 = 0 := by omega
        rcases h4 with (h4 | h4) <;> simp [h4] <;> omega
      }) <;>
      omega
    simpa using h1
  constructor
  · -- Prove ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat
    intros a b ha hb
    have h1 : a > 0 := ha
    have h2 : b > 0 := hb
    by_cases h10 : a = 4
    · -- Case 1: a = 4
      have ha1 : a = 4 := h10
      by_cases h11 : b = 4
      · -- Subcase 1.1: b = 4
        have hb1 : b = 4 := h11
        simp [ha1, hb1]
        <;> norm_num
        <;>
        use (256 - 16 ^ 16) / 16
        <;>
        norm_num <;>
        ring_nf <;>
        norm_num
      · -- Subcase 1.2: b ≠ 4
        have h12 : b ≠ 4 := h11
        by_cases h13 : b % 2 = 1
        · -- Subcase 1.2.1: b % 2 = 1
          have h131 : b % 2 = 1 := h13
          have h14 : (b ^ 4 - 1) % 16 = 0 := by
            have h141 : b % 2 = 1 := h131
            have h142 : b ^ 4 % 16 = 1 := by
              have h143 : b % 16 = 1 ∨ b % 16 = 3 ∨ b % 16 = 5 ∨ b % 16 = 7 ∨ b % 16 = 9 ∨ b % 16 = 11 ∨ b % 16 = 13 ∨ b % 16 = 15 := by omega
              rcases h143 with (h143 | h143 | h143 | h143 | h143 | h143 | h143 | h143) <;> simp [h143, pow_succ, Int.mul_emod]
            omega
          have h15 : (16 : ℤ) ∣ b ^ 4 - 1 := by
            omega
          simp [ha1, h12, h131] at *
          <;>
          (try omega) <;>
          (try {
            norm_num at *
            <;>
            (try {
              use (b ^ 4 - 1) / 16
              <;>
              ring_nf at * <;>
              omega
            })
          })
        · -- Subcase 1.2.2: b % 2 ≠ 1
          have h132 : b % 2 ≠ 1 := h13
          have h133 : b % 2 = 0 := by omega
          have h14 : (b ^ 4 - 2 ^ 16) % 16 = 0 := by
            have h141 : b % 2 = 0 := h133
            have h142 : b ^ 4 % 16 = 0 := by
              have h144 : b % 16 = 0 ∨ b % 16 = 2 ∨ b % 16 = 4 ∨ b % 16 = 6 ∨ b % 16 = 8 ∨ b % 16 = 10 ∨ b % 16 = 12 ∨ b % 16 = 14 := by omega
              rcases h144 with (h144 | h144 | h144 | h144 | h144 | h144 | h144 | h144) <;> simp [h144, pow_succ, Int.mul_emod] <;> norm_num <;> omega
            norm_num at *
            <;> omega
          have h15 : (16 : ℤ) ∣ b ^ 4 - 2 ^ 16 := by
            omega
          simp [ha1, h12, h132, h133] at *
          <;>
          (try omega) <;>
          (try {
            norm_num at *
            <;>
            (try {
              use (b ^ 4 - 2 ^ 16) / 16
              <;>
              ring_nf at * <;>
              omega
            })
          })
    · -- Case 2: a ≠ 4
      have h101 : a ≠ 4 := h10
      by_cases h102 : a % 2 = 1
      · -- Subcase 2.1: a % 2 = 1
        have h1021 : a % 2 = 1 := h102
        have h103 : (if a > 0 then (if a = 4 then 16 else (if a % 2 = 1 then 1 else 2)) else 0 : ℤ) = 1 := by
          simp [h1, h101, h1021]
          <;> aesop
        rw [h103]
        norm_num
        <;>
        aesop
      · -- Subcase 2.2: a % 2 ≠ 1
        have h1022 : a % 2 ≠ 1 := h102
        have h104 : a % 2 = 0 := by omega
        have h105 : (if a > 0 then (if a = 4 then 16 else (if a % 2 = 1 then 1 else 2)) else 0 : ℤ) = 2 := by
          simp [h1, h101, h1022, h104]
          <;> aesop
        have h106 : (if a > 0 then (if a = 4 then 16 else (if a % 2 = 1 then 1 else 2)) else 0 : ℤ) = 2 := h105
        have h107 : ((if a > 0 then (if a = 4 then 16 else (if a % 2 = 1 then 1 else 2)) else 0 : ℤ)).toNat = 2 := by
          simp [h106]
          <;> aesop
        have h108 : (2 : ℤ) ∣ b ^ a.toNat - (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ^ 2 := by
          have h109 : (b ^ a.toNat) % 2 = b % 2 := by
            by_cases h1104 : b % 2 = 0
            · -- Case b % 2 = 0 (b is even)
              have h1105 : (b ^ a.toNat) % 2 = 0 := by
                have h1106 : a.toNat > 0 := by
                  have h11061 : 0 < a := by linarith
                  have h11062 : a ≥ 1 := by linarith
                  have h11063 : a.toNat ≥ 1 := by
                    omega
                  have h11064 : 0 < a.toNat := by omega
                  exact h11064
                have h1107 : (b ^ a.toNat) % 2 = 0 := by
                  have h1108 : b % 2 = 0 := h1104
                  have h1109 : ∀ n : ℕ, n > 0 → (b ^ n) % 2 = 0 := by
                    intro n hn
                    induction n with
                    | zero => contradiction
                    | succ n ih =>
                      by_cases h1110 : n = 0
                      · -- n = 0, so n + 1 = 1
                        simp [h1110, h1108]
                        <;> omega
                      · -- n > 0
                        have h1111 : n > 0 := by omega
                        have ih' := ih h1111
                        simp [pow_succ, Int.mul_emod, h1108, ih'] <;> omega
                  exact h1109 a.toNat h1106
                exact h1107
              have h1109 : b % 2 = 0 := h1104
              omega
            · -- Case b % 2 ≠ 0
              have h11041 : b % 2 = 1 := by omega
              have h1105 : (b ^ a.toNat) % 2 = 1 := by
                have h1106 : a.toNat > 0 := by
                  have h11061 : 0 < a := by linarith
                  have h11062 : a ≥ 1 := by linarith
                  have h11063 : a.toNat ≥ 1 := by omega
                  have h11064 : 0 < a.toNat := by omega
                  exact h11064
                have h1107 : (b ^ a.toNat) % 2 = 1 := by
                  have h1108 : b % 2 = 1 := h11041
                  have h1109 : ∀ n : ℕ, (b ^ n) % 2 = 1 := by
                    intro n
                    induction n with
                    | zero => simp [h1108]
                    | succ n ih =>
                      simp [pow_succ, Int.mul_emod, h1108, ih]
                      <;> omega
                  exact h1109 a.toNat
                exact h1107
              have h1109 : b % 2 = 1 := h11041
              omega
          have h111 : ( (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ) % 2 = b % 2 := by
            have h21 : b > 0 := by linarith
            have h22 : (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) = (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) := by
              simp [h21]
            rw [h22]
            by_cases h23 : b = 4
            · -- Case b = 4
              rw [if_pos h23]
              norm_num
              <;> omega
            · -- Case b ≠ 4
              rw [if_neg h23]
              by_cases h24 : b % 2 = 1
              · -- Case b % 2 = 1
                rw [if_pos h24]
                <;> omega
              · -- Case b % 2 ≠ 1
                rw [if_neg h24]
                have h25 : b % 2 = 0 := by omega
                have h1 : (2 : ℤ) % 2 = 0 := by norm_num
                omega
          have h112 : ( (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ^ 2) % 2 = ( (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ) % 2 := by
            have h1121 : ∀ x : ℤ, (x ^ 2) % 2 = x % 2 := by
              intro x
              have h1122 : x % 2 = 0 ∨ x % 2 = 1 := by omega
              rcases h1122 with (h1122 | h1122) <;> simp [h1122, pow_two, Int.mul_emod] <;> omega
            exact h1121 ((if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ))
          have h113 : ( (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ^ 2) % 2 = b % 2 := by omega
          have h114 : (b ^ a.toNat - (if b > 0 then (if b = 4 then 16 else (if b % 2 = 1 then 1 else 2)) else 0 : ℤ) ^ 2) % 2 = 0 := by omega
          omega
        simpa [h106, h107] using h108
  · -- Prove f n ≥ 4 * n
    norm_num
    <;>
    aesop

#print axioms imo2025_p3_right