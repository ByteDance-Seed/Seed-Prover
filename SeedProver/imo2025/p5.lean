import Mathlib
import Aesop
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat

lemma round8_LoseA_iff (l : ℝ) (WinA : ℕ → ℝ → ℝ → Prop)
    (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
      ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
        ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
          WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (n : ℕ) (sum1 sum2 : ℝ) :
    ¬ WinA n sum1 sum2 ↔ ∀ (a : ℝ), a ≥ 0 → sum1 + a > (2 * n + 1) * l ∨ (∃ (b : ℝ), b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧ ¬ WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)) := by
  have h2 : WinA n sum1 sum2 ↔ ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧ ∀ (b : ℝ), b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 → WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2) := winA_iff n sum1 sum2
  constructor
  · -- Forward direction: ¬WinA n sum1 sum2 → ∀ (a : ℝ), a ≥ 0 → sum1 + a > (2 * n + 1) * l ∨ (∃ (b : ℝ), b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧ ¬WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    intro h_Ln
    intro a ha
    have h1 : ¬ (∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧ ∀ (b : ℝ), b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 → WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)) := by
      rw [h2] at h_Ln
      exact h_Ln
    have h2' : ∀ (a' : ℝ), ¬ (a' ≥ 0 ∧ sum1 + a' ≤ (2 * n + 1) * l ∧ ∀ (b : ℝ), b ≥ 0 → sum2 + a' ^ 2 + b ^ 2 ≤ 2 * n + 2 → WinA (n + 1) (sum1 + a' + b) (sum2 + a' ^ 2 + b ^ 2)) := by
      intro a'
      intro h_conj
      exact h1 ⟨a', h_conj⟩
    have h3 : ¬ (sum1 + a ≤ (2 * n + 1) * l ∧ ∀ (b : ℝ), b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 → WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)) := by
      have h4 := h2' a
      tauto
    by_cases h5 : sum1 + a ≤ (2 * n + 1) * l
    · -- Case 1: sum1 + a ≤ (2 * n + 1) * l
      have h6 : ¬ (∀ (b : ℝ), b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 → WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)) := by
        tauto
      have h7 : ∃ (b : ℝ), b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧ ¬ WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2) := by
        push_neg at h6
        exact h6
      exact Or.inr h7
    · -- Case 2: ¬ (sum1 + a ≤ (2 * n + 1) * l)
      have h8 : sum1 + a > (2 * n + 1) * l := by linarith
      exact Or.inl h8
  · -- Backward direction: (∀ (a : ℝ), a ≥ 0 → sum1 + a > (2 * n + 1) * l ∨ (∃ (b : ℝ), b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧ ¬WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))) → ¬WinA n sum1 sum2
    intro h
    rw [h2]
    intro h_exists
    rcases h_exists with ⟨a, ha_nonneg, ha_le, h_forall_b⟩
    have h_or := h a ha_nonneg
    cases h_or with
    | inl h1 =>
      -- Case 1: sum1 + a > (2 * n + 1) * l
      linarith -- Contradiction with ha_le: sum1 + a ≤ (2 * n + 1) * l
    | inr h2 =>
      -- Case 2: ∃ (b : ℝ), b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧ ¬WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)
      rcases h2 with ⟨b, hb_nonneg, hb_cond, h_not_WinA_next⟩
      have h_WinA_next := h_forall_b b hb_nonneg hb_cond
      contradiction


lemma round1_main (l : ℝ)
  (hl : l > Real.sqrt 2 / 2):
  ∃ (N : ℕ), ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2 := by
  have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : l > 0 := by
    linarith [Real.sqrt_nonneg 2]
  have h3 : 2 * l > Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2]
  have h4 : 2 * l - Real.sqrt 2 > 0 := by linarith
  have h5 : (2 * l - Real.sqrt 2) ^ 2 > 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h51 : 4 / ((2 * l - Real.sqrt 2) ^ 2) > 0 := by
    apply div_pos
    · norm_num
    · linarith
  have h6 : ∃ (N : ℕ), (N : ℝ) > 4 / ((2 * l - Real.sqrt 2) ^ 2) + 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / ((2 * l - Real.sqrt 2) ^ 2) + 2)
    refine ⟨N, by exact_mod_cast hN⟩
  obtain ⟨N, hN⟩ := h6
  have hN2 : (N : ℝ) > 4 / ((2 * l - Real.sqrt 2) ^ 2) := by linarith
  have hN1 : (N : ℝ) > 2 := by linarith
  have h9 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) > 4 := by
    have h91 : (N : ℝ) > 4 / ((2 * l - Real.sqrt 2) ^ 2) := hN2
    have h92 : (2 * l - Real.sqrt 2) ^ 2 > 0 := by linarith
    have h93 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) > (2 * l - Real.sqrt 2) ^ 2 * (4 / ((2 * l - Real.sqrt 2) ^ 2)) := by
      nlinarith
    have h94 : (2 * l - Real.sqrt 2) ^ 2 * (4 / ((2 * l - Real.sqrt 2) ^ 2)) = 4 := by
      field_simp [h92.ne']
      <;> ring
    nlinarith
  have h10 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) ^ 2 > 4 * (N : ℝ) := by
    have h101 : (N : ℝ) > 0 := by linarith
    have h102 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) > 4 := by linarith
    have h103 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) ^ 2 = ((2 * l - Real.sqrt 2) ^ 2 * (N : ℝ)) * (N : ℝ) := by ring
    have h104 : ((2 * l - Real.sqrt 2) ^ 2 * (N : ℝ)) * (N : ℝ) > 4 * (N : ℝ) := by
      nlinarith
    linarith
  have h11 : 4 * (N : ℝ) > 2 * (N : ℝ) + 2 := by linarith
  have h12 : (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) ^ 2 > 2 * (N : ℝ) + 2 := by linarith
  have h13 : ((2 * l - Real.sqrt 2) * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2 := by
    have h131 : ((2 * l - Real.sqrt 2) * (N : ℝ)) ^ 2 = (2 * l - Real.sqrt 2) ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [h131]
    linarith
  have h14 : (2 * l - Real.sqrt 2) * (N : ℝ) > 0 := by
    have h141 : 2 * l - Real.sqrt 2 > 0 := by linarith
    have h142 : (N : ℝ) > 0 := by linarith
    nlinarith
  have h15 : (2 * l - Real.sqrt 2) * (N : ℝ) + l > (2 * l - Real.sqrt 2) * (N : ℝ) := by linarith
  have h16 : (2 * l - Real.sqrt 2) * (N : ℝ) + l > 0 := by nlinarith
  have h17 : ((2 * l - Real.sqrt 2) * (N : ℝ) + l) ^ 2 > ((2 * l - Real.sqrt 2) * (N : ℝ)) ^ 2 := by
    have h171 : (2 * l - Real.sqrt 2) * (N : ℝ) > 0 := by linarith
    have h172 : (2 * l - Real.sqrt 2) * (N : ℝ) + l > (2 * l - Real.sqrt 2) * (N : ℝ) := by linarith
    have h173 : (2 * l - Real.sqrt 2) * (N : ℝ) + l > 0 := by linarith
    nlinarith
  have h18 : ((2 * l - Real.sqrt 2) * (N : ℝ) + l) ^ 2 > 2 * (N : ℝ) + 2 := by linarith
  have h19 : (2 * l - Real.sqrt 2) * (N : ℝ) + l = (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) := by ring
  have h20 : ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2 := by
    have h201 : ((2 * l - Real.sqrt 2) * (N : ℝ) + l) ^ 2 > 2 * (N : ℝ) + 2 := by linarith
    have h202 : (2 * l - Real.sqrt 2) * (N : ℝ) + l = (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) := by linarith
    rw [h202] at h201
    linarith
  refine ⟨N,?_⟩
  exact h20


lemma round1_final (l : ℝ)
  (hl : l > Real.sqrt 2 / 2)
  (N : ℕ)
  (h20 : ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2):
  ∀ (s1 s2 : ℝ), 0 ≤ s1 → s1 ≤ Real.sqrt 2 * (N : ℝ) → 0 ≤ s2 → s2 ≤ 2 * (N : ℝ) → s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 > 2 * (N : ℝ) + 2 := by
  have h21 : ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2 := h20
  intro s1 s2 hs11 hs12 hs21 hs22
  have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : l > 0 := by
    have h211 : l > Real.sqrt 2 / 2 := hl
    have h212 : Real.sqrt 2 > 0 := by positivity
    linarith [Real.sqrt_nonneg 2]
  have h3 : 2 * l > Real.sqrt 2 := by
    have h31 : l > Real.sqrt 2 / 2 := hl
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h4 : 2 * l - Real.sqrt 2 > 0 := by linarith
  have h5 : (2 * l - Real.sqrt 2) * (N : ℝ) + l > 0 := by
    have h51 : (N : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le N
    have h52 : 2 * l - Real.sqrt 2 > 0 := by linarith
    have h53 : (2 * l - Real.sqrt 2) * (N : ℝ) ≥ 0 := by nlinarith
    nlinarith
  have h211 : (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) > 0 := by
    have h2111 : (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) = (2 * l - Real.sqrt 2) * (N : ℝ) + l := by
      ring
    rw [h2111]
    linarith
  have h212 : (2 * (N : ℝ) + 1) * l - s1 ≥ (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) := by linarith
  have h213 : (2 * (N : ℝ) + 1) * l - s1 ≥ 0 := by
    have h2131 : (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) ≥ 0 := by linarith
    linarith
  have h214 : ((2 * (N : ℝ) + 1) * l - s1) ^ 2 ≥ ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 := by
    have h2141 : (2 * (N : ℝ) + 1) * l - s1 ≥ (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) := by linarith
    have h2142 : (2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ) ≥ 0 := by linarith
    nlinarith
  have h215 : ((2 * (N : ℝ) + 1) * l - s1) ^ 2 > 2 * (N : ℝ) + 2 := by nlinarith
  nlinarith


lemma round8_quadratic_growth_contradiction (l : ℝ) (hl : l > Real.sqrt 2 / 2) :
    ∃ (N : ℕ), ∀ (s1 s2 : ℝ), 0 ≤ s1 → s1 ≤ Real.sqrt 2 * (N : ℝ) → 0 ≤ s2 → s2 ≤ 2 * (N : ℝ) → s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 > 2 * (N : ℝ) + 2 := by
  have h_main : ∃ (N : ℕ), ((2 * (N : ℝ) + 1) * l - Real.sqrt 2 * (N : ℝ)) ^ 2 > 2 * (N : ℝ) + 2 := by
    exact round1_main l hl
  obtain ⟨N, hN⟩ := h_main
  refine' ⟨N, _⟩
  exact round1_final l hl N hN


lemma round15_lemma1 (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2):
  ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2)) := by
  intro k s1 s2 h1 h2 h_s2_nonneg h3 h4
  have h5 := (round8_LoseA_iff l WinA winA_iff k s1 s2).mp h1
  have h6 := h5 0 (by linarith)
  have h7 : s1 ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by
    have h71 : s1 ^ 2 ≤ (k : ℝ) * s2 := h3
    have h72 : s2 ≤ 2 * (k : ℝ) := h4
    have h73 : (k : ℝ) * s2 ≤ (k : ℝ) * (2 * (k : ℝ)) := by
      have h731 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
      nlinarith
    have h74 : (k : ℝ) * (2 * (k : ℝ)) = 2 * (k : ℝ) ^ 2 := by ring
    nlinarith
  have h8 : s1 ≤ Real.sqrt 2 * (k : ℝ) := by
    have h81 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h82 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have h83 : s1 ^ 2 ≤ 2 * (k : ℝ) ^ 2 := h7
    have h84 : s1 ≤ Real.sqrt 2 * (k : ℝ) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg s1, sq_nonneg ((k : ℝ)), mul_nonneg h81 h82]
    linarith
  have h9 : (2 * (k : ℝ) + 1) * l ≥ Real.sqrt 2 * (k : ℝ) := by
    have h91 : l > Real.sqrt 2 / 2 := hl
    have h92 : 0 < l := by linarith
    have h93 : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have h94 : 2 * l - Real.sqrt 2 > 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h10 : s1 ≤ (2 * (k : ℝ) + 1) * l := by linarith
  have h11 : ∃ (b : ℝ), b ≥ 0 ∧ s2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + b) (s2 + b ^ 2) := by
    have h61 : s1 > (2 * (k : ℝ) + 1) * l ∨ (∃ (b : ℝ), b ≥ 0 ∧ s2 + 0 ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + 0 + b) (s2 + 0 ^ 2 + b ^ 2)) := by simpa using h6
    have h62 : ¬ (s1 > (2 * (k : ℝ) + 1) * l) := by linarith
    have h63 : ∃ (b : ℝ), b ≥ 0 ∧ s2 + 0 ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ ¬ WinA (k + 1) (s1 + 0 + b) (s2 + 0 ^ 2 + b ^ 2) := by tauto
    rcases h63 with ⟨b, hb1, hb2, hb3⟩
    refine ⟨b, hb1, ?_, ?_⟩
    · ring_nf at hb2 ⊢ <;> linarith
    · simpa using hb3
  rcases h11 with ⟨b, hb1, hb2, hb3⟩
  have h12 : (k : ℝ) * b ^ 2 - 2 * s1 * b + s2 ≥ 0 := by
    by_cases h121 : (k : ℝ) = 0
    · -- Case 1: (k : ℝ) = 0
      have h1211 : s1 = 0 := by
        have h1212 : s1 ^ 2 ≤ (k : ℝ) * s2 := h3
        rw [h121] at h1212
        have h1213 : s1 ^ 2 ≤ 0 := by nlinarith
        have h1214 : s1 ^ 2 ≥ 0 := by positivity
        have h1215 : s1 ^ 2 = 0 := by linarith
        have h1216 : s1 = 0 := by nlinarith
        exact h1216
      rw [h121, h1211]
      <;> nlinarith
    · -- Case 2: (k : ℝ) ≠ 0
      have h122 : (k : ℝ) > 0 := by
        have h1221 : (k : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le k
        by_contra h1222
        have h1223 : (k : ℝ) ≤ 0 := by linarith
        have h1224 : (k : ℝ) = 0 := by linarith
        contradiction
      nlinarith [sq_nonneg (b * (k : ℝ) - s1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, sq_nonneg (s1), sq_nonneg ((k : ℝ)), sq_nonneg (b), h3, mul_nonneg h122.le h_s2_nonneg]
  have h13 : (s1 + b) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b ^ 2) := by
    nlinarith
  refine ⟨b, hb1, hb3, by linarith, h13⟩


lemma round15_h_main (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2)
  (h : ¬ WinA 0 0 0)
  (lemma1 : ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2))):
  ∀ k : ℕ, ∃ s1 s2 : ℝ, (0 ≤ s1) ∧ (0 ≤ s2) ∧ (s1 ^ 2 ≤ (k : ℝ) * s2) ∧ (s2 ≤ 2 * (k : ℝ)) ∧ (¬ WinA k s1 s2) := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, 0, by norm_num, by norm_num, by norm_num, by norm_num, h⟩
  | succ k ih =>
    rcases ih with ⟨s1, s2, h1, h2, h3, h4, h5⟩
    have h6 := lemma1 k s1 s2 h5 h1 h2 h3 h4
    rcases h6 with ⟨b_next, h_b_next1, h_b_next2, h_b_next3, h_b_next4⟩
    refine ⟨s1 + b_next, s2 + b_next ^ 2, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 ≤ s1 + b_next
      nlinarith
    · -- 0 ≤ s2 + b_next ^ 2
      nlinarith [sq_nonneg b_next]
    · -- (s1 + b_next) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) * (s2 + b_next ^ 2)
      simp [Nat.cast_add, Nat.cast_one] at *
      <;> linarith
    · -- s2 + b_next ^ 2 ≤ 2 * ((k + 1 : ℕ) : ℝ)
      simp [Nat.cast_add, Nat.cast_one] at *
      <;> linarith
    · -- ¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)
      exact h_b_next2

/-
A will win when l > √2 / 2
-/
theorem imo2025_p5_algebra_A (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
    (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
      ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
        ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
          WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l > √2 / 2) : WinA 0 0 0 := by
  by_contra h
  have lemma1 : ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2)) := by
    exact round15_lemma1 l hl0 WinA winA_iff hl
  have h_main : ∀ k : ℕ, ∃ s1 s2 : ℝ, (0 ≤ s1) ∧ (0 ≤ s2) ∧ (s1 ^ 2 ≤ (k : ℝ) * s2) ∧ (s2 ≤ 2 * (k : ℝ)) ∧ (¬ WinA k s1 s2) := by
    exact round15_h_main l hl0 WinA winA_iff hl h lemma1
  have h14 := round8_quadratic_growth_contradiction l hl
  rcases h14 with ⟨N, hN⟩
  have h15 := h_main N
  rcases h15 with ⟨s1, s2, h1, h2, h3, h4, h5⟩
  have h6 : s1 ≤ Real.sqrt 2 * (N : ℝ) := by
    have h61 : s1 ^ 2 ≤ 2 * (N : ℝ) ^ 2 := by
      have h611 : s1 ^ 2 ≤ (N : ℝ) * s2 := h3
      have h612 : s2 ≤ 2 * (N : ℝ) := h4
      have h613 : (N : ℝ) * s2 ≤ (N : ℝ) * (2 * (N : ℝ)) := by
        have h614 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
        nlinarith
      have h614 : (N : ℝ) * (2 * (N : ℝ)) = 2 * (N : ℝ) ^ 2 := by ring
      nlinarith
    have h62 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have h63 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, sq_nonneg s1, sq_nonneg ((N : ℝ)), mul_nonneg h63 h62]
  have h7 := hN s1 s2 h1 h6 h2 h4
  have h9 : (2 * (N : ℝ) + 1) * l - s1 ≥ 0 := by
    have h91 : (2 * (N : ℝ) + 1) * l ≥ Real.sqrt 2 * (N : ℝ) := by
      have h911 : l > Real.sqrt 2 / 2 := hl
      have h912 : 0 < l := by linarith
      have h913 : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      have h914 : 2 * l - Real.sqrt 2 > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith
  have h10 := (round8_LoseA_iff l WinA winA_iff N s1 s2).mp h5
  have h11 := h10 ((2 * (N : ℝ) + 1) * l - s1) h9
  rcases h11 with h111 | ⟨b, hb1, hb2, _⟩
  · -- Case 1: s1 + ((2 * (N : ℝ) + 1) * l - s1) > (2 * (N : ℝ) + 1) * l
    have h1111 : s1 + ((2 * (N : ℝ) + 1) * l - s1) = (2 * (N : ℝ) + 1) * l := by ring
    linarith
  · -- Case 2: ∃ (b : ℝ), b ≥ 0 ∧ s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 + b ^ 2 ≤ 2 * (N : ℝ) + 2 ∧ ¬ WinA (N + 1) (s1 + ((2 * (N : ℝ) + 1) * l - s1) + b) (s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 + b ^ 2)
    have h12 : s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 ≤ 2 * (N : ℝ) + 2 := by
      have h121 : s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 + b ^ 2 ≤ 2 * (N : ℝ) + 2 := hb2
      have h122 : 0 ≤ b ^ 2 := by apply sq_nonneg
      linarith
    linarith

lemma round3_P_holds_for_large_n (l : ℝ) (hl0 : l > 0) (hl : l < √2 / 2)
  (WinB : ℕ → ℝ → ℝ → Prop)
  (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
    ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
      ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
        WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2)):
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ (n : ℝ) * Real.sqrt 2 → s₂ = 2 * (n : ℝ) → WinB n s₁ s₂ := by
  have h_pos : 0 < Real.sqrt 2 - 2 * l := by
    have h1 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)
    have h2 : 2 * l < Real.sqrt 2 := by linarith
    linarith
  rcases exists_nat_gt (l / (Real.sqrt 2 - 2 * l)) with ⟨N, hN⟩
  use N + 1
  intro n hn s₁ s₂ hs₁ hs₂
  have hN' : (N : ℝ) > l / (Real.sqrt 2 - 2 * l) := by exact_mod_cast hN
  have hN_ge_one : (N + 1 : ℝ) > l / (Real.sqrt 2 - 2 * l) := by linarith
  have hn' : (n : ℝ) ≥ (N + 1 : ℝ) := by exact_mod_cast hn
  have h_ineq1 : (n : ℝ) * (Real.sqrt 2 - 2 * l) > l := by
    have h : (n : ℝ) > l / (Real.sqrt 2 - 2 * l) := by linarith
    have h3 : 0 < Real.sqrt 2 - 2 * l := h_pos
    have h4 : (n : ℝ) * (Real.sqrt 2 - 2 * l) > (l / (Real.sqrt 2 - 2 * l)) * (Real.sqrt 2 - 2 * l) := by nlinarith
    have h5 : (l / (Real.sqrt 2 - 2 * l)) * (Real.sqrt 2 - 2 * l) = l := by
      field_simp [h3.ne']
      <;> ring
    nlinarith
  have h_ineq2 : (n : ℝ) * Real.sqrt 2 > (2 * (n : ℝ) + 1) * l := by linarith
  have h_main : s₁ > (2 * (n : ℝ) + 1) * l := by linarith [hs₁, h_ineq2]
  have hWinB : WinB n s₁ s₂ := by
    have hWinB' : ∀ (a : ℝ), a ≥ 0 → s₁ + a ≤ (2 * (n : ℝ) + 1) * l → ∃ b : ℝ, b ≥ 0 ∧ s₂ + a ^ 2 + b ^ 2 ≤ 2 * (n : ℝ) + 2 ∧ WinB (n + 1) (s₁ + a + b) (s₂ + a ^ 2 + b ^ 2) := by
      intro a ha1 ha2
      linarith
    exact (winB_iff n s₁ s₂).mpr hWinB'
  exact hWinB


lemma round3_P_inductive_step_backward (l : ℝ) (hl0 : l > 0) (hl : l < √2 / 2)
  (WinB : ℕ → ℝ → ℝ → Prop)
  (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
    ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
      ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
        WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (k : ℕ)
  (P_holds_for_k_plus_1 : ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 → s₂ = 2 * ((k + 1 : ℕ) : ℝ) → WinB (k + 1) s₁ s₂):
  ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ (k : ℝ) * Real.sqrt 2 → s₂ = 2 * (k : ℝ) → WinB k s₁ s₂ := by
  intro s₁ s₂ hs₁ hs₂
  have hWinB_k : WinB k s₁ s₂ := by
    have hWinB_k' : ∀ (a : ℝ), a ≥ 0 → s₁ + a ≤ (2 * (k : ℝ) + 1) * l → ∃ b : ℝ, b ≥ 0 ∧ s₂ + a ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 ∧ WinB (k + 1) (s₁ + a + b) (s₂ + a ^ 2 + b ^ 2) := by
      intro a ha_nonneg ha_le
      have h_a_lt_sqrt2_div_2 : a < Real.sqrt 2 / 2 := by
        have h1 : a ≤ (2 * (k : ℝ) + 1) * l - s₁ := by linarith
        have h2 : s₁ ≥ (k : ℝ) * Real.sqrt 2 := hs₁
        have h3 : (2 * (k : ℝ) + 1) * l - s₁ ≤ (2 * (k : ℝ) + 1) * l - (k : ℝ) * Real.sqrt 2 := by linarith
        have h4 : a ≤ (2 * (k : ℝ) + 1) * l - (k : ℝ) * Real.sqrt 2 := by linarith
        have h5 : (2 * (k : ℝ) + 1) * l < (2 * (k : ℝ) + 1) * (Real.sqrt 2 / 2) := by nlinarith [hl, show 0 < 2 * (k : ℝ) + 1 by positivity]
        have h6 : (2 * (k : ℝ) + 1) * (Real.sqrt 2 / 2) - (k : ℝ) * Real.sqrt 2 = (1 / 2) * Real.sqrt 2 := by ring
        have h7 : (2 * (k : ℝ) + 1) * l - (k : ℝ) * Real.sqrt 2 < (1 / 2) * Real.sqrt 2 := by linarith
        have h8 : (1 / 2) * Real.sqrt 2 = Real.sqrt 2 / 2 := by ring
        have h9 : (2 * (k : ℝ) + 1) * l - (k : ℝ) * Real.sqrt 2 < Real.sqrt 2 / 2 := by linarith [h7, h8]
        linarith
      have h_2_minus_a_sq_pos : 0 < 2 - a ^ 2 := by
        have h_a_sq_lt_1_div_2 : a ^ 2 < 1 / 2 := by nlinarith [h_a_lt_sqrt2_div_2, Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sqrt_nonneg 2]
        nlinarith
      set b := Real.sqrt (2 - a ^ 2) with hb_def
      have hb_nonneg : b ≥ 0 := Real.sqrt_nonneg _
      have h_sum2_cond : s₂ + a ^ 2 + b ^ 2 ≤ 2 * (k : ℝ) + 2 := by
        have h_b_sq : b ^ 2 = 2 - a ^ 2 := by
          rw [hb_def]
          exact Real.sq_sqrt (by linarith)
        have h : s₂ + a ^ 2 + b ^ 2 = 2 * (k : ℝ) + 2 := by
          nlinarith [hs₂, h_b_sq]
        linarith
      have h_a_plus_b_ge_sqrt2 : a + b ≥ Real.sqrt 2 := by
        have h_a_nonneg' : 0 ≤ a := ha_nonneg
        have h : (a + b) ^ 2 ≥ (Real.sqrt 2) ^ 2 := by
          have h_b_sq' : b ^ 2 = 2 - a ^ 2 := by
            rw [hb_def]
            exact Real.sq_sqrt (by linarith)
          have h2 : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring
          have h3 : a ^ 2 + b ^ 2 + 2 * a * b = a ^ 2 + (2 - a ^ 2) + 2 * a * b := by rw [h_b_sq']
          have h4 : a ^ 2 + (2 - a ^ 2) + 2 * a * b = 2 + 2 * a * b := by ring
          have h5 : 2 + 2 * a * b ≥ 2 := by
            have h6 : 2 * a * b ≥ 0 := by
              have h7 : 0 ≤ a := by linarith
              have h8 : 0 ≤ b := hb_nonneg
              have h9 : 0 ≤ 2 * a * b := by positivity
              linarith
            linarith
          have h6 : (Real.sqrt 2) ^ 2 = 2 := by
            rw [Real.sq_sqrt] <;> norm_num
          nlinarith
        have h2 : 0 ≤ a + b := by
          have h3 : 0 ≤ a := by linarith
          have h4 : 0 ≤ b := hb_nonneg
          linarith
        have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        nlinarith
      have h_S1_next_ge : s₁ + a + b ≥ ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 := by
        have h_s1_ge_k_sqrt2 : s₁ ≥ (k : ℝ) * Real.sqrt 2 := hs₁
        have h : s₁ + a + b ≥ (k : ℝ) * Real.sqrt 2 + (a + b) := by linarith
        have h' : (k : ℝ) * Real.sqrt 2 + (a + b) ≥ (k : ℝ) * Real.sqrt 2 + Real.sqrt 2 := by linarith [h_a_plus_b_ge_sqrt2]
        have h'' : (k : ℝ) * Real.sqrt 2 + Real.sqrt 2 = ((k : ℝ) + 1) * Real.sqrt 2 := by ring
        have h''' : ((k : ℝ) + 1) * Real.sqrt 2 = ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 := by norm_cast
        linarith
      have h_S2_next : s₂ + a ^ 2 + b ^ 2 = 2 * ((k + 1 : ℕ) : ℝ) := by
        have h_b_sq : b ^ 2 = 2 - a ^ 2 := by
          rw [hb_def]
          exact Real.sq_sqrt (by linarith)
        have h1 : s₂ + a ^ 2 + b ^ 2 = 2 * (k : ℝ) + 2 := by nlinarith [hs₂, h_b_sq]
        have h2 : 2 * ((k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by
          simp
          <;> ring
        linarith
      have hWinB_k_plus_1_instance : WinB (k + 1) (s₁ + a + b) (s₂ + a ^ 2 + b ^ 2) := by
        apply P_holds_for_k_plus_1 (s₁ + a + b) (s₂ + a ^ 2 + b ^ 2) h_S1_next_ge
        <;> linarith
      refine' ⟨b, hb_nonneg, h_sum2_cond, _⟩
      simpa [h_S2_next] using hWinB_k_plus_1_instance
    exact (winB_iff k s₁ s₂).mpr hWinB_k'
  exact hWinB_k

/-
B will win when l < √2 / 2
-/
theorem imo2025_p5_algebra_B (l : ℝ) (hl0 : l > 0) (WinB : ℕ → ℝ → ℝ → Prop)
    (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
      ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
        ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
          WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l < √2 / 2) : WinB 0 0 0 := by
  have h_axiom := round3_P_holds_for_large_n l hl0 hl WinB winB_iff
  rcases h_axiom with ⟨N, hN⟩

  have h_P_N_minus_j : ∀ (j : ℕ), j ≤ N → (∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ ((N - j : ℕ) : ℝ) * Real.sqrt 2 → s₂ = 2 * ((N - j : ℕ) : ℝ) → WinB (N - j) s₁ s₂) := by
    intro j
    induction j with
    | zero =>
      intro hj
      intro s₁ s₂ hs₁ hs₂
      have hN' : N ≥ N := by linarith
      exact hN N hN' s₁ s₂ hs₁ hs₂
    | succ j' ih =>
      intro hj
      have h_j'_le_N : j' ≤ N := by linarith
      have ih' := ih h_j'_le_N

      intro s₁ s₂ hs₁ hs₂

      have h_k_plus_1_eq_N_minus_j' : ((N - (j' + 1)) + 1 : ℕ) = N - j' := by omega

      have h_P_k_plus_1 : ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ (((N - (j' + 1)) + 1 : ℕ) : ℝ) * Real.sqrt 2 → s₂ = 2 * (((N - (j' + 1)) + 1 : ℕ) : ℝ) → WinB ((N - (j' + 1)) + 1) s₁ s₂ := by
        intro s₁' s₂' hs₁' hs₂'
        rw [h_k_plus_1_eq_N_minus_j'] at *
        exact ih' s₁' s₂' hs₁' hs₂'

      exact round3_P_inductive_step_backward l hl0 hl WinB winB_iff (N - (j' + 1)) h_P_k_plus_1 s₁ s₂ hs₁ hs₂

  have h_P_0 : ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ ((N - N : ℕ) : ℝ) * Real.sqrt 2 → s₂ = 2 * ((N - N : ℕ) : ℝ) → WinB (N - N) s₁ s₂ := h_P_N_minus_j N (by linarith)

  have h_N_minus_N_eq_0 : (N - N : ℕ) = 0 := by omega

  have h_P_0_specific : WinB (N - N) 0 0 := h_P_0 0 0 (by norm_num) (by norm_num)

  rw [h_N_minus_N_eq_0] at h_P_0_specific

  exact h_P_0_specific

#print axioms imo2025_p5_algebra_A
#print axioms imo2025_p5_algebra_B


lemma imo2025_p5_draw1_main (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sa : (n : ℕ) → (Fin n → ℝ) → ℝ, (∀ i x, sa i x ≥ 0) ∧
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i ≥ 0) →
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i = sa i (fun j ↦ b (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by
  use fun n x => 0
  constructor
  · -- Show ∀ i x, (fun n x => 0) i x ≥ 0
    intro i x
    simp
  · -- Now for the second part
    intro b hb a ha n h1
    have ha1 : ∀ i : ℕ, a i = 0 := by
      intro i
      specialize ha i
      simpa using ha
    have h2 : ∀ m : ℕ, m ≤ n → (∑ i in Finset.range m, b i ^ 2) ≤ 2 * (m : ℝ) := by
      intro m hm
      induction m with
      | zero =>
        norm_num
        <;> simp
      | succ m ih =>
        have h11 : m < n := by linarith
        have h12 := h1 m h11
        have h122 := h12.2
        have ha_m : a m = 0 := ha1 m
        have h1222 : (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) + a m ^ 2 + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := by simpa using h122
        have h1223 : (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) + a m ^ 2 + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := h1222
        have h1224 : (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) + a m ^ 2 + b m ^ 2 = (∑ i in Finset.range m, (0 ^ 2 + b i ^ 2)) + 0 ^ 2 + b m ^ 2 := by
          have h12241 : ∀ i ∈ Finset.range m, a i = 0 := by
            intro i _
            exact ha1 i
          have h1 : (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) = ∑ i in Finset.range m, (0 ^ 2 + b i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [h12241 i hi]
          rw [h1]
          rw [ha_m]
          <;> ring
        have h1225 : (∑ i in Finset.range m, (0 ^ 2 + b i ^ 2)) + 0 ^ 2 + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := by linarith
        have h1226 : (∑ i in Finset.range m, b i ^ 2) + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := by
          have h12261 : (∑ i in Finset.range m, (0 ^ 2 + b i ^ 2)) = (∑ i in Finset.range m, b i ^ 2) := by
            simp
          rw [h12261] at h1225
          linarith
        have h1227 : (∑ i in Finset.range (m + 1), b i ^ 2) = (∑ i in Finset.range m, b i ^ 2) + b m ^ 2 := by
          rw [Finset.sum_range_succ]
        have h1228 : (∑ i in Finset.range (m + 1), b i ^ 2) ≤ 2 * ((m : ℝ) + 1) := by linarith
        norm_num at *
        <;> linarith
    have h21 : (∑ i in Finset.range n, b i ^ 2) ≤ 2 * (n : ℝ) := by
      specialize h2 n (by linarith)
      simpa using h2
    have h3 : (∑ i in Finset.range n, b i) ^ 2 ≤ (∑ i in Finset.range n, (1 : ℝ) ^ 2) * (∑ i in Finset.range n, b i ^ 2) := by
      have h31 : (∑ i in Finset.range n, b i * 1) ^ 2 ≤ (∑ i in Finset.range n, b i ^ 2) * (∑ i in Finset.range n, (1 : ℝ) ^ 2) := by
        apply?
      have h32 : (∑ i in Finset.range n, b i * 1) = ∑ i in Finset.range n, b i := by
        simp
      rw [h32] at h31
      linarith
    have h4 : (∑ i in Finset.range n, (1 : ℝ) ^ 2) = (n : ℝ) := by
      simp [Finset.sum_const, mul_one]
      <;> norm_num
    rw [h4] at h3
    have h5 : (∑ i in Finset.range n, b i) ^ 2 ≤ (n : ℝ) * (∑ i in Finset.range n, b i ^ 2) := by linarith
    have h51 : (n : ℝ) * (∑ i in Finset.range n, b i ^ 2) ≤ (n : ℝ) * (2 * (n : ℝ)) := by
      have h511 : (∑ i in Finset.range n, b i ^ 2) ≤ 2 * (n : ℝ) := h21
      have h512 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      nlinarith
    have h52 : (∑ i in Finset.range n, b i) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
      nlinarith
    have h6 : (2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2) ≥ 0 := by
      have h61 : (2 * (n : ℝ) + 1) ≥ 0 := by
        have h611 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
        linarith
      have h62 : Real.sqrt 2 / 2 ≥ 0 := by positivity
      nlinarith
    have h7 : 2 * (n : ℝ) ^ 2 ≤ ((2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2)) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h8 : (∑ i in Finset.range n, b i) ≥ 0 := by
      apply Finset.sum_nonneg
      intro i _
      exact hb i
    have h9 : (∑ i in Finset.range n, b i) ^ 2 ≤ ((2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2)) ^ 2 := by linarith
    have h10 : (∑ i in Finset.range n, b i) ≤ (2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2) := by nlinarith [h6, h9, Real.sqrt_nonneg 2]
    have h101 : (∑ i in Finset.range n, b i) ≤ (2 * (n : ℝ) + 1) * l := by
      have hl2 : l = Real.sqrt 2 / 2 := hl
      rw [hl2] at *
      linarith
    have h12 : (∑ i ∈ Finset.range n, (a i + b i)) + a n = (∑ i in Finset.range n, b i) := by
      have h121 : ∀ i ∈ Finset.range n, a i + b i = b i := by
        intro i _
        have h1211 : a i = 0 := ha1 i
        linarith
      have h122 : (∑ i in Finset.range n, (a i + b i)) = (∑ i in Finset.range n, b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h121 i hi
      have h123 : a n = 0 := ha1 n
      linarith
    have h_final : (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * (n : ℝ) + 1) * l := by linarith [h101, h12]
    simpa using h_final

#print axioms imo2025_p5_draw1_main


theorem imo2025_p5_draw_b (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sa : (n : ℕ) → (Fin n → ℝ) → ℝ, (∀ i x, sa i x ≥ 0) ∧
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i ≥ 0) →
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i = sa i (fun j ↦ b (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by
  exact imo2025_p5_draw1_main l hl0 hl

#print axioms imo2025_p5_draw_b



lemma imo2025_p5_draw_a_v22_main (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sb : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ, (∀ i x, sb i x ≥ 0) ∧
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i ≥ 0) →
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i = sb i (fun j ↦ a (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l →
        (∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2)) + a n ^ 2 + b n ^ 2 ≤ 2 * n + 2 := by
  use fun (n : ℕ) (f : Fin (n + 1) → ℝ) => if f ⟨n, by linarith⟩ ≤ Real.sqrt 2 then Real.sqrt 2 - f ⟨n, by linarith⟩ else 0
  constructor
  · -- Proof that ∀ i x, sb i x ≥ 0
    intro i x
    by_cases h : x ⟨i, by linarith⟩ ≤ Real.sqrt 2
    · -- Case 1: x ⟨i, _⟩ ≤ Real.sqrt 2
      simp [h]
      <;> linarith
    · -- Case 2: ¬ (x ⟨i, _⟩ ≤ Real.sqrt 2)
      simp [h]
      <;> linarith
  · intro a ha b h1 n h2 h3
    have h100 : ∀ m : ℕ, m ≤ n → ∑ i in Finset.range m, (a i ^ 2 + b i ^ 2) ≤ 2 * (m : ℝ) := by
      intro m hm
      induction m with
      | zero =>
        norm_num
      | succ m ih =>
        have h4 : m ≤ n := by linarith
        have h5 : m < n := by linarith
        have h6 := h2 m h5
        have h61 := h6.2
        have h7 : ∑ i in Finset.range (m + 1), (a i ^ 2 + b i ^ 2) = (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) + (a m ^ 2 + b m ^ 2) := by
          rw [Finset.sum_range_succ]
          <;> ring
        have h8 : (∑ i in Finset.range m, (a i ^ 2 + b i ^ 2)) + a m ^ 2 + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := by simpa using h61
        have h9 : (∑ i in Finset.range (m + 1), (a i ^ 2 + b i ^ 2)) ≤ 2 * (m : ℝ) + 2 := by linarith [h7, h8]
        have h10 : (2 * (m : ℝ) + 2 : ℝ) = 2 * ((m + 1 : ℕ) : ℝ) := by
          simp [Nat.cast_add, Nat.cast_one]
          <;> ring
        linarith
    have h4 : ∀ i : ℕ, b i = if a i ≤ Real.sqrt 2 then Real.sqrt 2 - a i else 0 := by
      intro i
      have h11 := h1 i
      simpa using h11
    have h5 : ∀ i : ℕ, b i ≥ 0 := by
      intro i
      have h51 := h4 i
      rw [h51]
      by_cases h52 : a i ≤ Real.sqrt 2
      · -- Case 1: a i ≤ Real.sqrt 2
        rw [if_pos h52]
        linarith [Real.sqrt_nonneg 2]
      · -- Case 2: ¬ (a i ≤ Real.sqrt 2)
        rw [if_neg h52]
        <;> norm_num
    have h6 : ∀ i : ℕ, a i + b i ≥ Real.sqrt 2 := by
      intro i
      have h41 := h4 i
      rw [h41]
      by_cases h61 : a i ≤ Real.sqrt 2
      · -- Case 1: a i ≤ Real.sqrt 2
        rw [if_pos h61]
        linarith
      · -- Case 2: ¬ (a i ≤ Real.sqrt 2)
        rw [if_neg h61]
        have h62 : a i > Real.sqrt 2 := by linarith
        linarith
    have h7 : (∑ i in Finset.range n, (a i + b i)) ≥ (n : ℝ) * Real.sqrt 2 := by
      have h71 : ∀ i ∈ Finset.range n, a i + b i ≥ Real.sqrt 2 := fun i _ => h6 i
      have h72 : (∑ i in Finset.range n, (a i + b i)) ≥ ∑ i in Finset.range n, Real.sqrt 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact h71 i ‹_›
      have h73 : (∑ i in Finset.range n, Real.sqrt 2) = (n : ℝ) * Real.sqrt 2 := by
        simp [mul_comm]
        <;> ring
      linarith
    have h8 : (∑ i in Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by simpa using h3
    have h9 : (∑ i in Finset.range n, (a i + b i)) + a n ≤ (2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2) := by
      have h91 : l = Real.sqrt 2 / 2 := by linarith [hl]
      rw [h91] at h8
      linarith
    have h10 : (n : ℝ) * Real.sqrt 2 + a n ≤ (2 * (n : ℝ) + 1) * (Real.sqrt 2 / 2) := by linarith [h7, h9]
    have h11 : a n ≤ Real.sqrt 2 / 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h12 : a n ≤ Real.sqrt 2 := by linarith [Real.sqrt_nonneg 2, h11]
    have h13 : b n = Real.sqrt 2 - a n := by
      have h131 := h4 n
      rw [h131]
      rw [if_pos h12]
    have h14 : a n ^ 2 + b n ^ 2 ≤ 2 := by
      rw [h13]
      have h141 : 0 ≤ a n := ha n
      have h142 : a n ≤ Real.sqrt 2 / 2 := h11
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h15 : ∑ i in Finset.range n, (a i ^ 2 + b i ^ 2) ≤ 2 * (n : ℝ) := by
      specialize h100 n (by linarith)
      simpa using h100
    have h_final : (∑ i in Finset.range n, (a i ^ 2 + b i ^ 2)) + a n ^ 2 + b n ^ 2 ≤ 2 * (n : ℝ) + 2 := by linarith
    norm_cast at h_final ⊢
    <;> linarith

#print axioms imo2025_p5_draw_a_v22_main


theorem imo2025_p5_draw_a (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sb : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ, (∀ i x, sb i x ≥ 0) ∧
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i ≥ 0) →
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i = sb i (fun j ↦ a (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l →
        (∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2)) + a n ^ 2 + b n ^ 2 ≤ 2 * n + 2 := by
  exact imo2025_p5_draw_a_v22_main l hl0 hl

#print axioms imo2025_p5_draw_a
