import Mathlib
import Aesop
set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial

lemma k_le_3_for_n_le_4_round1_main (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn2 : n = 4):
  k ≤ 3 := by
  by_cases h16 : k > 3
  · -- Assume k > 3, we will derive a contradiction
    have h161 : k ≥ 4 := by linarith
    have h162 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card ≥ 4 := by linarith
    have h163 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card ≤ lines.card := by apply Finset.card_filter_le
    have h164 : lines.card + verts.card = 4 := by linarith
    have h165 : lines.card ≥ 4 := by omega
    have h166 : lines.card = 4 := by omega
    have h167 : verts.card = 0 := by omega
    have h168 : verts = ∅ := by
      exact Finset.card_eq_zero.mp h167
    have h170 : ∀ (p : ℕ × ℕ), p ∈ points → ∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by
      intro p hp
      have h1701 := hmain p hp
      rcases h1701 with (h1701 | h1702)
      · exact h1701
      · rcases h1702 with ⟨x, hx, _⟩
        have h1703 : x ∈ verts := hx
        rw [h168] at h1703
        contradiction
    have h176 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = 4 := by
      have h1761 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card ≥ 4 := h162
      have h1762 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card ≤ lines.card := h163
      have h1763 : lines.card = 4 := h166
      linarith
    have h1761 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by linarith
    have h177 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := by
      intro l hl
      by_contra h1771
      have h1772 : ¬(l.1 ≠ 0 ∧ l.1 ≠ -1) := by tauto
      have h1773 : l ∉ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
        simp [Finset.mem_filter]
        <;> tauto
      have h1774 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) ⊂ lines := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · exact Finset.filter_subset _ _
        · intro h1775
          have h1776 : l ∈ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
            rw [h1775]
            exact hl
          contradiction
      have h1777 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card < lines.card := by
        apply Finset.card_lt_card
        exact h1774
      linarith
    have h171 : (1, 1) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    have h172 : (1, 2) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    have h173 : (1, 3) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    have h174 : (1, 4) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    obtain ⟨l1, hl1_in_lines, h11_eq⟩ := h170 (1, 1) h171
    obtain ⟨l2, hl2_in_lines, h12_eq⟩ := h170 (1, 2) h172
    obtain ⟨l3, hl3_in_lines, h13_eq⟩ := h170 (1, 3) h173
    obtain ⟨l4, hl4_in_lines, h14_eq⟩ := h170 (1, 4) h174
    have h111 : l1.1 + l1.2 = 1 := by
      norm_num at h11_eq ⊢
      <;> linarith
    have h122 : l2.1 + l2.2 = 2 := by
      norm_num at h12_eq ⊢
      <;> linarith
    have h133 : l3.1 + l3.2 = 3 := by
      norm_num at h13_eq ⊢
      <;> linarith
    have h144 : l4.1 + l4.2 = 4 := by
      norm_num at h14_eq ⊢
      <;> linarith
    have h11_ne_12 : l1 ≠ l2 := by
      intro h
      have h1 : l1.1 + l1.2 = 2 := by
        have h11 : l1 = l2 := h
        have h1221 : l2.1 + l2.2 = 2 := h122
        simp [h11] at *
        <;> linarith
      linarith
    have h11_ne_13 : l1 ≠ l3 := by
      intro h
      have h1 : l1.1 + l1.2 = 3 := by
        have h11 : l1 = l3 := h
        have h1331 : l3.1 + l3.2 = 3 := h133
        simp [h11] at *
        <;> linarith
      linarith
    have h11_ne_14 : l1 ≠ l4 := by
      intro h
      have h1 : l1.1 + l1.2 = 4 := by
        have h11 : l1 = l4 := h
        have h1441 : l4.1 + l4.2 = 4 := h144
        simp [h11] at *
        <;> linarith
      linarith
    have h12_ne_13 : l2 ≠ l3 := by
      intro h
      have h1 : l2.1 + l2.2 = 3 := by
        have h11 : l2 = l3 := h
        have h1331 : l3.1 + l3.2 = 3 := h133
        simp [h11] at *
        <;> linarith
      linarith
    have h12_ne_14 : l2 ≠ l4 := by
      intro h
      have h1 : l2.1 + l2.2 = 4 := by
        have h11 : l2 = l4 := h
        have h1441 : l4.1 + l4.2 = 4 := h144
        simp [h11] at *
        <;> linarith
      linarith
    have h13_ne_14 : l3 ≠ l4 := by
      intro h
      have h1 : l3.1 + l3.2 = 4 := by
        have h11 : l3 = l4 := h
        have h1441 : l4.1 + l4.2 = 4 := h144
        simp [h11] at *
        <;> linarith
      linarith
    have h178 : ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) ⊆ lines := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with (rfl | rfl | rfl | rfl)
      · exact hl1_in_lines
      · exact hl2_in_lines
      · exact hl3_in_lines
      · exact hl4_in_lines
    have h179 : ({l1, l2, l3, l4} : Finset (ℝ × ℝ)).card = 4 := by
      simp [h11_ne_12, h11_ne_13, h11_ne_14, h12_ne_13, h12_ne_14, h13_ne_14]
      <;> aesop
    have h180 : ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) = lines := by
      apply Finset.eq_of_subset_of_card_le h178
      rw [h179, h166]
      <;> aesop
    have h171_2 : (2, 2) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    obtain ⟨l5, hl5_in_lines, h15_eq⟩ := h170 (2, 2) h171_2
    have h15_eq' : l5.1 * 2 + l5.2 = 2 := by
      norm_num at h15_eq ⊢
      <;> linarith
    have h171_3 : (2, 3) ∈ points := by
      rw [hallpoints]
      norm_num [hn2]
      <;> aesop
    obtain ⟨l6, hl6_in_lines, h16_eq⟩ := h170 (2, 3) h171_3
    have h16_eq' : l6.1 * 2 + l6.2 = 3 := by
      norm_num at h16_eq ⊢
      <;> linarith
    have h1801 : lines = ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by tauto
    have h15_in_set : l5 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
      rw [h1801] at hl5_in_lines
      tauto
    have h16_in_set : l6 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
      rw [h1801] at hl6_in_lines
      tauto
    have h15_cases : l5 = l1 ∨ l5 = l2 ∨ l5 = l3 ∨ l5 = l4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h15_in_set
      tauto
    have h16_cases : l6 = l1 ∨ l6 = l2 ∨ l6 = l3 ∨ l6 = l4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h16_in_set
      tauto
    have h15_ne_2 : l5 ≠ l2 := by
      by_contra h15_eq_2
      have h177_l2 := h177 l2 hl2_in_lines
      have h151 : l2.1 * 2 + l2.2 = 2 := by
        have h1511 : l5 = l2 := by tauto
        rw [h1511] at h15_eq'
        <;> linarith
      have h152 : l2.1 = 0 := by linarith
      have h177_l21 : l2.1 ≠ 0 := h177_l2.1
      contradiction
    have h15_ne_3 : l5 ≠ l3 := by
      by_contra h15_eq_3
      have h177_l3 := h177 l3 hl3_in_lines
      have h151 : l3.1 * 2 + l3.2 = 2 := by
        have h1511 : l5 = l3 := by tauto
        rw [h1511] at h15_eq'
        <;> linarith
      have h152 : l3.1 = -1 := by linarith
      have h177_l32 : l3.1 ≠ -1 := h177_l3.2
      contradiction
    have h15_cases2 : l5 = l1 ∨ l5 = l4 := by tauto
    have h16_ne_3 : l6 ≠ l3 := by
      by_contra h16_eq_3
      have h177_l3 := h177 l3 hl3_in_lines
      have h161 : l3.1 * 2 + l3.2 = 3 := by
        have h1611 : l6 = l3 := by tauto
        rw [h1611] at h16_eq'
        <;> linarith
      have h162 : l3.1 = 0 := by linarith
      have h177_l31 : l3.1 ≠ 0 := h177_l3.1
      contradiction
    have h16_ne_4 : l6 ≠ l4 := by
      by_contra h16_eq_4
      have h177_l4 := h177 l4 hl4_in_lines
      have h161 : l4.1 * 2 + l4.2 = 3 := by
        have h1611 : l6 = l4 := by tauto
        rw [h1611] at h16_eq'
        <;> linarith
      have h162 : l4.1 = -1 := by linarith
      have h177_l42 : l4.1 ≠ -1 := h177_l4.2
      contradiction
    have h16_cases2 : l6 = l1 ∨ l6 = l2 := by tauto
    rcases h15_cases2 with (h15_eq_l1 | h15_eq_l4)
    · -- Case 1: l5 = l1
      have h15_eq_l11 : l5 = l1 := h15_eq_l1
      have h15_eq_l12 : l1.1 * 2 + l1.2 = 2 := by
        rw [h15_eq_l11] at h15_eq'
        <;> linarith
      have h1111 : l1.1 = 1 := by linarith
      have h1112 : l1.2 = 0 := by linarith
      rcases h16_cases2 with (h16_eq_l1 | h16_eq_l2)
      · -- Subcase 1.1: l6 = l1
        have h16_eq_l11 : l6 = l1 := h16_eq_l1
        have h16_eq_l12 : l1.1 * 2 + l1.2 = 3 := by
          rw [h16_eq_l11] at h16_eq'
          <;> linarith
        norm_num [h1111, h1112] at h16_eq_l12
        <;> linarith
      · -- Subcase 1.2: l6 = l2
        have h16_eq_l21 : l6 = l2 := h16_eq_l2
        have h16_eq_l22 : l2.1 * 2 + l2.2 = 3 := by
          rw [h16_eq_l21] at h16_eq'
          <;> linarith
        have h1221 : l2.1 = 1 := by linarith
        have h1222 : l2.2 = 1 := by linarith
        have h171_4 : (3, 1) ∈ points := by
          rw [hallpoints]
          norm_num [hn2]
          <;> aesop
        obtain ⟨l9, hl9_in_lines, h19_eq⟩ := h170 (3, 1) h171_4
        have h19_eq' : l9.1 * 3 + l9.2 = 1 := by
          norm_num at h19_eq ⊢ <;> linarith
        have h19_in_set : l9 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
          rw [h1801] at hl9_in_lines
          tauto
        have h19_cases : l9 = l1 ∨ l9 = l2 ∨ l9 = l3 ∨ l9 = l4 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at h19_in_set <;> tauto
        rcases h19_cases with (h19_eq_l1 | h19_eq_l2 | h19_eq_l3 | h19_eq_l4)
        · -- l9 = l1
          have h19_eq_l11 : l9 = l1 := h19_eq_l1
          have h19_eq1 : l1.1 * 3 + l1.2 = 1 := by
            rw [h19_eq_l11] at h19_eq'
            <;> linarith
          norm_num [h1111, h1112] at h19_eq1
          <;> linarith
        · -- l9 = l2
          have h19_eq_l21 : l9 = l2 := h19_eq_l2
          have h19_eq2 : l2.1 * 3 + l2.2 = 1 := by
            rw [h19_eq_l21] at h19_eq'
            <;> linarith
          norm_num [h1221, h1222] at h19_eq2
          <;> linarith
        · -- l9 = l3
          have h19_eq_l31 : l9 = l3 := h19_eq_l3
          have h19_eq3 : l3.1 * 3 + l3.2 = 1 := by
            rw [h19_eq_l31] at h19_eq'
            <;> linarith
          have h31 : l3.1 = -1 := by linarith
          have h177_l3 := h177 l3 hl3_in_lines
          have h177_l32 : l3.1 ≠ -1 := h177_l3.2
          contradiction
        · -- l9 = l4
          have h19_eq_l41 : l9 = l4 := h19_eq_l4
          have h19_eq4 : l4.1 * 3 + l4.2 = 1 := by
            rw [h19_eq_l41] at h19_eq'
            <;> linarith
          have h41 : l4.1 = -3 / 2 := by linarith
          have h42 : l4.2 = 11 / 2 := by linarith
          have h171_5 : (2, 1) ∈ points := by
            rw [hallpoints]
            norm_num [hn2]
            <;> aesop
          obtain ⟨l10, hl10_in_lines, h20_eq⟩ := h170 (2, 1) h171_5
          have h20_eq' : l10.1 * 2 + l10.2 = 1 := by
            norm_num at h20_eq ⊢ <;> linarith
          have h20_in_set : l10 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
            rw [h1801] at hl10_in_lines
            tauto
          have h20_cases : l10 = l1 ∨ l10 = l2 ∨ l10 = l3 ∨ l10 = l4 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at h20_in_set <;> tauto
          rcases h20_cases with (h20_eq_l1 | h20_eq_l2 | h20_eq_l3 | h20_eq_l4)
          · -- l10 = l1
            have h20_eq_l11 : l10 = l1 := h20_eq_l1
            have h20_eq1 : l1.1 * 2 + l1.2 = 1 := by
              rw [h20_eq_l11] at h20_eq'
              <;> linarith
            norm_num [h1111, h1112] at h20_eq1
            <;> linarith
          · -- l10 = l2
            have h20_eq_l21 : l10 = l2 := h20_eq_l2
            have h20_eq2 : l2.1 * 2 + l2.2 = 1 := by
              rw [h20_eq_l21] at h20_eq'
              <;> linarith
            norm_num [h1221, h1222] at h20_eq2
            <;> linarith
          · -- l10 = l3
            have h20_eq_l31 : l10 = l3 := h20_eq_l3
            have h20_eq3 : l3.1 * 2 + l3.2 = 1 := by
              rw [h20_eq_l31] at h20_eq'
              <;> linarith
            have h31 : l3.1 = -2 := by linarith
            have h32 : l3.2 = 5 := by linarith
            have h171_6 : (4, 1) ∈ points := by
              rw [hallpoints]
              norm_num [hn2]
              <;> aesop
            obtain ⟨l11, hl11_in_lines, h21_eq⟩ := h170 (4, 1) h171_6
            have h21_eq' : l11.1 * 4 + l11.2 = 1 := by
              norm_num at h21_eq ⊢ <;> linarith
            have h21_in_set : l11 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
              rw [h1801] at hl11_in_lines
              tauto
            have h21_cases : l11 = l1 ∨ l11 = l2 ∨ l11 = l3 ∨ l11 = l4 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at h21_in_set <;> tauto
            rcases h21_cases with (h21_eq_l1 | h21_eq_l2 | h21_eq_l3 | h21_eq_l4)
            · -- l11 = l1
              have h21_eq_l11 : l11 = l1 := h21_eq_l1
              have h21_eq1 : l1.1 * 4 + l1.2 = 1 := by
                rw [h21_eq_l11] at h21_eq'
                <;> linarith
              norm_num [h1111, h1112] at h21_eq1
              <;> linarith
            · -- l11 = l2
              have h21_eq_l21 : l11 = l2 := h21_eq_l2
              have h21_eq2 : l2.1 * 4 + l2.2 = 1 := by
                rw [h21_eq_l21] at h21_eq'
                <;> linarith
              norm_num [h1221, h1222] at h21_eq2
              <;> linarith
            · -- l11 = l3
              have h21_eq_l31 : l11 = l3 := h21_eq_l3
              have h21_eq3 : l3.1 * 4 + l3.2 = 1 := by
                rw [h21_eq_l31] at h21_eq'
                <;> linarith
              norm_num [h31, h32] at h21_eq3
              <;> linarith
            · -- l11 = l4
              have h21_eq_l41 : l11 = l4 := h21_eq_l4
              have h21_eq4 : l4.1 * 4 + l4.2 = 1 := by
                rw [h21_eq_l41] at h21_eq'
                <;> linarith
              norm_num [h41, h42] at h21_eq4
              <;> linarith
          · -- l10 = l4
            have h20_eq_l41 : l10 = l4 := h20_eq_l4
            have h20_eq4 : l4.1 * 2 + l4.2 = 1 := by
              rw [h20_eq_l41] at h20_eq'
              <;> linarith
            norm_num [h41, h42] at h20_eq4
            <;> linarith
    · -- Case 2: l5 = l4
      have h15_eq_l41 : l5 = l4 := h15_eq_l4
      have h15_eq_l42 : l4.1 * 2 + l4.2 = 2 := by
        rw [h15_eq_l41] at h15_eq'
        <;> linarith
      have h41 : l4.1 = -2 := by linarith
      have h42 : l4.2 = 6 := by linarith
      rcases h16_cases2 with (h16_eq_l1 | h16_eq_l2)
      · -- Subcase 2.1: l6 = l1
        have h16_eq_l11 : l6 = l1 := h16_eq_l1
        have h16_eq_l12 : l1.1 * 2 + l1.2 = 3 := by
          rw [h16_eq_l11] at h16_eq'
          <;> linarith
        have h1111 : l1.1 = 2 := by linarith
        have h1112 : l1.2 = -1 := by linarith
        have h171_4 : (3, 1) ∈ points := by
          rw [hallpoints]
          norm_num [hn2]
          <;> aesop
        obtain ⟨l9, hl9_in_lines, h19_eq⟩ := h170 (3, 1) h171_4
        have h19_eq' : l9.1 * 3 + l9.2 = 1 := by
          norm_num at h19_eq ⊢ <;> linarith
        have h19_in_set : l9 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
          rw [h1801] at hl9_in_lines
          tauto
        have h19_cases : l9 = l1 ∨ l9 = l2 ∨ l9 = l3 ∨ l9 = l4 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at h19_in_set <;> tauto
        rcases h19_cases with (h19_eq_l1 | h19_eq_l2 | h19_eq_l3 | h19_eq_l4)
        · -- l9 = l1
          have h19_eq_l11 : l9 = l1 := h19_eq_l1
          have h19_eq1 : l1.1 * 3 + l1.2 = 1 := by
            rw [h19_eq_l11] at h19_eq'
            <;> linarith
          norm_num [h1111, h1112] at h19_eq1
          <;> linarith
        · -- l9 = l2
          have h19_eq_l21 : l9 = l2 := h19_eq_l2
          have h19_eq2 : l2.1 * 3 + l2.2 = 1 := by
            rw [h19_eq_l21] at h19_eq'
            <;> linarith
          have h21 : l2.1 = -1 / 2 := by linarith
          have h22 : l2.2 = 5 / 2 := by linarith
          have h171_5 : (2, 1) ∈ points := by
            rw [hallpoints]
            norm_num [hn2]
            <;> aesop
          obtain ⟨l10, hl10_in_lines, h20_eq⟩ := h170 (2, 1) h171_5
          have h20_eq' : l10.1 * 2 + l10.2 = 1 := by
            norm_num at h20_eq ⊢ <;> linarith
          have h20_in_set : l10 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
            rw [h1801] at hl10_in_lines
            tauto
          have h20_cases : l10 = l1 ∨ l10 = l2 ∨ l10 = l3 ∨ l10 = l4 := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at h20_in_set <;> tauto
          rcases h20_cases with (h20_eq_l1 | h20_eq_l2 | h20_eq_l3 | h20_eq_l4)
          · -- l10 = l1
            have h20_eq_l11 : l10 = l1 := h20_eq_l1
            have h20_eq1 : l1.1 * 2 + l1.2 = 1 := by
              rw [h20_eq_l11] at h20_eq'
              <;> linarith
            norm_num [h1111, h1112] at h20_eq1
            <;> linarith
          · -- l10 = l2
            have h20_eq_l21 : l10 = l2 := h20_eq_l2
            have h20_eq2 : l2.1 * 2 + l2.2 = 1 := by
              rw [h20_eq_l21] at h20_eq'
              <;> linarith
            norm_num [h21, h22] at h20_eq2
            <;> linarith
          · -- l10 = l3
            have h20_eq_l31 : l10 = l3 := h20_eq_l3
            have h20_eq3 : l3.1 * 2 + l3.2 = 1 := by
              rw [h20_eq_l31] at h20_eq'
              <;> linarith
            have h31 : l3.1 = -2 := by linarith
            have h32 : l3.2 = 5 := by linarith
            have h171_6 : (4, 1) ∈ points := by
              rw [hallpoints]
              norm_num [hn2]
              <;> aesop
            obtain ⟨l11, hl11_in_lines, h21_eq⟩ := h170 (4, 1) h171_6
            have h21_eq' : l11.1 * 4 + l11.2 = 1 := by
              norm_num at h21_eq ⊢ <;> linarith
            have h21_in_set : l11 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
              rw [h1801] at hl11_in_lines
              tauto
            have h21_cases : l11 = l1 ∨ l11 = l2 ∨ l11 = l3 ∨ l11 = l4 := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at h21_in_set <;> tauto
            rcases h21_cases with (h21_eq_l1 | h21_eq_l2 | h21_eq_l3 | h21_eq_l4)
            · -- l11 = l1
              have h21_eq_l11 : l11 = l1 := h21_eq_l1
              have h21_eq1 : l1.1 * 4 + l1.2 = 1 := by
                rw [h21_eq_l11] at h21_eq'
                <;> linarith
              norm_num [h1111, h1112] at h21_eq1
              <;> linarith
            · -- l11 = l2
              have h21_eq_l21 : l11 = l2 := h21_eq_l2
              have h21_eq2 : l2.1 * 4 + l2.2 = 1 := by
                rw [h21_eq_l21] at h21_eq'
                <;> linarith
              norm_num [h21, h22] at h21_eq2
              <;> linarith
            · -- l11 = l3
              have h21_eq_l31 : l11 = l3 := h21_eq_l3
              have h21_eq3 : l3.1 * 4 + l3.2 = 1 := by
                rw [h21_eq_l31] at h21_eq'
                <;> linarith
              norm_num [h31, h32] at h21_eq3
              <;> linarith
            · -- l11 = l4
              have h21_eq_l41 : l11 = l4 := h21_eq_l4
              have h21_eq4 : l4.1 * 4 + l4.2 = 1 := by
                rw [h21_eq_l41] at h21_eq'
                <;> linarith
              norm_num [h41, h42] at h21_eq4
              <;> linarith
          · -- l10 = l4
            have h20_eq_l41 : l10 = l4 := h20_eq_l4
            have h20_eq4 : l4.1 * 2 + l4.2 = 1 := by
              rw [h20_eq_l41] at h20_eq'
              <;> linarith
            norm_num [h41, h42] at h20_eq4
            <;> linarith
        · -- l9 = l3
          have h19_eq_l31 : l9 = l3 := h19_eq_l3
          have h19_eq3 : l3.1 * 3 + l3.2 = 1 := by
            rw [h19_eq_l31] at h19_eq'
            <;> linarith
          have h31 : l3.1 = -1 := by linarith
          have h177_l3 := h177 l3 hl3_in_lines
          have h177_l32 : l3.1 ≠ -1 := h177_l3.2
          contradiction
        · -- l9 = l4
          have h19_eq_l41 : l9 = l4 := h19_eq_l4
          have h19_eq4 : l4.1 * 3 + l4.2 = 1 := by
            rw [h19_eq_l41] at h19_eq'
            <;> linarith
          norm_num [h41, h42] at h19_eq4
          <;> linarith
      · -- Subcase 2.2: l6 = l2
        have h16_eq_l21 : l6 = l2 := h16_eq_l2
        have h16_eq_l22 : l2.1 * 2 + l2.2 = 3 := by
          rw [h16_eq_l21] at h16_eq'
          <;> linarith
        have h1221 : l2.1 = 1 := by linarith
        have h1222 : l2.2 = 1 := by linarith
        have h171_4 : (3, 1) ∈ points := by
          rw [hallpoints]
          norm_num [hn2]
          <;> aesop
        obtain ⟨l9, hl9_in_lines, h19_eq⟩ := h170 (3, 1) h171_4
        have h19_eq' : l9.1 * 3 + l9.2 = 1 := by
          norm_num at h19_eq ⊢ <;> linarith
        have h19_in_set : l9 ∈ ({l1, l2, l3, l4} : Finset (ℝ × ℝ)) := by
          rw [h1801] at hl9_in_lines
          tauto
        have h19_cases : l9 = l1 ∨ l9 = l2 ∨ l9 = l3 ∨ l9 = l4 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at h19_in_set <;> tauto
        rcases h19_cases with (h19_eq_l1 | h19_eq_l2 | h19_eq_l3 | h19_eq_l4)
        · -- l9 = l1
          have h19_eq_l11 : l9 = l1 := h19_eq_l1
          have h19_eq1 : l1.1 * 3 + l1.2 = 1 := by
            rw [h19_eq_l11] at h19_eq'
            <;> linarith
          have h1111 : l1.1 = 0 := by linarith
          have h177_l1 := h177 l1 hl1_in_lines
          have h177_l11 : l1.1 ≠ 0 := h177_l1.1
          contradiction
        · -- l9 = l2
          have h19_eq_l21 : l9 = l2 := h19_eq_l2
          have h19_eq2 : l2.1 * 3 + l2.2 = 1 := by
            rw [h19_eq_l21] at h19_eq'
            <;> linarith
          norm_num [h1221, h1222] at h19_eq2
          <;> linarith
        · -- l9 = l3
          have h19_eq_l31 : l9 = l3 := h19_eq_l3
          have h19_eq3 : l3.1 * 3 + l3.2 = 1 := by
            rw [h19_eq_l31] at h19_eq'
            <;> linarith
          have h31 : l3.1 = -1 := by linarith
          have h177_l3 := h177 l3 hl3_in_lines
          have h177_l32 : l3.1 ≠ -1 := h177_l3.2
          contradiction
        · -- l9 = l4
          have h19_eq_l41 : l9 = l4 := h19_eq_l4
          have h19_eq4 : l4.1 * 3 + l4.2 = 1 := by
            rw [h19_eq_l41] at h19_eq'
            <;> linarith
          norm_num [h41, h42] at h19_eq4
          <;> linarith
  · -- Case 2: ¬ (k > 3)
    linarith

lemma round1_case_n_eq_3 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn2 : n = 3):
  k ≤ 3 := by
  have h11 : n = 3 := hn2
  have h12 : lines.card + verts.card = 3 := by linarith
  have h13 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card ≤ lines.card := by apply Finset.card_filter_le
  have h14 : k = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by linarith
  have h15 : k ≤ lines.card := by linarith
  omega

theorem k_le_3_for_n_le_4 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n = 3 ∨ n = 4):
  k ≤ 3  := by

  rcases hn with (h1 | h1)
  · -- Case 1: n = 3
    exact round1_case_n_eq_3 n k verts lines points (by linarith) hcard hallpoints hmain hk h1
  · -- Case 2: n = 4
    exact k_le_3_for_n_le_4_round1_main n k verts lines points (by linarith) hcard hallpoints hmain hk h1

lemma round1_case1 (n : ℕ)
  (k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n = 3)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (h411 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1)
  (h412 : verts.card = 1):
  False := by
  by_cases h1inverts : (1 : ℝ) ∈ verts
  · -- Case 1.1.2: `1 ∈ verts`
    have h4122 : verts = ({(1 : ℝ)} : Finset ℝ) := by
      have h41221 : verts.card = 1 := h412
      have h41222 : (1 : ℝ) ∈ verts := h1inverts
      have h41223 : ∃ x, verts = {x} := by
        exact?
      rcases h41223 with ⟨x, hx⟩
      have hx1 : x ∈ verts := by simp [hx]
      have h1in : (1 : ℝ) ∈ verts := h41222
      have h1eqx : (1 : ℝ) = x := by
        rw [hx] at h1in hx1
        simp_all
      have h : verts = ({(1 : ℝ)} : Finset ℝ) := by
        rw [hx, h1eqx]
        <;> aesop
      exact h
    have h21inpoints : (⟨2, 1⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨2, 1⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h31inpoints : (⟨3, 1⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨3, 1⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h22inpoints : (⟨2, 2⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨2, 2⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h5 : ∃ l ∈ lines, l.1 * 2 + l.2 = 1 := by
      have h211 := hmain (⟨2, 1⟩ : ℕ × ℕ) h21inpoints
      cases h211 with
      | inl h2111 =>
        rcases h2111 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h2112 =>
        rcases h2112 with ⟨x, hx, hx2⟩
        have h41224 : verts = ({(1 : ℝ)} : Finset ℝ) := h4122
        rw [h41224] at hx
        norm_num at hx
        <;> aesop
    have h6 : ∃ l ∈ lines, l.1 * 3 + l.2 = 1 := by
      have h311 := hmain (⟨3, 1⟩ : ℕ × ℕ) h31inpoints
      cases h311 with
      | inl h3111 =>
        rcases h3111 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h3112 =>
        rcases h3112 with ⟨x, hx, hx2⟩
        have h41224 : verts = ({(1 : ℝ)} : Finset ℝ) := h4122
        rw [h41224] at hx
        norm_num at hx
        <;> aesop
    rcases h5 with ⟨l1, hl1_in_lines, h1_eq1⟩
    rcases h6 with ⟨l2, hl2_in_lines, h1_eq2⟩
    have h_l1_ne_l2 : l1 ≠ l2 := by
      by_contra h_l1_eq_l2
      have h111 : l1.1 * 2 + l1.2 = 1 := h1_eq1
      have h112 : l2.1 * 3 + l2.2 = 1 := h1_eq2
      have h113 : l1.1 * 3 + l1.2 = 1 := by
        have h1131 : l2.1 * 3 + l2.2 = 1 := h112
        have h1132 : l1 = l2 := by tauto
        simp [h1132] at *
        <;> linarith
      have h114 : l1.1 = 0 := by linarith
      have h115 := h411 l1 hl1_in_lines
      have h116 : l1.1 ≠ 0 := h115.1
      contradiction
    have h7 : ∃ l ∈ lines, l.1 * 2 + l.2 = 2 := by
      have h222 := hmain (⟨2, 2⟩ : ℕ × ℕ) h22inpoints
      cases h222 with
      | inl h2221 =>
        rcases h2221 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h2222 =>
        rcases h2222 with ⟨x, hx, hx2⟩
        have h41224 : verts = ({(1 : ℝ)} : Finset ℝ) := h4122
        rw [h41224] at hx
        norm_num at hx
        <;> aesop
    rcases h7 with ⟨l3, hl3_in_lines, h1_eq3⟩
    have h4111 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by
      have h4112 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := h411
      have h4113 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) = lines := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        constructor
        · intro h
          tauto
        · intro hx
          have h4114 := h4112 x hx
          tauto
      have h4114 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by
        rw [h4113]
        <;> rfl
      have h4115 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by
        have h4116 : Disjoint (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) := by
          simp [Finset.disjoint_left]
          <;> aesop
        have h4117 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) = lines := by
          ext x
          simp [or_iff_not_imp_left]
          <;> by_cases h121 : x.1 ≠ 0 <;> by_cases h122 : x.1 ≠ -1 <;> simp_all <;> aesop
        have h4118 : ((lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1))).card = (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          rw [Finset.card_union_of_disjoint h4116]
        have h4119 : lines.card = (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          rw [h4117] at h4118
          linarith
        have h4120 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by linarith
        have h4121 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by linarith
        exact h4121
      exact h4115
    have h4114 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by
      have h4113 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) = lines := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        constructor
        · intro h
          tauto
        · intro hx
          have h4114 := h411 x hx
          tauto
      rw [h4113]
      <;> rfl
    have h_lines_card : lines.card = 2 := by linarith
    have h121 : ({l1, l2} : Finset (ℝ × ℝ)) ⊆ lines := by
      intro x hx
      simp at hx
      rcases hx with (rfl | rfl)
      · exact hl1_in_lines
      · exact hl2_in_lines
    have h122 : ({l1, l2} : Finset (ℝ × ℝ)).card = 2 := by
      simp [Finset.card_pair, h_l1_ne_l2]
      <;> aesop
    have h123 : ({l1, l2} : Finset (ℝ × ℝ)) = lines := by
      apply Finset.eq_of_subset_of_card_le h121
      <;> simp [h122, h_lines_card]
      <;> aesop
    have h124 : l3 ∈ ({l1, l2} : Finset (ℝ × ℝ)) := by
      rw [h123]
      exact hl3_in_lines
    have h1241 : l3 = l1 ∨ l3 = l2 := by
      simp at h124
      tauto
    rcases h1241 with (h1241 | h1241)
    · -- Case l3 = l1
      have h12411 : l3 = l1 := h1241
      have h1_eq3' : l3.1 * 2 + l3.2 = 2 := h1_eq3
      rw [h12411] at h1_eq3'
      have h1_eq11 : l1.1 * 2 + l1.2 = 1 := h1_eq1
      linarith
    · -- Case l3 = l2
      have h12412 : l3 = l2 := h1241
      have h1_eq3' : l3.1 * 2 + l3.2 = 2 := h1_eq3
      have h1_eq3'' : l2.1 * 2 + l2.2 = 2 := by
        rw [h12412] at h1_eq3'
        tauto
      have h1_eq22 : l2.1 * 3 + l2.2 = 1 := h1_eq2
      have h12421 : l2.1 = -1 := by linarith
      have h4112 := h411 l2 hl2_in_lines
      have h4113 : l2.1 ≠ -1 := h4112.2
      contradiction
  · -- Case 1.1.1: `1 ∉ verts`
    have h11inpoints : (⟨1, 1⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨1, 1⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h12inpoints : (⟨1, 2⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨1, 2⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h13inpoints : (⟨1, 3⟩ : ℕ × ℕ) ∈ points := by
      rw [hallpoints (⟨1, 3⟩ : ℕ × ℕ)]
      <;> simp [hn]
      <;> norm_num
    have h51 : ∃ l ∈ lines, l.1 + l.2 = 1 := by
      have h111 := hmain (⟨1, 1⟩ : ℕ × ℕ) h11inpoints
      cases h111 with
      | inl h1111 =>
        rcases h1111 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h1112 =>
        rcases h1112 with ⟨x, hx, hx2⟩
        have h1inverts1 : (1 : ℝ) ∈ verts := by
          have h11121 : (1 : ℝ) = x := by simpa using hx2
          have h11122 : x ∈ verts := hx
          rw [← h11121] at h11122
          tauto
        contradiction
    have h52 : ∃ l ∈ lines, l.1 + l.2 = 2 := by
      have h121 := hmain (⟨1, 2⟩ : ℕ × ℕ) h12inpoints
      cases h121 with
      | inl h1211 =>
        rcases h1211 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h1212 =>
        rcases h1212 with ⟨x, hx, hx2⟩
        have h1inverts1 : (1 : ℝ) ∈ verts := by
          have h12121 : (1 : ℝ) = x := by simpa using hx2
          have h12122 : x ∈ verts := hx
          rw [← h12121] at h12122
          tauto
        contradiction
    have h53 : ∃ l ∈ lines, l.1 + l.2 = 3 := by
      have h131 := hmain (⟨1, 3⟩ : ℕ × ℕ) h13inpoints
      cases h131 with
      | inl h1311 =>
        rcases h1311 with ⟨l, hl, h_eq⟩
        refine ⟨l, hl,?_⟩
        norm_num at h_eq ⊢
        <;> linarith
      | inr h1312 =>
        rcases h1312 with ⟨x, hx, hx2⟩
        have h1inverts1 : (1 : ℝ) ∈ verts := by
          have h13121 : (1 : ℝ) = x := by simpa using hx2
          have h13122 : x ∈ verts := hx
          rw [← h13121] at h13122
          tauto
        contradiction
    rcases h51 with ⟨l1, hl1_in_lines, h1_eq1⟩
    rcases h52 with ⟨l2, hl2_in_lines, h1_eq2⟩
    rcases h53 with ⟨l3, hl3_in_lines, h1_eq3⟩
    have h_l1_ne_l2 : l1 ≠ l2 := by
      intro h
      have h1 : l1.1 + l1.2 = 1 := h1_eq1
      have h2 : l2.1 + l2.2 = 2 := h1_eq2
      have h3 : l1 = l2 := by tauto
      simp [h3] at *
      <;> linarith
    have h_l1_ne_l3 : l1 ≠ l3 := by
      intro h
      have h1 : l1.1 + l1.2 = 1 := h1_eq1
      have h2 : l3.1 + l3.2 = 3 := h1_eq3
      have h3 : l1 = l3 := by tauto
      simp [h3] at *
      <;> linarith
    have h_l2_ne_l3 : l2 ≠ l3 := by
      intro h
      have h1 : l2.1 + l2.2 = 2 := h1_eq2
      have h2 : l3.1 + l3.2 = 3 := h1_eq3
      have h3 : l2 = l3 := by tauto
      simp [h3] at *
      <;> linarith
    have h125 : ({l1, l2, l3} : Finset (ℝ × ℝ)) ⊆ lines := by
      intro x hx
      simp at hx
      rcases hx with (rfl | rfl | rfl)
      · exact hl1_in_lines
      · exact hl2_in_lines
      · exact hl3_in_lines
    have h126 : ({l1, l2, l3} : Finset (ℝ × ℝ)).card = 3 := by
      have h1 : l1 ≠ l2 := h_l1_ne_l2
      have h2 : l1 ≠ l3 := h_l1_ne_l3
      have h3 : l2 ≠ l3 := h_l2_ne_l3
      simp [Finset.card_insert_of_not_mem, Finset.mem_singleton, h1, h2, h3]
      <;> aesop
    have h4111 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by
      have h4112 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := h411
      have h4113 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) = lines := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_filter]
        constructor
        · intro h
          tauto
        · intro hx
          have h4114 := h4112 x hx
          tauto
      have h4114 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by
        rw [h4113]
        <;> rfl
      have h4115 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by
        have h4116 : Disjoint (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) := by
          simp [Finset.disjoint_left]
          <;> aesop
        have h4117 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) = lines := by
          ext x
          simp [or_iff_not_imp_left]
          <;> by_cases h121 : x.1 ≠ 0 <;> by_cases h122 : x.1 ≠ -1 <;> simp_all <;> aesop
        have h4118 : ((lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1))).card = (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          rw [Finset.card_union_of_disjoint h4116]
        have h4119 : lines.card = (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          rw [h4117] at h4118
          linarith
        have h4120 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by linarith
        have h4121 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by linarith
        exact h4121
      exact h4115
    have h4112 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := h411
    have h4113 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) = lines := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter]
      constructor
      · intro h
        tauto
      · intro hx
        have h4114 := h4112 x hx
        tauto
    have h4114 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = lines.card := by
      rw [h4113]
      <;> rfl
    have h_lines_card : lines.card = 2 := by linarith
    have h127 : ({l1, l2, l3} : Finset (ℝ × ℝ)).card ≤ lines.card := Finset.card_le_card h125
    linarith

lemma round1_case2 (n : ℕ)
  (k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n = 3)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (h421 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1)
  (h422 : verts.card = 0):
  False := by
  have h_lines_card : lines.card = 3 := by
    have h4221 : verts.card = 0 := h422
    have h4222 : lines.card + verts.card = n := hcard
    have h4223 : n = 3 := hn
    linarith
  have h_verts_empty : verts = ∅ := by
    have h : verts.card = 0 := h422
    have h' : verts = ∅ := by
      exact Finset.card_eq_zero.mp h
    exact h'
  have h11inpoints : (⟨1, 1⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨1, 1⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h12inpoints : (⟨1, 2⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨1, 2⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h13inpoints : (⟨1, 3⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨1, 3⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h21inpoints : (⟨2, 1⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨2, 1⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h22inpoints : (⟨2, 2⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨2, 2⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h31inpoints : (⟨3, 1⟩ : ℕ × ℕ) ∈ points := by
    rw [hallpoints (⟨3, 1⟩ : ℕ × ℕ)]
    <;> simp [hn]
    <;> norm_num
  have h51 : ∃ l ∈ lines, l.1 + l.2 = 1 := by
    have h111 := hmain (⟨1, 1⟩ : ℕ × ℕ) h11inpoints
    cases h111 with
    | inl h1111 =>
      rcases h1111 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h1112 =>
      rcases h1112 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  have h52 : ∃ l ∈ lines, l.1 + l.2 = 2 := by
    have h121 := hmain (⟨1, 2⟩ : ℕ × ℕ) h12inpoints
    cases h121 with
    | inl h1211 =>
      rcases h1211 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h1212 =>
      rcases h1212 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  have h53 : ∃ l ∈ lines, l.1 + l.2 = 3 := by
    have h131 := hmain (⟨1, 3⟩ : ℕ × ℕ) h13inpoints
    cases h131 with
    | inl h1311 =>
      rcases h1311 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h1312 =>
      rcases h1312 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  rcases h51 with ⟨l1, hl1_in_lines, h1_eq1⟩
  rcases h52 with ⟨l2, hl2_in_lines, h1_eq2⟩
  rcases h53 with ⟨l3, hl3_in_lines, h1_eq3⟩
  have h_l1_ne_l2 : l1 ≠ l2 := by
    intro h
    have h1 : l1.1 + l1.2 = 1 := h1_eq1
    have h2 : l2.1 + l2.2 = 2 := h1_eq2
    have h3 : l1 = l2 := by tauto
    simp [h3] at *
    <;> linarith
  have h_l1_ne_l3 : l1 ≠ l3 := by
    intro h
    have h1 : l1.1 + l1.2 = 1 := h1_eq1
    have h2 : l3.1 + l3.2 = 3 := h1_eq3
    have h3 : l1 = l3 := by tauto
    simp [h3] at *
    <;> linarith
  have h_l2_ne_l3 : l2 ≠ l3 := by
    intro h
    have h1 : l2.1 + l2.2 = 2 := h1_eq2
    have h2 : l3.1 + l3.2 = 3 := h1_eq3
    have h3 : l2 = l3 := by tauto
    simp [h3] at *
    <;> linarith
  have h125 : ({l1, l2, l3} : Finset (ℝ × ℝ)) ⊆ lines := by
    intro x hx
    simp at hx
    rcases hx with (rfl | rfl | rfl)
    · exact hl1_in_lines
    · exact hl2_in_lines
    · exact hl3_in_lines
  have h126 : ({l1, l2, l3} : Finset (ℝ × ℝ)).card = 3 := by
    have h1 : l1 ≠ l2 := h_l1_ne_l2
    have h2 : l1 ≠ l3 := h_l1_ne_l3
    have h3 : l2 ≠ l3 := h_l2_ne_l3
    simp [Finset.card_insert_of_not_mem, Finset.mem_singleton, h1, h2, h3]
    <;> aesop
  have h123 : ({l1, l2, l3} : Finset (ℝ × ℝ)) = lines := by
    apply Finset.eq_of_subset_of_card_le h125
    <;> simp [h126, h_lines_card]
    <;> aesop
  have h54 : ∃ l4 ∈ lines, l4.1 * 2 + l4.2 = 1 := by
    have h211 := hmain (⟨2, 1⟩ : ℕ × ℕ) h21inpoints
    cases h211 with
    | inl h2111 =>
      rcases h2111 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h2112 =>
      rcases h2112 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  have h55 : ∃ l5 ∈ lines, l5.1 * 2 + l5.2 = 2 := by
    have h221 := hmain (⟨2, 2⟩ : ℕ × ℕ) h22inpoints
    cases h221 with
    | inl h2211 =>
      rcases h2211 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h2212 =>
      rcases h2212 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  have h56 : ∃ l6 ∈ lines, l6.1 * 3 + l6.2 = 1 := by
    have h311 := hmain (⟨3, 1⟩ : ℕ × ℕ) h31inpoints
    cases h311 with
    | inl h3111 =>
      rcases h3111 with ⟨l, hl, h_eq⟩
      refine ⟨l, hl,?_⟩
      norm_num at h_eq ⊢
      <;> linarith
    | inr h3112 =>
      rcases h3112 with ⟨x, hx, hx2⟩
      rw [h_verts_empty] at hx
      simp at hx
      <;> aesop
  rcases h54 with ⟨l4, hl4_in_lines, h4_eq⟩
  rcases h55 with ⟨l5, hl5_in_lines, h5_eq⟩
  rcases h56 with ⟨l6, hl6_in_lines, h6_eq⟩
  have h_l4_in_set : l4 ∈ ({l1, l2, l3} : Finset (ℝ × ℝ)) := by
    rw [h123]
    exact hl4_in_lines
  have h_l5_in_set : l5 ∈ ({l1, l2, l3} : Finset (ℝ × ℝ)) := by
    rw [h123]
    exact hl5_in_lines
  have h_l6_in_set : l6 ∈ ({l1, l2, l3} : Finset (ℝ × ℝ)) := by
    rw [h123]
    exact hl6_in_lines
  have h_l4_eq : l4 = l1 ∨ l4 = l2 ∨ l4 = l3 := by
    simp at h_l4_in_set
    tauto
  have h_l5_eq : l5 = l1 ∨ l5 = l2 ∨ l5 = l3 := by
    simp at h_l5_in_set
    tauto
  have h_l6_eq : l6 = l1 ∨ l6 = l2 ∨ l6 = l3 := by
    simp at h_l6_in_set
    tauto
  have h4211 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 := h421
  rcases h_l4_eq with (h_l4_eq1 | h_l4_eq2 | h_l4_eq3)
  · -- Case l4 = l1
    have h_l4_eq11 : l4 = l1 := h_l4_eq1
    have h4_eq11 : l1.1 * 2 + l1.2 = 1 := by
      rw [h_l4_eq11] at h4_eq
      exact h4_eq
    have h1_eq11 : l1.1 + l1.2 = 1 := h1_eq1
    have h_l1_1_eq_0 : l1.1 = 0 := by linarith
    rcases h_l5_eq with (h_l5_eq1 | h_l5_eq2 | h_l5_eq3)
    · -- Case l5 = l1
      have h_l5_eq11 : l5 = l1 := h_l5_eq1
      have h5_eq11 : l1.1 * 2 + l1.2 = 2 := by
        rw [h_l5_eq11] at h5_eq
        exact h5_eq
      have h1_eq111 : l1.1 + l1.2 = 1 := h1_eq1
      have h_l1_1_eq_01 : l1.1 = 0 := by linarith
      have h12 : l1.2 = 1 := by linarith
      have h13 : l1.1 * 2 + l1.2 = 1 := by linarith
      linarith
    · -- Case l5 = l2
      have h_l5_eq22 : l5 = l2 := h_l5_eq2
      have h5_eq22 : l2.1 * 2 + l2.2 = 2 := by
        rw [h_l5_eq22] at h5_eq
        exact h5_eq
      have h1_eq22 : l2.1 + l2.2 = 2 := h1_eq2
      have h_l2_1_eq_0 : l2.1 = 0 := by linarith
      have h_l1_in_L : l1 ∈ lines := hl1_in_lines
      have h_l2_in_L : l2 ∈ lines := hl2_in_lines
      have h_l1_1_eq_01 : l1.1 = 0 := h_l1_1_eq_0
      have h_l2_1_eq_01 : l2.1 = 0 := h_l2_1_eq_0
      have h_l1_in_filter : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l2_in_filter : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l1_ne_l21 : l1 ≠ l2 := h_l1_ne_l2
      have h14 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card ≥ 2 := by
        have h141 : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l1_in_filter
        have h142 : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l2_in_filter
        have h143 : l1 ≠ l2 := h_l1_ne_l21
        have h : ({l1, l2} : Finset (ℝ × ℝ)) ⊆ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          intro x hx
          simp at hx
          rcases hx with (rfl | rfl)
          · exact h141
          · exact h142
        have h144 : ({l1, l2} : Finset (ℝ × ℝ)).card = 2 := by
          simp [Finset.card_pair, h143]
          <;> aesop
        have h145 : ({l1, l2} : Finset (ℝ × ℝ)).card ≤ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          apply Finset.card_le_card h
        linarith
      linarith
    · -- Case l5 = l3
      have h_l5_eq33 : l5 = l3 := h_l5_eq3
      have h5_eq33 : l3.1 * 2 + l3.2 = 2 := by
        rw [h_l5_eq33] at h5_eq
        exact h5_eq
      have h1_eq33 : l3.1 + l3.2 = 3 := h1_eq3
      have h_l3_1_eq_neg1 : l3.1 = -1 := by linarith
      have h_l1_in_L : l1 ∈ lines := hl1_in_lines
      have h_l3_in_L : l3 ∈ lines := hl3_in_lines
      have h_l1_1_eq_01 : l1.1 = 0 := h_l1_1_eq_0
      have h_l3_1_eq_neg11 : l3.1 = -1 := h_l3_1_eq_neg1
      have h_l1_in_filter : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l3_in_filter : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l1_ne_l31 : l1 ≠ l3 := h_l1_ne_l3
      have h14 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card ≥ 2 := by
        have h141 : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l1_in_filter
        have h142 : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l3_in_filter
        have h143 : l1 ≠ l3 := h_l1_ne_l31
        have h : ({l1, l3} : Finset (ℝ × ℝ)) ⊆ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          intro x hx
          simp at hx
          rcases hx with (rfl | rfl)
          · exact h141
          · exact h142
        have h144 : ({l1, l3} : Finset (ℝ × ℝ)).card = 2 := by
          simp [Finset.card_pair, h143]
          <;> aesop
        have h145 : ({l1, l3} : Finset (ℝ × ℝ)).card ≤ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          apply Finset.card_le_card h
        linarith
      linarith
  · -- Case l4 = l2
    have h_l4_eq22 : l4 = l2 := h_l4_eq2
    have h4_eq22 : l2.1 * 2 + l2.2 = 1 := by
      rw [h_l4_eq22] at h4_eq
      exact h4_eq
    have h1_eq22 : l2.1 + l2.2 = 2 := h1_eq2
    have h_l2_1_eq_neg1 : l2.1 = -1 := by linarith
    rcases h_l5_eq with (h_l5_eq1 | h_l5_eq2 | h_l5_eq3)
    · -- Case l5 = l1
      have h_l5_eq11 : l5 = l1 := h_l5_eq1
      have h5_eq11 : l1.1 * 2 + l1.2 = 2 := by
        rw [h_l5_eq11] at h5_eq
        exact h5_eq
      have h1_eq11 : l1.1 + l1.2 = 1 := h1_eq1
      have h_l1_1_eq_1 : l1.1 = 1 := by linarith
      rcases h_l6_eq with (h_l6_eq1 | h_l6_eq2 | h_l6_eq3)
      · -- Case l6 = l1
        have h_l6_eq11 : l6 = l1 := h_l6_eq1
        have h6_eq11 : l1.1 * 3 + l1.2 = 1 := by
          rw [h_l6_eq11] at h6_eq
          exact h6_eq
        have h1_eq111 : l1.1 + l1.2 = 1 := h1_eq1
        have h_l1_1_eq_11 : l1.1 = 1 := h_l1_1_eq_1
        linarith
      · -- Case l6 = l2
        have h_l6_eq22 : l6 = l2 := h_l6_eq2
        have h6_eq22 : l2.1 * 3 + l2.2 = 1 := by
          rw [h_l6_eq22] at h6_eq
          exact h6_eq
        have h1_eq222 : l2.1 + l2.2 = 2 := h1_eq2
        have h_l2_1_eq_neg11 : l2.1 = -1 := h_l2_1_eq_neg1
        linarith
      · -- Case l6 = l3
        have h_l6_eq33 : l6 = l3 := h_l6_eq3
        have h6_eq33 : l3.1 * 3 + l3.2 = 1 := by
          rw [h_l6_eq33] at h6_eq
          exact h6_eq
        have h_l3_1_eq_neg1 : l3.1 = -1 := by linarith
        have h_l3_2_eq_4 : l3.2 = 4 := by linarith
        have h_l2_in_filter : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          simp [Finset.mem_filter]
          <;> aesop
        -- And l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)
        have h_l3_in_filter : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          simp [Finset.mem_filter]
          <;> aesop
        -- l2 ≠ l3 (h_l2_ne_l3)
        have h14 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card ≥ 2 := by
          have h141 : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l2_in_filter
          have h142 : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l3_in_filter
          have h143 : l2 ≠ l3 := h_l2_ne_l3
          have h : ({l2, l3} : Finset (ℝ × ℝ)) ⊆ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
            intro x hx
            simp at hx
            rcases hx with (rfl | rfl)
            · exact h141
            · exact h142
          have h144 : ({l2, l3} : Finset (ℝ × ℝ)).card = 2 := by
            simp [Finset.card_pair, h143]
            <;> aesop
          have h145 : ({l2, l3} : Finset (ℝ × ℝ)).card ≤ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
            apply Finset.card_le_card h
          linarith
        linarith
    · -- Case l5 = l2
      have h_l5_eq22 : l5 = l2 := h_l5_eq2
      have h5_eq22 : l2.1 * 2 + l2.2 = 2 := by
        rw [h_l5_eq22] at h5_eq
        exact h5_eq
      have h1_eq222 : l2.1 + l2.2 = 2 := h1_eq2
      have h_l2_1_eq_neg11 : l2.1 = -1 := by linarith
      have h_l2_2_eq_3 : l2.2 = 3 := by linarith
      linarith
    · -- Case l5 = l3
      have h_l5_eq33 : l5 = l3 := h_l5_eq3
      have h5_eq33 : l3.1 * 2 + l3.2 = 2 := by
        rw [h_l5_eq33] at h5_eq
        exact h5_eq
      have h1_eq333 : l3.1 + l3.2 = 3 := h1_eq3
      have h_l3_1_eq_neg1 : l3.1 = -1 := by linarith
      have h_l2_in_L : l2 ∈ lines := hl2_in_lines
      have h_l2_1_eq_neg11 : l2.1 = -1 := h_l2_1_eq_neg1
      have h_l2_in_filter : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l3_in_L : l3 ∈ lines := hl3_in_lines
      have h_l3_1_eq_neg11 : l3.1 = -1 := h_l3_1_eq_neg1
      have h_l3_in_filter : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l2_ne_l31 : l2 ≠ l3 := by
        intro h
        have h1 : l2.1 + l2.2 = 2 := h1_eq2
        have h2 : l3.1 + l3.2 = 3 := h1_eq3
        have h3 : l2 = l3 := by tauto
        simp [h3] at *
        <;> linarith
      have h14 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card ≥ 2 := by
        have h141 : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l2_in_filter
        have h142 : l3 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l3_in_filter
        have h143 : l2 ≠ l3 := h_l2_ne_l31
        have h : ({l2, l3} : Finset (ℝ × ℝ)) ⊆ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          intro x hx
          simp at hx
          rcases hx with (rfl | rfl)
          · exact h141
          · exact h142
        have h144 : ({l2, l3} : Finset (ℝ × ℝ)).card = 2 := by
          simp [Finset.card_pair, h143]
          <;> aesop
        have h145 : ({l2, l3} : Finset (ℝ × ℝ)).card ≤ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
          apply Finset.card_le_card h
        linarith
      linarith
  · -- Case l4 = l3
    have h_l4_eq33 : l4 = l3 := h_l4_eq3
    have h4_eq33 : l3.1 * 2 + l3.2 = 1 := by
      rw [h_l4_eq33] at h4_eq
      exact h4_eq
    have h1_eq33 : l3.1 + l3.2 = 3 := h1_eq3
    have h_l3_1_eq_neg2 : l3.1 = -2 := by linarith
    have h_l3_2_eq_5 : l3.2 = 5 := by linarith
    have h_l5_ne_l3 : l5 ≠ l3 := by
      by_contra h_l5_eq_l3
      have h5_eq2 : l5.1 * 2 + l5.2 = 2 := h5_eq
      have h5_eq3 : l5 = l3 := h_l5_eq_l3
      rw [h5_eq3] at h5_eq2
      norm_num [h_l3_1_eq_neg2, h_l3_2_eq_5] at h5_eq2
      <;> linarith
    have h_l5_eq_l1_or_l5_eq_l2 : l5 = l1 ∨ l5 = l2 := by
      rcases h_l5_eq with (h51 | h52 | h53)
      · exact Or.inl h51
      · exact Or.inr h52
      · contradiction
    -- Now we have two cases: l5 = l1 or l5 = l2
    rcases h_l5_eq_l1_or_l5_eq_l2 with (h_l5_eq_l1 | h_l5_eq_l2)
    · -- Case l5 = l1
      have h5_eq2 : l5.1 * 2 + l5.2 = 2 := h5_eq
      rw [h_l5_eq_l1] at h5_eq2
      have h_l6_ne_l3 : l6 ≠ l3 := by
        by_contra h_l6_eq_l3
        have h6_eq2 : l6.1 * 3 + l6.2 = 1 := h6_eq
        rw [h_l6_eq_l3] at h6_eq2
        norm_num [h_l3_1_eq_neg2, h_l3_2_eq_5] at h6_eq2
        <;> linarith
      have h_l6_eq_l1_or_l6_eq_l2 : l6 = l1 ∨ l6 = l2 := by
        rcases h_l6_eq with (h61 | h62 | h63)
        · exact Or.inl h61
        · exact Or.inr h62
        · contradiction
      -- Now we have l6 = l1 ∨ l6 = l2
      rcases h_l6_eq_l1_or_l6_eq_l2 with (h_l6_eq_l1 | h_l6_eq_l2)
      · -- Subcase l6 = l1
        -- We have h6_eq: l6.1 * 3 + l6.2 = 1, and l6 = l1, so l1.1 * 3 + l1.2 = 1
        have h6_eq1 : l1.1 * 3 + l1.2 = 1 := by
          rw [h_l6_eq_l1] at h6_eq
          exact h6_eq
        have h_l1_1_eq_neg1 : l1.1 = -1 := by linarith
        -- And from l1.1 * 2 + l1.2 = 2, we have -1 * 2 + l1.2 = 2 → -2 + l1.2 = 2 → l1.2 = 4
        have h_l1_2_eq_4 : l1.2 = 4 := by linarith
        have h_l1_in_filter : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          simp [Finset.mem_filter]
          <;> aesop
        have h1 : l1.1 + l1.2 = 1 := h1_eq1
        have h2 : l1.1 = -1 := h_l1_1_eq_neg1
        have h3 : l1.2 = 4 := h_l1_2_eq_4
        norm_num [h2, h3] at h1
        <;> linarith
      · -- Subcase l6 = l2
        -- We have h6_eq: l6.1 * 3 + l6.2 = 1, and l6 = l2, so l2.1 * 3 + l2.2 = 1
        have h6_eq2 : l2.1 * 3 + l2.2 = 1 := by
          rw [h_l6_eq_l2] at h6_eq
          exact h6_eq
        have h_l2_1_eq_neg1_2 : l2.1 = -1 / 2 := by linarith
        have h_l1_1_eq_1 : l1.1 = 1 := by linarith
        -- And from l1.1 + l1.2 = 1, we have 1 + l1.2 = 1, so l1.2 = 0
        have h_l1_2_eq_0 : l1.2 = 0 := by linarith
        have h42111 : ∃ l7, l7 ∈ lines.filter (fun l ↦ l.1 = 0 ∨ l.1 = -1) := by
          have h1 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 := h4211
          have h2 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            by_contra h
            have h3 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) = ∅ := by simpa using h
            have h4 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := by
              rw [h3]
              simp
            linarith
          exact h2
        rcases h42111 with ⟨l7, hl7_in_filter⟩
        have hl7_in_lines : l7 ∈ lines := (Finset.mem_filter.mp hl7_in_filter).1
        have hl7_prop : l7.1 = 0 ∨ l7.1 = -1 := (Finset.mem_filter.mp hl7_in_filter).2
        -- l7 ∈ lines, and lines = {l1, l2, l3}, so l7 = l1 ∨ l7 = l2 ∨ l7 = l3
        have h_l7_eq : l7 = l1 ∨ l7 = l2 ∨ l7 = l3 := by
          have h1231 : l7 ∈ ({l1, l2, l3} : Finset (ℝ × ℝ)) := by
            rw [h123]
            exact hl7_in_lines
          simp at h1231
          tauto
        rcases h_l7_eq with (h_l7_eq1 | h_l7_eq2 | h_l7_eq3)
        · -- Case l7 = l1
          have h_l7_eq11 : l7 = l1 := h_l7_eq1
          have h1 : l7.1 = 0 ∨ l7.1 = -1 := hl7_prop
          have h2 : l7.1 = l1.1 := by rw [h_l7_eq11]
          have h3 : l1.1 = 1 := h_l1_1_eq_1
          have h4 : l7.1 = 1 := by linarith
          rcases h1 with (h11 | h12)
          · -- l7.1 = 0
            linarith
          · -- l7.1 = -1
            linarith
        · -- Case l7 = l2
          have h_l7_eq22 : l7 = l2 := h_l7_eq2
          have h1 : l7.1 = 0 ∨ l7.1 = -1 := hl7_prop
          have h2 : l7.1 = l2.1 := by rw [h_l7_eq22]
          have h3 : l2.1 = -1 / 2 := h_l2_1_eq_neg1_2
          have h4 : l7.1 = -1 / 2 := by linarith
          rcases h1 with (h11 | h12)
          · -- l7.1 = 0
            linarith
          · -- l7.1 = -1
            linarith
        · -- Case l7 = l3
          have h_l7_eq33 : l7 = l3 := h_l7_eq3
          have h1 : l7.1 = 0 ∨ l7.1 = -1 := hl7_prop
          have h2 : l7.1 = l3.1 := by rw [h_l7_eq33]
          have h3 : l3.1 = -2 := h_l3_1_eq_neg2
          have h4 : l7.1 = -2 := by linarith
          rcases h1 with (h11 | h12)
          · -- l7.1 = 0
            linarith
          · -- l7.1 = -1
            linarith
    · -- Case l5 = l2
      have h5_eq22 : l2.1 * 2 + l2.2 = 2 := by
        rw [h_l5_eq_l2] at h5_eq
        exact h5_eq
      have h_l2_1_eq_0 : l2.1 = 0 := by linarith
      have h_l2_in_filter : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp [Finset.mem_filter]
        <;> aesop
      have h_l6_ne_l3 : l6 ≠ l3 := by
        by_contra h_l6_eq_l3
        have h6_eq2 : l6.1 * 3 + l6.2 = 1 := h6_eq
        rw [h_l6_eq_l3] at h6_eq2
        norm_num [h_l3_1_eq_neg2, h_l3_2_eq_5] at h6_eq2
        <;> linarith
      have h_l6_eq_l1_or_l6_eq_l2 : l6 = l1 ∨ l6 = l2 := by
        rcases h_l6_eq with (h61 | h62 | h63)
        · exact Or.inl h61
        · exact Or.inr h62
        · contradiction
      -- Case l6 = l1 or l6 = l2
      rcases h_l6_eq_l1_or_l6_eq_l2 with (h_l6_eq_l1 | h_l6_eq_l2)
      · -- Case l6 = l1
        -- We have h6_eq: l6.1 * 3 + l6.2 = 1, and l6 = l1, so l1.1 * 3 + l1.2 = 1
        have h6_eq1 : l1.1 * 3 + l1.2 = 1 := by
          rw [h_l6_eq_l1] at h6_eq
          exact h6_eq
        have h_l1_1_eq_0 : l1.1 = 0 := by linarith
        have h_l1_in_filter : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
          simp [Finset.mem_filter]
          <;> aesop
        have h14 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card ≥ 2 := by
          have h141 : l1 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l1_in_filter
          have h142 : l2 ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := h_l2_in_filter
          have h143 : l1 ≠ l2 := h_l1_ne_l2
          have h : ({l1, l2} : Finset (ℝ × ℝ)) ⊆ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
            intro x hx
            simp at hx
            rcases hx with (rfl | rfl)
            · exact h141
            · exact h142
          have h144 : ({l1, l2} : Finset (ℝ × ℝ)).card = 2 := by
            simp [Finset.card_pair, h143]
            <;> aesop
          have h145 : ({l1, l2} : Finset (ℝ × ℝ)).card ≤ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
            apply Finset.card_le_card h
          linarith
        linarith
      · -- Case l6 = l2
        -- We have h6_eq: l6.1 * 3 + l6.2 = 1, and l6 = l2, so l2.1 * 3 + l2.2 = 1
        have h6_eq2 : l2.1 * 3 + l2.2 = 1 := by
          rw [h_l6_eq_l2] at h6_eq
          exact h6_eq
        have h_l2_2_eq_1 : l2.2 = 1 := by linarith
        have h1 : l2.1 + l2.2 = 2 := h1_eq2
        norm_num [h_l2_1_eq_0, h_l2_2_eq_1] at h1
        <;> linarith

theorem k2_impossible_for_n3 (n : ℕ) (k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : n = 3) (hk : k = 2)
  (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (hk_sunny : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) :
  False := by

  have h1 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = lines.card := by
    have h11 : Disjoint (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) := by
      simp [Finset.disjoint_left]
      <;> aesop
    have h12 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)) = lines := by
      ext x
      simp [or_iff_not_imp_left]
      <;> by_cases h121 : x.1 ≠ 0 <;> by_cases h122 : x.1 ≠ -1 <;> simp_all <;> aesop
    have h13 : ((lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1))).card = (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card + (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
      rw [Finset.card_union_of_disjoint h11]
    have h14 : lines.card = ((lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)) ∪ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1))).card := by
      rw [h12]
      <;> rfl
    linarith

  have h3 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card + verts.card = 1 := by
    have h2 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := hk_sunny
    have h21 : k = 2 := hk
    have h22 : (lines.filter (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)).card = 2 := by linarith
    have h23 : lines.card + verts.card = n := hcard
    have h24 : n = 3 := hn
    linarith

  have h4 : ((lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 ∧ verts.card = 1) ∨ ((lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 ∧ verts.card = 0) := by omega

  rcases h4 with (h41 | h42)
  · -- Case 1: (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 ∧ verts.card = 1
    have h4111 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 := h41.1
    have h412 : verts.card = 1 := h41.2
    have h411 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := by
      intro l hl
      by_contra h22
      have h23 : l.1 = 0 ∨ l.1 = -1 := by tauto
      have h24 : l ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := by
        simp only [Finset.mem_filter]
        exact ⟨hl, h23⟩
      have h25 : 0 < (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := by
        apply Finset.card_pos.mpr
        exact ⟨l, h24⟩
      linarith
    exact round1_case1 n k verts lines points hn hcard hallpoints hmain h411 h412
  · -- Case 2: (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 ∧ verts.card = 0
    have h421 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 := h42.1
    have h422 : verts.card = 0 := h42.2
    exact round1_case2 n k verts lines points hn hcard hallpoints hmain h421 h422



lemma round1_h1 (k : ℕ)
  (lines : Finset (ℝ × ℝ))
  (verts : Finset ℝ)
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = 3)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  k ≤ 3 := by
  have h11 := k_le_3_for_n_le_4 3 k verts lines points (by norm_num) hcard hallpoints hmain hk (by norm_num)
  linarith

lemma round1_h2 (k : ℕ)
  (lines : Finset (ℝ × ℝ))
  (verts : Finset ℝ)
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = 3)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  k ≠ 2 := by
  by_contra h21
  have h_contra : False := k2_impossible_for_n3 3 k verts lines points (by norm_num) h21 hcard hallpoints hmain hk
  contradiction

theorem imo2025_p1_prop_n_eq_3_k_eq_0_1_3 (k : ℕ) (lines : Finset (ℝ × ℝ)) (verts : Finset ℝ) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = 3) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) :
  k = 0 ∨ k = 1 ∨ k = 3 := by

    have h1 : k ≤ 3 := by
      exact round1_h1 k lines verts points hcard hallpoints hmain hk
    have h2 : k ≠ 2 := by
      exact round1_h2 k lines verts points hcard hallpoints hmain hk
    omega

lemma inductive_step_if_contains_horizontal_line_h_sum_card_h1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl_in_lines : l ∈ lines):
  1 ≤ lines.card := by
  have h11 : lines.Nonempty := ⟨l, hl_in_lines⟩
  have h12 : 0 < lines.card := Finset.card_pos.mpr h11
  linarith

lemma inductive_step_if_contains_horizontal_line_h_sum_card_h2 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl_in_lines : l ∈ lines):
  (lines.erase l).card = lines.card - 1 := by
  rw [Finset.card_erase_of_mem hl_in_lines]
  <;> rfl

lemma inductive_step_if_contains_horizontal_line_h_sum_card_h3 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = n)
  (l : ℝ × ℝ)
  (h1 : 1 ≤ lines.card):
  verts.card + (lines.card - 1) = n - 1 := by
  have h4 : lines.card + verts.card = n := hcard
  have h5 : 1 ≤ lines.card := h1
  omega

lemma inductive_step_if_contains_horizontal_line_h_sum_card_h4 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (h2 : (lines.erase l).card = lines.card - 1)
  (h3 : verts.card + (lines.card - 1) = n - 1):
  verts.card + (lines.erase l).card = n - 1 := by
  rw [h2]
  exact h3

lemma inductive_step_if_contains_horizontal_line_h_sum_card (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = n)
  (l : ℝ × ℝ)
  (hl_in_lines : l ∈ lines)
  (hn : n ≥ 4):
  verts.card + (lines.erase l).card = n - 1 := by

  have h1 : 1 ≤ lines.card := by
    exact inductive_step_if_contains_horizontal_line_h_sum_card_h1 n k verts lines points l hl_in_lines
  have h2 : (lines.erase l).card = lines.card - 1 := by
    exact inductive_step_if_contains_horizontal_line_h_sum_card_h2 n k verts lines points l hl_in_lines
  have h3 : verts.card + (lines.card - 1) = n - 1 := by
    exact inductive_step_if_contains_horizontal_line_h_sum_card_h3 n k verts lines points hcard l h1
  have h4 : verts.card + (lines.erase l).card = n - 1 := by
    exact inductive_step_if_contains_horizontal_line_h_sum_card_h4 n k verts lines points l h2 h3
  exact h4

lemma translation_equivalence_y_axis_h_main (n k_local : ℕ)
  (hn : n > 3)
  (H : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h1 : verts.card + lines.card = n - 1)
  (h2 : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1)
  (h3 : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (h4 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k_local):
  k_local = 0 ∨ k_local = 1 ∨ k_local = 3 := by
  have h_inj : Function.Injective (fun (p : ℝ × ℝ) => (p.1, p.2 - 1)) := by
    intro p q h
    simp_all [Prod.ext_iff]
    <;>
    (try constructor <;> linarith) <;>
    aesop
  set f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 - 1) with hf
  have h_inj_f : Function.Injective f := h_inj
  set lines' := Finset.image f lines with hlines'_def
  set verts' := verts with hverts'_def
  have h_card_lines' : lines'.card = lines.card := by
    rw [hlines'_def]
    apply Finset.card_image_of_injective
    exact h_inj_f
  have h_card_sum : verts'.card + lines'.card = n - 1 := by
    rw [hverts'_def, h_card_lines']
    exact h1
  have h_cond_points : ∀ (p : ℕ × ℕ), p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
    (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x) := by
    intro p hp
    have h_p1 : p.1 ≥ 1 := hp.1
    have h_p2 : p.2 ≥ 1 := hp.2.1
    have h_p3 : p.1 + p.2 ≤ n := hp.2.2
    set p' : ℕ × ℕ := (p.1, p.2 + 1) with hp'
    have h_p'_1 : p'.1 ≥ 1 := by simp [hp']
      <;> omega
    have h_p'_2 : p'.2 ≥ 2 := by simp [hp']
      <;> omega
    have h_p'_3 : p'.1 + p'.2 ≤ n + 1 := by
      simp [hp']
      <;> omega
    have h_p'_in_points : p' ∈ points := by
      rw [h2]
      <;> aesop
    have h_h3_p' : (∃ l ∈ lines, l.1 * p'.1 + l.2 = p'.2) ∨ (∃ x ∈ verts, p'.1 = x) := h3 p' h_p'_in_points
    cases h_h3_p' with
    | inl h_h3_p'_1 =>
      rcases h_h3_p'_1 with ⟨l, hl_in_lines, h_eq⟩
      have h_l : l ∈ lines := hl_in_lines
      have h_eq' : l.1 * (p'.1 : ℝ) + l.2 = (p'.2 : ℝ) := by simpa using h_eq
      have h_eq_p1 : (p'.1 : ℝ) = (p.1 : ℝ) := by
        simp [hp']
        <;> norm_cast
        <;> aesop
      have h_eq_p2 : (p'.2 : ℝ) = (p.2 : ℝ) + 1 := by
        simp [hp']
        <;> norm_cast
        <;> aesop
      have h_eq_l : l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ) + 1 := by
        have h1 : l.1 * (p'.1 : ℝ) + l.2 = (p'.2 : ℝ) := h_eq'
        rw [h_eq_p1] at h1
        rw [h_eq_p2] at h1
        linarith
      set l' := f l with hl'
      have h_l'_in_lines' : l' ∈ lines' := by
        rw [hlines'_def]
        simp [hl']
        <;> aesop
      have h_l'_1 : l'.1 = l.1 := by
        simp [hl', f]
        <;> aesop
      have h_l'_2 : l'.2 = l.2 - 1 := by
        simp [hl', f]
        <;> aesop
      have h_main_eq : l'.1 * (p.1 : ℝ) + l'.2 = (p.2 : ℝ) := by
        rw [h_l'_1, h_l'_2]
        linarith
      exact Or.inl ⟨l', h_l'_in_lines', h_main_eq⟩
    | inr h_h3_p'_2 =>
      rcases h_h3_p'_2 with ⟨x, hx_in_verts, h_eq⟩
      have h_eq_p1 : p'.1 = p.1 := by
        simp [hp']
        <;> aesop
      have h_eq' : ∃ x ∈ verts, (p.1 : ℝ) = x := by
        refine' ⟨x, hx_in_verts, _⟩
        have h1 : p'.1 = p.1 := h_eq_p1
        have h2 : (p'.1 : ℝ) = x := by simpa using h_eq
        have h3 : (p.1 : ℝ) = x := by
          have h4 : (p'.1 : ℝ) = (p.1 : ℝ) := by
            norm_cast
            <;> aesop
          linarith
        linarith
      have h_verts'_eq : ∃ x ∈ verts', (p.1 : ℝ) = x := by
        simpa [hverts'_def] using h_eq'
      exact Or.inr h_verts'_eq
  have h_card_filter : ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k_local) := by
    have h10 : ((Finset.image f lines).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
      have h11 : ∀ (x : ℝ × ℝ), (f x).1 = x.1 := by
        intro x
        simp [f]
        <;> aesop
      have h12 : (Finset.image f (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1))).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
        apply Finset.card_image_of_injective
        exact h_inj_f
      have h13 : (Finset.image f (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1))) = ((Finset.image f lines).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
        apply Finset.ext
        intro x
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine' ⟨_, _⟩
          · aesop
          · aesop
        · rintro ⟨hx, hx'⟩
          have h14 : ∃ y, y ∈ lines ∧ f y = x := by
            aesop
          rcases h14 with ⟨y, hy, h15⟩
          refine' ⟨y, _⟩
          aesop
      rw [← h13, h12]
    have h14 : lines' = Finset.image f lines := by simp [hlines'_def]
    rw [h14] at *
    simpa [h10] using h4
  have h5 : k_local = 0 ∨ k_local = 1 ∨ k_local = 3 := H k_local verts' lines' h_card_sum h_cond_points h_card_filter
  exact h5

theorem translation_equivalence_y_axis (n k : ℕ) (hn :  n > 3) :
  (∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3) →
  (∀ (k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)),
    (verts.card + lines.card = n - 1) →
    (∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) →
    (∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) →
    ((lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) →
    k = 0 ∨ k = 1 ∨ k = 3)    := by

  intro H
  intro k_local verts lines points h1 h2 h3 h4
  have h_main : k_local = 0 ∨ k_local = 1 ∨ k_local = 3 := by
    exact translation_equivalence_y_axis_h_main n k_local hn H verts lines points h1 h2 h3 h4
  exact h_main

lemma inductive_step_if_contains_horizontal_line_h_filter_card_eq_k (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines)
  (hl₀_1 : l₀.1 = 0)
  (h_filter_card : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card):
  ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  have h₁ : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := h_filter_card
  have h₂ : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := hk
  linarith

lemma inductive_step_if_contains_horizontal_line_h_card_erase (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines):
  (lines.erase l₀).card = lines.card - 1 := by
  have h11 : l₀ ∈ lines := hl₀_in_lines
  have h12 : (lines.erase l₀).card = lines.card - 1 := by
    rw [Finset.card_erase_of_mem h11]
    <;> simp
  exact h12

lemma inductive_step_if_contains_horizontal_line_h_n_gt_3 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n ≥ 4):
  n > 3 := by
  omega

lemma inductive_step_if_contains_horizontal_line_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1):
  ∃ (l₀ : ℝ × ℝ), l₀ ∈ lines ∧ l₀.1 = 0 ∧ l₀.2 = 1 := by
  obtain ⟨l₀, hl₀_in_lines, hl₀_1, hl₀_2⟩ := h_has_horizontal
  refine' ⟨l₀, hl₀_in_lines, hl₀_1, hl₀_2⟩

lemma inductive_step_if_contains_horizontal_line_h_translation_equivalence (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (hn : n ≥ 4)
  (h_n_gt_3 : n > 3):
  ∀ (k'' : ℕ) (verts'' : Finset ℝ) (lines'' : Finset (ℝ × ℝ)) (points'' : Finset (ℕ × ℕ)), (verts''.card + lines''.card = n - 1) → (∀ p, p ∈ points'' ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) → (∀ p ∈ points'', (∃ l ∈ lines'', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts'', p.1 = x)) → ((lines''.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k'') → k'' = 0 ∨ k'' = 1 ∨ k'' = 3 := by
  have h₁ : n > 3 := h_n_gt_3
  exact (translation_equivalence_y_axis n k hn) h_ih

lemma inductive_step_if_contains_horizontal_line_h_filter_eq_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl1 : l.1 = 0)
  (hl_in_lines : l ∈ lines)
  (lines' : Finset (ℝ × ℝ))
  (h_lines'_def : lines' = lines.erase l):
  ∀ (x : ℝ × ℝ), x ∈ (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) ↔ x ∈ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
  intro x
  constructor
  · -- Forward direction
    intro hx
    have h1 : x ∈ lines' := (Finset.mem_filter.mp hx).1
    have h2 : x.1 ≠ 0 ∧ x.1 ≠ -1 := (Finset.mem_filter.mp hx).2
    have h3 : x ∈ lines.erase l := by
      rw [h_lines'_def] at h1
      exact h1
    have h4 : x ∈ lines := by
      simp only [Finset.mem_erase] at h3
      tauto
    have h5 : x.1 ≠ 0 ∧ x.1 ≠ -1 := h2
    have h6 : x ∈ lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1) := by
      simp only [Finset.mem_filter]
      exact ⟨h4, h5⟩
    exact h6
  · -- Backward direction
    intro hx
    have h1 : x ∈ lines := (Finset.mem_filter.mp hx).1
    have h2 : x.1 ≠ 0 ∧ x.1 ≠ -1 := (Finset.mem_filter.mp hx).2
    have h7 : x ≠ l := by
      by_contra h
      have h8 : x = l := h
      have h9 : l.1 ≠ 0 ∧ l.1 ≠ -1 := by simpa [h8] using h2
      have h10 : l.1 = 0 := hl1
      have h11 : l.1 ≠ 0 := h9.1
      rw [h10] at h11
      <;> norm_num at h11 <;> tauto
    have h10 : x ∈ lines.erase l := by
      simp only [Finset.mem_erase]
      exact ⟨h7, h1⟩
    have h12 : x ∈ lines' := by
      rw [h_lines'_def]
      exact h10
    have h13 : x.1 ≠ 0 ∧ x.1 ≠ -1 := h2
    have h14 : x ∈ (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
      simp only [Finset.mem_filter]
      exact ⟨h12, h13⟩
    exact h14

lemma inductive_step_if_contains_horizontal_line_h_filter_eq_h_final (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (lines' : Finset (ℝ × ℝ))
  (h_main : ∀ (x : ℝ × ℝ), x ∈ (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) ↔ x ∈ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1))):
  (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
  apply Finset.ext
  intro x
  have h15 := h_main x
  tauto

lemma inductive_step_if_contains_horizontal_line_h_filter_eq (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl1 : l.1 = 0)
  (hl_in_lines : l ∈ lines)
  (lines' : Finset (ℝ × ℝ))
  (h_lines'_def : lines' = lines.erase l):
  (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by

  have h_main : ∀ (x : ℝ × ℝ), x ∈ (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) ↔ x ∈ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
    exact inductive_step_if_contains_horizontal_line_h_filter_eq_h_main n k verts lines points l hl1 hl_in_lines lines' h_lines'_def
  have h_final : (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
    exact inductive_step_if_contains_horizontal_line_h_filter_eq_h_final n k verts lines points l lines' h_main
  exact h_final

lemma inductive_step_if_contains_horizontal_line_h_main' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1):
  ∃ (l₀ : ℝ × ℝ), l₀ ∈ lines ∧ l₀.1 = 0 ∧ l₀.2 = 1 := by
  exact inductive_step_if_contains_horizontal_line_h_main n k verts lines points h_has_horizontal

lemma inductive_step_if_contains_horizontal_line_h_card_erase' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines):
  (lines.erase l₀).card = lines.card - 1 := by
  exact inductive_step_if_contains_horizontal_line_h_card_erase n k verts lines points l₀ hl₀_in_lines

lemma inductive_step_if_contains_horizontal_line_h_sum_card' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = n)
  (l : ℝ × ℝ)
  (hl_in_lines : l ∈ lines)
  (hn : n ≥ 4):
  verts.card + (lines.erase l).card = n - 1 := by
  exact inductive_step_if_contains_horizontal_line_h_sum_card n k verts lines points hcard l hl_in_lines hn

lemma inductive_step_if_contains_horizontal_line_h_filter_card_eq_k' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines)
  (hl₀_1 : l₀.1 = 0)
  (h_filter_card : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card):
  ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  exact inductive_step_if_contains_horizontal_line_h_filter_card_eq_k n k verts lines points hk l₀ hl₀_in_lines hl₀_1 h_filter_card

lemma inductive_step_if_contains_horizontal_line_h_n_gt_3' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n ≥ 4):
  n > 3 := by
  exact inductive_step_if_contains_horizontal_line_h_n_gt_3 n k verts lines points hn

lemma inductive_step_if_contains_horizontal_line_h_translation_equivalence' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (hn : n ≥ 4)
  (h_n_gt_3 : n > 3):
  ∀ (k'' : ℕ) (verts'' : Finset ℝ) (lines'' : Finset (ℝ × ℝ)) (points'' : Finset (ℕ × ℕ)), (verts''.card + lines''.card = n - 1) → (∀ p, p ∈ points'' ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) → (∀ p ∈ points'', (∃ l ∈ lines'', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts'', p.1 = x)) → ((lines''.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k'') → k'' = 0 ∨ k'' = 1 ∨ k'' = 3 := by
  exact inductive_step_if_contains_horizontal_line_h_translation_equivalence n k verts lines points h_ih hn h_n_gt_3

lemma inductive_step_if_contains_horizontal_line_h_filter_eq' (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl1 : l.1 = 0)
  (hl_in_lines : l ∈ lines)
  (lines' : Finset (ℝ × ℝ))
  (h_lines'_def : lines' = lines.erase l):
  (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
  exact inductive_step_if_contains_horizontal_line_h_filter_eq n k verts lines points l hl1 hl_in_lines lines' h_lines'_def

lemma inductive_step_if_contains_horizontal_line_h_main_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1):
  ∃ (l₀ : ℝ × ℝ), l₀ ∈ lines ∧ l₀.1 = 0 ∧ l₀.2 = 1 := by
  exact inductive_step_if_contains_horizontal_line_h_main' n k verts lines points h_has_horizontal

lemma inductive_step_if_contains_horizontal_line_h_card_erase_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines):
  (lines.erase l₀).card = lines.card - 1 := by
  exact inductive_step_if_contains_horizontal_line_h_card_erase' n k verts lines points l₀ hl₀_in_lines

lemma inductive_step_if_contains_horizontal_line_h_sum_card_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = n)
  (l : ℝ × ℝ)
  (hl_in_lines : l ∈ lines)
  (hn : n ≥ 4):
  verts.card + (lines.erase l).card = n - 1 := by
  exact inductive_step_if_contains_horizontal_line_h_sum_card' n k verts lines points hcard l hl_in_lines hn

lemma inductive_step_if_contains_horizontal_line_h_filter_card_eq_k_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l₀ : ℝ × ℝ)
  (hl₀_in_lines : l₀ ∈ lines)
  (hl₀_1 : l₀.1 = 0)
  (h_filter_card : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card):
  ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  exact inductive_step_if_contains_horizontal_line_h_filter_card_eq_k' n k verts lines points hk l₀ hl₀_in_lines hl₀_1 h_filter_card

lemma inductive_step_if_contains_horizontal_line_h_n_gt_3_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n ≥ 4):
  n > 3 := by
  exact inductive_step_if_contains_horizontal_line_h_n_gt_3' n k verts lines points hn

lemma inductive_step_if_contains_horizontal_line_h_translation_equivalence_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (hn : n ≥ 4)
  (h_n_gt_3 : n > 3):
  ∀ (k'' : ℕ) (verts'' : Finset ℝ) (lines'' : Finset (ℝ × ℝ)) (points'' : Finset (ℕ × ℕ)), (verts''.card + lines''.card = n - 1) → (∀ p, p ∈ points'' ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) → (∀ p ∈ points'', (∃ l ∈ lines'', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts'', p.1 = x)) → ((lines''.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k'') → k'' = 0 ∨ k'' = 1 ∨ k'' = 3 := by
  exact inductive_step_if_contains_horizontal_line_h_translation_equivalence' n k verts lines points h_ih hn h_n_gt_3

lemma inductive_step_if_contains_horizontal_line_h_filter_eq_1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (hl1 : l.1 = 0)
  (hl_in_lines : l ∈ lines)
  (lines' : Finset (ℝ × ℝ))
  (h_lines'_def : lines' = lines.erase l):
  (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
  exact inductive_step_if_contains_horizontal_line_h_filter_eq' n k verts lines points l hl1 hl_in_lines lines' h_lines'_def

theorem inductive_step_if_contains_horizontal_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3  := by

  have h_main : ∃ (l₀ : ℝ × ℝ), l₀ ∈ lines ∧ l₀.1 = 0 ∧ l₀.2 = 1 := by
    exact inductive_step_if_contains_horizontal_line_h_main_1 n k verts lines points h_has_horizontal

  obtain ⟨l₀, hl₀_in_lines, hl₀_1, hl₀_2⟩ := h_main

  have h_card_erase : (lines.erase l₀).card = lines.card - 1 := by
    exact inductive_step_if_contains_horizontal_line_h_card_erase_1 n k verts lines points l₀ hl₀_in_lines

  have h_sum_card : verts.card + (lines.erase l₀).card = n - 1 := by
    exact inductive_step_if_contains_horizontal_line_h_sum_card_1 n k verts lines points hcard l₀ hl₀_in_lines hn

  have h_n_gt_3 : n > 3 := by
    exact inductive_step_if_contains_horizontal_line_h_n_gt_3_1 n k verts lines points hn

  have h_translation_equivalence : ∀ (k'' : ℕ) (verts'' : Finset ℝ) (lines'' : Finset (ℝ × ℝ)) (points'' : Finset (ℕ × ℕ)), (verts''.card + lines''.card = n - 1) → (∀ p, p ∈ points'' ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) → (∀ p ∈ points'', (∃ l ∈ lines'', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts'', p.1 = x)) → ((lines''.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k'') → k'' = 0 ∨ k'' = 1 ∨ k'' = 3 := by
    exact inductive_step_if_contains_horizontal_line_h_translation_equivalence_1 n k verts lines points h_ih hn h_n_gt_3

  set lines' := lines.erase l₀ with h_lines'_def
  set verts' := verts with h_verts'_def

  have h_filter_eq : (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := by
    exact inductive_step_if_contains_horizontal_line_h_filter_eq_1 n k verts lines points l₀ hl₀_1 hl₀_in_lines lines' h_lines'_def

  have h_filter_card : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
    have h1 : (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) := h_filter_eq
    have h2 : lines' = lines.erase l₀ := by simpa using h_lines'_def
    rw [h2] at h1
    exact congr_arg Finset.card h1

  have h_filter_card_eq_k : ((lines.erase l₀).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
    exact inductive_step_if_contains_horizontal_line_h_filter_card_eq_k_1 n k verts lines points hk l₀ hl₀_in_lines hl₀_1 h_filter_card

  have h1 : verts'.card + lines'.card = n - 1 := by
    simpa [h_lines'_def, h_verts'_def] using h_sum_card

  set points' : Finset (ℕ × ℕ) := (Finset.Icc 1 n ×ˢ Finset.Icc 2 (n + 1)).filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1) with h_points'_def

  have h2 : ∀ p : ℕ × ℕ, p ∈ points' ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1 := by
    intro p
    constructor
    · -- Prove the forward direction: if p ∈ points', then p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1
      intro hp
      simp only [h_points'_def, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      tauto
    · -- Prove the reverse direction: if p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1, then p ∈ points'
      rintro ⟨h1, h2, h3⟩
      simp only [h_points'_def, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · constructor <;> omega
      · exact ⟨h1, h2, h3⟩

  have h3 : ∀ p ∈ points', (∃ l ∈ lines', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts', p.1 = x) := by
    intro p hp
    have h3₁ : p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1 := (h2 p).mp hp
    have h3₂ : p.1 ≥ 1 := h3₁.1
    have h3₃ : p.2 ≥ 2 := h3₁.2.1
    have h3₄ : p.1 + p.2 ≤ n + 1 := h3₁.2.2
    have h3₅ : p.2 ≥ 1 := by linarith
    have h3₆ : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := ⟨h3₂, h3₅, h3₄⟩
    have h3₇ : (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := hcover p h3₆
    cases h3₇ with
    | inl h3₇ =>
      rcases h3₇ with ⟨l, hl_in_lines, hl_eq⟩
      by_cases h3₈ : l = l₀
      · -- Case l = l₀
        have h3₈₁ : l = l₀ := h3₈
        have h3₈₂ : l.1 = l₀.1 := by rw [h3₈₁]
        have h3₈₃ : l.2 = l₀.2 := by rw [h3₈₁]
        have h3₈₄ : l.1 = 0 := by
          rw [h3₈₂, hl₀_1]
        have h3₈₅ : l.2 = 1 := by
          rw [h3₈₃, hl₀_2]
        have h3₈₆ : (l.1 : ℝ) * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by simpa using hl_eq
        rw [h3₈₄, h3₈₅] at h3₈₆
        have h3₈₇ : (0 : ℝ) * (p.1 : ℝ) + (1 : ℝ) = (p.2 : ℝ) := h3₈₆
        have h3₈₈ : (1 : ℝ) = (p.2 : ℝ) := by linarith
        have h3₈₉ : (p.2 : ℝ) = 1 := by linarith
        have h3₉₀ : p.2 = 1 := by exact_mod_cast h3₈₉
        linarith
      · -- Case l ≠ l₀
        have h3₈ : l ≠ l₀ := h3₈
        have h3₈₁ : l ∈ lines' := by
          have h3₈₂ : l ∈ lines := hl_in_lines
          have h3₈₃ : l ≠ l₀ := h3₈
          have h3₈₄ : l ∈ lines.erase l₀ := Finset.mem_erase.mpr ⟨h3₈₃, h3₈₂⟩
          simpa [h_lines'_def] using h3₈₄
        have h3₈₄ : ∃ l ∈ lines', l.1 * p.1 + l.2 = p.2 := by
          refine' ⟨l, h3₈₁, _⟩
          simpa using hl_eq
        exact Or.inl h3₈₄
    | inr h3₇ =>
      have h3₇₁ : ∃ x ∈ verts, (p.1 : ℝ) = x := h3₇
      have h3₇₂ : ∃ x ∈ verts', p.1 = x := by
        rcases h3₇₁ with ⟨x, hx_in_verts, hx_eq⟩
        refine' ⟨x, _⟩
        constructor
        · simpa [h_verts'_def] using hx_in_verts
        · linarith
      exact Or.inr h3₇₂

  have h4 : ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card) = k := by simpa [h_lines'_def] using h_filter_card_eq_k

  have h5 : k = 0 ∨ k = 1 ∨ k = 3 := by
    specialize h_translation_equivalence k verts' lines' points' h1 h2 h3 h4
    simpa using h_translation_equivalence

  exact h5

lemma translation_equivalence_x_axis_h6 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n > 3)
  (h₁ : verts.card + lines.card = n - 1)
  (h₂ : ∀ p, p ∈ points ↔ p.1 ≥ 2 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (h₃ : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (h₄ : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  ∀ (p : ℕ × ℕ), p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n → (∃ l ∈ (lines.image (fun l => (l.1, l.1 + l.2))), l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ (verts.image (fun x => x - 1)), (p.1 : ℝ) = x) := by
  intro p hp
  have h61 : p.1 ≥ 1 := hp.1
  have h62 : p.2 ≥ 1 := hp.2.1
  have h63 : p.1 + p.2 ≤ n := hp.2.2
  have h64 : ((p.1 + 1, p.2) : ℕ × ℕ) ∈ points := by
    have h641 : (p.1 + 1) ≥ 2 := by linarith
    have h642 : p.2 ≥ 1 := by linarith
    have h643 : (p.1 + 1) + p.2 ≤ n + 1 := by linarith
    have h644 : ((p.1 + 1, p.2) : ℕ × ℕ) ∈ points := by
      rw [h₂ ((p.1 + 1, p.2))]
      <;> simp [h641, h642, h643]
      <;> aesop
    exact h644
  have h65 : (∃ l ∈ lines, l.1 * ((p.1 + 1 : ℕ) : ℝ) + l.2 = ((p.2 : ℕ) : ℝ)) ∨ (∃ x ∈ verts, x = ((p.1 + 1 : ℕ) : ℝ)) := by
    have h650 := h₃ ((p.1 + 1, p.2)) h64
    simpa using h650
  cases h65 with
  | inl h651 =>
    rcases h651 with ⟨l, hl1, hl2⟩
    have h6511 : (l.1, l.1 + l.2) ∈ (lines.image (fun l => (l.1, l.1 + l.2))) := by
      apply Finset.mem_image.mpr
      refine ⟨l, hl1, rfl⟩
    have h6512 : l.1 * (p.1 : ℝ) + (l.1 + l.2) = (p.2 : ℝ) := by
      have h65121 : l.1 * ((p.1 + 1 : ℕ) : ℝ) + l.2 = ((p.2 : ℕ) : ℝ) := by simpa using hl2
      have h65122 : ((p.1 + 1 : ℕ) : ℝ) = (p.1 : ℝ) + 1 := by norm_cast
      rw [h65122] at h65121
      ring_nf at h65121 ⊢
      linarith
    have h6513 : ∃ l' ∈ (lines.image (fun l => (l.1, l.1 + l.2))), l'.1 * (p.1 : ℝ) + l'.2 = (p.2 : ℝ) := by
      refine ⟨(l.1, l.1 + l.2), h6511, ?_⟩
      simpa using h6512
    rcases h6513 with ⟨l', hl'1, hl'2⟩
    exact Or.inl ⟨l', hl'1, hl'2⟩
  | inr h652 =>
    rcases h652 with ⟨x, hx1, hx2⟩
    have h6521 : x - 1 ∈ (verts.image (fun x => x - 1)) := by
      apply Finset.mem_image.mpr
      refine ⟨x, hx1, rfl⟩
    have h6522 : (p.1 : ℝ) = x - 1 := by
      have h65221 : x = ((p.1 + 1 : ℕ) : ℝ) := by simpa using hx2
      have h65222 : x = (p.1 : ℝ) + 1 := by
        norm_cast at h65221 ⊢ <;> linarith
      linarith
    have h6523 : ∃ x' ∈ (verts.image (fun x => x - 1)), (p.1 : ℝ) = x' := by
      refine ⟨x - 1, h6521, ?_⟩
      linarith
    rcases h6523 with ⟨x', hx'1, hx'2⟩
    exact Or.inr ⟨x', hx'1, by linarith⟩


lemma translation_equivalence_x_axis_h8 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (hn : n > 3)
  (h₁ : verts.card + lines.card = n - 1)
  (h₄ : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h7 : (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card):
  (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  have h71 : (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := h7
  have h41 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := h₄
  linarith

lemma translation_equivalence_x_axis_h5 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (hn : n > 3)
  (h₁ : verts.card + lines.card = n - 1):
  ( (verts.image (fun x => x - 1)) ).card + ( (lines.image (fun l => (l.1, l.1 + l.2))) ).card = n - 1 := by
  have h_inj1 : Function.Injective (fun x : ℝ => x - 1) := by
    intro x y h
    simp_all
    <;> linarith
  have h_card1 : (verts.image (fun x => x - 1)).card = verts.card := by
    rw [Finset.card_image_of_injective verts h_inj1]
  have h_inj2 : Function.Injective (fun (l : ℝ × ℝ) => (l.1, l.1 + l.2)) := by
    intro l1 l2 h
    simp_all [Prod.ext_iff]
    <;> aesop
  have h_card2 : (lines.image (fun l => (l.1, l.1 + l.2))).card = lines.card := by
    rw [Finset.card_image_of_injective lines h_inj2]
  linarith


lemma translation_equivalence_x_axis_main_proof (n k : ℕ) (hn : n > 3)
  (h : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ))
  (h₁ : verts'.card + lines'.card = n - 1)
  (h₂ : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
    (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x))
  (h₃ : (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k')
  (h₄ : k' = k):
  k = 0 ∨ k = 1 ∨ k = 3 := by
  have h₅ : k' = 0 ∨ k' = 1 ∨ k' = 3 := h k' verts' lines' h₁ h₂ h₃
  have h₆ : k = k' := by linarith
  have h₇ : k = 0 ∨ k = 1 ∨ k = 3 := by
    have h₈ : k' = 0 ∨ k' = 1 ∨ k' = 3 := h₅
    have h₉ : k = k' := by linarith
    rcases h₈ with (h₈ | h₈ | h₈)
    · -- Case k' = 0
      have h₁₀ : k = 0 := by linarith
      exact Or.inl h₁₀
    · -- Case k' = 1
      have h₁₀ : k = 1 := by linarith
      exact Or.inr (Or.inl h₁₀)
    · -- Case k' = 3
      have h₁₀ : k = 3 := by linarith
      exact Or.inr (Or.inr h₁₀)
  exact h₇

lemma translation_equivalence_x_axis_h7 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (hn : n > 3)
  (h₁ : verts.card + lines.card = n - 1)
  (h₄ : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
  have h_inj : Function.Injective (fun (l : ℝ × ℝ) => (l.1, l.1 + l.2)) := by
    intro l1 l2 h
    simp_all [Prod.ext_iff]
    <;> aesop
  have h9 : ( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1) = ((lines.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1)).image (fun l => (l.1, l.1 + l.2))) := by
    ext x
    simp [Finset.mem_filter, Finset.mem_image]
    <;> aesop
    <;> aesop
  rw [h9]
  have h10 : ( (lines.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1)).image (fun l => (l.1, l.1 + l.2)) ).card = (lines.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
    apply Finset.card_image_of_injective
    exact h_inj
  linarith

theorem translation_equivalence_x_axis (n k : ℕ) (hn :  n > 3) :
  (∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3) →
  (∀ (k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)),
    (verts.card + lines.card = n - 1) →
    (∀ p, p ∈ points ↔ p.1 ≥ 2 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) →
    (∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) →
    ((lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) →
    k = 0 ∨ k = 1 ∨ k = 3)  := by

  intro h
  intro k verts lines points h₁ h₂ h₃ h₄

  have h5 : ( (verts.image (fun x => x - 1)) ).card + ( (lines.image (fun l => (l.1, l.1 + l.2))) ).card = n - 1 := by
    exact translation_equivalence_x_axis_h5 n k verts lines hn h₁

  have h6 : ∀ (p : ℕ × ℕ), p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n → (∃ l ∈ (lines.image (fun l => (l.1, l.1 + l.2))), l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ (verts.image (fun x => x - 1)), (p.1 : ℝ) = x) := by
    exact translation_equivalence_x_axis_h6 n k verts lines points hn h₁ h₂ h₃ h₄

  have h7 : (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by
    exact translation_equivalence_x_axis_h7 n k verts lines hn h₁ h₄

  have h8 : (( (lines.image (fun l => (l.1, l.1 + l.2)))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
    exact translation_equivalence_x_axis_h8 n k verts lines hn h₁ h₄ h7

  have h9 := translation_equivalence_x_axis_main_proof n k hn h k (verts.image (fun x => x - 1)) (lines.image (fun l => (l.1, l.1 + l.2))) h5 h6 h8 (by rfl)
  exact h9

lemma inductive_step_if_contains_vertical_line_round1_h1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_has_vert : ∃ x ∈ verts, x = 1):
  (1 : ℝ) ∈ verts := by
  aesop

lemma round1_h_verts_card_ge_one (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h1_in_verts : (1 : ℝ) ∈ verts):
  verts.card ≥ 1 := by
  have h21 : 0 < verts.card := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty (fun h => by simp_all))
  linarith

lemma round1_h_erase_card (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h1_in_verts : (1 : ℝ) ∈ verts):
  (verts.erase (1 : ℝ)).card = verts.card - 1 := by
  exact Finset.card_erase_of_mem h1_in_verts

lemma round1_h_main_card (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = n)
  (h1_in_verts : (1 : ℝ) ∈ verts)
  (h_verts_card_ge_one : verts.card ≥ 1)
  (h_erase_card : (verts.erase (1 : ℝ)).card = verts.card - 1):
  (verts.erase (1 : ℝ)).card + lines.card + 1 = n := by
  have h31 : (verts.erase (1 : ℝ)).card = verts.card - 1 := h_erase_card
  have h32 : verts.card ≥ 1 := h_verts_card_ge_one
  have h33 : (verts.card - 1) + 1 = verts.card := by omega
  have h34 : (verts.erase (1 : ℝ)).card + lines.card + 1 = ((verts.card - 1) + lines.card) + 1 := by
    rw [h31]
    <;> rfl
  have h35 : ((verts.card - 1) + lines.card) + 1 = (verts.card - 1) + (lines.card + 1) := by omega
  have h36 : (verts.card - 1) + (lines.card + 1) = ((verts.card - 1) + 1) + lines.card := by omega
  have h37 : ((verts.card - 1) + 1) + lines.card = verts.card + lines.card := by
    have h371 : (verts.card - 1) + 1 = verts.card := by omega
    rw [h371]
    <;> omega
  have h38 : verts.card + lines.card = n := by linarith
  linarith

lemma round1_h14 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n ≥ 4)
  (hcard : lines.card + verts.card = n)
  (h1_in_verts : (1 : ℝ) ∈ verts)
  (h_verts_card_ge_one : verts.card ≥ 1)
  (h_erase_card : (verts.erase (1 : ℝ)).card = verts.card - 1)
  (h_main_card : (verts.erase (1 : ℝ)).card + lines.card + 1 = n):
  (verts.erase (1 : ℝ)).card + lines.card = n - 1 := by
  have h41 : n ≥ 4 := hn
  have h42 : (verts.erase (1 : ℝ)).card + lines.card + 1 = n := h_main_card
  omega

theorem inductive_step_if_contains_vertical_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_vert : ∃ x ∈ verts, x = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3  := by

  have h1_in_verts : (1 : ℝ) ∈ verts := by
    exact inductive_step_if_contains_vertical_line_round1_h1 n k verts lines points h_has_vert
  have h_verts_card_ge_one : verts.card ≥ 1 := by
    exact round1_h_verts_card_ge_one n k verts lines points h1_in_verts
  have h_erase_card : (verts.erase (1 : ℝ)).card = verts.card - 1 := by
    exact round1_h_erase_card n k verts lines points h1_in_verts
  have h_main_card : (verts.erase (1 : ℝ)).card + lines.card + 1 = n := by
    exact round1_h_main_card n k verts lines points hcard h1_in_verts h_verts_card_ge_one h_erase_card
  have h14 : (verts.erase (1 : ℝ)).card + lines.card = n - 1 := by
    exact round1_h14 n k verts lines points hn hcard h1_in_verts h_verts_card_ge_one h_erase_card h_main_card
  have h1 : n > 3 := by linarith
  have h2 := translation_equivalence_x_axis n k h1
  have h2' := h2 h_ih
  set points' : Finset (ℕ × ℕ) := ((Finset.Icc 2 (n + 1)) ×ˢ (Finset.Icc 1 (n + 1))).filter (fun p : ℕ × ℕ => p.1 + p.2 ≤ n + 1) with hpoints'_def
  have h15 : ∀ (p : ℕ × ℕ), p ∈ points' ↔ p.1 ≥ 2 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by
    intro p
    simp [hpoints'_def, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    <;> omega
  have h16 : ∀ p ∈ points', (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ (verts.erase (1 : ℝ)), p.1 = x) := by
    intro p hp
    have h161 : p.1 ≥ 2 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := (h15 p).mp hp
    have h1611 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by omega
    have h162 : (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := hcover p h1611
    cases h162 with
    | inl h162_left =>
      left
      exact h162_left
    | inr h162_right =>
      rcases h162_right with ⟨x, hx_in_verts, h_eq⟩
      have h16111 : p.1 ≥ 2 := h161.1
      have h16112 : p.2 ≥ 1 := h161.2.1
      have h16113 : p.1 + p.2 ≤ n + 1 := h161.2.2
      have h1622 : x ≠ (1 : ℝ) := by
        by_contra h16221
        have h162211 : (p.1 : ℝ) = 1 := by linarith
        have h162212 : p.1 ≥ 2 := h16111
        have h162213 : (p.1 : ℝ) ≥ 2 := by exact_mod_cast h162212
        linarith
      have hx_in_verts_erase : x ∈ verts.erase (1 : ℝ) := by
        exact Finset.mem_erase.mpr ⟨h1622, hx_in_verts⟩
      right
      refine ⟨x, hx_in_verts_erase,?_⟩
      norm_cast at h_eq ⊢
      <;> linarith
  have h17 : k = 0 ∨ k = 1 ∨ k = 3 := by
    have h171 := h2' k (verts.erase (1 : ℝ)) lines points' h14 (fun p => (h15 p)) h16 hk
    exact h171
  exact h17

lemma inductive_step_if_contains_rainy_diagonal_line_refined_main_proof (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn1 : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_rainy_diagonal : ∃ l ∈ lines, l.1 = -1 ∧ l.2 = (n : ℝ) + 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  rcases h_has_rainy_diagonal with ⟨l0, hl0_in_lines, hl01, hl02⟩
  have h1330 : (lines.erase l0).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1) = lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · -- Assume x ∈ (lines.erase l0).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)
      rintro ⟨⟨h1, h2⟩, hx2⟩
      exact ⟨h2, hx2⟩
    · -- Assume x ∈ lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)
      rintro ⟨hx1, hx2⟩
      have h1331 : x ≠ l0 := by
        by_contra h13311
        have h13312 : x.1 = l0.1 := by rw [h13311]
        have h13313 : l0.1 = -1 := hl01
        have h13314 : x.1 = -1 := by linarith
        have h13315 : x.1 ≠ -1 := hx2.2
        contradiction
      exact ⟨⟨h1331, hx1⟩, hx2⟩
  have h13 : ((lines.erase l0).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
    have h13301 : ((lines.erase l0).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card := by rw [h1330]
    linarith
  have h11 : verts.card + (lines.erase l0).card = n - 1 := by
    have h111 : (lines.erase l0).card = lines.card - 1 := by
      rw [Finset.card_erase_of_mem hl0_in_lines]
      <;> aesop
    have h1 : lines.card ≥ 1 := by
      have h112 : l0 ∈ lines := hl0_in_lines
      have h113 : 0 < lines.card := by
        apply Finset.card_pos.mpr
        exact ⟨l0, h112⟩
      linarith
    have h114 : lines.card ≥ 1 := by linarith
    have h115 : n ≥ 1 := by linarith
    have h116 : lines.card + verts.card = n := hcard
    have h117 : ∃ a', lines.card = a' + 1 := by
      use lines.card - 1
      omega
    rcases h117 with ⟨a', ha'⟩
    have h118 : lines.card = a' + 1 := ha'
    have h119 : a' + verts.card = n - 1 := by omega
    have h120 : lines.card - 1 = a' := by omega
    have h121 : verts.card + (lines.card - 1) = n - 1 := by omega
    omega
  have h12 : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n → (∃ l ∈ lines.erase l0, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := by
    intro p hp
    have h121 : p.1 ≥ 1 := hp.1
    have h122 : p.2 ≥ 1 := hp.2.1
    have h123 : p.1 + p.2 ≤ n := hp.2.2
    have h124 : p.1 + p.2 ≤ n + 1 := by linarith
    have h125 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := ⟨h121, h122, h124⟩
    have h126 : (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := hcover p h125
    cases h126 with
    | inl h126 =>
      rcases h126 with ⟨l, hl_in_lines, h_eq⟩
      have h1261 : l ≠ l0 := by
        by_contra h1261
        have h1261' : l = l0 := by tauto
        have h1263 : l.1 = -1 := by
          rw [h1261']
          linarith
        have h1264 : l.2 = (n : ℝ) + 1 := by
          rw [h1261']
          linarith
        have h1265 : (n : ℝ) + 1 = (p.1 : ℝ) + (p.2 : ℝ) := by
          rw [h1263, h1264] at h_eq
          ring_nf at h_eq ⊢
          linarith
        have h1266 : (p.1 : ℝ) + (p.2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h123
        linarith
      have h1267 : l ∈ lines.erase l0 := by
        exact Finset.mem_erase_of_ne_of_mem h1261 hl_in_lines
      apply Or.inl
      exact ⟨l, h1267, h_eq⟩
    | inr h126 =>
      rcases h126 with ⟨x, hx_in_verts, h126_eq⟩
      apply Or.inr
      exact ⟨x, hx_in_verts, h126_eq⟩
  have h140 : 3 ≤ n := by linarith
  have h141 := h_ih k verts (lines.erase l0) h11 h12 h13
  exact h141

theorem inductive_step_if_contains_rainy_diagonal_line_refined (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_rainy_diagonal : ∃ l ∈ lines, l.1 = -1 ∧ l.2 = (n : ℝ) + 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3  := by

  have h1 : 3 ≤ n := by linarith
  exact inductive_step_if_contains_rainy_diagonal_line_refined_main_proof n k verts lines points h1 hcard hallpoints hmain hk hcover h_has_rainy_diagonal h_ih

lemma num_points_on_boundary_main (n : ℕ) (hpoints : Finset (ℕ × ℕ)) (hpoints_def : ∀ p, p ∈ hpoints ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints).card = 3 * n - (if n = 1 then 2 else if n = 2 then 3 else 3) := by
  by_cases h10 : n = 0
  · -- Case 1: n = 0
    have h2 : hpoints = ∅ := by
      apply Finset.eq_empty_of_forall_not_mem
      intro p
      intro h4
      have h5 := (hpoints_def p).mp h4
      simp [h10] at h5
      <;> omega
    simp [h2, h10]
    <;> aesop
  · -- Case 2: n ≠ 0
    by_cases h11 : n = 1
    · -- Subcase 2.1: n = 1
      have h4 : hpoints = {(1, 1)} := by
        ext ⟨x, y⟩
        simp [hpoints_def, h11]
        <;> omega
      rw [h4, h11]
      <;> aesop
    · -- Subcase 2.2: n ≠ 1
      by_cases h12 : n = 2
      · -- Subcase 2.2.1: n = 2
        have h4 : hpoints = {(1, 1), (1, 2), (2, 1)} := by
          ext ⟨x, y⟩
          simp [hpoints_def, h12]
          <;> omega
        rw [h4, h12]
        <;> aesop
      · -- Subcase 2.2.2: n ≠ 2
        have h41 : n ≥ 3 := by omega
        have h51 : ∀ p : ℕ × ℕ, p ∈ hpoints → (p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) := by
          intro p hp
          exact (hpoints_def p).mp hp
        have h52 : ∀ p : ℕ × ℕ, (p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) → p ∈ hpoints := by
          intro p h
          exact (hpoints_def p).mpr h
        set A : Finset (ℕ × ℕ) := Finset.image (fun y => (1, y)) (Finset.Icc 1 n) with hA
        set B : Finset (ℕ × ℕ) := Finset.image (fun x => (x, 1)) (Finset.Icc 2 n) with hB
        set C : Finset (ℕ × ℕ) := Finset.image (fun x => (x, n + 1 - x)) (Finset.Icc 2 (n - 1)) with hC
        have h531 : Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints ⊆ A ∪ B ∪ C := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          have h5311 : p ∈ hpoints := hp.1
          have h5312 : p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1 := hp.2
          have h5313 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := h51 p h5311
          by_cases h5314 : p.1 = 1
          · -- Case 1: p.1 = 1
            have h1_eq : p.1 = 1 := h5314
            have h5315 : 1 ≤ p.2 := by linarith
            have h5316 : p.2 ≤ n := by linarith
            have h5317 : p.2 ∈ Finset.Icc 1 n := by
              simp [Finset.mem_Icc]
              <;> omega
            have h5318 : p ∈ A := by
              rw [hA]
              refine' Finset.mem_image.mpr ⟨p.2, h5317, _⟩
              simp [h1_eq, Prod.ext_iff]
              <;> aesop
            simp [h5318]
            <;> aesop
          · -- Case 2: p.1 ≠ 1
            have h1_ne : p.1 ≠ 1 := h5314
            have h53110 : p.1 ≥ 2 := by omega
            by_cases h53111 : p.2 = 1
            · -- Subcase 2a: p.2 = 1
              have h2_eq : p.2 = 1 := h53111
              have h53112 : 2 ≤ p.1 := by linarith
              have h53113 : p.1 ≤ n := by linarith
              have h53114 : p.1 ∈ Finset.Icc 2 n := by
                simp [Finset.mem_Icc]
                <;> omega
              have h53115 : p ∈ B := by
                rw [hB]
                refine' Finset.mem_image.mpr ⟨p.1, h53114, _⟩
                simp [h2_eq, Prod.ext_iff]
                <;> aesop
              simp [h53115]
              <;> aesop
            · -- Subcase 2b: p.2 ≠ 1
              have h2_ne : p.2 ≠ 1 := h53111
              have h53117 : p.2 ≥ 2 := by omega
              have h53118 : p.1 + p.2 = n + 1 := by
                rcases h5312 with (h5312 | h5312 | h5312)
                · contradiction
                · contradiction
                · tauto
              have h53119 : p.1 ≤ n - 1 := by omega
              have h53120 : 2 ≤ p.1 := by linarith
              have h53122 : p.1 ∈ Finset.Icc 2 (n - 1) := by
                simp [Finset.mem_Icc]
                <;> omega
              have h53123 : p ∈ C := by
                rw [hC]
                refine' Finset.mem_image.mpr ⟨p.1, h53122, _⟩
                have h53124 : p.2 = n + 1 - p.1 := by omega
                simp [h53124, Prod.ext_iff]
                <;> aesop
              simp [h53123]
              <;> aesop
        have h532 : A ∪ B ∪ C ⊆ Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints := by
          intro p hp
          simp only [Finset.mem_union] at hp
          have h53214 : p ∈ A ∨ p ∈ B ∨ p ∈ C := by tauto
          rcases h53214 with (h53214 | h53214 | h53214)
          · -- Case 1: p ∈ A
            have h532141 : p ∈ A := h53214
            rw [hA] at h532141
            simp only [Finset.mem_image] at h532141
            rcases h532141 with ⟨y, hy, h532142⟩
            have hy1 : 1 ≤ y := by
              simp [Finset.mem_Icc] at hy
              <;> linarith
            have hy2 : y ≤ n := by
              simp [Finset.mem_Icc] at hy
              <;> linarith
            have h5321421 : p.1 = 1 := by
              simp [Prod.ext_iff] at h532142
              <;> aesop
            have h532143 : p.2 = y := by
              have h532142' : p = (1, y) := by simp [Prod.ext_iff] at h532142 ⊢ <;> tauto
              rw [h532142']
              <;> simp
            have h532144 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by
              constructor
              · linarith
              constructor
              · linarith
              · linarith
            have h532145 : p ∈ hpoints := h52 p h532144
            simp only [Finset.mem_filter]
            refine' ⟨h532145, _⟩
            tauto
          · -- Case 2: p ∈ B
            have h532141 : p ∈ B := h53214
            rw [hB] at h532141
            simp only [Finset.mem_image] at h532141
            rcases h532141 with ⟨x, hx, h532142⟩
            have hx1 : 2 ≤ x := by
              simp [Finset.mem_Icc] at hx
              <;> linarith
            have hx2 : x ≤ n := by
              simp [Finset.mem_Icc] at hx
              <;> linarith
            have h5321421 : p.1 = x := by
              simp [Prod.ext_iff] at h532142
              <;> aesop
            have h5321422 : p.2 = 1 := by
              simp [Prod.ext_iff] at h532142
              <;> aesop
            have h532144 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by
              constructor
              · linarith
              constructor
              · linarith
              · linarith
            have h532145 : p ∈ hpoints := h52 p h532144
            simp only [Finset.mem_filter]
            refine' ⟨h532145, _⟩
            tauto
          · -- Case 3: p ∈ C
            have h532141 : p ∈ C := h53214
            rw [hC] at h532141
            simp only [Finset.mem_image] at h532141
            rcases h532141 with ⟨x, hx, h532142⟩
            have hx1 : 2 ≤ x := by
              simp [Finset.mem_Icc] at hx
              <;> omega
            have hx2 : x ≤ n - 1 := by
              simp [Finset.mem_Icc] at hx
              <;> omega
            have h5321421 : p.1 = x := by
              simp [Prod.ext_iff] at h532142
              <;> aesop
            have h5321422 : p.2 = n + 1 - x := by
              simp [Prod.ext_iff] at h532142
              <;> aesop
            have h532144 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by
              constructor
              · linarith
              constructor
              · omega
              · omega
            have h532145 : p ∈ hpoints := h52 p h532144
            have h532146 : p.1 + p.2 = n + 1 := by omega
            simp only [Finset.mem_filter]
            refine' ⟨h532145, _⟩
            tauto
        have h53 : Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints = A ∪ B ∪ C := by
          apply Finset.Subset.antisymm h531 h532
        have h_disj1 : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro p hpA hpB
          rw [hA] at hpA
          rw [hB] at hpB
          simp only [Finset.mem_image] at hpA hpB
          rcases hpA with ⟨y, hy, hpy⟩
          rcases hpB with ⟨x, hx, hpx⟩
          have h11 : p.1 = 1 := by
            simp [Prod.ext_iff] at hpy
            <;> aesop
          have h12 : p.1 ≥ 2 := by
            simp [Finset.mem_Icc] at hx
            simp [Prod.ext_iff] at hpx
            <;> omega
          omega
        have h_disj2 : Disjoint A C := by
          rw [Finset.disjoint_left]
          intro p hpA hpC
          rw [hA] at hpA
          rw [hC] at hpC
          simp only [Finset.mem_image] at hpA hpC
          rcases hpA with ⟨y, hy, hpy⟩
          rcases hpC with ⟨x, hx, hpx⟩
          have h11 : p.1 = 1 := by
            simp [Prod.ext_iff] at hpy
            <;> aesop
          have h12 : p.1 ≥ 2 := by
            simp [Finset.mem_Icc] at hx
            simp [Prod.ext_iff] at hpx
            <;> omega
          omega
        have h_disj3 : Disjoint B C := by
          rw [Finset.disjoint_left]
          intro p hpB hpC
          rw [hB] at hpB
          rw [hC] at hpC
          simp only [Finset.mem_image] at hpB hpC
          rcases hpB with ⟨x, hx, hpx⟩
          rcases hpC with ⟨x1, hx1, hpx1⟩
          have h1 : x1 < n := by
            have h11 : x1 ∈ Finset.Icc 2 (n - 1) := hx1
            have h12 : x1 ≤ n - 1 := by
              simp [Finset.mem_Icc] at h11
              <;> omega
            omega
          have h13 : (x, 1) = p := by tauto
          have h14 : (x1, n + 1 - x1) = p := by tauto
          have h15 : (x, 1) = (x1, n + 1 - x1) := by rw [h13, h14]
          have h2 : (x, 1).2 = (x1, n + 1 - x1).2 := by rw [h15]
          have h21 : (x, 1).2 = 1 := rfl
          have h22 : (x1, n + 1 - x1).2 = n + 1 - x1 := rfl
          rw [h21, h22] at h2
          omega
        have hA_card : A.card = n := by
          rw [hA]
          have h_inj : Function.Injective (fun y : ℕ => (1, y)) := by
            intro y1 y2 h
            simp [Prod.ext_iff] at h
            <;> aesop
          rw [Finset.card_image_of_injective _ h_inj]
          simp [Finset.Icc_eq_empty_of_lt]
          <;> omega
        have hB_card : B.card = n - 1 := by
          rw [hB]
          have h_inj : Function.Injective (fun x : ℕ => (x, 1)) := by
            intro x1 x2 h
            simp [Prod.ext_iff] at h
            <;> aesop
          rw [Finset.card_image_of_injective _ h_inj]
          simp [Finset.Icc_eq_empty_of_lt]
          <;> omega
        have hC_card : C.card = n - 2 := by
          rw [hC]
          have h_inj : Function.Injective (fun x : ℕ => (x, n + 1 - x)) := by
            intro x1 x2 h
            simp [Prod.ext_iff] at h
            <;> aesop
          rw [Finset.card_image_of_injective _ h_inj]
          simp [Finset.Icc_eq_empty_of_lt]
          <;> omega
        have h544 : Disjoint (A ∪ B) C := by
          apply Finset.disjoint_union_left.mpr
          constructor
          · exact h_disj2
          · exact h_disj3
        have h_union_card : (A ∪ B ∪ C).card = A.card + B.card + C.card := by
          have h1 : (A ∪ B ∪ C).card = ((A ∪ B) ∪ C).card := by rfl
          rw [h1]
          have h2 : ((A ∪ B) ∪ C).card = (A ∪ B).card + C.card := by
            rw [Finset.card_union_of_disjoint h544]
          rw [h2]
          have h3 : (A ∪ B).card = A.card + B.card := by
            rw [Finset.card_union_of_disjoint h_disj1]
          rw [h3]
          <;> ring
        have h54 : (A ∪ B ∪ C).card = n + (n - 1) + (n - 2) := by
          linarith [hA_card, hB_card, hC_card, h_union_card]
        have h545 : n + (n - 1) + (n - 2) = 3 * n - 3 := by
          omega
        have h546 : (A ∪ B ∪ C).card = 3 * n - 3 := by omega
        have h55 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints).card = (A ∪ B ∪ C).card := by rw [h53]
        have h551 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints).card = 3 * n - 3 := by linarith
        have h56 : 3 * n - (if n = 1 then 2 else if n = 2 then 3 else 3) = 3 * n - 3 := by
          have h561 : n ≠ 1 := by tauto
          have h562 : n ≠ 2 := by tauto
          simp [h561, h562]
          <;> aesop
        omega

theorem num_points_on_boundary (n : ℕ) (hpoints : Finset (ℕ × ℕ)) (hpoints_def : ∀ p, p ∈ hpoints ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n+1) hpoints).card = 3*n - (if n=1 then 2 else if n=2 then 3 else 3) := by

  exact num_points_on_boundary_main n hpoints hpoints_def

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq (n : ℕ) (l : ℝ × ℝ) (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n) (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (p q : ℕ × ℕ)
  (hp : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)))
  (hq : (q.1 = 1 ∨ q.2 = 1 ∨ q.1 + q.2 = n + 1) ∧ (l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ)))
  (h_same_boundary : (p.1 = 1 ∧ q.1 = 1) ∨ (p.2 = 1 ∧ q.2 = 1) ∨ (p.1 + p.2 = n + 1 ∧ q.1 + q.2 = n + 1)) :
  p = q := by
  rcases h_same_boundary with (h1 | h2 | h3)
  · -- Case 1: p.1 = 1 and q.1 = 1
    have hp1 : p.1 = 1 := h1.1
    have hq1 : q.1 = 1 := h1.2
    have h4 : (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) := hp.2
    have h5 : (l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ)) := hq.2
    have h6 : (p.1 : ℝ) = 1 := by exact_mod_cast hp1
    have h7 : (q.1 : ℝ) = 1 := by exact_mod_cast hq1
    have h8 : l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := hp.2
    have h9 : l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ) := hq.2
    have h10 : l.1 * 1 + l.2 = (p.2 : ℝ) := by simpa [h6] using h8
    have h11 : l.1 * 1 + l.2 = (q.2 : ℝ) := by simpa [h7] using h9
    have h12 : (p.2 : ℝ) = (q.2 : ℝ) := by linarith
    have h13 : p.2 = q.2 := by exact_mod_cast h12
    have h14 : p.1 = q.1 := by simp [hp1, hq1]
    exact Prod.ext h14 h13
  · -- Case 2: p.2 = 1 and q.2 = 1
    have hp2 : p.2 = 1 := h2.1
    have hq2 : q.2 = 1 := h2.2
    have h4 : (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) := hp.2
    have h5 : (l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ)) := hq.2
    have h6 : (p.2 : ℝ) = 1 := by exact_mod_cast hp2
    have h7 : (q.2 : ℝ) = 1 := by exact_mod_cast hq2
    have h8 : l.1 * (p.1 : ℝ) + l.2 = 1 := by simpa [h6] using h4
    have h9 : l.1 * (q.1 : ℝ) + l.2 = 1 := by simpa [h7] using h5
    have h10 : l.1 * (p.1 : ℝ) = l.1 * (q.1 : ℝ) := by linarith
    have h11 : (p.1 : ℝ) = (q.1 : ℝ) := by
      have h12 : l.1 ≠ 0 := h_non_sunny.1
      apply mul_left_cancel₀ h12
      linarith
    have h12 : p.1 = q.1 := by exact_mod_cast h11
    have h13 : p.2 = q.2 := by simp [hp2, hq2]
    exact Prod.ext h12 h13
  · -- Case 3: p.1 + p.2 = n + 1 and q.1 + q.2 = n + 1
    have hp_sum : p.1 + p.2 = n + 1 := h3.1
    have hq_sum : q.1 + q.2 = n + 1 := h3.2
    have h4 : (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) := hp.2
    have h5 : (l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ)) := hq.2
    have h6 : (p.1 : ℝ) + (p.2 : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hp_sum
    have h7 : (q.1 : ℝ) + (q.2 : ℝ) = (n : ℝ) + 1 := by exact_mod_cast hq_sum
    have h8 : (p.2 : ℝ) = (n : ℝ) + 1 - (p.1 : ℝ) := by linarith
    have h9 : (q.2 : ℝ) = (n : ℝ) + 1 - (q.1 : ℝ) := by linarith
    have h10 : l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := h4
    have h11 : l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ) := h5
    have h12 : l.1 * (p.1 : ℝ) + l.2 = (n : ℝ) + 1 - (p.1 : ℝ) := by
      rw [h8] at h10
      linarith
    have h13 : l.1 * (q.1 : ℝ) + l.2 = (n : ℝ) + 1 - (q.1 : ℝ) := by
      rw [h9] at h11
      linarith
    have h14 : (p.1 : ℝ) * (l.1 + 1) + l.2 = (n : ℝ) + 1 := by linarith
    have h15 : (q.1 : ℝ) * (l.1 + 1) + l.2 = (n : ℝ) + 1 := by linarith
    have h16 : (p.1 : ℝ) * (l.1 + 1) = (q.1 : ℝ) * (l.1 + 1) := by linarith
    have h17 : l.1 + 1 ≠ 0 := by
      intro h18
      have h19 : l.1 = -1 := by linarith
      have h20 : l.1 ≠ -1 := h_non_sunny.2
      contradiction
    have h18 : (p.1 : ℝ) = (q.1 : ℝ) := by
      apply mul_left_cancel₀ h17
      linarith
    have h19 : p.1 = q.1 := by exact_mod_cast h18
    have h20 : p.2 = q.2 := by
      have h21 : p.1 + p.2 = n + 1 := hp_sum
      have h22 : q.1 + q.2 = n + 1 := hq_sum
      have h23 : p.1 = q.1 := h19
      omega
    exact Prod.ext h19 h20


lemma non_sunny_lines_cover_at_most_2_points_on_boundary_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (p q r : ℕ × ℕ)
  (hp : p ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hq : q ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hr : r ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hp1 : p.1 = 1)
  (hq2 : q.2 = 1)
  (hr3 : r.1 + r.2 = n + 1)
  (hpq : p ≠ q)
  (hpr : p ≠ r)
  (hqr : q ≠ r)
  (hn : 3 ≤ n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) :
  False := by
  have h1 : p ∈ points := by
    have h11 : p ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points := hp
    exact (Finset.mem_filter.mp h11).1
  have h2 : q ∈ points := by
    have h21 : q ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points := hq
    exact (Finset.mem_filter.mp h21).1
  have h3 : r ∈ points := by
    have h31 : r ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points := hr
    exact (Finset.mem_filter.mp h31).1
  have h12_original : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := (hallpoints p).mp h1
  have h22 : q.1 ≥ 1 ∧ q.2 ≥ 1 ∧ q.1 + q.2 ≤ n + 1 := (hallpoints q).mp h2
  have h32 : r.1 ≥ 1 ∧ r.2 ≥ 1 ∧ r.1 + r.2 ≤ n + 1 := (hallpoints r).mp h3
  have h13 : l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by
    have h14 : (p ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := hp
    have h15 : ( (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) := (Finset.mem_filter.mp h14).2
    exact h15.2
  have h23 : l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ) := by
    have h24 : (q ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := hq
    have h25 : ( (q.1 = 1 ∨ q.2 = 1 ∨ q.1 + q.2 = n + 1) ∧ (l.1 * (q.1 : ℝ) + l.2 = (q.2 : ℝ))) := (Finset.mem_filter.mp h24).2
    exact h25.2
  have h33 : l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ) := by
    have h34 : (r ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := hr
    have h35 : ( (r.1 = 1 ∨ r.2 = 1 ∨ r.1 + r.2 = n + 1) ∧ (l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ))) := (Finset.mem_filter.mp h34).2
    exact h35.2
  norm_num [hp1, hq2] at h13 h23
  have h13' : l.1 + l.2 = (p.2 : ℝ) := by simpa using h13
  have h23' : l.1 * (q.1 : ℝ) + l.2 = 1 := by simpa using h23
  have h4 : l.1 * ((q.1 : ℝ) - 1) = 1 - (p.2 : ℝ) := by linarith
  have h5 : q.1 ≥ 1 := h22.1
  have h6 : p.2 ≥ 1 := h12_original.2.1
  have h7 : (p.2 : ℝ) ≥ 1 := by exact_mod_cast h6
  have h8 : 1 - (p.2 : ℝ) ≤ 0 := by linarith
  have h9 : l.1 * ((q.1 : ℝ) - 1) ≤ 0 := by linarith [h4, h8]
  by_cases h10 : q.1 = 1
  · -- Case 1: q.1 = 1
    have h10' : (q.1 : ℝ) = 1 := by exact_mod_cast h10
    have h11 : l.1 * ((q.1 : ℝ) - 1) = 0 := by
      rw [h10']
      ring
    have h12 : 1 - (p.2 : ℝ) = 0 := by linarith [h4, h11]
    have h13 : (p.2 : ℝ) = 1 := by linarith
    have h14 : p.2 = 1 := by exact_mod_cast h13
    have h15 : p.1 = 1 := hp1
    have h16 : p = (1, 1) := by
      ext <;> simp [h15, h14] <;> aesop
    have h17 : q.1 = 1 := h10
    have h18 : q.2 = 1 := hq2
    have h19 : q = (1, 1) := by
      ext <;> simp [h17, h18] <;> aesop
    have h20 : p = q := by rw [h16, h19]
    contradiction
  · -- Case 2: q.1 ≠ 1
    have h10' : q.1 > 1 := by omega
    have h10'' : (q.1 : ℝ) - 1 > 0 := by
      have h10''' : (q.1 : ℝ) > 1 := by exact_mod_cast h10'
      linarith
    have h12_ne_0 : l.1 ≠ 0 := h_non_sunny.1
    have h12_ne_neg1 : l.1 ≠ -1 := h_non_sunny.2
    have h19 : p.2 ≥ 1 := h12_original.2.1
    have h20 : p.2 = 1 ∨ p.2 > 1 := by omega
    cases h20 with
    | inl h20 =>
      -- Case p.2 = 1
      have h21 : (p.2 : ℝ) = 1 := by exact_mod_cast h20
      have h22_l1_mul : l.1 * ((q.1 : ℝ) - 1) = 0 := by
        have h23 : l.1 * ((q.1 : ℝ) - 1) = 1 - (p.2 : ℝ) := h4
        rw [h21] at h23
        linarith
      have h24 : (q.1 : ℝ) - 1 ≠ 0 := by linarith
      have h25 : l.1 = 0 := by
        apply mul_left_cancel₀ h24
        linarith
      contradiction
    | inr h20 =>
      -- Case p.2 > 1
      have h21 : p.2 > 1 := h20
      have h22_p2_gt_1 : (p.2 : ℝ) > 1 := by exact_mod_cast h21
      have h23 : 1 - (p.2 : ℝ) < 0 := by linarith
      have h24 : l.1 * ((q.1 : ℝ) - 1) < 0 := by linarith [h4, h23]
      have h25 : l.1 < 0 := by nlinarith
      have h33' : l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ) := h33
      have h14 : (r.1 : ℝ) + (r.2 : ℝ) = (n : ℝ) + 1 := by
        have h141 : (r.1 : ℝ) + (r.2 : ℝ) = ((r.1 + r.2 : ℕ) : ℝ) := by norm_cast
        have h142 : r.1 + r.2 = n + 1 := hr3
        have h143 : ((r.1 + r.2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by rw [h142]
        have h144 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
        linarith
      have h15 : l.1 * (r.1 : ℝ) - l.1 + (p.2 : ℝ) = (r.2 : ℝ) := by
        have h151 : l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ) := h33'
        have h152 : l.1 + l.2 = (p.2 : ℝ) := h13'
        nlinarith
      have h16 : l.1 * ((r.1 : ℝ) - 1) + (p.2 : ℝ) = (r.2 : ℝ) := by linarith
      by_cases h17 : p.2 = r.2
      · -- Case 1: p.2 = r.2
        have h17' : (p.2 : ℝ) = (r.2 : ℝ) := by exact_mod_cast h17
        have h18 : l.1 * ((r.1 : ℝ) - 1) = 0 := by linarith [h16, h17']
        have h19 : (r.1 : ℝ) - 1 = 0 := by
          have h191 : l.1 * ((r.1 : ℝ) - 1) = 0 := h18
          have h192 : l.1 ≠ 0 := h12_ne_0
          have h193 : (r.1 : ℝ) - 1 = 0 := by
            apply mul_left_cancel₀ h192
            linarith
          exact h193
        have h20 : (r.1 : ℝ) = 1 := by linarith
        have h21 : r.1 = 1 := by exact_mod_cast h20
        have h22 : r.2 = n := by omega
        have h23 : p.2 = n := by linarith [h17, h22]
        have h24 : p.1 = 1 := hp1
        have h25 : p = (1, n) := by
          ext <;> simp [h24, h23] <;> aesop
        have h26 : r.1 = 1 := h21
        have h27 : r.2 = n := h22
        have h28 : r = (1, n) := by
          ext <;> simp [h26, h27] <;> aesop
        have h29 : p = r := by rw [h25, h28]
        contradiction
      · -- Case 2: p.2 ≠ r.2
        by_cases h17' : q.2 = r.2
        · -- Case 2.1: q.2 = r.2
          have h17'' : q.2 = r.2 := h17'
          have h17''' : q.2 = 1 := hq2
          have h17'''' : r.2 = 1 := by linarith
          have h20 : r.1 = n := by omega
          have h21 : l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ) := h33
          have h22 : (r.1 : ℝ) = (n : ℝ) := by exact_mod_cast h20
          have h23 : (r.2 : ℝ) = 1 := by exact_mod_cast h17''''
          have h24 : l.1 * (n : ℝ) + l.2 = 1 := by
            rw [h22, h23] at h21
            linarith
          have h25 : l.1 * (q.1 : ℝ) + l.2 = 1 := by simpa using h23'
          have h26 : l.1 + l.2 = (p.2 : ℝ) := h13'
          have h27 : l.1 * (n : ℝ) + l.2 - (l.1 + l.2) = 1 - (p.2 : ℝ) := by linarith
          have h28 : l.1 * (n : ℝ) - l.1 = 1 - (p.2 : ℝ) := by linarith
          have h29 : l.1 * ((n : ℝ) - 1) = 1 - (p.2 : ℝ) := by linarith
          have h30 : l.1 * ((q.1 : ℝ) - 1) = 1 - (p.2 : ℝ) := by linarith
          have h31 : l.1 * ((q.1 : ℝ) - 1) = l.1 * ((n : ℝ) - 1) := by linarith
          have h32 : (q.1 : ℝ) - 1 = (n : ℝ) - 1 := by
            have h321 : l.1 * ((q.1 : ℝ) - 1) = l.1 * ((n : ℝ) - 1) := h31
            have h322 : l.1 ≠ 0 := h12_ne_0
            have h323 : (q.1 : ℝ) - 1 = (n : ℝ) - 1 := by
              apply mul_left_cancel₀ h322
              linarith
            exact h323
          have h33 : (q.1 : ℝ) = (n : ℝ) := by linarith
          have h34 : q.1 = n := by exact_mod_cast h33
          have h35 : q.2 = 1 := hq2
          have h36 : q = (n, 1) := by
            ext <;> simp [h34, h35] <;> aesop
          have h37 : r.1 = n := h20
          have h38 : r.2 = 1 := h17''''
          have h39 : r = (n, 1) := by
            ext <;> simp [h37, h38] <;> aesop
          have h40 : q = r := by rw [h36, h39]
          contradiction
        · -- Case 2.2: q.2 ≠ r.2
          have h26 : r.2 ≥ 2 := by
            have h261 : r.2 ≥ 1 := h32.2.1
            have h262 : q.2 ≠ r.2 := h17'
            have h263 : q.2 = 1 := hq2
            have h264 : 1 ≠ r.2 := by
              rw [h263] at h262
              exact h262
            omega
          by_cases h31 : r.1 = 1
          · -- Subcase: r.1 = 1
            have h31' : (r.1 : ℝ) = 1 := by exact_mod_cast h31
            have h32 : (r.1 : ℝ) - 1 = 0 := by linarith
            have h33 : l.1 * ((r.1 : ℝ) - 1) = 0 := by
              rw [h32]
              <;> ring
            have h34 : (r.2 : ℝ) - (p.2 : ℝ) = 0 := by linarith [h16, h33]
            have h35 : (r.2 : ℝ) = (p.2 : ℝ) := by linarith
            have h36 : r.2 = p.2 := by exact_mod_cast h35
            have h37 : p.2 = r.2 := by linarith
            contradiction
          · -- Subcase: r.1 ≠ 1
            have h31' : r.1 ≥ 2 := by omega
            have h31'' : (r.1 : ℝ) ≥ 2 := by exact_mod_cast h31'
            have h31''' : (r.1 : ℝ) - 1 > 0 := by linarith
            by_cases h50 : l.1 < -1
            · -- Case 1: l.1 < -1
              have h51 : l.1 * ((r.1 : ℝ) - 1) < -1 * ((r.1 : ℝ) - 1) := by nlinarith
              have h52 : (r.2 : ℝ) - (p.2 : ℝ) < - (r.1 : ℝ) + 1 := by
                have h521 : l.1 * ((r.1 : ℝ) - 1) = (r.2 : ℝ) - (p.2 : ℝ) := by linarith
                linarith
              have h522 : (r.1 : ℝ) + (r.2 : ℝ) - (p.2 : ℝ) - 1 < 0 := by linarith
              have h523 : (n : ℝ) + 1 - (p.2 : ℝ) - 1 < 0 := by linarith [h14, h522]
              have h524 : (n : ℝ) < (p.2 : ℝ) := by linarith
              have h531 : p.2 ≤ n := by linarith [h12_original.2.2]
              have h53 : (p.2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h531
              linarith
            · -- Case 2: l.1 ≥ -1
              have h50' : l.1 > -1 := by
                by_contra h501
                have h502 : l.1 ≤ -1 := by linarith
                have h503 : l.1 = -1 := by linarith
                contradiction
              have h54 : l.1 * ((q.1 : ℝ) - (r.1 : ℝ)) = 1 - (r.2 : ℝ) := by
                have h541 : l.1 * (q.1 : ℝ) + l.2 = 1 := by simpa using h23'
                have h542 : l.1 * (r.1 : ℝ) + l.2 = (r.2 : ℝ) := by simpa using h33
                have h : l.1 * (q.1 : ℝ) + l.2 - (l.1 * (r.1 : ℝ) + l.2) = 1 - (r.2 : ℝ) := by linarith
                have h' : l.1 * (q.1 : ℝ) - l.1 * (r.1 : ℝ) = 1 - (r.2 : ℝ) := by linarith
                have h'' : l.1 * ((q.1 : ℝ) - (r.1 : ℝ)) = 1 - (r.2 : ℝ) := by
                  linarith
                linarith
              have h55 : (q.1 : ℝ) > (r.1 : ℝ) := by
                have h545 : l.1 * ((q.1 : ℝ) - (r.1 : ℝ)) = 1 - (r.2 : ℝ) := h54
                have h546 : (r.2 : ℝ) ≥ 2 := by exact_mod_cast h26
                have h547 : 1 - (r.2 : ℝ) ≤ -1 := by linarith
                have h548 : l.1 * ((q.1 : ℝ) - (r.1 : ℝ)) ≤ -1 := by linarith
                nlinarith
              have h55' : (q.1 : ℝ) - (r.1 : ℝ) > 0 := by linarith
              have h56 : l.1 * ((q.1 : ℝ) - (r.1 : ℝ)) > -1 * ((q.1 : ℝ) - (r.1 : ℝ)) := by nlinarith
              have h57 : (q.1 : ℝ) + 1 > (r.1 : ℝ) + (r.2 : ℝ) := by linarith [h54, h56]
              have h58 : (q.1 : ℝ) > (n : ℝ) := by linarith [h14, h57]
              have h59 : q.1 > n := by exact_mod_cast h58
              have h22_part3 : q.1 + q.2 ≤ n + 1 := h22.2.2
              have h60 : q.1 ≤ n := by omega
              linarith

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_final (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (p q r : ℕ × ℕ)
  (hp : p ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hq : q ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hr : r ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points))
  (hp1 : p.1 = 1)
  (hq2 : q.2 = 1)
  (hr3 : r.1 + r.2 = n + 1)
  (hpq : p ≠ q)
  (hpr : p ≠ r)
  (hqr : q ≠ r)
  (hn : 3 ≤ n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) :
  False := by
  exact non_sunny_lines_cover_at_most_2_points_on_boundary_main n k verts lines points l h_non_sunny p q r hp hq hr hp1 hq2 hr3 hpq hpr hqr hn hallpoints

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (p q r : ℕ × ℕ)
  (hp : p ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points))
  (hq : q ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points))
  (hr : r ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points))
  (hp1 : p.1 = 1)
  (hq2 : q.2 = 1)
  (hr3 : r.1 + r.2 = n + 1)
  (hpq : p ≠ q)
  (hpr : p ≠ r)
  (hqr : q ≠ r)
  (hn : 3 ≤ n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) :
  False := by

    have h1 : p ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := by simpa using hp
    have h2 : q ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := by simpa using hq
    have h3 : r ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ))) points) := by simpa using hr
    exact non_sunny_lines_cover_at_most_2_points_on_boundary_final n k verts lines points l h_non_sunny p q r h1 h2 h3 hp1 hq2 hr3 hpq hpr hqr hn hallpoints


lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_final (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (h_main : ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z):
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  by_contra h
  have h₁ : (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card > 2 := by linarith
  have h₂ : ∃ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
    have h₃ : (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card > 2 := h₁
    have h₄ : ∃ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      exact?
    exact h₄
  rcases h₂ with ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  have h₃ := h_main x y z hx hy hz
  tauto

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1):
  ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z := by
  intros x y z hx hy hz
  by_cases h1 : x = y
  · tauto
  by_cases h2 : x = z
  · tauto
  by_cases h3 : y = z
  · tauto
  have h1' : x ≠ y := by tauto
  have h2' : x ≠ z := by tauto
  have h3' : y ≠ z := by tauto
  have hx_prop : (x.1 = 1 ∨ x.2 = 1 ∨ x.1 + x.2 = n + 1) ∧ (l.1 * (x.1 : ℝ) + l.2 = (x.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hx
    tauto
  have hy_prop : (y.1 = 1 ∨ y.2 = 1 ∨ y.1 + y.2 = n + 1) ∧ (l.1 * (y.1 : ℝ) + l.2 = (y.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hy
    tauto
  have hz_prop : (z.1 = 1 ∨ z.2 = 1 ∨ z.1 + z.2 = n + 1) ∧ (l.1 * (z.1 : ℝ) + l.2 = (z.2 : ℝ)) := by
    simp only [Finset.mem_filter] at hz
    tauto
  have hx_cond : x.1 = 1 ∨ x.2 = 1 ∨ x.1 + x.2 = n + 1 := hx_prop.1
  have hy_cond : y.1 = 1 ∨ y.2 = 1 ∨ y.1 + y.2 = n + 1 := hy_prop.1
  have hz_cond : z.1 = 1 ∨ z.2 = 1 ∨ z.1 + z.2 = n + 1 := hz_prop.1
  rcases hx_cond with (hx1 | hx2 | hx3)
  · -- Case x.1 = 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto
    · -- Subcase y.2 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_z_eq_x : z = x := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny z x hz_prop hx_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny x y z hx hy hz hx1 hy2 hz3 h1' (by tauto) (by tauto) hn hallpoints
    · -- Subcase y.1 + y.2 = n + 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_z_eq_x : z = x := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny z x hz_prop hx_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny x z y hx hz hy hx1 hz2 hy3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
  · -- Case x.2 = 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny y x z hy hx hz hy1 hx2 hz3 (by tauto) (by tauto) (by tauto) hn hallpoints
    · -- Subcase y.2 = 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto
    · -- Subcase y.1 + y.2 = n + 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny z x y hz hx hy hz1 hx2 hy3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.2 = 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
  · -- Case x.1 + x.2 = n + 1
    rcases hy_cond with (hy1 | hy2 | hy3)
    · -- Subcase y.1 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.2 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny y z x hy hz hx hy1 hz2 hx3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
    · -- Subcase y.2 = 1
      rcases hz_cond with (hz1 | hz2 | hz3)
      · -- Sub-subcase z.1 = 1
        exfalso
        exact non_sunny_lines_cover_at_most_2_points_on_boundary_contradiction_from_conditions n k verts lines points l h_non_sunny z y x hz hy hx hz1 hy2 hx3 (by tauto) (by tauto) (by tauto) hn hallpoints
      · -- Sub-subcase z.2 = 1
        have h_y_eq_z : y = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny y z hy_prop hz_prop
          tauto
        tauto
      · -- Sub-subcase z.1 + z.2 = n + 1
        have h_x_eq_z : x = z := by
          apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x z hx_prop hz_prop
          tauto
        tauto
    · -- Subcase y.1 + y.2 = n + 1
      have h_x_eq_y : x = y := by
        apply non_sunny_lines_cover_at_most_2_points_on_boundary_same_boundary_condition_implies_eq n l points hn h_non_sunny x y hx_prop hy_prop
        tauto
      tauto

theorem non_sunny_lines_cover_at_most_2_points_on_boundary (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (l : ℝ × ℝ) (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧
    (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2   := by

  have h_main : ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z := by
    exact non_sunny_lines_cover_at_most_2_points_on_boundary_h_main n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny

  exact non_sunny_lines_cover_at_most_2_points_on_boundary_h_final n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny h_main

lemma round1_case_l1_eq_0 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n) (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1))
  (h10 : l.1 = 0) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  have h11 : l.2 ≠ 1 := by
    have h111 : ¬ (l.1 = 0 ∧ l.2 = 1) := h_non_boundary.1
    intro h112
    have h113 : l.1 = 0 := by linarith
    have h114 : l.1 = 0 ∧ l.2 = 1 := ⟨h113, by linarith⟩
    contradiction
  set S := Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points with hS
  have h14 : ∀ p ∈ S, p.2 ≠ 1 := by
    intro p hp
    have h141 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h142 : l.1 * p.1 + l.2 = (p.2 : ℝ) := by simpa using h141.2
    have h143 : l.1 = 0 := h10
    rw [h143] at h142
    have h144 : (0 : ℝ) * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by simpa using h142
    have h145 : l.2 = (p.2 : ℝ) := by linarith
    by_contra h146
    have h147 : p.2 = 1 := by omega
    have h148 : (p.2 : ℝ) = 1 := by exact_mod_cast h147
    have h149 : l.2 = 1 := by linarith
    contradiction
  have h15 : ∀ p ∈ S, p.1 = 1 ∨ p.1 + p.2 = n + 1 := by
    intro p hp
    have h151 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h152 : p.2 ≠ 1 := h14 p hp
    have h153 : p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1 := h151.1
    rcases h153 with (h153 | h153 | h153)
    · exact Or.inl h153
    · exfalso
      exact h152 h153
    · exact Or.inr h153
  have h16 : ∀ p ∈ S, l.2 = (p.2 : ℝ) := by
    intro p hp
    have h161 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h162 : l.1 * p.1 + l.2 = (p.2 : ℝ) := h161.2
    have h163 : l.1 = 0 := h10
    rw [h163] at h162
    have h164 : (0 : ℝ) * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by simpa using h162
    linarith
  set A := S.filter (fun p ↦ p.1 = 1) with hA
  set B := S.filter (fun p ↦ p.1 + p.2 = n + 1) with hB
  have h17 : ∀ p ∈ S, p ∈ A ∨ p ∈ B := by
    intro p hp
    have h171 : p.1 = 1 ∨ p.1 + p.2 = n + 1 := h15 p hp
    rcases h171 with (h171 | h171)
    · -- p.1 = 1
      have h172 : p ∈ A := by
        simp [hA, Finset.mem_filter]
        <;> tauto
      exact Or.inl h172
    · -- p.1 + p.2 = n + 1
      have h172 : p ∈ B := by
        simp [hB, Finset.mem_filter]
        <;> tauto
      exact Or.inr h172
  have h18 : S ⊆ A ∪ B := by
    intro p hp
    have h181 : p ∈ A ∨ p ∈ B := h17 p hp
    cases h181 with
    | inl h181 =>
      exact Finset.mem_union_left B h181
    | inr h181 =>
      exact Finset.mem_union_right A h181
  have h19 : A.card ≤ 1 := by
    have h191 : ∀ p ∈ A, ∀ q ∈ A, p = q := by
      intro p hp q hq
      have hp1 : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq1 : q ∈ S := (Finset.mem_filter.mp hq).1
      have hp2 : p.1 = 1 := (Finset.mem_filter.mp hp).2
      have hq2 : q.1 = 1 := (Finset.mem_filter.mp hq).2
      have h192 : l.2 = (p.2 : ℝ) := h16 p hp1
      have h193 : l.2 = (q.2 : ℝ) := h16 q hq1
      have h194 : (p.2 : ℝ) = (q.2 : ℝ) := by linarith
      have h195 : p.2 = q.2 := by exact_mod_cast h194
      have h196 : p.1 = q.1 := by simp [hp2, hq2]
      have h197 : p = q := by
        ext <;> tauto
      exact h197
    have h198 : A.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      exact h191 p hp q hq
    exact h198
  have h20 : B.card ≤ 1 := by
    have h201 : ∀ p ∈ B, ∀ q ∈ B, p = q := by
      intro p hp q hq
      have hp1 : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq1 : q ∈ S := (Finset.mem_filter.mp hq).1
      have hp2 : p.1 + p.2 = n + 1 := (Finset.mem_filter.mp hp).2
      have hq2 : q.1 + q.2 = n + 1 := (Finset.mem_filter.mp hq).2
      have h202 : l.2 = (p.2 : ℝ) := h16 p hp1
      have h203 : l.2 = (q.2 : ℝ) := h16 q hq1
      have h204 : (p.2 : ℝ) = (q.2 : ℝ) := by linarith
      have h205 : p.2 = q.2 := by exact_mod_cast h204
      have h206 : (p.1 : ℕ) + p.2 = n + 1 := by simpa using hp2
      have h207 : (q.1 : ℕ) + q.2 = n + 1 := by simpa using hq2
      have h208 : p.1 = q.1 := by omega
      have h209 : p = q := by
        ext <;> tauto
      exact h209
    have h208 : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      exact h201 p hp q hq
    exact h208
  have h21 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have h22 : S.card ≤ (A ∪ B).card := Finset.card_le_card h18
  linarith

lemma round1_case_l1_eq_neg1 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n) (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1))
  (h12 : l.1 = -1) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  have h13 : l.2 ≠ (n : ℝ) + 1 := by
    have h131 : ¬ (l.1 = -1 ∧ l.2 = (n : ℝ) + 1) := h_non_boundary.2
    intro h132
    have h133 : l.1 = -1 := by linarith
    have h134 : l.1 = -1 ∧ l.2 = (n : ℝ) + 1 := ⟨h133, by linarith⟩
    contradiction
  set S := Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points with hS
  have h14 : ∀ p ∈ S, p.1 + p.2 ≠ n + 1 := by
    intro p hp
    have h141 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h142 : l.1 * p.1 + l.2 = (p.2 : ℝ) := h141.2
    have h143 : l.1 = -1 := h12
    rw [h143] at h142
    have h144 : (-1 : ℝ) * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by simpa using h142
    have h145 : l.2 = (p.1 : ℝ) + (p.2 : ℝ) := by linarith
    by_contra h146
    have h147 : p.1 + p.2 = n + 1 := by tauto
    have h148 : (p.1 : ℝ) + (p.2 : ℝ) = (n : ℝ) + 1 := by exact_mod_cast h147
    have h149 : l.2 = (n : ℝ) + 1 := by linarith
    contradiction
  have h15 : ∀ p ∈ S, p.1 = 1 ∨ p.2 = 1 := by
    intro p hp
    have h151 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h152 : p.1 + p.2 ≠ n + 1 := h14 p hp
    have h153 : p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1 := h151.1
    rcases h153 with (h153 | h153 | h153)
    · exact Or.inl h153
    · exact Or.inr h153
    · contradiction
  have h16 : ∀ p ∈ S, l.2 = (p.1 : ℝ) + (p.2 : ℝ) := by
    intro p hp
    have h161 : (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2) := (Finset.mem_filter.mp hp).2
    have h162 : l.1 * p.1 + l.2 = (p.2 : ℝ) := h161.2
    have h163 : l.1 = -1 := h12
    rw [h163] at h162
    have h164 : (-1 : ℝ) * (p.1 : ℝ) + l.2 = (p.2 : ℝ) := by simpa using h162
    linarith
  set A := S.filter (fun p ↦ p.1 = 1) with hA
  set B := S.filter (fun p ↦ p.2 = 1) with hB
  have h17 : ∀ p ∈ S, p ∈ A ∨ p ∈ B := by
    intro p hp
    have h171 : p.1 = 1 ∨ p.2 = 1 := h15 p hp
    rcases h171 with (h171 | h171)
    · -- p.1 = 1
      have h172 : p ∈ A := by
        simp [hA, Finset.mem_filter]
        <;> tauto
      exact Or.inl h172
    · -- p.2 = 1
      have h172 : p ∈ B := by
        simp [hB, Finset.mem_filter]
        <;> tauto
      exact Or.inr h172
  have h18 : S ⊆ A ∪ B := by
    intro p hp
    have h181 : p ∈ A ∨ p ∈ B := h17 p hp
    cases h181 with
    | inl h181 =>
      exact Finset.mem_union_left B h181
    | inr h181 =>
      exact Finset.mem_union_right A h181
  have h19 : A.card ≤ 1 := by
    have h191 : ∀ p ∈ A, ∀ q ∈ A, p = q := by
      intro p hp q hq
      have hp1 : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq1 : q ∈ S := (Finset.mem_filter.mp hq).1
      have hp2 : p.1 = 1 := (Finset.mem_filter.mp hp).2
      have hq2 : q.1 = 1 := (Finset.mem_filter.mp hq).2
      have h192 : l.2 = (p.1 : ℝ) + (p.2 : ℝ) := h16 p hp1
      have h193 : l.2 = (q.1 : ℝ) + (q.2 : ℝ) := h16 q hq1
      have h194 : (p.1 : ℝ) = 1 := by exact_mod_cast hp2
      have h195 : (q.1 : ℝ) = 1 := by exact_mod_cast hq2
      rw [h194] at h192
      rw [h195] at h193
      have h196 : (1 : ℝ) + (p.2 : ℝ) = l.2 := by linarith
      have h197 : (1 : ℝ) + (q.2 : ℝ) = l.2 := by linarith
      have h198 : (p.2 : ℝ) = (q.2 : ℝ) := by linarith
      have h199 : p.2 = q.2 := by exact_mod_cast h198
      have h200 : p.1 = q.1 := by simp [hp2, hq2]
      have h201 : p = q := by
        ext <;> tauto
      exact h201
    have h198 : A.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      exact h191 p hp q hq
    exact h198
  have h20 : B.card ≤ 1 := by
    have h201 : ∀ p ∈ B, ∀ q ∈ B, p = q := by
      intro p hp q hq
      have hp1 : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq1 : q ∈ S := (Finset.mem_filter.mp hq).1
      have hp2 : p.2 = 1 := (Finset.mem_filter.mp hp).2
      have hq2 : q.2 = 1 := (Finset.mem_filter.mp hq).2
      have h202 : l.2 = (p.1 : ℝ) + (p.2 : ℝ) := h16 p hp1
      have h203 : l.2 = (q.1 : ℝ) + (q.2 : ℝ) := h16 q hq1
      have h204 : (p.2 : ℝ) = 1 := by exact_mod_cast hp2
      have h205 : (q.2 : ℝ) = 1 := by exact_mod_cast hq2
      rw [h204] at h202
      rw [h205] at h203
      have h206 : (p.1 : ℝ) + 1 = l.2 := by linarith
      have h207 : (q.1 : ℝ) + 1 = l.2 := by linarith
      have h208 : (p.1 : ℝ) = (q.1 : ℝ) := by linarith
      have h209 : p.1 = q.1 := by exact_mod_cast h208
      have h210 : p.2 = q.2 := by simp [hp2, hq2]
      have h211 : p = q := by
        ext <;> tauto
      exact h211
    have h208 : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      exact h201 p hp q hq
    exact h208
  have h21 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have h22 : S.card ≤ (A ∪ B).card := Finset.card_le_card h18
  linarith

theorem line_not_boundary_covers_at_most_2_boundary_points (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1)) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧
    (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2   := by

  by_cases h1 : l.1 ≠ 0 ∧ l.1 ≠ -1
  · -- Case 1: l.1 ≠ 0 ∧ l.1 ≠ -1
    have h2 : l.1 ≠ 0 ∧ l.1 ≠ -1 := h1
    exact non_sunny_lines_cover_at_most_2_points_on_boundary n k verts lines points hn hcard hallpoints hmain hk l h2
  · -- Case 2: ¬ (l.1 ≠ 0 ∧ l.1 ≠ -1)
    have h1' : l.1 = 0 ∨ l.1 = -1 := by
      by_cases h11 : l.1 = 0
      · exact Or.inl h11
      · -- Case l.1 ≠ 0
        by_cases h12 : l.1 = -1
        · exact Or.inr h12
        · exfalso
          have h13 : l.1 ≠ 0 := h11
          have h14 : l.1 ≠ -1 := h12
          have h15 : l.1 ≠ 0 ∧ l.1 ≠ -1 := ⟨h13, h14⟩
          contradiction
    cases h1' with
    | inl h10 =>
      -- Subcase 2.1: l.1 = 0
      exact round1_case_l1_eq_0 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary h10
    | inr h12 =>
      -- Subcase 2.2: l.1 = -1
      exact round1_case_l1_eq_neg1 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary h12

lemma vert_line_covers_at_most_two_boundary_points (n : ℕ)
  (points : Finset (ℕ × ℕ))
  (x : ℝ)
  (hx_neq1 : x ≠ 1):
  (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
  have h1 : ∀ (p : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p.1 ≠ 1 := by
    intro p hp
    have h1₁ : (p.1 : ℝ) = x := by
      simp only [Finset.mem_filter] at hp
      tauto
    by_contra h1₂
    have h1₃ : p.1 = 1 := h1₂
    have h1₄ : (p.1 : ℝ) = 1 := by exact_mod_cast h1₃
    have h1₅ : x = 1 := by linarith
    contradiction
  have h2 : ∀ (p : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p.2 = 1 ∨ p.1 + p.2 = n + 1 := by
    intro p hp
    have h2₁ : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x) := by
      simp only [Finset.mem_filter] at hp
      tauto
    have h2₂ : p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1 := h2₁.2.2.2.1
    have h2₃ : p.1 ≠ 1 := h1 p hp
    tauto
  have h3 : ∀ (p q : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → q ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p.1 = q.1 := by
    intro p q hp hq
    have h3₁ : (p.1 : ℝ) = x := by
      simp only [Finset.mem_filter] at hp
      tauto
    have h3₂ : (q.1 : ℝ) = x := by
      simp only [Finset.mem_filter] at hq
      tauto
    have h3₃ : (p.1 : ℝ) = (q.1 : ℝ) := by linarith
    norm_cast at h3₃ ⊢
    <;> linarith
  have h4 : ∃ (m : ℕ), ∀ (p : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p.1 = m := by
    by_cases h4₁ : (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).Nonempty
    · rcases h4₁ with ⟨p₀, hp₀⟩
      refine' ⟨p₀.1, _⟩
      intro p hp
      have h4₂ : p.1 = p₀.1 := h3 p p₀ hp hp₀
      linarith
    · refine' ⟨0, _⟩
      intro p hp
      exfalso
      have h4₂ : ¬(Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).Nonempty := by simpa using h4₁
      have h4₃ : p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) := hp
      have h4₄ : (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).Nonempty := ⟨p, h4₃⟩
      contradiction
  rcases h4 with ⟨m, hm⟩
  have h5 : ∀ (p : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p.2 = 1 ∨ p.2 = n + 1 - p.1 := by
    intro p hp
    have h5₁ : p.2 = 1 ∨ p.1 + p.2 = n + 1 := h2 p hp
    cases h5₁ with
    | inl h5₁ =>
      exact Or.inl h5₁
    | inr h5₁ =>
      have h5₂ : p.1 + p.2 = n + 1 := h5₁
      have h5₃ : p.2 = n + 1 - p.1 := by omega
      exact Or.inr h5₃
  have h6 : ∀ (p : ℕ × ℕ), p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) → p = (m, 1) ∨ p = (m, n + 1 - m) := by
    intro p hp
    have h6₁ : p.1 = m := hm p hp
    have h6₂ : p.2 = 1 ∨ p.2 = n + 1 - p.1 := h5 p hp
    cases h6₂ with
    | inl h6₂ =>
      have h6₃ : p.2 = 1 := h6₂
      have h6₄ : p = (m, 1) := by
        ext <;> simp [h6₁, h6₃] <;> aesop
      exact Or.inl h6₄
    | inr h6₂ =>
      have h6₃ : p.2 = n + 1 - p.1 := h6₂
      have h6₄ : p.2 = n + 1 - m := by
        rw [h6₁] at h6₃
        linarith
      have h6₅ : p = (m, n + 1 - m) := by
        ext <;> simp [h6₁, h6₄] <;> aesop
      exact Or.inr h6₅
  have h7 : (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) ⊆ ({(m, 1), (m, n + 1 - m)} : Finset (ℕ × ℕ)) := by
    intro p hp
    have h7₁ : p = (m, 1) ∨ p = (m, n + 1 - m) := h6 p hp
    cases h7₁ with
    | inl h7₁ =>
      simp [h7₁]
      <;> aesop
    | inr h7₁ =>
      simp [h7₁]
      <;> aesop
  have h8 : (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ ({(m, 1), (m, n + 1 - m)} : Finset (ℕ × ℕ)).card := by
    apply Finset.card_le_card
    exact h7
  have h9 : ({(m, 1), (m, n + 1 - m)} : Finset (ℕ × ℕ)).card ≤ 2 := by
    have h9₁ : ({(m, 1), (m, n + 1 - m)} : Finset (ℕ × ℕ)).card ≤ 2 := by
      cases' Classical.em ((m, 1) = (m, n + 1 - m)) with h h <;> simp [h] <;> norm_num
      <;> aesop
    exact h9₁
  linarith

lemma total_boundary_points_covered_by_at_most_2n_h1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)):
  ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1) := by
  intro l hl
  have h11 : ¬ (l.1 = 0 ∧ l.2 = 1) := h_not_y1 l hl
  have h12 : ¬ (l.1 = -1 ∧ l.2 = n + 1) := h_not_xn1 l hl
  exact ⟨h11, h12⟩

lemma total_boundary_points_covered_by_at_most_2n_h2 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1))
  (h1 : ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1)):
  ∀ l ∈ lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  intro l hl
  have h5 : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1) := h1 l hl
  exact line_not_boundary_covers_at_most_2_boundary_points n k verts lines points hn hcard hallpoints hmain hk l h5

lemma total_boundary_points_covered_by_at_most_2n_h3 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_not_v1 : 1 ∉ verts):
  ∀ x ∈ verts, x ≠ 1 := by
  intro x hx
  by_contra h
  have h6 : x = 1 := by linarith
  rw [h6] at hx
  contradiction

lemma total_boundary_points_covered_by_at_most_2n_h4 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h3 : ∀ x ∈ verts, x ≠ 1):
  ∀ x ∈ verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
  intro x hx
  have hx_neq1 : x ≠ 1 := h3 x hx
  exact vert_line_covers_at_most_two_boundary_points n points x hx_neq1

lemma total_boundary_points_covered_by_at_most_2n_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1))
  (h2 : ∀ l ∈ lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2)
  (h4 : ∀ x ∈ verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2):
  (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ 2 * n := by
  set LinesCoveredPoints : Finset (ℕ × ℕ) := Finset.biUnion lines (fun l => Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) with hLinesCoveredPoints
  set VerticesCoveredPoints : Finset (ℕ × ℕ) := Finset.biUnion verts (fun x => Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) with hVerticesCoveredPoints
  have h11 : LinesCoveredPoints.card ≤ ∑ l in lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card := by
    apply Finset.card_biUnion_le
  have h12 : ∑ l in lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ ∑ l in lines, 2 := by
    apply Finset.sum_le_sum
    intro l hl
    exact h2 l hl
  have h13 : ∑ l in lines, 2 = 2 * lines.card := by
    simp [mul_comm]
    <;>
    ring
  have h14 : LinesCoveredPoints.card ≤ 2 * lines.card := by linarith
  have h21 : VerticesCoveredPoints.card ≤ ∑ x in verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card := by
    apply Finset.card_biUnion_le
  have h22 : ∑ x in verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ ∑ x in verts, 2 := by
    apply Finset.sum_le_sum
    intro x hx
    exact h4 x hx
  have h23 : ∑ x in verts, 2 = 2 * verts.card := by
    simp [mul_comm]
    <;>
    ring
  have h24 : VerticesCoveredPoints.card ≤ 2 * verts.card := by linarith
  have h30 : Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points ⊆ LinesCoveredPoints ∪ VerticesCoveredPoints := by
    intro p hp
    have hp1 : p ∈ points := by
      simp only [Finset.mem_filter] at hp
      tauto
    have h31 : (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x) := hmain p hp1
    cases h31 with
    | inl h311 =>
      rcases h311 with ⟨l, hl, h3112⟩
      have h3113 : p ∈ Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points := by
        simp only [Finset.mem_filter] at *
        <;> aesop
      have h3114 : p ∈ LinesCoveredPoints := by
        rw [hLinesCoveredPoints]
        simp only [Finset.mem_biUnion]
        refine ⟨l, hl, h3113⟩
      exact Finset.mem_union_left VerticesCoveredPoints h3114
    | inr h312 =>
      rcases h312 with ⟨x, hx, h3122⟩
      have hp2 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 := by
        have h3123 : p ∈ points := hp1
        have h3124 := (hallpoints p).mp h3123
        tauto
      have hp3 : p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1 := by
        simp only [Finset.mem_filter] at hp
        tauto
      have h3125 : p ∈ Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points := by
        simp only [Finset.mem_filter] at *
        <;> aesop
      have h3126 : p ∈ VerticesCoveredPoints := by
        rw [hVerticesCoveredPoints]
        simp only [Finset.mem_biUnion]
        refine ⟨x, hx, h3125⟩
      exact Finset.mem_union_right LinesCoveredPoints h3126
  have h32 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ (LinesCoveredPoints ∪ VerticesCoveredPoints).card := by
    apply Finset.card_le_card
    exact h30
  have h33 : (LinesCoveredPoints ∪ VerticesCoveredPoints).card ≤ LinesCoveredPoints.card + VerticesCoveredPoints.card := Finset.card_union_le LinesCoveredPoints VerticesCoveredPoints
  have h34 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ LinesCoveredPoints.card + VerticesCoveredPoints.card := by linarith
  have h35 : LinesCoveredPoints.card + VerticesCoveredPoints.card ≤ 2 * lines.card + 2 * verts.card := by linarith
  have h36 : 2 * lines.card + 2 * verts.card = 2 * (lines.card + verts.card) := by ring
  have h37 : 2 * (lines.card + verts.card) = 2 * n := by
    linarith
  linarith

theorem total_boundary_points_covered_by_at_most_2n (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (h_not_v1 : 1 ∉ verts) (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1)) (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n+1) points).card ≤ 2 * n  := by

  have h1 : ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1) := by
    exact total_boundary_points_covered_by_at_most_2n_h1 n k verts lines points h_not_y1 h_not_xn1
  have h2 : ∀ l ∈ lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
    exact total_boundary_points_covered_by_at_most_2n_h2 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 h1
  have h3 : ∀ x ∈ verts, x ≠ 1 := by
    exact total_boundary_points_covered_by_at_most_2n_h3 n k verts lines points h_not_v1
  have h4 : ∀ x ∈ verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
    exact total_boundary_points_covered_by_at_most_2n_h4 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h3
  have h_main : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ 2 * n := by
    exact total_boundary_points_covered_by_at_most_2n_h_main n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 h2 h4
  exact h_main

lemma boundary_line_exists_at_any_cover_simplified_h_main (n : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 4 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)):
  (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
  by_cases h_neg : (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1))
  · exact h_neg
  · -- Assume the negation of the goal
    have h1 : 1 ∉ verts := by
      by_contra h1_in
      have h1' : ∃ x ∈ verts, x = 1 := ⟨1, h1_in, rfl⟩
      have h1'' : (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := Or.inl h1'
      contradiction
    have h2 : ∀ l ∈ lines, ¬ ((l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
      intro l hl
      by_contra h2_contra
      have h2' : ∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1) := ⟨l, hl, h2_contra⟩
      have h2'' : (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := Or.inr h2'
      contradiction
    have h21 : ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) := by
      intro l hl
      have h21' : ¬ ((l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := h2 l hl
      intro h21_contra
      have h21'' : (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1) := Or.inl h21_contra
      exact h21' h21''
    have h22 : ∀ l ∈ lines, ¬ (l.1 = -1 ∧ l.2 = n + 1) := by
      intro l hl
      have h22' : ¬ ((l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := h2 l hl
      intro h22_contra
      have h22'' : (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1) := Or.inr h22_contra
      exact h22' h22''
    set k := (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card with hk_def
    have hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := rfl
    have h3 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ 2 * n := by
      have h4 : 3 ≤ n := by linarith
      have h5 : 1 ∉ verts := h1
      have h6 : ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) := h21
      have h7 : ∀ l ∈ lines, ¬ (l.1 = -1 ∧ l.2 = n + 1) := h22
      exact total_boundary_points_covered_by_at_most_2n n k verts lines points h4 hcard hallpoints hmain hk h5 h6 h7
    have h4 : n ≠ 1 := by linarith
    have h5 : n ≠ 2 := by linarith
    have h6 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card = 3 * n - 3 := by
      have h61 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card = 3 * n - (if n = 1 then 2 else if n = 2 then 3 else 3) := by
        exact num_points_on_boundary n points hallpoints
      rw [h61]
      have h62 : (if n = 1 then 2 else if n = 2 then 3 else 3) = 3 := by
        split_ifs <;> tauto
      rw [h62]
      <;> omega
    have h7 : 3 * n - 3 > 2 * n := by omega
    have h8 : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card > 2 * n := by
      linarith [h6, h7]
    linarith

theorem boundary_line_exists_at_any_cover_simplified (n : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
    (hn : 4 ≤ n)
    (hcard : lines.card + verts.card = n)
    (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
    (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)):
  (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1))  := by

  have h_main : (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
    exact boundary_line_exists_at_any_cover_simplified_h_main n verts lines points hn hcard hallpoints hmain
  exact h_main

lemma round1_main (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by
  have h : ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, ∀ (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)),
    (hcard : lines.card + verts.card = n) →
    (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) →
    (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) →
    (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) →
    k = 0 ∨ k = 1 ∨ k = 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn3 k verts lines points hcard hallpoints hmain hk
      by_cases h1 : n = 3
      · -- Case 1: n = 3
        subst h1
        exact imo2025_p1_prop_n_eq_3_k_eq_0_1_3 k lines verts points hcard hallpoints hmain hk
      · -- Case 2: n ≠ 3
        have h2 : n ≥ 4 := by omega
        have h4 : (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
          exact boundary_line_exists_at_any_cover_simplified n verts lines points (by linarith) hcard hallpoints hmain
        have hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
          (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := by
          intro p hp
          have h11 : p ∈ points := by
            rw [hallpoints p]
            <;> tauto
          have h12 : (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x) := hmain p h11
          simpa using h12
        have h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
          (verts'.card + lines'.card = n - 1) →
          (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
            (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
          ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
          k' = 0 ∨ k' = 1 ∨ k' = 3 := by
          intro k' verts' lines' h13 h14 h15
          have h16 : n - 1 < n := by omega
          have h17 : 3 ≤ n - 1 := by omega
          set points' : Finset (ℕ × ℕ) := (Finset.Ico 1 (n + 1) ×ˢ Finset.Ico 1 (n + 1)).filter (fun p => p.1 + p.2 ≤ n) with h18
          have h19 : ∀ p : ℕ × ℕ, p ∈ points' ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n := by
            intro p
            simp [h18, Finset.mem_filter, Finset.mem_Ico]
            <;> omega
          have h20 : ∀ p ∈ points', (∃ l ∈ lines', l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts', p.1 = x) := by
            intro p hp
            have h21 : p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n := by
              rw [h19 p] at hp
              tauto
            have h22 := h14 p h21
            simpa using h22
          have h23 : lines'.card + verts'.card = n - 1 := by
            linarith
          have h24 : ∀ p, p ∈ points' ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ (n - 1) + 1 := by
            intro p
            have h25 : (n - 1) + 1 = n := by omega
            rw [h25]
            exact h19 p
          have h26 := ih (n - 1) (by omega) (by omega) k' verts' lines' points' h23 h24 h20 h15
          tauto
        rcases h4 with h41 | h42
        · -- Case 2.1: ∃ x ∈ verts, x = 1
          exact inductive_step_if_contains_vertical_line n k verts lines points hcard hallpoints hmain hk (by linarith) hcover h41 h_ih
        · -- Case 2.2: ∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)
          rcases h42 with ⟨l, hl_in_lines, h421⟩
          rcases h421 with h4211 | h4212
          · -- Subcase 2.2.1: l.1 = 0 ∧ l.2 = 1
            have h42111 : ∃ l' ∈ lines, l'.1 = 0 ∧ l'.2 = 1 := ⟨l, hl_in_lines, by tauto⟩
            exact inductive_step_if_contains_horizontal_line n k verts lines points hcard hallpoints hmain hk (by linarith) hcover h42111 h_ih
          · -- Subcase 2.2.2: l.1 = -1 ∧ l.2 = n + 1
            have h42121 : ∃ l' ∈ lines, l'.1 = -1 ∧ l'.2 = (n : ℝ) + 1 := ⟨l, hl_in_lines, by tauto⟩
            exact inductive_step_if_contains_rainy_diagonal_line_refined n k verts lines points (by linarith) hcard hallpoints hmain hk (by linarith) hcover h42121 h_ih
  exact h n hn k verts lines points hcard hallpoints hmain hk

theorem imo2025_p1_left (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by

  exact round1_main n k verts lines points hn hcard hallpoints hmain hk

#print axioms imo2025_p1_left

lemma round3_k3_card (n : ℕ) (hn : 3 ≤ n) :
  (({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ)).card) = 3 := by
  have h4 : ((-1 / 2, 1 + (n : ℝ) / 2) : ℝ × ℝ) ≠ (1, 3 - (n : ℝ)) := by
    intro h
    have h41 : (-1 / 2 : ℝ) = (1 : ℝ) := by simpa using congrArg Prod.fst h
    norm_num at h41
  have h5 : ((-1 / 2, 1 + (n : ℝ) / 2) : ℝ × ℝ) ≠ (-2, 2 * (n : ℝ) - 1) := by
    intro h
    have h51 : (-1 / 2 : ℝ) = (-2 : ℝ) := by simpa using congrArg Prod.fst h
    norm_num at h51
  have h6 : ((1, 3 - (n : ℝ)) : ℝ × ℝ) ≠ (-2, 2 * (n : ℝ) - 1) := by
    intro h
    have h61 : (1 : ℝ) = (-2 : ℝ) := by simpa using congrArg Prod.fst h
    norm_num at h61
  have h1 : ((-1 / 2, 1 + (n : ℝ) / 2) : ℝ × ℝ) ≠ (1, 3 - (n : ℝ)) := h4
  have h2 : ((-1 / 2, 1 + (n : ℝ) / 2) : ℝ × ℝ) ≠ (-2, 2 * (n : ℝ) - 1) := h5
  have h3 : ((1, 3 - (n : ℝ)) : ℝ × ℝ) ≠ (-2, 2 * (n : ℝ) - 1) := h6
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton, h1, h2, h3]
  <;> aesop

lemma round3_k1_third_cond (n : ℕ) (hn : 3 ≤ n) :
  (Finset.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1) ({(1, 1 - (n : ℝ))} : Finset (ℝ × ℝ))).card = 1 := by
  have h11 : (1 : ℝ) ≠ 0 := by norm_num
  have h12 : (1 : ℝ) ≠ -1 := by norm_num
  have h14 : Finset.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1) ({(1, 1 - (n : ℝ))} : Finset (ℝ × ℝ)) = ({(1, 1 - (n : ℝ))} : Finset (ℝ × ℝ)) := by
    apply Finset.ext
    intro x
    simp [h11, h12]
    <;> aesop
  rw [h14]
  simp

lemma round3_k3_third_cond (n : ℕ) (hn : 3 ≤ n) :
  (Finset.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1) ({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ))).card = 3 := by
  have h1 : (-1 / 2 : ℝ) ≠ 0 := by norm_num
  have h2 : (-1 / 2 : ℝ) ≠ -1 := by norm_num
  have h3 : (1 : ℝ) ≠ 0 := by norm_num
  have h4 : (1 : ℝ) ≠ -1 := by norm_num
  have h5 : (-2 : ℝ) ≠ 0 := by norm_num
  have h6 : (-2 : ℝ) ≠ -1 := by norm_num
  have h14 : Finset.filter (fun l => l.1 ≠ 0 ∧ l.1 ≠ -1) ({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ)) = ({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ)) := by
    apply Finset.ext
    intro x
    simp [h1, h2, h3, h4, h5, h6]
    <;> aesop
  rw [h14]
  exact round3_k3_card n hn

theorem imo2025_p1_right (n k : ℕ) (hn : 3 ≤ n) (hk : k = 0 ∨ k = 1 ∨ k = 3) : ∃ lines : Finset (ℝ × ℝ), ∃ xs : Finset ℝ, lines.card + xs.card = n ∧ (∀ a b : ℕ, a > 0 → b > 0 → a + b ≤ n + 1 → (∃ l ∈ lines, l.1 * a + l.2 = b) ∨ (∃ x ∈ xs, a = x)) ∧ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  rcases hk with (h | h | h)
  · -- Case 1: k = 0
    have h1 : k = 0 := h
    use (∅ : Finset (ℝ × ℝ))
    use (Finset.range n).image (fun (i : ℕ) => (i + 1 : ℝ))
    constructor
    · -- Proof of lines.card + xs.card = n
      have h21 : ((Finset.range n).image (fun (i : ℕ) => (i + 1 : ℝ))).card = n := by
        have h_inj : Function.Injective (fun (i : ℕ) => (i + 1 : ℝ)) := by
          intro i j h
          simp at h
          <;> linarith
        have h211 : ((Finset.range n).image (fun (i : ℕ) => (i + 1 : ℝ))).card = (Finset.range n).card := by
          apply Finset.card_image_of_injective
          exact h_inj
        have h212 : (Finset.range n).card = n := by simp
        linarith
      simp [h21]
      <;> aesop
    constructor
    · -- Proof of the second condition
      intro a b ha_pos hb_pos hab
      have h11 : a ≤ n := by
        omega
      have h12 : a - 1 < n := by omega
      have h13 : (a - 1) ∈ Finset.range n := Finset.mem_range.mpr h12
      have h14 : (( (a - 1 : ℕ) : ℝ) + 1) ∈ (Finset.range n).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
        refine Finset.mem_image.mpr ⟨(a - 1), h13, ?_⟩
        <;> simp [add_comm]
        <;> ring
      have h15 : (( (a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
        simp [Nat.cast_sub (by omega : 0 < a)]
        <;> ring
      have h16 : (a : ℝ) ∈ (Finset.range n).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
        rw [h15] at h14
        exact h14
      refine Or.inr ⟨(a : ℝ), h16, by simp⟩
    · -- Proof of the third condition
      simp [h1]
      <;> aesop
  · -- Case 2: k = 1
    have h1 : k = 1 := h
    use ({(1, 1 - (n : ℝ))} : Finset (ℝ × ℝ))
    use (Finset.range (n - 1)).image (fun (i : ℕ) => (i + 1 : ℝ))
    constructor
    · -- Proof of lines.card + xs.card = n
      have h21 : ((Finset.range (n - 1)).image (fun (i : ℕ) => (i + 1 : ℝ))).card = n - 1 := by
        have h_inj : Function.Injective (fun (i : ℕ) => (i + 1 : ℝ)) := by
          intro i j h
          simp at h
          <;> linarith
        have h211 : ((Finset.range (n - 1)).image (fun (i : ℕ) => (i + 1 : ℝ))).card = (Finset.range (n - 1)).card := by
          apply Finset.card_image_of_injective
          exact h_inj
        have h212 : (Finset.range (n - 1)).card = n - 1 := by simp
        linarith
      have h22 : (({(1, 1 - (n : ℝ))} : Finset (ℝ × ℝ)).card) = 1 := by simp
      omega
    constructor
    · -- Proof of the second condition
      intro a b ha_pos hb_pos hab
      by_cases h17 : a ≤ n - 1
      · -- Case 1: a ≤ n - 1
        have h171 : a ≤ n - 1 := h17
        have h172 : a ≥ 1 := by linarith
        have h173 : a - 1 < n - 1 := by omega
        have h174 : (a - 1) ∈ Finset.range (n - 1) := Finset.mem_range.mpr h173
        have h175 : (( (a - 1 : ℕ) : ℝ) + 1) ∈ (Finset.range (n - 1)).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
          refine Finset.mem_image.mpr ⟨(a - 1), h174, ?_⟩
          <;> simp [add_comm]
          <;> ring
        have h176 : (( (a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
          simp [Nat.cast_sub (by omega : 0 < a)]
          <;> ring
        have h177 : (a : ℝ) ∈ (Finset.range (n - 1)).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
          rw [h176] at h175
          exact h175
        refine Or.inr ⟨(a : ℝ), h177, by simp⟩
      · -- Case 2: ¬ (a ≤ n - 1)
        have h17' : a > n - 1 := by omega
        have h180 : a = n := by omega
        have h181 : b = 1 := by
          have h101 : a + b ≤ n + 1 := hab
          have h102 : a = n := h180
          have h103 : b > 0 := hb_pos
          rw [h102] at h101
          omega
        refine Or.inl ⟨(1, 1 - (n : ℝ)), by simp, ?_⟩
        simp [h180, h181]
        <;> ring_nf <;> norm_num <;> linarith
    · -- Proof of the third condition
      rw [h1]
      exact round3_k1_third_cond n hn
  · -- Case 3: k = 3
    have h1 : k = 3 := h
    use ({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ))
    use (Finset.range (n - 3)).image (fun (i : ℕ) => (i + 1 : ℝ))
    constructor
    · -- Proof of lines.card + xs.card = n
      have h21 : ((Finset.range (n - 3)).image (fun (i : ℕ) => (i + 1 : ℝ))).card = n - 3 := by
        have h_inj : Function.Injective (fun (i : ℕ) => (i + 1 : ℝ)) := by
          intro i j h
          simp at h
          <;> linarith
        have h211 : ((Finset.range (n - 3)).image (fun (i : ℕ) => (i + 1 : ℝ))).card = (Finset.range (n - 3)).card := by
          apply Finset.card_image_of_injective
          exact h_inj
        have h212 : (Finset.range (n - 3)).card = n - 3 := by simp
        linarith
      have h22 : (({(-1 / 2, 1 + (n : ℝ) / 2), (1, 3 - (n : ℝ)), (-2, 2 * (n : ℝ) - 1)} : Finset (ℝ × ℝ)).card) = 3 := by
        exact round3_k3_card n hn
      omega
    constructor
    · -- Proof of the second condition
      intro a b ha_pos hb_pos hab
      by_cases h17 : a ≤ n - 3
      · -- Case 1: a ≤ n - 3
        have h171 : a ≤ n - 3 := h17
        have h172 : a ≥ 1 := by linarith
        have h173 : a - 1 < n - 3 := by omega
        have h174 : (a - 1) ∈ Finset.range (n - 3) := Finset.mem_range.mpr h173
        have h175 : (( (a - 1 : ℕ) : ℝ) + 1) ∈ (Finset.range (n - 3)).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
          refine Finset.mem_image.mpr ⟨(a - 1), h174, ?_⟩
          <;> simp [add_comm]
          <;> ring
        have h176 : (( (a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
          simp [Nat.cast_sub (by omega : 0 < a)]
          <;> ring
        have h177 : (a : ℝ) ∈ (Finset.range (n - 3)).image (fun (i : ℕ) => (i + 1 : ℝ)) := by
          rw [h176] at h175
          exact h175
        refine Or.inr ⟨(a : ℝ), h177, by simp⟩
      · -- Case 2: ¬ (a ≤ n - 3)
        have h17' : a > n - 3 := by omega
        have h178 : a ≥ n - 2 := by omega
        have h179 : a ≤ n := by omega
        have h180 : a = n - 2 ∨ a = n - 1 ∨ a = n := by omega
        rcases h180 with (h180 | h180 | h180)
        · -- Subcase 2.1: a = n - 2
          have h1801 : a = n - 2 := h180
          have h181 : b ≤ 3 := by omega
          have h182 : b ≥ 1 := by linarith
          have h183 : b = 1 ∨ b = 2 ∨ b = 3 := by omega
          rcases h183 with (h183 | h183 | h183)
          · -- Subcase 2.1.1: b = 1
            refine Or.inl ⟨(1, 3 - (n : ℝ)), by simp,?_⟩
            simp [h1801, h183]
            <;> ring_nf <;> norm_num <;>
            (try simp [Nat.cast_sub (show 2 ≤ n by omega)]) <;>
            ring_nf <;> norm_num <;>
            linarith
          · -- Subcase 2.1.2: b = 2
            refine Or.inl ⟨(-1 / 2, 1 + (n : ℝ) / 2), by simp,?_⟩
            simp [h1801, h183]
            <;> ring_nf <;> norm_num <;>
            (try simp [Nat.cast_sub (show 2 ≤ n by omega)]) <;>
            ring_nf <;> norm_num <;>
            linarith
          · -- Subcase 2.1.3: b = 3
            refine Or.inl ⟨(-2, 2 * (n : ℝ) - 1), by simp,?_⟩
            simp [h1801, h183]
            <;> ring_nf <;> norm_num <;>
            (try simp [Nat.cast_sub (show 2 ≤ n by omega)]) <;>
            ring_nf <;> norm_num <;>
            linarith
        · -- Subcase 2.2: a = n - 1
          have h1802 : a = n - 1 := h180
          have h181 : b ≤ 2 := by omega
          have h182 : b ≥ 1 := by linarith
          have h183 : b = 1 ∨ b = 2 := by omega
          rcases h183 with (h183 | h183)
          · -- Subcase 2.2.1: b = 1
            refine Or.inl ⟨(-2, 2 * (n : ℝ) - 1), by simp,?_⟩
            simp [h1802, h183]
            <;> ring_nf <;> norm_num <;>
            (try simp [Nat.cast_sub (show 1 ≤ n by omega)]) <;>
            ring_nf <;> norm_num <;>
            linarith
          · -- Subcase 2.2.2: b = 2
            refine Or.inl ⟨(1, 3 - (n : ℝ)), by simp,?_⟩
            simp [h1802, h183]
            <;> ring_nf <;> norm_num <;>
            (try simp [Nat.cast_sub (show 1 ≤ n by omega)]) <;>
            ring_nf <;> norm_num <;>
            linarith
        · -- Subcase 2.3: a = n
          have h1803 : a = n := h180
          have h181 : b ≤ 1 := by omega
          have h182 : b ≥ 1 := by linarith
          have h183 : b = 1 := by omega
          refine Or.inl ⟨(-1 / 2, 1 + (n : ℝ) / 2), by simp,?_⟩
          simp [h1803, h183]
          <;> ring_nf <;> norm_num <;>
          linarith
    · -- Proof of the third condition
      rw [h1]
      exact round3_k3_third_cond n hn

#print axioms imo2025_p1_right
