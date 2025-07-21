import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

theorem imo_1977_p6
  (f : ℕ → ℕ)
  (h₀ : ∀ n, 0 < f n)
  (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1)) :
  ∀ n, 0 < n → f n = n := by
  letI P_prop := fun k : ℕ => (f k = k) ∧ (∀ (x : ℕ), 0 < x → f x = k → x = k)
  retro' P_prop_def : P_prop = fun (k : ℕ) => f k = k ∧ ∀ (x : ℕ), (0 : ℕ) < x → f x = k → x = k := by funext; rfl
  letI S_k_prop := fun k : ℕ => (k = 0) ∨ P_prop k
  retro' S_k_prop_def : S_k_prop = fun (k : ℕ) => k = (0 : ℕ) ∨ P_prop k := by funext; rfl
  retro' P_prop_def' : ∀ (k : ℕ), P_prop k = (f k = k ∧ ∀ (x : ℕ), (0 : ℕ) < x → f x = k → x = k) := by intros; rfl
  letI succ_func_for_a_seq_rec := fun (step : ℕ) (prev_val : ℕ) => f (prev_val - 1)
  retro' succ_func_for_a_seq_rec_def' : ∀ (step : ℕ), ∀ (prev_val : ℕ), succ_func_for_a_seq_rec step prev_val = f (prev_val - (1 : ℕ)) := by intros; rfl
  letI a_sequence_func := fun (a_0_val_param : ℕ) (k_idx : ℕ) => Nat.recOn (motive := fun (_ : ℕ) => ℕ) k_idx a_0_val_param succ_func_for_a_seq_rec
  retro' a_sequence_func_def' : ∀ (a_0_val_param : ℕ), ∀ (k_idx : ℕ), a_sequence_func a_0_val_param k_idx = Nat.recOn (motive := fun (x : ℕ) => ℕ) k_idx a_0_val_param succ_func_for_a_seq_rec := by intros; rfl
  have subprob_lemma_a_seq_terminates_producing_1_proof : ∀ (a_0_val : ℕ) (h_a_0_val_gt_1 : a_0_val > 1), ∃ (K_idx : ℕ), K_idx > 0 ∧ (a_sequence_func a_0_val K_idx = 1) ∧ (∀ (l_idx : ℕ), l_idx < K_idx → a_sequence_func a_0_val l_idx > 1) := by
    mkOpaque
    intro a_0_val h_a_0_val_gt_1
    let a k := a_sequence_func a_0_val k
    have a_sequence_func_def'_rec : ∀ (a_0_val_param : ℕ), ∀ (k_idx : ℕ), a_sequence_func a_0_val_param k_idx = Nat.rec a_0_val_param succ_func_for_a_seq_rec k_idx := by
      intro a0 k
      rw [a_sequence_func_def']
    have h_set_nonempty : ∃ (k : ℕ), a k ≤ 1 := by
      by_contra h_a_gt_1_forall_k
      push_neg at h_a_gt_1_forall_k
      let b k := f (a k)
      have h_b_strict_anti : ∀ (k : ℕ), b (k + 1) < b k := by
        intro k
        have ha_rec : a (k + 1) = f (a k - 1) := by
          dsimp only [a]
          rw [a_sequence_func_def'_rec]
          dsimp
          rw [succ_func_for_a_seq_rec_def']
          rw [a_sequence_func_def'_rec]
        dsimp [b]
        rw [ha_rec]
        have hak_gt_1 := h_a_gt_1_forall_k k
        have han_gt_0 : 0 < a k - 1 := Nat.sub_pos_of_lt hak_gt_1
        have h_h1_applied := h₁ (a k - 1) han_gt_0
        have hak_ge_1 : a k ≥ 1 := Nat.le_of_lt hak_gt_1
        simp only [Nat.sub_add_cancel hak_ge_1] at h_h1_applied
        exact h_h1_applied
      have hbn_ge_1 : ∀ n, b n ≥ 1 := by
        intro n
        have h_bn_gt_0 := h₀ (a n)
        exact Nat.succ_le_of_lt h_bn_gt_0
      have hb0_ge_bn_plus_n : ∀ n, b 0 ≥ b n + n := by
        intro n
        induction n with
        | zero => simp
        | succ k ih =>
          have h_bk_gt_bk_succ := h_b_strict_anti k
          have h_bk_ge_bk_succ_plus_1 : b k ≥ b (k + 1) + 1 := Nat.succ_le_of_lt h_bk_gt_bk_succ
          have temp : b (k + 1) + 1 + k ≤ b k + k := Nat.add_le_add_right h_bk_ge_bk_succ_plus_1 k
          rw [Nat.add_assoc, Nat.add_comm 1 k] at temp
          apply Nat.le_trans temp ih
      let n0 := b 0
      have h_contradictory_inequality := hb0_ge_bn_plus_n n0
      have h_b_n0_ge_1 : b n0 ≥ 1 := hbn_ge_1 n0
      have h_rhs_ge : b n0 + n0 ≥ 1 + n0 := by
        dsimp [n0]
        apply Nat.add_le_add_right h_b_n0_ge_1
      have h_b0_ge_1_plus_n0 : b 0 ≥ 1 + n0 := Nat.le_trans h_rhs_ge h_contradictory_inequality
      dsimp [n0] at h_b0_ge_1_plus_n0
      linarith [h_b0_ge_1_plus_n0]
    let K : ℕ := Nat.find h_set_nonempty
    use K
    have hK_le_1 : a K ≤ 1 := Nat.find_spec h_set_nonempty
    have h_a_gt_1_lt_K : ∀ (l : ℕ), l < K → a l > 1 := by
      intro l hl_lt_K
      have h_not_le : ¬(a l ≤ 1) := Nat.find_min h_set_nonempty (show l < Nat.find h_set_nonempty from hl_lt_K)
      exact Nat.not_le.mp h_not_le
    have hK_pos : K > 0 := by
      by_contra hK_not_pos
      push_neg at hK_not_pos
      have hK_eq_0 : K = 0 := le_zero_iff.mp hK_not_pos
      have ha0_le_1 : a 0 ≤ 1 := by rw [hK_eq_0] at hK_le_1; exact hK_le_1
      have ha0_eq_a0val : a 0 = a_0_val := by
        dsimp [a]
        rw [a_sequence_func_def'_rec]
        rw [Nat.rec_zero]
      have ha0_val_le_1 : a_0_val ≤ 1 := by
        rw [ha0_eq_a0val] at ha0_le_1
        exact ha0_le_1
      have ha0_val_ge_2 : a_0_val ≥ 2 := Nat.succ_le_of_lt h_a_0_val_gt_1
      linarith [ha0_val_le_1, ha0_val_ge_2]
    have haK_eq_1 : a K = 1 := by
      apply Nat.le_antisymm hK_le_1
      have hK_ne_zero : K ≠ 0 := Nat.pos_iff_ne_zero.mp hK_pos
      rcases Nat.exists_eq_succ_of_ne_zero hK_ne_zero with ⟨K', hK_eq⟩
      rw [hK_eq]
      have haK_rec : a (K' + 1) = f (a K' - 1) := by
        dsimp only [a]
        rw [a_sequence_func_def'_rec]
        dsimp
        rw [succ_func_for_a_seq_rec_def']
        rw [a_sequence_func_def'_rec]
      rw [haK_rec]
      have hK'_lt_K : K' < K := by
        rw [hK_eq]
        exact Nat.lt.base K'
      have haK'_gt_1 : a K' > 1 := h_a_gt_1_lt_K K' hK'_lt_K
      have haK'_minus_1_gt_0 : 0 < a K' - 1 := Nat.sub_pos_of_lt haK'_gt_1
      have hf_aK'_minus_1_gt_0 : f (a K' - 1) > 0 := h₀ (a K' - 1)
      exact Nat.succ_le_of_lt hf_aK'_minus_1_gt_0
    exact ⟨hK_pos, haK_eq_1, h_a_gt_1_lt_K⟩
  retro' S_k_prop_def' : ∀ (k : ℕ), S_k_prop k = (k = (0 : ℕ) ∨ P_prop k) := by intros; rfl
  have subprob_IH_strong_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → ∀ (m : ℕ), (0 : ℕ) < m ∧ m < k → P_prop m := by
    intro k IH_strong_prime
    exact
      show ∀ (m : ℕ), (0 : ℕ) < m ∧ m < k → P_prop m by
        exact
          show ∀ (m : ℕ), (0 < m ∧ m < k) → P_prop m by
            mkOpaque
            intro m hm
            have h_S_k_prop_m := IH_strong_prime m hm.2
            rw [S_k_prop_def'] at h_S_k_prop_m
            cases' h_S_k_prop_m with h_m_0 h_P_prop_m
            exfalso
            linarith
            exact h_P_prop_m
  have subprob_exists_t_ft_eq_k_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → (0 : ℕ) < k → ∃ (t : ℕ), (0 : ℕ) < t ∧ f t = k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    exact
      show (0 : ℕ) < k → ∃ (t : ℕ), (0 : ℕ) < t ∧ f t = k by
        intro hk_pos
        retro' subprob_IH_strong_proof := subprob_IH_strong_proof
        exact
          show ∃ (t : ℕ), 0 < t ∧ f t = k by
            mkOpaque
            by_cases hfk : f k = k
            . exact ⟨k, hk_pos, hfk⟩
            . have hfk_gt_k : f k > k := by
                by_contra hfk_le_k
                have hfk_le_k_as_le : f k ≤ k := Nat.le_of_not_gt hfk_le_k
                have hfk_lt_k : f k < k := Ne.lt_of_le hfk hfk_le_k_as_le
                have hfk_pos' : 0 < f k := by apply h₀ k
                let m := f k
                have hm_bounds : 0 < m ∧ m < k := by constructor; exact hfk_pos'; exact hfk_lt_k
                have hP_prop_m : P_prop m := by apply subprob_IH_strong_proof m; exact hm_bounds
                rw [P_prop_def' m] at hP_prop_m
                have h_implication := hP_prop_m.right
                have h_apply := h_implication k hk_pos
                have h_k_eq_fk : k = f k := by apply h_apply; rfl
                exact hfk (Eq.symm h_k_eq_fk)
              have hfk_gt_1 : f k > 1 := by linarith [hfk_gt_k, hk_pos]
              let a := fun i => a_sequence_func (f k) i
              let a_0 := f k
              have h_term := subprob_lemma_a_seq_terminates_producing_1_proof a_0 hfk_gt_1
              rcases h_term with ⟨K_idx, hK_idx_pos, hK_idx_val, h_gt_1⟩
              have h_set_non_empty : ∃ i, a i ≤ k := by
                exists K_idx
                have h_aj_eq_1 : a K_idx = 1 := by
                  dsimp [a]
                  exact hK_idx_val
                rw [h_aj_eq_1]
                linarith [hk_pos]
              let ⟨j, hj_spec⟩ := Nat.findX h_set_non_empty
              have hj_le : a j ≤ k := hj_spec.left
              have hj_min : ∀ i < j, ¬(a i ≤ k) := hj_spec.right
              have hj_min' : ∀ i < j, a i > k := by {intro i hi; simp at hj_min; apply hj_min i hi
              }
              have hj_pos : j > 0 := by
                by_contra h_not_j_pos
                have h_j_eq_0 : j = 0 := by linarith [h_not_j_pos]
                have h_a0_eq_fk : a 0 = f k := by
                  dsimp [a]
                  rw [a_sequence_func_def' (f k) 0]
                  rfl
                simp [h_j_eq_0, h_a0_eq_fk] at hj_le
                apply not_le_of_gt hfk_gt_k hj_le
              have hj_pred_lt_j : j - 1 < j := by omega
              have haj_pred_gt_k : a (j - 1) > k := by apply hj_min' (j - 1); exact hj_pred_lt_j
              have haj_recurrence : a j = f (a (j - 1) - 1) := by
                cases j with
                | zero => {contradiction
                }
                | succ n => {
                  dsimp [a]
                  rw [a_sequence_func_def' (f k) (n + 1)]
                  dsimp
                  rw [succ_func_for_a_seq_rec_def' n (Nat.recOn (motive := fun x => ℕ) n (f k) succ_func_for_a_seq_rec)]
                  rw [← a_sequence_func_def' (f k) n]
                }
              have h_aj_pred_ge_2 : a (j - 1) >= 2 := by linarith [haj_pred_gt_k, hk_pos]
              have haj_pred_minus_1_pos : a (j - 1) - 1 > 0 := by omega
              have haj_pos' : a j > 0 := by
                rw [haj_recurrence]
                exact h₀ (a (j - 1) - 1)
              by_cases haj_eq_k : a j = k
              . exists (a (j - 1) - 1)
                constructor
                . exact haj_pred_minus_1_pos
                . rw [haj_recurrence.symm]
                  exact haj_eq_k
              . have haj_lt_k : a j < k := by {apply Ne.lt_of_le haj_eq_k; exact hj_le
                }
                have hm_bounds : 0 < a j ∧ a j < k := by constructor; exact haj_pos'; exact haj_lt_k
                have hP_prop_aj : P_prop (a j) := by apply subprob_IH_strong_proof (a j); exact hm_bounds
                rw [P_prop_def' (a j)] at hP_prop_aj
                have h_implication := hP_prop_aj.right
                have h_apply := h_implication (a (j - 1) - 1) haj_pred_minus_1_pos
                have h_eq : a (j - 1) - 1 = a j := by apply h_apply; rw [haj_recurrence.symm]
                have h_1_le_ajpred : 1 ≤ a (j - 1) := by linarith [h_aj_pred_ge_2]
                have haj_pred_eq_aj_plus_1 : a (j - 1) = a j + 1 := (Nat.sub_eq_iff_eq_add h_1_le_ajpred).mp h_eq
                have haj_plus_1_le_k : a j + 1 ≤ k := by linarith [haj_lt_k]
                have haj_pred_le_k : a (j - 1) ≤ k := by rw [haj_pred_eq_aj_plus_1]; exact haj_plus_1_le_k
                exact False.elim ((not_le_of_gt haj_pred_gt_k) haj_pred_le_k)
  have subprob_ft_eq_k_implies_t_eq_k_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → (0 : ℕ) < k → ∀ (t : ℕ), (0 : ℕ) < t → f t = k → t = k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof k IH_strong_prime
    exact
      show (0 : ℕ) < k → ∀ (t : ℕ), (0 : ℕ) < t → f t = k → t = k by
        intro hk_pos
        retro' subprob_IH_strong_proof := subprob_IH_strong_proof
        retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof hk_pos
        exact
          show ∀ (t : ℕ) (ht_pos : 0 < t) (h_ft_eq_k : f t = k), t = k by
            mkOpaque
            intro t ht_pos h_ft_eq_k
            by_contra h_t_ne_k
            have h_t_lt_k_or_h_t_gt_k : t < k ∨ t > k := Nat.ne_iff_lt_or_gt.mp h_t_ne_k
            cases h_t_lt_k_or_h_t_gt_k with
            | inl h_t_lt_k =>
              have h_t_gt_0_lt_k : 0 < t ∧ t < k := And.intro ht_pos h_t_lt_k
              have h_P_prop_t : P_prop t := subprob_IH_strong_proof t h_t_gt_0_lt_k
              rw [P_prop_def'] at h_P_prop_t
              have h_ft_eq_t : f t = t := h_P_prop_t.left
              have h_t_eq_k : t = k := by rwa [h_ft_eq_t] at h_ft_eq_k
              contradiction
            | inr h_t_gt_k =>
              have h_t_gt_1 : t > 1 := by omega
              have h_t_minus_1_pos : 0 < t - 1 := Nat.sub_pos_of_lt h_t_gt_1
              have h_f_ft_minus_1_lt_ft : f (f (t - 1)) < f ((t - 1) + 1) := h₁ (t - 1) h_t_minus_1_pos
              have h_f_ft_minus_1_lt_ft' : f (f (t - 1)) < f t := by
                have h_add_cancel : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.le_of_lt h_t_gt_1)
                rw [h_add_cancel] at h_f_ft_minus_1_lt_ft
                exact h_f_ft_minus_1_lt_ft
              have h_f_ft_minus_1_lt_k : f (f (t - 1)) < k := by rwa [h_ft_eq_k] at h_f_ft_minus_1_lt_ft'
              let m := f (t - 1)
              let m' := f m
              have h_m_prime_lt_k : m' < k := h_f_ft_minus_1_lt_k
              have h_m_pos : 0 < m := h₀ (t - 1)
              have h_m_prime_pos : 0 < m' := h₀ m
              have h_m_prime_gt_0_lt_k : 0 < m' ∧ m' < k := And.intro h_m_prime_pos h_m_prime_lt_k
              have h_P_prop_m_prime : P_prop m' := subprob_IH_strong_proof m' h_m_prime_gt_0_lt_k
              rw [P_prop_def'] at h_P_prop_m_prime
              have h_m_eq_m_prime : m = m' := h_P_prop_m_prime.right m h_m_pos (by rfl)
              have h_m_lt_k : m < k := Eq.trans_lt h_m_eq_m_prime h_m_prime_lt_k
              have h_m_gt_0_lt_k : 0 < m ∧ m < k := And.intro h_m_pos h_m_lt_k
              have h_P_prop_m : P_prop m := subprob_IH_strong_proof m h_m_gt_0_lt_k
              rw [P_prop_def'] at h_P_prop_m
              have h_t_minus_1_eq_m : t - 1 = m := h_P_prop_m.right (t - 1) h_t_minus_1_pos (by rfl)
              have h_t_minus_1_lt_k : t - 1 < k := by rwa [h_t_minus_1_eq_m.symm] at h_m_lt_k
              have h_t_minus_1_eq_pred_t : t - 1 = Nat.pred t := by rfl
              have h_pred_t_lt_k : Nat.pred t < k := by rwa [h_t_minus_1_eq_pred_t] at h_t_minus_1_lt_k
              have h_t_le_k : t ≤ k := Nat.le_of_pred_lt h_pred_t_lt_k
              linarith
  have subprob_pk_val_part_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → (0 : ℕ) < k → f k = k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof k IH_strong_prime
    retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof k IH_strong_prime
    exact
      show (0 : ℕ) < k → f k = k by
        intro hk_pos
        retro' subprob_IH_strong_proof := subprob_IH_strong_proof
        retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof hk_pos
        retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof hk_pos
        exact
          show f k = k by
            mkOpaque
            rcases subprob_exists_t_ft_eq_k_proof with ⟨t, ht_pos, hft_eq_k⟩
            have h_t_eq_k : t = k := subprob_ft_eq_k_implies_t_eq_k_proof t ht_pos hft_eq_k
            rw [h_t_eq_k] at hft_eq_k
            exact hft_eq_k
  have subprob_pk_unique_part_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → (0 : ℕ) < k → ∀ (x : ℕ), (0 : ℕ) < x → f x = k → x = k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof k IH_strong_prime
    retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof k IH_strong_prime
    exact
      show (0 : ℕ) < k → ∀ (x : ℕ), (0 : ℕ) < x → f x = k → x = k by
        intro hk_pos
        retro' subprob_IH_strong_proof := subprob_IH_strong_proof
        retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof hk_pos
        retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof hk_pos
        exact
          show ∀ (x : ℕ), 0 < x → f x = k → x = k by
            mkOpaque
            intro x hx hfx
            have h := subprob_ft_eq_k_implies_t_eq_k_proof x hx hfx
            simpa using h
  have subprob_P_prop_k_holds_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → (0 : ℕ) < k → P_prop k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof k IH_strong_prime
    retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof k IH_strong_prime
    retro' subprob_pk_val_part_proof := subprob_pk_val_part_proof k IH_strong_prime
    retro' subprob_pk_unique_part_proof := subprob_pk_unique_part_proof k IH_strong_prime
    exact
      show (0 : ℕ) < k → P_prop k by
        intro hk_pos
        retro' subprob_IH_strong_proof := subprob_IH_strong_proof
        retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof hk_pos
        retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof hk_pos
        retro' subprob_pk_val_part_proof := subprob_pk_val_part_proof hk_pos
        retro' subprob_pk_unique_part_proof := subprob_pk_unique_part_proof hk_pos
        exact
          show P_prop k by
            mkOpaque
            rw [P_prop_def']
            constructor
            exact subprob_pk_val_part_proof
            intro x hx hx'
            exact subprob_pk_unique_part_proof x hx hx'
  have subprob_S_k_holds_overall_proof : ∀ (k : ℕ), (∀ (m : ℕ), m < k → S_k_prop m) → S_k_prop k := by
    intro k IH_strong_prime
    retro' subprob_IH_strong_proof := subprob_IH_strong_proof k IH_strong_prime
    retro' subprob_exists_t_ft_eq_k_proof := subprob_exists_t_ft_eq_k_proof k IH_strong_prime
    retro' subprob_ft_eq_k_implies_t_eq_k_proof := subprob_ft_eq_k_implies_t_eq_k_proof k IH_strong_prime
    retro' subprob_pk_val_part_proof := subprob_pk_val_part_proof k IH_strong_prime
    retro' subprob_pk_unique_part_proof := subprob_pk_unique_part_proof k IH_strong_prime
    retro' subprob_P_prop_k_holds_proof := subprob_P_prop_k_holds_proof k IH_strong_prime
    exact
      show S_k_prop k by
        mkOpaque
        rw [S_k_prop_def']
        by_cases hk : k = 0
        exact Or.inl hk
        exact Or.inr (subprob_P_prop_k_holds_proof (Nat.pos_of_ne_zero hk))
  have subprob_all_k_S_k_holds_proof : ∀ (k : ℕ), S_k_prop k := by
    mkOpaque
    intro k
    apply Nat.strong_induction_on
    exact subprob_S_k_holds_overall_proof
  have subprob_final_goal_proof : ∀ (n : ℕ), 0 < n → f n = n := by
    mkOpaque
    intro n hn
    have h_S_k_prop := subprob_all_k_S_k_holds_proof n
    rw [S_k_prop_def] at h_S_k_prop
    cases' h_S_k_prop with hk hk
    · exfalso
      linarith
    · rw [P_prop_def] at hk
      exact hk.1
  exact
    show ∀ (n : ℕ), (0 : ℕ) < n → f n = n by
      mkOpaque
      intro n hn
      exact subprob_final_goal_proof n hn

#print axioms imo_1977_p6

/- Sketch
variable (f : ℕ → ℕ) (h₀ : ∀ n, 0 < f n) (h₁ : ∀ n, 0 < n → f (f n) < f (n + 1))
play
  -- Q(n) is the property: f n = n AND (∀ x > 0, f x = n → x = n).
  Q_n_statement := fun (n : ℕ) => (f n = n ∧ (∀ (x : ℕ), 0 < x → f x = n → x = n))

  -- Base Case: Q(1)
  -- Part 1.1.1: f(1) is a minimum value in the range of f.
  -- Helper: The range of f is non-empty.
  subprob_range_nonempty :≡ Set.Nonempty (Set.range f)
  subprob_range_nonempty_proof ⇐ show subprob_range_nonempty by sorry
  -- Helper: There exists a minimum value m₀ in the range of f. (This uses well-ordering of ℕ)
  subprob_exists_min_val_in_range :≡ ∃ m₀, m₀ ∈ Set.range f ∧ (∀ y ∈ Set.range f, m₀ ≤ y)
  subprob_exists_min_val_in_range_proof ⇐ show subprob_exists_min_val_in_range by sorry
  ⟨m₀, hm₀_in_range, hm₀_is_min⟩ := subprob_exists_min_val_in_range_proof
  -- Helper: There exists k₀ > 0 such that f(k₀) = m₀. (This follows from m₀ ∈ Set.range f)
  subprob_k0_achieves_min_val :≡ ∃ k₀, 0 < k₀ ∧ f k₀ = m₀
  subprob_k0_achieves_min_val_proof ⇐ show subprob_k0_achieves_min_val by sorry
  ⟨k₀, hk₀_pos, hfk₀_eq_m₀⟩ := subprob_k0_achieves_min_val_proof
  -- Helper: This k₀ must be 1. (Proof by contradiction using h₁)
  subprob_k0_must_be_1 :≡ k₀ = 1
  subprob_k0_must_be_1_proof ⇐ show subprob_k0_must_be_1 by sorry
  -- Consequence: f(1) is a minimum value in the range of f. (Combine previous steps)
  subprob_f1_is_min_val_direct :≡ ∀ y ∈ Set.range f, f 1 ≤ y
  subprob_f1_is_min_val_direct_proof ⇐ show subprob_f1_is_min_val_direct by sorry

  -- Part 1.1.2: 1 is in the range of f. (Uses sequence argument and h₁)
  subprob_one_in_image :≡ ∃ t, (0 < t ∧ f t = 1)
  subprob_one_in_image_proof ⇐ show subprob_one_in_image by sorry
  ⟨t_for_f_eq_1, ht_for_f_eq_1_pos, hf_t_for_f_eq_1_is_1⟩ := subprob_one_in_image_proof

  -- Part 1.1.3: f(1)=1. (Uses f(1) is min from 1.1.1, 1 is in range from 1.1.2, and f(1)>0 from h₀)
  subprob_f1_eq_1 :≡ f 1 = 1
  subprob_f1_eq_1_proof ⇐ show subprob_f1_eq_1 by sorry

  -- Part 1.2: Uniqueness for f(1)=1. (∀x, 0 < x → f x = 1 → x = 1). (Proof by contradiction using h₁)
  subprob_f1_unique :≡ ∀ (x : ℕ), 0 < x → f x = 1 → x = 1
  subprob_f1_unique_proof ⇐ show subprob_f1_unique by sorry

  -- Q(1) holds (combines f(1)=1 and uniqueness for f(1)=1).
  Q_1_holds :≡ Q_n_statement 1
  Q_1_holds_proof ⇐ show Q_1_holds by sorry

  -- Inductive step definition: For n > 1, if (∀ m, 0 < m → m < n → Q m) then Q n.
  -- This is encapsulated in a single lemma representing the reasoning for the inductive step.
  inductive_step_implication :≡ ∀ (n : ℕ), 0 < n → n > 1 →
    (∀ (m : ℕ), 0 < m → m < n → Q_n_statement m) →
    Q_n_statement n
  inductive_step_implication_proof ⇐ show inductive_step_implication by sorry
  -- To prove inductive_step_implication, we'd break it down further:
  -- Suppose n, hn_pos, hn_gt_1, and ih_hypothesis are given.
  -- Then prove Q_n_statement n.
  -- This internal proof would use the sub-steps 2.1, 2.2, 2.3 as outlined in the natural language proof.
  -- Play is for breaking down the main theorem, so these sub-steps can be top-level lemmas
  -- made available to the proof of `inductive_step_implication`.

  -- Example breakdown for substeps of the inductive step (these are lemmas):
  -- Lemma for Part 2.1: f(n) ≥ n.
  lemma_fn_ge_n :≡ ∀ (n : ℕ), 0 < n → n > 1 →
    (Q_n_statement (n-1)) →
    f n ≥ n
  lemma_fn_ge_n_proof ⇐ show lemma_fn_ge_n by sorry

  -- Lemma for Part 2.2 (helper): For any x ≥ n, f(x) ≥ n.
  lemma_fx_ge_n_for_x_ge_n :≡ ∀ (n : ℕ), 0 < n → n > 1 →
    (∀ (m : ℕ), 0 < m → m < n → Q_n_statement m) →
    (∀ x, 0 < x → x ≥ n → f x ≥ n)
  lemma_fx_ge_n_for_x_ge_n_proof ⇐ show lemma_fx_ge_n_for_x_ge_n by sorry

  -- Lemma for Part 2.2 (main): n is in the range of f.
  lemma_n_in_image :≡ ∀ (n : ℕ), 0 < n → n > 1 →
    (∀ (m : ℕ), 0 < m → m < n → Q_n_statement m) →
    (∀ x, 0 < x → x ≥ n → f x ≥ n) → -- Premise from previous lemma
    (∃ t, 0 < t ∧ f t = n)
  lemma_n_in_image_proof ⇐ show lemma_n_in_image by sorry

  -- Lemma for Part 2.3: if f(t)=n, then t=n.
  lemma_ft_eq_n_implies_t_eq_n :≡ ∀ (n : ℕ), 0 < n → n > 1 →
    (∀ (m : ℕ), 0 < m → m < n → Q_n_statement m) →
    (∀ t, 0 < t → f t = n → t = n)
  lemma_ft_eq_n_implies_t_eq_n_proof ⇐ show lemma_ft_eq_n_implies_t_eq_n by sorry

  -- Final proof by strong induction for positive integers.
  -- This combines Q_1_holds and inductive_step_implication.
  Q_n_all_positive_n_holds :≡ ∀ n : ℕ, 0 < n → Q_n_statement n
  Q_n_all_positive_n_holds_proof ⇐ show Q_n_all_positive_n_holds by sorry

  -- Extract the final goal from Q_n_all_positive_n_holds.
  subprob_final_goal :≡ ∀ n, 0 < n → f n = n
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketch with proof
variable (f: ℕ → ℕ) (h₀: ∀ (n : ℕ), (0 : ℕ) < f n) (h₁: ∀ (n : ℕ), (0 : ℕ) < n → f (f n) < f (n + (1 : ℕ)))
play
  P_prop := fun k : ℕ => (f k = k) ∧ (∀ (x : ℕ), 0 < x → f x = k → x = k)
  succ_func_for_a_seq_rec := fun (step : ℕ) (prev_val : ℕ) => f (prev_val - 1)
  a_sequence_func := fun (a_0_val_param : ℕ) (k_idx : ℕ) =>
    Nat.recOn (motive := fun (_ : ℕ) => ℕ) k_idx a_0_val_param succ_func_for_a_seq_rec
  subprob_lemma_a_seq_terminates_producing_1 :≡ ∀ (a_0_val : ℕ) (h_a_0_val_gt_1 : a_0_val > 1),
    ∃ (K_idx : ℕ), K_idx > 0 ∧ (a_sequence_func a_0_val K_idx = 1) ∧ (∀ (l_idx : ℕ), l_idx < K_idx → a_sequence_func a_0_val l_idx > 1)
  subprob_lemma_a_seq_terminates_producing_1_proof ⇐ show subprob_lemma_a_seq_terminates_producing_1 by
    intro a_0_val h_a_0_val_gt_1
    let a k := a_sequence_func a_0_val k
    have a_sequence_func_def'_rec : ∀ (a_0_val_param : ℕ), ∀ (k_idx : ℕ), a_sequence_func a_0_val_param k_idx = Nat.rec a_0_val_param succ_func_for_a_seq_rec k_idx := by
      intro a0 k
      rw [a_sequence_func_def']
    have h_set_nonempty : ∃ (k : ℕ), a k ≤ 1 := by
      by_contra h_a_gt_1_forall_k
      push_neg at h_a_gt_1_forall_k
      let b k := f (a k)
      have h_b_strict_anti : ∀ (k : ℕ), b (k + 1) < b k := by
        intro k
        have ha_rec : a (k + 1) = f (a k - 1) := by
          dsimp only [a]
          rw [a_sequence_func_def'_rec]
          dsimp
          rw [succ_func_for_a_seq_rec_def']
          rw [a_sequence_func_def'_rec]
        dsimp [b]
        rw [ha_rec]
        have hak_gt_1 := h_a_gt_1_forall_k k
        have han_gt_0 : 0 < a k - 1 := Nat.sub_pos_of_lt hak_gt_1
        have h_h1_applied := h₁ (a k - 1) han_gt_0
        have hak_ge_1 : a k ≥ 1 := Nat.le_of_lt hak_gt_1
        simp only [Nat.sub_add_cancel hak_ge_1] at h_h1_applied
        exact h_h1_applied
      have hbn_ge_1 : ∀ n, b n ≥ 1 := by
        intro n
        have h_bn_gt_0 := h₀ (a n)
        exact Nat.succ_le_of_lt h_bn_gt_0
      have hb0_ge_bn_plus_n : ∀ n, b 0 ≥ b n + n := by
        intro n
        induction n with
        | zero =>
          simp
        | succ k ih =>
          have h_bk_gt_bk_succ := h_b_strict_anti k
          have h_bk_ge_bk_succ_plus_1 : b k ≥ b (k + 1) + 1 := Nat.succ_le_of_lt h_bk_gt_bk_succ
          have temp : b (k + 1) + 1 + k ≤ b k + k := Nat.add_le_add_right h_bk_ge_bk_succ_plus_1 k
          rw [Nat.add_assoc, Nat.add_comm 1 k] at temp
          apply Nat.le_trans temp ih
      let n0 := b 0
      have h_contradictory_inequality := hb0_ge_bn_plus_n n0
      have h_b_n0_ge_1 : b n0 ≥ 1 := hbn_ge_1 n0
      have h_rhs_ge : b n0 + n0 ≥ 1 + n0 := by
        dsimp [n0]
        apply Nat.add_le_add_right h_b_n0_ge_1
      have h_b0_ge_1_plus_n0 : b 0 ≥ 1 + n0 := Nat.le_trans h_rhs_ge h_contradictory_inequality
      dsimp [n0] at h_b0_ge_1_plus_n0
      linarith [h_b0_ge_1_plus_n0]
    let K : ℕ := Nat.find h_set_nonempty
    use K
    have hK_le_1 : a K ≤ 1 := Nat.find_spec h_set_nonempty
    have h_a_gt_1_lt_K : ∀ (l : ℕ), l < K → a l > 1 := by
      intro l hl_lt_K
      have h_not_le : ¬ (a l ≤ 1) := Nat.find_min h_set_nonempty (show l < Nat.find h_set_nonempty from hl_lt_K)
      exact Nat.not_le.mp h_not_le
    have hK_pos : K > 0 := by
      by_contra hK_not_pos
      push_neg at hK_not_pos
      have hK_eq_0 : K = 0 := le_zero_iff.mp hK_not_pos
      have ha0_le_1 : a 0 ≤ 1 := by rw [hK_eq_0] at hK_le_1; exact hK_le_1
      have ha0_eq_a0val : a 0 = a_0_val := by
        dsimp [a]
        rw [a_sequence_func_def'_rec]
        rw [Nat.rec_zero]
      have ha0_val_le_1 : a_0_val ≤ 1 := by
        rw [ha0_eq_a0val] at ha0_le_1
        exact ha0_le_1
      have ha0_val_ge_2 : a_0_val ≥ 2 := Nat.succ_le_of_lt h_a_0_val_gt_1
      linarith [ha0_val_le_1, ha0_val_ge_2]
    have haK_eq_1 : a K = 1 := by
      apply Nat.le_antisymm hK_le_1
      have hK_ne_zero : K ≠ 0 := Nat.pos_iff_ne_zero.mp hK_pos
      rcases Nat.exists_eq_succ_of_ne_zero hK_ne_zero with ⟨K', hK_eq⟩
      rw [hK_eq]
      have haK_rec : a (K' + 1) = f (a K' - 1) := by
        dsimp only [a]
        rw [a_sequence_func_def'_rec]
        dsimp
        rw [succ_func_for_a_seq_rec_def']
        rw [a_sequence_func_def'_rec]
      rw [haK_rec]
      have hK'_lt_K : K' < K := by
        rw [hK_eq]
        exact Nat.lt.base K'
      have haK'_gt_1 : a K' > 1 := h_a_gt_1_lt_K K' hK'_lt_K
      have haK'_minus_1_gt_0 : 0 < a K' - 1 := Nat.sub_pos_of_lt haK'_gt_1
      have hf_aK'_minus_1_gt_0 : f (a K' - 1) > 0 := h₀ (a K' - 1)
      exact Nat.succ_le_of_lt hf_aK'_minus_1_gt_0
    exact ⟨hK_pos, haK_eq_1, h_a_gt_1_lt_K⟩
  S_k_prop := fun k : ℕ => (k = 0) ∨ P_prop k
  suppose (k : ℕ) (IH_strong_prime : ∀ (m : ℕ), m < k → S_k_prop m) then
    suppose (hk_is_0 : k = 0) then
      subprob_S_k_holds_for_k0 :≡ S_k_prop k
      subprob_S_k_holds_for_k0_proof ⇐ show subprob_S_k_holds_for_k0 by
        rw [S_k_prop_def']
        simp_all
        <;> try
          cases k with
          | zero => simp_all
          | succ k' =>
            simp_all [P_prop_def']
            <;> try
              linarith [h₀ 0, h₀ 1, h₁ 0 (by linarith), h₁ 1 (by linarith)]
            <;> try
              aesop
    suppose (hk_pos : 0 < k) then
      subprob_IH_strong :≡ ∀ (m : ℕ), (0 < m ∧ m < k) → P_prop m
      subprob_IH_strong_proof ⇐ show subprob_IH_strong by
        intro m hm
        have h_S_k_prop_m := IH_strong_prime m hm.2
        rw [S_k_prop_def'] at h_S_k_prop_m
        cases' h_S_k_prop_m with h_m_0 h_P_prop_m
        exfalso
        linarith
        exact h_P_prop_m
      subprob_exists_t_ft_eq_k :≡ ∃ (t : ℕ), 0 < t ∧ f t = k
      subprob_exists_t_ft_eq_k_proof ⇐ show subprob_exists_t_ft_eq_k by
        by_cases hfk : f k = k
        .
          exact ⟨k, hk_pos, hfk⟩
        .
          have hfk_gt_k : f k > k := by
            by_contra hfk_le_k
            have hfk_le_k_as_le : f k ≤ k := Nat.le_of_not_gt hfk_le_k
            have hfk_lt_k : f k < k := Ne.lt_of_le hfk hfk_le_k_as_le
            have hfk_pos' : 0 < f k := by apply h₀ k
            let m := f k
            have hm_bounds : 0 < m ∧ m < k := by constructor; exact hfk_pos'; exact hfk_lt_k
            have hP_prop_m : P_prop m := by apply subprob_IH_strong_proof m; exact hm_bounds
            rw [P_prop_def' m] at hP_prop_m
            have h_implication := hP_prop_m.right
            have h_apply := h_implication k hk_pos
            have h_k_eq_fk : k = f k := by apply h_apply; rfl
            exact hfk (Eq.symm h_k_eq_fk)
          have hfk_gt_1 : f k > 1 := by linarith [hfk_gt_k, hk_pos]
          let a := fun i => a_sequence_func (f k) i
          let a_0 := f k
          have h_term := subprob_lemma_a_seq_terminates_producing_1_proof a_0 hfk_gt_1
          rcases h_term with ⟨K_idx, hK_idx_pos, hK_idx_val, h_gt_1⟩
          have h_set_non_empty : ∃ i, a i ≤ k := by
            exists K_idx
            have h_aj_eq_1 : a K_idx = 1 := by
              dsimp [a]
              exact hK_idx_val
            rw [h_aj_eq_1]
            linarith [hk_pos]
          let ⟨j, hj_spec⟩ := Nat.findX h_set_non_empty
          have hj_le : a j ≤ k := hj_spec.left
          have hj_min : ∀ i < j, ¬(a i ≤ k) := hj_spec.right
          have hj_min' : ∀ i < j, a i > k := by { intro i hi; simp at hj_min; apply hj_min i hi }
          have hj_pos : j > 0 := by
            by_contra h_not_j_pos
            have h_j_eq_0 : j = 0 := by linarith [h_not_j_pos]
            have h_a0_eq_fk : a 0 = f k := by
              dsimp [a]
              rw [a_sequence_func_def' (f k) 0]
              rfl
            simp [h_j_eq_0, h_a0_eq_fk] at hj_le
            apply not_le_of_gt hfk_gt_k hj_le
          have hj_pred_lt_j : j - 1 < j := by
            omega
          have haj_pred_gt_k : a (j - 1) > k := by apply hj_min' (j - 1); exact hj_pred_lt_j
          have haj_recurrence : a j = f (a (j - 1) - 1) := by
            cases j with
            | zero => {
              contradiction
            }
            | succ n => {
              dsimp [a]
              rw [a_sequence_func_def' (f k) (n + 1)]
              dsimp
              rw [succ_func_for_a_seq_rec_def' n (Nat.recOn (motive := fun x => ℕ) n (f k) succ_func_for_a_seq_rec)]
              rw [← a_sequence_func_def' (f k) n]
            }
          have h_aj_pred_ge_2 : a (j - 1) >= 2 := by linarith [haj_pred_gt_k, hk_pos]
          have haj_pred_minus_1_pos : a (j - 1) - 1 > 0 := by
            omega
          have haj_pos' : a j > 0 := by
            rw [haj_recurrence]
            exact h₀ (a (j - 1) - 1)
          by_cases haj_eq_k : a j = k
          .
            exists (a (j - 1) - 1)
            constructor
            .
              exact haj_pred_minus_1_pos
            .
              rw [haj_recurrence.symm]
              exact haj_eq_k
          .
            have haj_lt_k : a j < k := by { apply Ne.lt_of_le haj_eq_k; exact hj_le }
            have hm_bounds : 0 < a j ∧ a j < k := by constructor; exact haj_pos'; exact haj_lt_k
            have hP_prop_aj : P_prop (a j) := by apply subprob_IH_strong_proof (a j); exact hm_bounds
            rw [P_prop_def' (a j)] at hP_prop_aj
            have h_implication := hP_prop_aj.right
            have h_apply := h_implication (a (j - 1) - 1) haj_pred_minus_1_pos
            have h_eq : a (j - 1) - 1 = a j := by apply h_apply; rw [haj_recurrence.symm]
            have h_1_le_ajpred : 1 ≤ a (j - 1) := by linarith [h_aj_pred_ge_2]
            have haj_pred_eq_aj_plus_1 : a (j - 1) = a j + 1 := (Nat.sub_eq_iff_eq_add h_1_le_ajpred).mp h_eq
            have haj_plus_1_le_k : a j + 1 ≤ k := by linarith [haj_lt_k]
            have haj_pred_le_k : a (j - 1) ≤ k := by rw [haj_pred_eq_aj_plus_1]; exact haj_plus_1_le_k
            exact False.elim ((not_le_of_gt haj_pred_gt_k) haj_pred_le_k)
      subprob_ft_eq_k_implies_t_eq_k :≡ ∀ (t : ℕ) (ht_pos : 0 < t) (h_ft_eq_k : f t = k), t = k
      subprob_ft_eq_k_implies_t_eq_k_proof ⇐ show subprob_ft_eq_k_implies_t_eq_k by
        intro t ht_pos h_ft_eq_k
        by_contra h_t_ne_k
        have h_t_lt_k_or_h_t_gt_k : t < k ∨ t > k := Nat.ne_iff_lt_or_gt.mp h_t_ne_k
        cases h_t_lt_k_or_h_t_gt_k with
        | inl h_t_lt_k =>
          have h_t_gt_0_lt_k : 0 < t ∧ t < k := And.intro ht_pos h_t_lt_k
          have h_P_prop_t : P_prop t := subprob_IH_strong_proof t h_t_gt_0_lt_k
          rw [P_prop_def'] at h_P_prop_t
          have h_ft_eq_t : f t = t := h_P_prop_t.left
          have h_t_eq_k : t = k := by rwa [h_ft_eq_t] at h_ft_eq_k
          contradiction
        | inr h_t_gt_k =>
          have h_t_gt_1 : t > 1 := by omega
          have h_t_minus_1_pos : 0 < t - 1 := Nat.sub_pos_of_lt h_t_gt_1
          have h_f_ft_minus_1_lt_ft : f (f (t - 1)) < f ((t - 1) + 1) := h₁ (t - 1) h_t_minus_1_pos
          have h_f_ft_minus_1_lt_ft' : f (f (t - 1)) < f t := by
            have h_add_cancel : (t - 1) + 1 = t := Nat.sub_add_cancel (Nat.le_of_lt h_t_gt_1)
            rw [h_add_cancel] at h_f_ft_minus_1_lt_ft
            exact h_f_ft_minus_1_lt_ft
          have h_f_ft_minus_1_lt_k : f (f (t - 1)) < k := by rwa [h_ft_eq_k] at h_f_ft_minus_1_lt_ft'
          let m := f (t - 1)
          let m' := f m
          have h_m_prime_lt_k : m' < k := h_f_ft_minus_1_lt_k
          have h_m_pos : 0 < m := h₀ (t - 1)
          have h_m_prime_pos : 0 < m' := h₀ m
          have h_m_prime_gt_0_lt_k : 0 < m' ∧ m' < k := And.intro h_m_prime_pos h_m_prime_lt_k
          have h_P_prop_m_prime : P_prop m' := subprob_IH_strong_proof m' h_m_prime_gt_0_lt_k
          rw [P_prop_def'] at h_P_prop_m_prime
          have h_m_eq_m_prime : m = m' := h_P_prop_m_prime.right m h_m_pos (by rfl)
          have h_m_lt_k : m < k := Eq.trans_lt h_m_eq_m_prime h_m_prime_lt_k
          have h_m_gt_0_lt_k : 0 < m ∧ m < k := And.intro h_m_pos h_m_lt_k
          have h_P_prop_m : P_prop m := subprob_IH_strong_proof m h_m_gt_0_lt_k
          rw [P_prop_def'] at h_P_prop_m
          have h_t_minus_1_eq_m : t - 1 = m := h_P_prop_m.right (t - 1) h_t_minus_1_pos (by rfl)
          have h_t_minus_1_lt_k : t - 1 < k := by
            rwa [h_t_minus_1_eq_m.symm] at h_m_lt_k
          have h_t_minus_1_eq_pred_t : t - 1 = Nat.pred t := by rfl
          have h_pred_t_lt_k : Nat.pred t < k := by rwa [h_t_minus_1_eq_pred_t] at h_t_minus_1_lt_k
          have h_t_le_k : t ≤ k := Nat.le_of_pred_lt h_pred_t_lt_k
          linarith
      subprob_pk_val_part :≡ f k = k
      subprob_pk_val_part_proof ⇐ show subprob_pk_val_part by
        rcases subprob_exists_t_ft_eq_k_proof with ⟨t, ht_pos, hft_eq_k⟩
        have h_t_eq_k : t = k := subprob_ft_eq_k_implies_t_eq_k_proof t ht_pos hft_eq_k
        rw [h_t_eq_k] at hft_eq_k
        exact hft_eq_k
      subprob_pk_unique_part :≡ ∀ (x : ℕ), 0 < x → f x = k → x = k
      subprob_pk_unique_part_proof ⇐ show subprob_pk_unique_part by
        intro x hx hfx
        have h := subprob_ft_eq_k_implies_t_eq_k_proof x hx hfx
        simpa using h
      subprob_P_prop_k_holds :≡ P_prop k
      subprob_P_prop_k_holds_proof ⇐ show subprob_P_prop_k_holds by
        rw [P_prop_def']
        constructor
        exact subprob_pk_val_part_proof
        intro x hx hx'
        exact subprob_pk_unique_part_proof x hx hx'
      subprob_S_k_holds_for_k_pos :≡ S_k_prop k
      subprob_S_k_holds_for_k_pos_proof ⇐ show subprob_S_k_holds_for_k_pos by
        rw [S_k_prop_def']
        right
        rw [P_prop_def']
        constructor
        exact subprob_pk_val_part_proof
        intro x hx hx'
        exact subprob_ft_eq_k_implies_t_eq_k_proof x hx hx'
    subprob_S_k_holds_overall :≡ S_k_prop k
    subprob_S_k_holds_overall_proof ⇐ show subprob_S_k_holds_overall by
      rw [S_k_prop_def']
      by_cases hk : k = 0
      exact Or.inl hk
      exact Or.inr (subprob_P_prop_k_holds_proof (Nat.pos_of_ne_zero hk))
  subprob_all_k_S_k_holds :≡ ∀ (k : ℕ), S_k_prop k
  subprob_all_k_S_k_holds_proof ⇐ show subprob_all_k_S_k_holds by
    intro k
    apply Nat.strong_induction_on
    exact subprob_S_k_holds_overall_proof
  subprob_final_goal :≡ ∀ (n : ℕ), 0 < n → f n = n
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    intro n hn
    have h_S_k_prop := subprob_all_k_S_k_holds_proof n
    rw [S_k_prop_def] at h_S_k_prop
    cases' h_S_k_prop with hk hk
    ·
      exfalso
      linarith
    ·
      rw [P_prop_def] at hk
      exact hk.1
  original_target :≡ ∀ (n : ℕ), (0 : ℕ) < n → f n = n
  original_target_proof ⇐ show original_target by
    intro n hn
    exact subprob_final_goal_proof n hn
-/
