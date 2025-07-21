import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem amc12a_2021_p22 (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x^3 + a * x^2 + b * x + c) (h₁ : f⁻¹' {0} = {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)}) : a * b * c = (1 : ℝ) / (32 : ℝ) := by
  letI r₁ := Real.cos (2 * Real.pi / 7)
  retro' r₁_def : r₁ = Real.cos ((2 : ℝ) * Real.pi / (7 : ℝ)) := by funext; rfl
  letI r₂ := Real.cos (4 * Real.pi / 7)
  retro' r₂_def : r₂ = Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) := by funext; rfl
  letI r₃ := Real.cos (6 * Real.pi / 7)
  retro' r₃_def : r₃ = Real.cos ((6 : ℝ) * Real.pi / (7 : ℝ)) := by funext; rfl
  have subprob_roots_distinct_aux1_proof : 2 * Real.pi / 7 < 4 * Real.pi / 7 := by
    mkOpaque
    have seven_pos : (7 : ℝ) > 0 := by norm_num
    apply ((div_lt_div_iff seven_pos seven_pos).trans (mul_lt_mul_iff_of_pos_right seven_pos)).mpr
    have pi_pos : Real.pi > 0 := by exact Real.pi_pos
    apply (mul_lt_mul_right pi_pos).mpr
    norm_num
  have subprob_roots_distinct_aux2_proof : 4 * Real.pi / 7 < 6 * Real.pi / 7 := by
    mkOpaque
    apply (div_lt_div_right (by norm_num : (0 : ℝ) < (7 : ℝ))).mpr
    apply (mul_lt_mul_right Real.pi_pos).mpr
    norm_num
  have subprob_roots_distinct_aux3_proof : (0 : ℝ) < 2 * Real.pi / 7 := by
    mkOpaque
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_pi_pos : 0 < Real.pi := by exact Real.pi_pos
    have h_numerator_pos : 0 < 2 * Real.pi := by
      apply mul_pos
      exact h_two_pos
      exact h_pi_pos
    have h_denominator_pos : (0 : ℝ) < 7 := by norm_num
    apply div_pos
    exact h_numerator_pos
    exact h_denominator_pos
  have subprob_roots_distinct_aux4_proof : 6 * Real.pi / 7 < Real.pi := by
    mkOpaque
    have h_seven_pos : (7 : ℝ) > 0 := by norm_num
    rw [div_lt_iff h_seven_pos]
    rw [mul_comm Real.pi (7 : ℝ)]
    have h_pi_pos : Real.pi > 0 := by exact Real.pi_pos
    rw [mul_lt_mul_iff_of_pos_right h_pi_pos]
    norm_num
  have subprob_r₁_gt_r₂_proof : r₁ > r₂ := by
    mkOpaque
    rw [r₁_def, r₂_def]
    let x₁ := (2 : ℝ) * Real.pi / (7 : ℝ)
    let x₂ := (4 : ℝ) * Real.pi / (7 : ℝ)
    let x₃_arg := (6 : ℝ) * Real.pi / (7 : ℝ)
    have h_0_lt_x₁ : 0 < x₁ := by exact subprob_roots_distinct_aux3_proof
    have h_x₁_lt_x₂ : x₁ < x₂ := by exact subprob_roots_distinct_aux1_proof
    have h_x₂_lt_x₃_arg : x₂ < x₃_arg := by exact subprob_roots_distinct_aux2_proof
    have h_x₃_arg_lt_pi : x₃_arg < Real.pi := by exact subprob_roots_distinct_aux4_proof
    have h_x₁_lt_pi : x₁ < Real.pi := by
      apply lt_trans h_x₁_lt_x₂
      apply lt_trans h_x₂_lt_x₃_arg
      exact h_x₃_arg_lt_pi
    have h_x₁_in_Ioo : x₁ ∈ Set.Ioo 0 Real.pi := by exact Set.mem_Ioo.mpr ⟨h_0_lt_x₁, h_x₁_lt_pi⟩
    have h_0_lt_x₂ : 0 < x₂ := by
      apply lt_trans h_0_lt_x₁
      exact h_x₁_lt_x₂
    have h_x₂_lt_pi : x₂ < Real.pi := by
      apply lt_trans h_x₂_lt_x₃_arg
      exact h_x₃_arg_lt_pi
    have h_x₂_in_Ioo : x₂ ∈ Set.Ioo 0 Real.pi := by exact Set.mem_Ioo.mpr ⟨h_0_lt_x₂, h_x₂_lt_pi⟩
    have cos_strict_anti_on_Icc : StrictAntiOn Real.cos (Set.Icc 0 Real.pi) := Real.strictAntiOn_cos
    have Ioo_subset_Icc_zero_pi : Set.Ioo 0 Real.pi ⊆ Set.Icc 0 Real.pi := Set.Ioo_subset_Icc_self
    have cos_strict_anti_on_Ioo_zero_pi : StrictAntiOn Real.cos (Set.Ioo 0 Real.pi) := StrictAntiOn.mono cos_strict_anti_on_Icc Ioo_subset_Icc_zero_pi
    exact cos_strict_anti_on_Ioo_zero_pi h_x₁_in_Ioo h_x₂_in_Ioo h_x₁_lt_x₂
  have subprob_r₂_gt_r₃_proof : r₂ > r₃ := by
    mkOpaque
    rw [r₂_def, r₃_def]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    . show (0 : ℝ) ≤ (4 : ℝ) * Real.pi / (7 : ℝ)
      exact le_of_lt (lt_trans subprob_roots_distinct_aux3_proof subprob_roots_distinct_aux1_proof)
    . show (6 : ℝ) * Real.pi / (7 : ℝ) ≤ Real.pi
      exact le_of_lt subprob_roots_distinct_aux4_proof
    . show (4 : ℝ) * Real.pi / (7 : ℝ) < (6 : ℝ) * Real.pi / (7 : ℝ)
      exact subprob_roots_distinct_aux2_proof
  have subprob_r₁_ne_r₂_proof : r₁ ≠ r₂ := by
    mkOpaque
    apply @_root_.ne_of_gt
    exact subprob_r₁_gt_r₂_proof
  have subprob_r₁_ne_r₃_proof : r₁ ≠ r₃ := by
    mkOpaque
    have h_r1_gt_r3 : r₁ > r₃ := by exact gt_trans subprob_r₁_gt_r₂_proof subprob_r₂_gt_r₃_proof
    apply @_root_.ne_of_gt
    exact h_r1_gt_r3
  have subprob_r₂_ne_r₃_proof : r₂ ≠ r₃ := by
    mkOpaque
    apply @_root_.ne_of_gt
    exact subprob_r₂_gt_r₃_proof
  letI P := Polynomial.X ^ (3 : ℕ) + (Polynomial.C a) * Polynomial.X ^ (2 : ℕ) + (Polynomial.C b) * Polynomial.X + (Polynomial.C c)
  retro' P_def : P = X ^ (3 : ℕ) + C a * X ^ (2 : ℕ) + C b * X + C c := by funext; rfl
  have subprob_P_eval_expr_proof : ∀ x : ℝ, Polynomial.eval x P = x ^ 3 + a * x ^ 2 + b * x + c := by
    mkOpaque
    intro x
    rw [P_def]
    simp
  have subprob_P_eval_eq_f_proof : ∀ x : ℝ, Polynomial.eval x P = f x := by
    mkOpaque
    intro x
    rw [subprob_P_eval_expr_proof x]
    rw [h₀ x]
  have subprob_P_natDegree_proof : Polynomial.natDegree P = 3 := by
    mkOpaque
    rw [P_def]
    have h_deg_P₁ : Polynomial.natDegree (X ^ 3 : ℝ[X]) = 3 := by exact Polynomial.natDegree_X_pow 3
    have h_deg_P₂_le : Polynomial.natDegree (C a * X ^ 2 + (C b * X + C c) : ℝ[X]) ≤ 2 := by
      apply Nat.le_trans (Polynomial.natDegree_add_le (C a * X ^ 2) (C b * X + C c))
      have h_deg_CaX2 : Polynomial.natDegree (C a * X ^ 2) ≤ 2 := by exact Polynomial.natDegree_C_mul_X_pow_le a 2
      have h_deg_CbX_Cc : Polynomial.natDegree (C b * X + C c) ≤ 1 := by
        apply Nat.le_trans (Polynomial.natDegree_add_le (C b * X) (C c))
        apply max_le_iff.mpr
        constructor
        · by_cases h_b_eq_0 : b = 0
          · simp_rw [h_b_eq_0, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero]
            decide
          · rw [Polynomial.natDegree_C_mul_X b h_b_eq_0]
        · apply Nat.le_trans (Polynomial.natDegree_C c).le
          apply Nat.zero_le
      apply max_le h_deg_CaX2
      apply Nat.le_trans h_deg_CbX_Cc
      decide
    have h_deg_P₂_lt_P₁ : Polynomial.natDegree (C a * X ^ 2 + (C b * X + C c) : ℝ[X]) < Polynomial.natDegree (X ^ 3 : ℝ[X]) := by
      rw [h_deg_P₁]
      linarith [h_deg_P₂_le]
    rw [add_assoc ((X ^ 3 : ℝ[X]) + C a * X ^ 2) (C b * X) (C c)]
    rw [add_assoc (X ^ 3 : ℝ[X]) (C a * X ^ 2) (C b * X + C c)]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h_deg_P₂_lt_P₁]
    exact h_deg_P₁
  have subprob_P_coeff3_proof : Polynomial.coeff P 3 = (1 : ℝ) := by
    mkOpaque
    rw [P_def]
    simp only [Polynomial.coeff_add]
    have h_coeff_X_pow_3 : Polynomial.coeff (X ^ 3) 3 = (1 : ℝ) := by
      rw [Polynomial.coeff_X_pow 3 3]
      rw [if_pos (rfl : 3 = 3)]
    rw [h_coeff_X_pow_3]
    have h_coeff_C_a_X_sq : Polynomial.coeff (Polynomial.C a * X ^ 2) 3 = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow a 2 3]
      rw [if_neg (by norm_num : 3 ≠ 2)]
    rw [h_coeff_C_a_X_sq]
    have h_coeff_C_b_X : Polynomial.coeff (Polynomial.C b * X) 3 = 0 := by
      rw [Polynomial.coeff_C_mul_X b 3]
      rw [if_neg (by norm_num : 3 ≠ 1)]
    rw [h_coeff_C_b_X]
    have h_coeff_C_c : Polynomial.coeff (Polynomial.C c) 3 = 0 := by
      rw [Polynomial.coeff_C]
      rw [if_neg (by norm_num : 3 ≠ 0)]
    rw [h_coeff_C_c]
    norm_num
  have subprob_P_coeff2_proof : Polynomial.coeff P 2 = a := by
    mkOpaque
    rw [P_def]
    simp only [coeff_add]
    have h_coeff_X3 : coeff (X ^ (3 : ℕ) : ℝ[X]) 2 = 0 := by
      rw [Polynomial.coeff_X_pow 3 2]
      simp
    rw [h_coeff_X3]
    have h_coeff_CaX2 : coeff (C a * X ^ (2 : ℕ) : ℝ[X]) 2 = a := by
      rw [Polynomial.coeff_C_mul_X_pow a 2 2]
      simp
    rw [h_coeff_CaX2]
    have h_coeff_CbX : coeff (C b * X : ℝ[X]) 2 = 0 := by
      rw [coeff_C_mul_X b 2]
      simp
    rw [h_coeff_CbX]
    have h_coeff_Cc : coeff (C c : ℝ[X]) 2 = 0 := by
      apply Polynomial.coeff_C_ne_zero
      decide
    rw [h_coeff_Cc]
    simp
  have subprob_P_coeff1_proof : Polynomial.coeff P 1 = b := by
    mkOpaque
    rw [P_def]
    simp
  have subprob_P_coeff0_proof : Polynomial.coeff P 0 = c := by
    mkOpaque
    rw [P_def]
    rw [Polynomial.coeff_add]
    rw [Polynomial.coeff_C_zero]
    rw [add_left_eq_self]
    rw [Polynomial.coeff_add]
    rw [Polynomial.coeff_mul_X_zero]
    rw [add_zero]
    rw [Polynomial.coeff_add]
    rw [Polynomial.coeff_X_pow 3 0]
    rw [if_neg (show (0 : ℕ) ≠ 3 by decide)]
    rw [zero_add]
    rw [Polynomial.coeff_C_mul_X_pow a 2 0]
    rw [if_neg (show (0 : ℕ) ≠ 2 by decide)]
  have subprob_P_monic_proof : Polynomial.Monic P := by
    mkOpaque
    rw [Polynomial.Monic]
    rw [Polynomial.leadingCoeff]
    rw [subprob_P_natDegree_proof]
    exact subprob_P_coeff3_proof
  have subprob_P_is_root_r₁_proof : Polynomial.IsRoot P r₁ := by
    mkOpaque
    rw [Polynomial.IsRoot]
    rw [subprob_P_eval_eq_f_proof r₁]
    rw [← Set.mem_singleton_iff, ← Set.mem_preimage, h₁]
    rw [r₁_def]
    simp
  have subprob_P_is_root_r₂_proof : Polynomial.IsRoot P r₂ := by
    mkOpaque
    rw [Polynomial.IsRoot.def]
    rw [subprob_P_eval_eq_f_proof]
    rw [← Set.mem_singleton_iff]
    rw [← Set.mem_preimage]
    rw [h₁]
    rw [r₂_def]
    apply Set.mem_insert_of_mem
    apply Set.mem_insert
  have subprob_P_is_root_r₃_proof : Polynomial.IsRoot P r₃ := by
    mkOpaque
    rw [Polynomial.IsRoot.def]
    rw [subprob_P_eval_eq_f_proof r₃]
    rw [← (Set.mem_preimage.trans Set.mem_singleton_iff)]
    rw [h₁]
    rw [r₃_def]
    simp
  letI Rts_ms := Polynomial.roots P
  retro' Rts_ms_def : Rts_ms = roots P := by funext; rfl
  have subprob_roots_multiset_eq_r1r2r3_proof : Rts_ms = ({ r₁, r₂, r₃ } : Multiset ℝ) := by
    mkOpaque
    rw [Rts_ms_def]
    let S : Multiset ℝ := { r₁, r₂, r₃ }
    have hS_nodup : S.Nodup := by
      dsimp [S]
      rw [Multiset.nodup_cons]
      constructor
      . simp only [Multiset.mem_cons, Multiset.mem_singleton, not_or]
        exact ⟨subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof⟩
      . dsimp
        rw [Multiset.nodup_cons]
        constructor
        . simp only [Multiset.mem_singleton]
          exact subprob_r₂_ne_r₃_proof
        . exact Multiset.nodup_singleton _
    have h_all_S_are_roots : ∀ r ∈ S, IsRoot P r := by
      intro r hr_mem
      dsimp [S] at hr_mem
      simp only [Multiset.mem_cons, Multiset.mem_singleton, Multiset.not_mem_zero] at hr_mem
      rcases hr_mem with (h_r_eq_r1 | h_r_eq_r2 | h_r_eq_r3)
      . subst h_r_eq_r1
        exact subprob_P_is_root_r₁_proof
      . subst h_r_eq_r2
        exact subprob_P_is_root_r₂_proof
      . subst h_r_eq_r3
        exact subprob_P_is_root_r₃_proof
    have hS_card_eq_3 : Multiset.card S = 3 := by
      dsimp [S]
      rw [Multiset.card_cons]
      rw [Multiset.card_cons]
      rw [Multiset.card_singleton]
    apply Eq.symm
    apply Multiset.eq_of_le_of_card_le
    . apply (Multiset.le_iff_count).mpr
      intro x
      by_cases hxS : x ∈ S
      . rw [Multiset.count_eq_one_of_mem hS_nodup hxS]
        rw [Nat.one_le_iff_ne_zero, Multiset.count_ne_zero]
        have hP_ne_0 : P ≠ 0 := Polynomial.Monic.ne_zero subprob_P_monic_proof
        apply (Polynomial.mem_roots hP_ne_0).mpr
        exact h_all_S_are_roots x hxS
      . rw [Multiset.count_eq_zero_of_not_mem hxS]
        exact Nat.zero_le _
    . rw [hS_card_eq_3]
      have hP_ne_0 : P ≠ 0 := Monic.ne_zero subprob_P_monic_proof
      have h_card_roots_P_le_natDegree_P := Polynomial.card_roots' P
      rw [subprob_P_natDegree_proof] at h_card_roots_P_le_natDegree_P
      exact h_card_roots_P_le_natDegree_P
  have subprob_card_Rts_ms_eq_3_proof : Multiset.card Rts_ms = 3 := by
    mkOpaque
    rw [subprob_roots_multiset_eq_r1r2r3_proof]
    have h_nodup_r123 : Multiset.Nodup ({ r₁, r₂, r₃ } : Multiset ℝ) := by
      dsimp
      rw [Multiset.nodup_cons]
      constructor
      · simp [subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof]
      · rw [Multiset.nodup_cons]
        constructor
        · simp [subprob_r₂_ne_r₃_proof]
        · rw [(@Multiset.singleton_eq_cons_iff ℝ r₃ r₃ 0).mpr ⟨rfl, rfl⟩]
          rw [Multiset.nodup_cons]
          constructor
          · simp
          · exact Multiset.nodup_zero
    have h_toFinset_eq : ({ r₁, r₂, r₃ } : Multiset ℝ).toFinset = ({ r₁, r₂, r₃ } : Finset ℝ) := by
      dsimp
      rw [Multiset.toFinset_cons]
      rw [Multiset.toFinset_cons]
      rw [(@Multiset.singleton_eq_cons_iff ℝ r₃ r₃ (0 : Multiset ℝ)).mpr ⟨rfl, rfl⟩]
      rw [Multiset.toFinset_cons]
      rw [Multiset.toFinset_zero]
      rfl
    have h_val_eq_self_of_nodup : (({ r₁, r₂, r₃ } : Multiset ℝ).toFinset).val = ({ r₁, r₂, r₃ } : Multiset ℝ) := by
      rw [Multiset.toFinset_val]
      rw [Multiset.dedup_eq_self]
      exact h_nodup_r123
    rw [← h_val_eq_self_of_nodup, h_toFinset_eq]
    rw [Finset.card_val]
    simp [subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof, subprob_r₂_ne_r₃_proof]
  have subprob_card_roots_eq_natDegree_proof : Multiset.card Rts_ms = Polynomial.natDegree P := by
    mkOpaque
    rw [subprob_card_Rts_ms_eq_3_proof]
    rw [subprob_P_natDegree_proof]
  have subprob_P_splits_proof : Polynomial.Splits (RingHom.id ℝ) P := by
    mkOpaque
    apply (Polynomial.splits_iff_card_roots (K := ℝ) (p := P)).mpr
    rw [← Rts_ms_def]
    exact subprob_card_roots_eq_natDegree_proof
  letI S₁ := r₁ + r₂ + r₃
  retro' S₁_def : S₁ = r₁ + r₂ + r₃ := by funext; rfl
  letI S₂ := r₁ * r₂ + r₁ * r₃ + r₂ * r₃
  retro' S₂_def : S₂ = r₁ * r₂ + r₁ * r₃ + r₂ * r₃ := by funext; rfl
  letI S₃ := r₁ * r₂ * r₃
  retro' S₃_def : S₃ = r₁ * r₂ * r₃ := by funext; rfl
  have subprob_S₁_eq_esymm_roots_1_proof : S₁ = Multiset.esymm Rts_ms 1 := by
    mkOpaque
    rw [S₁_def]
    rw [subprob_roots_multiset_eq_r1r2r3_proof]
    have esymm_eq_sum_for_roots : Multiset.esymm ({ r₁, r₂, r₃ } : Multiset ℝ) 1 = Multiset.sum ({ r₁, r₂, r₃ } : Multiset ℝ) := by
      let s_roots := ({ r₁, r₂, r₃ } : Multiset ℝ)
      unfold Multiset.esymm
      have h_powerset_inst : Multiset.powersetCard 1 s_roots = Multiset.map (fun x => ({ x } : Multiset ℝ)) s_roots := Multiset.powersetCard_one s_roots
      rw [h_powerset_inst]
      rw [Multiset.map_map]
      have h_comp_prod_singleton : Multiset.prod ∘ (fun x : ℝ => ({ x } : Multiset ℝ)) = id := by
        funext x
        simp only [Function.comp_apply, Multiset.prod_singleton]
        rfl
      rw [h_comp_prod_singleton]
      rw [Multiset.map_id]
    rw [esymm_eq_sum_for_roots]
    simp
    ring
  have subprob_S₂_eq_esymm_roots_2_proof : S₂ = Multiset.esymm Rts_ms 2 := by
    mkOpaque
    rw [S₂_def]
    rw [subprob_roots_multiset_eq_r1r2r3_proof]
    rw [Multiset.esymm]
    simp [*, Multiset.powersetCard_one, Multiset.map_singleton, Multiset.prod_singleton, Multiset.sum_singleton, add_comm, mul_comm, add_assoc]
  have subprob_S₃_eq_esymm_roots_3_proof : S₃ = Multiset.esymm Rts_ms 3 := by
    mkOpaque
    rw [S₃_def]
    rw [subprob_roots_multiset_eq_r1r2r3_proof]
    have h_card_eq_k : Multiset.card ({ r₁, r₂, r₃ } : Multiset ℝ) = 3 := by simp
    have h_esymm_rw : Multiset.esymm ({ r₁, r₂, r₃ } : Multiset ℝ) 3 = Multiset.prod ({ r₁, r₂, r₃ } : Multiset ℝ) := by
      rw [← h_card_eq_k]
      rw [Multiset.esymm]
      let M_val := ({ r₁, r₂, r₃ } : Multiset ℝ)
      have H_powerset_card_eq : Multiset.powersetCard (Multiset.card M_val) M_val = { M_val } := by
        rw [(show Multiset.card M_val = 3 from h_card_eq_k)]
        let M0 := (0 : Multiset ℝ)
        let M1 := r₃ ::ₘ M0
        let M2 := r₂ ::ₘ M1
        have H_M0_card : Multiset.card M0 = 0 := Multiset.card_zero
        have H_M1_card : Multiset.card M1 = 1 := by rw [Multiset.card_cons, H_M0_card]
        have H_M2_card : Multiset.card M2 = 2 := by rw [Multiset.card_cons, H_M1_card]
        have h_powerset_M0 : Multiset.powersetCard 0 M0 = { M0 } := by exact Multiset.powersetCard_zero_left M0
        have h_powerset_M1 : Multiset.powersetCard 1 M1 = { M1 } := by
          rw [show M1 = r₃ ::ₘ M0 by rfl, Multiset.powersetCard_cons 0 r₃ M0]
          have h_first_term_zero : Multiset.powersetCard ((0 : ℕ) + 1) M0 = 0 := by
            rw [← H_M0_card]
            exact Multiset.powersetCard_card_add M0 Nat.one_pos
          rw [h_first_term_zero]
          rw [zero_add]
          rw [h_powerset_M0]
          rw [Multiset.map_singleton]
        have h_powerset_M2 : Multiset.powersetCard 2 M2 = { M2 } := by
          rw [show M2 = r₂ ::ₘ M1 by rfl]
          rw [Multiset.powersetCard_cons 1 r₂ M1]
          have h_card_M1_lt_2 : Multiset.card M1 < 2 := by (rw [H_M1_card]; norm_num)
          have h_term1_zero : Multiset.powersetCard 2 M1 = 0 := Multiset.powersetCard_eq_empty 2 h_card_M1_lt_2
          rw [h_term1_zero, zero_add]
          rw [h_powerset_M1]
          rw [Multiset.map_singleton]
        rw [show M_val = r₁ ::ₘ M2 by rfl, Multiset.powersetCard_cons 2 r₁ M2]
        have h_first_term_zero' : Multiset.powersetCard ((2 : ℕ) + 1) M2 = 0 := by
          rw [← H_M2_card]
          exact Multiset.powersetCard_card_add M2 Nat.one_pos
        rw [h_first_term_zero']
        rw [zero_add]
        rw [h_powerset_M2]
        rw [Multiset.map_singleton]
      rw [H_powerset_card_eq]
      rw [Multiset.map_singleton]
      rw [Multiset.sum_singleton]
    rw [h_esymm_rw]
    simp
    ring
  have subprob_natDeg_P_minus_2_is_1_proof : Polynomial.natDegree P - 2 = 1 := by
    mkOpaque
    rw [subprob_P_natDegree_proof]
  have subprob_vieta_coeff2_form_proof : Polynomial.coeff P 2 = (-1 : ℝ) ^ (Polynomial.natDegree P - 2) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 2) := by
    mkOpaque
    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof
    let j_for_theorem := Polynomial.natDegree P - 2
    have h_j_le_deg : j_for_theorem ≤ natDegree P := by apply Nat.sub_le (natDegree P) 2
    have vieta_result : coeff P (natDegree P - j_for_theorem) = (-1 : ℝ) ^ j_for_theorem * Multiset.esymm (roots P) j_for_theorem := by
      have h_k_idx_le_deg : (natDegree P - j_for_theorem) ≤ natDegree P := by apply Nat.sub_le (natDegree P) j_for_theorem
      have h_main_vieta_eq := Polynomial.coeff_eq_esymm_roots_of_card h_card_roots_eq_natDegree h_k_idx_le_deg
      rw [Nat.sub_sub_self h_j_le_deg] at h_main_vieta_eq
      rw [subprob_P_monic_proof] at h_main_vieta_eq
      rw [one_mul] at h_main_vieta_eq
      exact h_main_vieta_eq
    have h_2_le_natDegree_P : 2 ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num
    have coeff_index_simpl : natDegree P - j_for_theorem = 2 := by apply Nat.sub_sub_self h_2_le_natDegree_P
    rw [coeff_index_simpl] at vieta_result
    rw [← Rts_ms_def] at vieta_result
    exact vieta_result
  have subprob_coeff_P_2_eq_neg_S₁_proof : Polynomial.coeff P 2 = -S₁ := by
    mkOpaque
    rw [subprob_vieta_coeff2_form_proof]
    rw [subprob_natDeg_P_minus_2_is_1_proof]
    rw [pow_one (-(1 : ℝ))]
    rw [subprob_S₁_eq_esymm_roots_1_proof]
    rw [neg_one_mul]
  have subprob_vieta_a_proof : a = -S₁ := by
    mkOpaque
    have h_a_eq_coeffP2 : a = coeff P (2 : ℕ) := by exact subprob_P_coeff2_proof.symm
    have h_coeffP2_eq_negS1 : coeff P (2 : ℕ) = -S₁ := by exact subprob_coeff_P_2_eq_neg_S₁_proof
    rw [h_a_eq_coeffP2]
    exact h_coeffP2_eq_negS1
  have subprob_natDeg_P_minus_1_is_2_proof : Polynomial.natDegree P - 1 = 2 := by
    mkOpaque
    rw [subprob_P_natDegree_proof]
  have subprob_vieta_coeff1_form_proof : Polynomial.coeff P 1 = (-1 : ℝ) ^ (Polynomial.natDegree P - 1) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 1) := by
    mkOpaque
    rw [Rts_ms_def]
    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof
    have h_one_le_natDegree : (1 : ℕ) ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num
    rw [Polynomial.coeff_eq_esymm_roots_of_card h_card_roots_eq_natDegree h_one_le_natDegree]
    rw [subprob_P_monic_proof]
    rw [one_mul]
  have subprob_coeff_P_1_eq_S₂_proof : Polynomial.coeff P 1 = S₂ := by
    mkOpaque
    rw [subprob_vieta_coeff1_form_proof]
    rw [subprob_natDeg_P_minus_1_is_2_proof]
    simp
    rw [← subprob_S₂_eq_esymm_roots_2_proof]
  have subprob_vieta_b_proof : b = S₂ := by
    mkOpaque
    have h1 : b = coeff P (1 : ℕ) := by exact Eq.symm subprob_P_coeff1_proof
    have h2 : coeff P (1 : ℕ) = S₂ := by exact subprob_coeff_P_1_eq_S₂_proof
    rw [h1]
    rw [h2]
  have subprob_natDeg_P_minus_0_is_3_proof : Polynomial.natDegree P - 0 = 3 := by
    mkOpaque
    rw [subprob_P_natDegree_proof]
  have subprob_vieta_coeff0_form_proof : Polynomial.coeff P 0 = (-1 : ℝ) ^ (Polynomial.natDegree P - 0) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 0) := by
    mkOpaque
    have h_k_le_natDegree : 0 ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num
    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof
    have h_vieta := Polynomial.coeff_eq_esymm_roots_of_card h_card_roots_eq_natDegree h_k_le_natDegree
    rw [Polynomial.leadingCoeff, Monic.coeff_natDegree subprob_P_monic_proof, one_mul] at h_vieta
    rw [← Rts_ms_def] at h_vieta
    exact h_vieta
  have subprob_coeff_P_0_eq_neg_S₃_proof : Polynomial.coeff P 0 = -S₃ := by
    mkOpaque
    rw [subprob_vieta_coeff0_form_proof]
    rw [subprob_natDeg_P_minus_0_is_3_proof]
    have h_pow_neg_one_cubed : (-(1 : ℝ)) ^ (3 : ℕ) = -1 := by norm_num
    rw [h_pow_neg_one_cubed]
    rw [subprob_S₃_eq_esymm_roots_3_proof]
    rw [neg_mul, one_mul]
  have subprob_vieta_c_proof : c = -S₃ := by
    mkOpaque
    rw [← subprob_P_coeff0_proof]
    exact subprob_coeff_P_0_eq_neg_S₃_proof
  have subprob_abc_eq_S1S2S3_proof : a * b * c = S₁ * S₂ * S₃ := by
    mkOpaque
    rw [subprob_vieta_a_proof]
    rw [subprob_vieta_b_proof]
    rw [subprob_vieta_c_proof]
    simp
  letI z := Complex.exp ((2 * Real.pi / 7) * Complex.I)
  retro' z_def : z = cexp ((2 : ℂ) * ofReal' Real.pi / (7 : ℂ) * I) := by funext; rfl
  have subprob_z_pow_7_eq_1_proof : z ^ (7 : ℕ) = (1 : ℂ) := by
    mkOpaque
    rw [z_def]
    have h_arg_coerce : (2 : ℂ) * Complex.ofReal Real.pi / (7 : ℂ) = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) := by simp
    change (Complex.exp (((2 : ℂ) * Complex.ofReal Real.pi / (7 : ℂ)) * I)) ^ (7 : ℕ) = (1 : ℂ)
    rw [h_arg_coerce]
    rw [← Complex.exp_nsmul]
    rw [nsmul_eq_mul]
    rw [← mul_assoc]
    have h_complex_coeff_simplify : (↑(7 : ℕ) : ℂ) * Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) = Complex.ofReal ((2 : ℝ) * Real.pi) := by
      rw [← Complex.ofReal_natCast]
      simp only [Complex.ofReal_eq_coe]
      rw [← Complex.ofReal_mul]
      apply congr_arg Complex.ofReal
      norm_cast
      field_simp [(by norm_num : (7 : ℝ) ≠ 0)]
    rw [h_complex_coeff_simplify]
    apply Complex.ext_iff.mpr
    constructor
    . rw [Complex.ofReal_eq_coe]
      rw [Complex.exp_ofReal_mul_I_re]
      rw [Complex.one_re]
      rw [Real.cos_two_pi]
    . rw [Complex.ofReal_eq_coe]
      rw [Complex.exp_ofReal_mul_I_im]
      rw [Complex.one_im]
      rw [Real.sin_two_pi]
  have subprob_z_ne_1_proof : z ≠ (1 : ℂ) := by
    mkOpaque
    by_contra h_contra
    let θ₀ : ℝ := (2 * Real.pi) / 7
    have h_arg_rewrite : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) * I = (↑θ₀ : ℂ) * I := by simp [θ₀]
    rw [z_def, h_arg_rewrite] at h_contra
    rw [mul_comm (↑θ₀ : ℂ) I] at h_contra
    rw [Complex.exp_eq_one_iff] at h_contra
    rcases h_contra with ⟨k, hk_complex_eq⟩
    have hk : θ₀ = (↑(2 * k) : ℝ) * Real.pi :=
      by
      have h_rhs_transformed : ((↑k : ℂ) * ((2 : ℂ) * (ofReal' Real.pi : ℂ))) * I = (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi)) : ℂ) * I := by
        rw [mul_left_inj' Complex.I_ne_zero]
        rw [← Complex.ofReal_intCast k]
        rw [← Complex.ofReal_ofNat 2]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        apply Complex.ofReal_inj.mpr
        apply congr_arg ((↑(k) : ℝ) * ·)
        apply congr_arg (· * Real.pi)
        exact Nat.cast_two
      have h_eq_rewritten : I * (↑θ₀ : ℂ) = (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi)) : ℂ) * I := by
        rw [hk_complex_eq]
        rw [← mul_assoc (↑k : ℂ) ((2 : ℂ) * (ofReal' Real.pi : ℂ)) I]
        rw [h_rhs_transformed]
      rw [mul_comm (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi))) I] at h_eq_rewritten
      replace h_eq_rewritten := (mul_right_inj' Complex.I_ne_zero).mp h_eq_rewritten
      rw [Complex.ofReal_eq_coe] at h_eq_rewritten
      rw [Complex.ofReal_inj] at h_eq_rewritten
      rw [h_eq_rewritten]
      rw [← mul_assoc]
      rw [mul_comm ((k : ℝ) : ℝ) (2 : ℝ)]
      rw [← Int.cast_two]
      rw [← Int.cast_mul]
    have hk_val_subst : (2 * Real.pi) / 7 = (↑(2 * k) : ℝ) * Real.pi := by rw [← hk]
    have h_cast_detail : (↑(2 * k) : ℝ) = (2 : ℝ) * (k : ℝ) := by rw [Int.cast_mul, Int.cast_two]
    rw [h_cast_detail] at hk_val_subst
    have h_two_pi_ne_zero : 2 * Real.pi ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact Real.pi_ne_zero
    have h_frac_eq_int_real : (1 / 7 : ℝ) = (k : ℝ) := by
      have h_rhs_rearranged : (2 : ℝ) * (k : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) := by ac_rfl
      have h_eq_rearranged : (2 * Real.pi) / 7 = (k : ℝ) * (2 * Real.pi) := by rw [hk_val_subst, h_rhs_rearranged]
      rw [div_eq_mul_inv] at h_eq_rearranged
      rw [mul_comm ((2 : ℝ) * Real.pi) (7 : ℝ)⁻¹] at h_eq_rearranged
      rw [mul_eq_mul_right_iff] at h_eq_rearranged
      cases h_eq_rearranged with
      | inl h_eq =>
        rw [inv_eq_one_div] at h_eq
        exact h_eq
      | inr h_zero_pi => exfalso; exact h_two_pi_ne_zero h_zero_pi
    have h_k_mul_7_eq_1 : (k : ℤ) * 7 = 1 := by
      rw [← Int.cast_inj (α := ℝ)]
      rw [Int.cast_mul, Int.cast_ofNat 7]
      rw [← h_frac_eq_int_real]
      field_simp
    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at h_k_mul_7_eq_1
    cases h_k_mul_7_eq_1 with
    | inl h_left =>
      have h_7_eq_1 : (7 : ℤ) = 1 := h_left.right
      contradiction
    | inr h_right =>
      have h_7_eq_neg_1 : (7 : ℤ) = -1 := h_right.right
      contradiction
  have subprob_sum_z_k_0_6_eq_0_proof : ∑ k in Finset.range (7 : ℕ), z ^ k = (0 : ℂ) := by
    mkOpaque
    have h_z_minus_one_ne_zero : z - (1 : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact subprob_z_ne_1_proof
    have h_sum_eq_zero_iff_pow_eq_one : (∑ k in Finset.range (7 : ℕ), z ^ k = 0) ↔ z ^ (7 : ℕ) = 1 := by
      have h_seven_pos : 0 < (7 : ℕ) := by norm_num
      have h_geom_sum_formula : ∑ k in Finset.range (7 : ℕ), z ^ k = (z ^ (7 : ℕ) - 1) / (z - 1) := geom_sum_eq subprob_z_ne_1_proof (7 : ℕ)
      rw [h_geom_sum_formula]
      have h_div_form_equiv : ((z ^ (7 : ℕ) - (1 : ℂ)) / (z - (1 : ℂ)) = (0 : ℂ)) ↔ ((z ^ (7 : ℕ) - (1 : ℂ)) = (0 : ℂ) ∨ z - (1 : ℂ) = (0 : ℂ)) := div_eq_zero_iff
      rw [h_div_form_equiv]
      rw [or_iff_left h_z_minus_one_ne_zero]
      rw [sub_eq_zero]
    apply h_sum_eq_zero_iff_pow_eq_one.mpr
    exact subprob_z_pow_7_eq_1_proof
  letI sum_zk_1_to_6 := ∑ k in Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k
  retro' sum_zk_1_to_6_def : sum_zk_1_to_6 = ∑ k ∈ Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k := by funext; rfl
  have subprob_sum_z_k_1_6_eq_neg_1_proof : sum_zk_1_to_6 = (-1 : ℂ) := by
    mkOpaque
    have h_sum_total : ∑ k ∈ Finset.range (7 : ℕ), z ^ k = (0 : ℂ) := by exact subprob_sum_z_k_0_6_eq_0_proof
    have h_decomp_sum : ∑ k ∈ Finset.range 7, z ^ k = z ^ 0 + ∑ k ∈ Finset.range 6, z ^ (k + 1) := by
      rw [add_comm]
      exact Finset.sum_range_succ' (fun k => z ^ k) 6
    have h_z_pow_0 : z ^ (0 : ℕ) = (1 : ℂ) := by exact pow_zero z
    rw [h_z_pow_0] at h_decomp_sum
    rw [h_decomp_sum] at h_sum_total
    have h_sum_shifted_eq_sum_Ioo : ∑ k ∈ Finset.range 6, z ^ (k + 1) = ∑ k ∈ Finset.Ioo 0 7, z ^ k :=
      by
      have h_sum_map : ∑ k ∈ Finset.range 6, z ^ (k + 1) = ∑ k ∈ Finset.Ico 1 (6 + 1), z ^ k := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add' (fun i => z ^ i) 0 6 1
      rw [h_sum_map]
      rw [Nat.add_one]
      have h_Ico_eq_Ioo : Finset.Ico (1 : ℕ) 7 = Finset.Ioo (0 : ℕ) 7 := by
        rw [← Finset.Ico_erase_left (0 : ℕ) 7]
        ext x
        simp [Nat.one_le_iff_ne_zero, Nat.zero_le]
      rw [h_Ico_eq_Ioo]
    rw [h_sum_shifted_eq_sum_Ioo] at h_sum_total
    rw [← sum_zk_1_to_6_def] at h_sum_total
    rw [add_comm] at h_sum_total
    exact (add_eq_zero_iff_eq_neg.mp h_sum_total)
  letI R₁_complex := (z + z ^ (6 : ℕ)) / (2 : ℂ)
  retro' R₁_complex_def : R₁_complex = (z + z ^ (6 : ℕ)) / (2 : ℂ) := by funext; rfl
  letI R₂_complex := (z ^ (2 : ℕ) + z ^ (5 : ℕ)) / (2 : ℂ)
  retro' R₂_complex_def : R₂_complex = (z ^ (2 : ℕ) + z ^ (5 : ℕ)) / (2 : ℂ) := by funext; rfl
  letI R₃_complex := (z ^ (3 : ℕ) + z ^ (4 : ℕ)) / (2 : ℂ)
  retro' R₃_complex_def : R₃_complex = (z ^ (3 : ℕ) + z ^ (4 : ℕ)) / (2 : ℂ) := by funext; rfl
  have subprob_ofReal_r₁_eq_R₁_proof : Complex.ofReal r₁ = R₁_complex := by
    mkOpaque
    rw [r₁_def, R₁_complex_def]
    let θ_real : ℝ := (2 : ℝ) * Real.pi / (7 : ℝ)
    have h_z_arg_eq_ofReal_θ_real : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) = Complex.ofReal θ_real := by
      dsimp only [θ_real]
      simp
    have h_z_alt : z = cexp (Complex.ofReal θ_real * I) := by
      rw [z_def]
      dsimp only [ofReal']
      rw [← Complex.ofReal_def Real.pi]
      apply congr_arg cexp
      apply congr_arg (fun x => x * I)
      exact h_z_arg_eq_ofReal_θ_real
    rw [h_z_alt]
    have hw_pow_7_eq_1 : (cexp (Complex.ofReal θ_real * I)) ^ 7 = 1 := by
      rw [← h_z_alt]
      exact subprob_z_pow_7_eq_1_proof
    have hw_ne_zero : cexp (Complex.ofReal θ_real * I) ≠ 0 := by
      intro hw_eq_zero
      have hw_pow_7_eq_zero : (cexp (Complex.ofReal θ_real * I)) ^ 7 = 0 ^ 7 := by rw [hw_eq_zero]
      rw [zero_pow (by norm_num)] at hw_pow_7_eq_zero
      rw [hw_pow_7_eq_1] at hw_pow_7_eq_zero
      exact one_ne_zero hw_pow_7_eq_zero
    have hw_pow_6_eq_inv_w : (cexp (Complex.ofReal θ_real * I)) ^ 6 = (cexp (Complex.ofReal θ_real * I))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ (cexp (Complex.ofReal θ_real * I)) 6]
      exact hw_pow_7_eq_1
    have h_inv_w_is_exp_neg : (cexp (Complex.ofReal θ_real * I))⁻¹ = cexp (-(Complex.ofReal θ_real * I)) := by rw [Complex.exp_neg]
    rw [hw_pow_6_eq_inv_w, h_inv_w_is_exp_neg]
    simp_rw [mul_comm (Complex.ofReal θ_real) I]
    change (Complex.ofReal (Real.cos θ_real) = _)
    have h_cos_def_applied : Complex.cos (Complex.ofReal θ_real) = (cexp (I * Complex.ofReal θ_real) + cexp (-(I * Complex.ofReal θ_real))) / (2 : ℂ) := by
      unfold Complex.cos
      simp_rw [mul_comm (Complex.ofReal θ_real) I]
      ring
    rw [← h_cos_def_applied]
    exact Complex.ofReal_cos θ_real
  have subprob_ofReal_r₂_eq_R₂_proof : Complex.ofReal r₂ = R₂_complex := by
    mkOpaque
    rw [r₂_def, R₂_complex_def, z_def]
    have hz_arg_rewrite : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) * I = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) * I := by
      apply congr_arg (fun x => x * I)
      change (Nat.cast 2 : ℂ) * ofReal' Real.pi / (Nat.cast 7 : ℂ) = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ))
      rw [(Complex.ofReal_natCast (2 : ℕ)).symm, (Complex.ofReal_natCast (7 : ℕ)).symm]
      rw [← Complex.ofReal_mul]
      rw [← Complex.ofReal_div]
      apply congr_arg Complex.ofReal
      simp only [Nat.cast_ofNat]
    rw [hz_arg_rewrite]
    let angle_unit : ℝ := (2 : ℝ) * Real.pi / (7 : ℝ)
    have h_z_pow_2 : cexp (Complex.ofReal angle_unit * I) ^ (2 : ℕ) = cexp (Complex.ofReal (↑(2 : ℕ) * angle_unit) * I) := by
      rw [← Complex.exp_nat_mul (Complex.ofReal angle_unit * I) (2 : ℕ)]
      apply congr_arg Complex.exp
      have h_cast_eq_2 : (Nat.cast 2 : ℂ) = Complex.ofReal (Nat.cast 2 : ℝ) := (Complex.ofReal_natCast 2).symm
      rw [h_cast_eq_2]
      rw [← mul_assoc]
      change (Complex.ofReal (Nat.cast 2 : ℝ) * Complex.ofReal angle_unit) * I = (ofReal' ((Nat.cast 2 : ℝ) * angle_unit)) * I
      rw [Complex.ofReal_mul]
      simp
    have h_z_pow_5 : cexp (Complex.ofReal angle_unit * I) ^ (5 : ℕ) = cexp (Complex.ofReal (↑(5 : ℕ) * angle_unit) * I) := by
      rw [← Complex.exp_nat_mul (Complex.ofReal angle_unit * I) (5 : ℕ)]
      apply congr_arg Complex.exp
      have h_nat_cast_5_eq : (Nat.cast 5 : ℂ) = Complex.ofReal (Nat.cast 5 : ℝ) := (Complex.ofReal_natCast 5).symm
      rw [h_nat_cast_5_eq]
      rw [← mul_assoc]
      change (Complex.ofReal (Nat.cast 5 : ℝ) * Complex.ofReal angle_unit) * I = (ofReal' ((Nat.cast 5 : ℝ) * angle_unit)) * I
      rw [Complex.ofReal_mul]
      simp
    rw [h_z_pow_2, h_z_pow_5]
    have h_2_angle_unit : ↑(2 : ℕ) * angle_unit = (4 : ℝ) * Real.pi / (7 : ℝ) := by
      simp only [angle_unit, Nat.cast_ofNat]
      ring
    have h_5_angle_unit : ↑(5 : ℕ) * angle_unit = (10 : ℝ) * Real.pi / (7 : ℝ) := by
      simp only [angle_unit, Nat.cast_ofNat]
      ring
    rw [h_2_angle_unit, h_5_angle_unit]
    apply Complex.ext_iff.mpr
    constructor
    . change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = re ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (2 : ℂ))
      change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = re ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (Nat.cast (2 : ℕ) : ℂ))
      rw [← Complex.ofReal_natCast (2 : ℕ)]
      rw [Complex.div_ofReal_re]
      rw [Complex.add_re]
      change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = (re (cexp (Complex.ofReal' ((4 : ℝ) * Real.pi / (7 : ℝ)) * I)) + re (cexp (Complex.ofReal' ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (Nat.cast 2 : ℝ)
      rw [Complex.exp_ofReal_mul_I_re]
      rw [Complex.exp_ofReal_mul_I_re]
      field_simp [show (2 : ℝ) ≠ 0 by norm_num]
      rw [mul_comm, ← sub_eq_iff_eq_add]
      have h_angle_equiv : (10 : ℝ) * Real.pi / (7 : ℝ) = 2 * Real.pi - (4 : ℝ) * Real.pi / (7 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        ring
      rw [h_angle_equiv]
      rw [Real.cos_two_pi_sub]
      ring
    . change 0 = im ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (2 : ℂ))
      change 0 = im ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (Nat.cast (2 : ℕ) : ℂ))
      rw [← Complex.ofReal_natCast (2 : ℕ)]
      rw [Complex.div_ofReal_im]
      rw [Complex.add_im]
      change (0 : ℝ) = (im (cexp (ofReal' ((4 : ℝ) * Real.pi / (7 : ℝ)) * I)) + im (cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (↑((2 : ℕ)) : ℝ)
      rw [Complex.exp_ofReal_mul_I_im ((4 : ℝ) * Real.pi / (7 : ℝ))]
      change (0 : ℝ) = (Real.sin ((4 : ℝ) * Real.pi / (7 : ℝ)) + im (cexp (ofReal' ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (↑((2 : ℕ)) : ℝ)
      rw [Complex.exp_ofReal_mul_I_im ((10 : ℝ) * Real.pi / (7 : ℝ))]
      field_simp [show (2 : ℝ) ≠ 0 by norm_num]
      have h_angle_equiv : (10 : ℝ) * Real.pi / (7 : ℝ) = 2 * Real.pi - (4 : ℝ) * Real.pi / (7 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        ring
      rw [h_angle_equiv]
      rw [Real.sin_two_pi_sub]
      rw [add_neg_self]
  have subprob_ofReal_r₃_eq_R₃_proof : Complex.ofReal r₃ = R₃_complex := by
    mkOpaque
    rw [r₃_def]
    rw [R₃_complex_def]
    rw [z_def]
    have hz3 : (cexp ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) ^ (3 : ℕ) = cexp (↑(3 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) := by rw [(Complex.exp_nat_mul _ _).symm]
    rw [hz3]
    have hz4 : (cexp ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) ^ (4 : ℕ) = cexp (↑(4 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) := by rw [(Complex.exp_nat_mul _ _).symm]
    rw [hz4]
    have exp_arg_3 : ↑(3 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I) = ((6 : ℂ) * ↑(Real.pi) / (7 : ℂ)) * I := by
      simp only [Nat.cast_ofNat]
      ring
    rw [exp_arg_3]
    have exp_arg_4 : ↑(4 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I) = ((8 : ℂ) * ↑(Real.pi) / (7 : ℂ)) * I := by
      simp only [Nat.cast_ofNat]
      ring
    rw [exp_arg_4]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    rw [Complex.ofReal_eq_coe, Complex.ofReal_cos]
    have arg3_is_real : ((6 : ℂ) * ↑(Real.pi) / (7 : ℂ)) = ↑((6 : ℝ) * Real.pi / (7 : ℝ)) := by simp [Complex.ofReal_mul, Complex.ofReal_div]
    rw [arg3_is_real]
    have arg4_is_real : ((8 : ℂ) * ↑(Real.pi) / (7 : ℂ)) = ↑((8 : ℝ) * Real.pi / (7 : ℝ)) := by simp [Complex.ofReal_mul, Complex.ofReal_div]
    rw [arg4_is_real]
    apply Complex.ext_iff.mpr
    constructor
    . simp only [Complex.cos_ofReal_re, Complex.add_re, Complex.mul_I_re, Complex.sin_ofReal_im, Complex.ofReal_re, Complex.div_re, Complex.ofReal_im, pow_two, Complex.sin_ofReal_re]
      norm_num
      have h_cos_eq : Real.cos ((6 : ℝ) * Real.pi / 7) = Real.cos ((8 : ℝ) * Real.pi / 7) := by
        have h_arg_rel : (8 : ℝ) * Real.pi / 7 = 2 * Real.pi - (6 : ℝ) * Real.pi / 7 := by field_simp; ring
        rw [h_arg_rel, Real.cos_two_pi_sub]
      rw [h_cos_eq]
      ring
    . simp only [Complex.cos_ofReal_im, Complex.add_im, Complex.mul_I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.ofReal_re, Complex.div_im, Complex.ofReal_im, pow_two, Complex.sin_ofReal_im]
      norm_num
      have h_sin_sum_eq_zero : Real.sin ((6 : ℝ) * Real.pi / 7) + Real.sin ((8 : ℝ) * Real.pi / 7) = 0 := by
        have h_6pi7_eq : (6 : ℝ) * Real.pi / 7 = Real.pi - Real.pi / 7 := by field_simp; ring
        have h_8pi7_eq : (8 : ℝ) * Real.pi / 7 = Real.pi + Real.pi / 7 := by field_simp; ring
        have sin_pi_plus_x (x : ℝ) : Real.sin (Real.pi + x) = -Real.sin x := by rw [add_comm, Real.sin_add_pi x]
        rw [h_6pi7_eq, Real.sin_pi_sub, h_8pi7_eq, sin_pi_plus_x (Real.pi / 7)]
        ring
      rw [h_sin_sum_eq_zero]
      norm_num
  letI S₁_complex_repr := R₁_complex + R₂_complex + R₃_complex
  retro' S₁_complex_repr_def : S₁_complex_repr = R₁_complex + R₂_complex + R₃_complex := by funext; rfl
  have subprob_S₁_complex_calc_proof : S₁_complex_repr = sum_zk_1_to_6 / (2 : ℂ) := by
    mkOpaque
    rw [S₁_complex_repr_def]
    rw [R₁_complex_def, R₂_complex_def, R₃_complex_def]
    rw [sum_zk_1_to_6_def]
    field_simp
    have h_sum_Ioo_to_Ico : ∑ k ∈ Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k = ∑ k ∈ Finset.Ico (0 + 1) 7, z ^ k :=
      by
      have h_finset_equality : Finset.Ioo (0 : ℕ) (7 : ℕ) = Finset.Ico (0 + 1) 7 := by
        ext k
        simp only [Finset.mem_Ioo, Finset.mem_Ico, Nat.lt_iff_add_one_le]
      rw [h_finset_equality]
    rw [h_sum_Ioo_to_Ico]
    simp only [Nat.zero_add]
    rw [Finset.sum_Ico_eq_sum_range (f := fun k => z ^ k) (m := 1) (n := 7)]
    norm_num
    have h_sum_expanded : ∑ k ∈ Finset.range 6, z ^ (1 + k) = z ^ 1 + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 := by
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (1 + k)) 5]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 2)) 4]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 3)) 3]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 4)) 2]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 5)) 1]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 6)) 0]
      rw [Finset.sum_range_zero]
      abel
    rw [h_sum_expanded]
    simp only [pow_one]
    abel
  have subprob_S₁_complex_val_proof : S₁_complex_repr = (-1 : ℂ) / (2 : ℂ) := by
    mkOpaque
    rw [subprob_S₁_complex_calc_proof]
    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]
  have subprob_S₁_val_proof : S₁ = (-1 : ℝ) / (2 : ℝ) := by
    mkOpaque
    have h_S₁_complex_eq_ofReal_S₁ : S₁_complex_repr = (S₁ : ℂ) := by
      rw [S₁_complex_repr_def]
      rw [← subprob_ofReal_r₁_eq_R₁_proof, ← subprob_ofReal_r₂_eq_R₂_proof, ← subprob_ofReal_r₃_eq_R₃_proof]
      simp only [← map_add Complex.ofReal]
      rw [S₁_def]
      rfl
    have h_ofReal_S₁_val : (S₁ : ℂ) = -(1 : ℂ) / (2 : ℂ) := by
      rw [← h_S₁_complex_eq_ofReal_S₁]
      rw [subprob_S₁_complex_val_proof]
    have h_complex_val_is_ofReal : -(1 : ℂ) / (2 : ℂ) = (((-1 : ℝ) / (2 : ℝ)) : ℂ) := by simp [Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div]
    have h_ofReal_S₁_eq_ofReal_val : (S₁ : ℂ) = (((-1 : ℝ) / (2 : ℝ)) : ℂ) := by rw [h_ofReal_S₁_val, h_complex_val_is_ofReal]
    exact (Complex.ofReal_inj).mp (h_ofReal_S₁_eq_ofReal_val.trans (Complex.ofReal_div (-1 : ℝ) (2 : ℝ)).symm)
  letI S₂_complex_term1 := R₁_complex * R₂_complex
  retro' S₂_complex_term1_def : S₂_complex_term1 = R₁_complex * R₂_complex := by funext; rfl
  have subprob_S₂_complex_term1_calc_proof : S₂_complex_term1 = (z ^ (3 : ℕ) + z ^ (6 : ℕ) + z + z ^ (4 : ℕ)) / (4 : ℂ) := by
    mkOpaque
    rw [S₂_complex_term1_def, R₁_complex_def, R₂_complex_def]
    rw [_root_.div_mul_div_comm]
    have h_two_mul_two : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    rw [h_two_mul_two]
    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by norm_num
    rw [div_left_inj' h_four_ne_zero]
    have h_z8 : z ^ (8 : ℕ) = z := by
      rw [show (8 : ℕ) = (7 : ℕ) + (1 : ℕ) by norm_num]
      rw [pow_add, subprob_z_pow_7_eq_1_proof, one_mul, pow_one]
    have h_z11 : z ^ (11 : ℕ) = z ^ (4 : ℕ) := by
      rw [show (11 : ℕ) = (7 : ℕ) + (4 : ℕ) by norm_num]
      rw [pow_add, subprob_z_pow_7_eq_1_proof, one_mul]
    ring_nf
    rw [h_z8, h_z11]
    ring
  letI S₂_complex_term2 := R₁_complex * R₃_complex
  retro' S₂_complex_term2_def : S₂_complex_term2 = R₁_complex * R₃_complex := by funext; rfl
  have subprob_S₂_complex_term2_calc_proof : S₂_complex_term2 = (z ^ (4 : ℕ) + z ^ (5 : ℕ) + z ^ (2 : ℕ) + z ^ (3 : ℕ)) / (4 : ℂ) := by
    mkOpaque
    rw [S₂_complex_term2_def, R₁_complex_def, R₃_complex_def]
    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by norm_num
    field_simp [h_four_ne_zero]
    ring_nf
    have h_z9 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by
      have h9_eq_2_add_7 : (9 : ℕ) = 2 + 7 := by norm_num
      rw [h9_eq_2_add_7, pow_add, subprob_z_pow_7_eq_1_proof, mul_one]
    have h_z10 : z ^ (10 : ℕ) = z ^ (3 : ℕ) := by
      have h10_eq_3_add_7 : (10 : ℕ) = 3 + 7 := by norm_num
      rw [h10_eq_3_add_7, pow_add, subprob_z_pow_7_eq_1_proof, mul_one]
    rw [h_z9, h_z10]
    ring
  letI S₂_complex_term3 := R₂_complex * R₃_complex
  retro' S₂_complex_term3_def : S₂_complex_term3 = R₂_complex * R₃_complex := by funext; rfl
  have subprob_S₂_complex_term3_calc_proof : S₂_complex_term3 = (z ^ (5 : ℕ) + z ^ (6 : ℕ) + z + z ^ (2 : ℕ)) / (4 : ℂ) := by
    mkOpaque
    rw [S₂_complex_term3_def]
    rw [R₂_complex_def, R₃_complex_def]
    field_simp
    have h_lhs_expand : (z ^ 2 + z ^ 5) * (z ^ 3 + z ^ 4) = z ^ 5 + z ^ 6 + z ^ 8 + z ^ 9 := by ring
    rw [h_lhs_expand]
    have hz7_eq_1 : z ^ (7 : ℕ) = (1 : ℂ) := subprob_z_pow_7_eq_1_proof
    have hz8_eq_z : z ^ (8 : ℕ) = z := by
      have h_8_is_7_plus_1 : (8 : ℕ) = 7 + 1 := by norm_num
      rw [h_8_is_7_plus_1]
      rw [pow_add z 7 1]
      rw [hz7_eq_1]
      rw [one_mul]
      rw [pow_one]
    have hz9_eq_z2 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by
      have h_9_is_7_plus_2 : (9 : ℕ) = 7 + 2 := by norm_num
      rw [h_9_is_7_plus_2]
      rw [pow_add z 7 2]
      rw [hz7_eq_1]
      rw [one_mul]
    rw [hz8_eq_z, hz9_eq_z2]
    ring
  letI S₂_complex_repr := S₂_complex_term1 + S₂_complex_term2 + S₂_complex_term3
  retro' S₂_complex_repr_def : S₂_complex_repr = S₂_complex_term1 + S₂_complex_term2 + S₂_complex_term3 := by funext; rfl
  have subprob_S₂_complex_num_sum_proof : (z ^ (3 : ℕ) + z ^ (6 : ℕ) + z + z ^ (4 : ℕ)) + (z ^ (4 : ℕ) + z ^ (5 : ℕ) + z ^ (2 : ℕ) + z ^ (3 : ℕ)) + (z ^ (5 : ℕ) + z ^ (6 : ℕ) + z + z ^ (2 : ℕ)) = (2 : ℂ) * sum_zk_1_to_6 := by
    mkOpaque
    rw [sum_zk_1_to_6_def]
    have h_0_lt_7 : (0 : ℕ) < (7 : ℕ) := by norm_num
    have h_sum_rewrite : (∑ k ∈ Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k) = (∑ k ∈ Finset.Ico (0 + 1) 7, z ^ k) := by
      apply congr_arg (fun s : Finset ℕ => ∑ k ∈ s, z ^ k)
      apply Finset.ext
      intro x
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      rw [Nat.lt_iff_add_one_le]
    rw [h_sum_rewrite]
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num
    simp [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, pow_one]
    ring
  have subprob_S₂_complex_calc_proof : S₂_complex_repr = ((2 : ℂ) * sum_zk_1_to_6) / (4 : ℂ) := by
    mkOpaque
    rw [S₂_complex_repr_def]
    rw [subprob_S₂_complex_term1_calc_proof, subprob_S₂_complex_term2_calc_proof, subprob_S₂_complex_term3_calc_proof]
    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by norm_num
    field_simp [h_four_ne_zero]
    rw [subprob_S₂_complex_num_sum_proof]
  have subprob_S₂_complex_val_proof : S₂_complex_repr = (-1 : ℂ) / (2 : ℂ) := by
    mkOpaque
    rw [subprob_S₂_complex_calc_proof]
    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]
    field_simp
    norm_num
  have subprob_S₂_val_proof : S₂ = (-1 : ℝ) / (2 : ℝ) := by
    mkOpaque
    have h_ofReal_S₂_expanded : ofReal S₂ = (ofReal r₁) * (ofReal r₂) + (ofReal r₁) * (ofReal r₃) + (ofReal r₂) * (ofReal r₃) := by
      rw [S₂_def]
      simp
    have h_S₂_complex_repr_expanded : S₂_complex_repr = R₁_complex * R₂_complex + R₁_complex * R₃_complex + R₂_complex * R₃_complex := by rw [S₂_complex_repr_def, S₂_complex_term1_def, S₂_complex_term2_def, S₂_complex_term3_def]
    have h_ofReal_S₂_eq_S₂_complex_repr : ofReal S₂ = S₂_complex_repr := by
      rw [h_ofReal_S₂_expanded]
      rw [subprob_ofReal_r₁_eq_R₁_proof, subprob_ofReal_r₂_eq_R₂_proof, subprob_ofReal_r₃_eq_R₃_proof]
      rw [h_S₂_complex_repr_expanded]
    have h_ofReal_S₂_value : ofReal S₂ = -(1 : ℂ) / (2 : ℂ) := by
      rw [h_ofReal_S₂_eq_S₂_complex_repr]
      exact subprob_S₂_complex_val_proof
    have h_target_val_equiv : -(1 : ℂ) / (2 : ℂ) = ofReal (-(1 : ℝ) / (2 : ℝ)) := by simp
    rw [h_target_val_equiv] at h_ofReal_S₂_value
    exact Complex.ofReal_inj.mp h_ofReal_S₂_value
  letI S₃_complex_num_factor12 := (z + z ^ (6 : ℕ)) * (z ^ (2 : ℕ) + z ^ (5 : ℕ))
  retro' S₃_complex_num_factor12_def : S₃_complex_num_factor12 = (z + z ^ (6 : ℕ)) * (z ^ (2 : ℕ) + z ^ (5 : ℕ)) := by funext; rfl
  have subprob_S₃_complex_num_factor12_calc_proof : S₃_complex_num_factor12 = z ^ (3 : ℕ) + z ^ (6 : ℕ) + z + z ^ (4 : ℕ) := by
    mkOpaque
    rw [S₃_complex_num_factor12_def]
    have h_expanded_product : (z + z ^ (6 : ℕ)) * (z ^ (2 : ℕ) + z ^ (5 : ℕ)) = z ^ (3 : ℕ) + z ^ (6 : ℕ) + z ^ (8 : ℕ) + z ^ (11 : ℕ) := by ring
    rw [h_expanded_product]
    have h_z_pow_8_simplified : z ^ (8 : ℕ) = z := by
      have eight_is_seven_plus_one : (8 : ℕ) = 7 + 1 := by norm_num
      rw [eight_is_seven_plus_one]
      rw [pow_add]
      rw [subprob_z_pow_7_eq_1_proof]
      rw [one_mul]
      rw [pow_one]
    rw [h_z_pow_8_simplified]
    have h_z_pow_11_simplified : z ^ (11 : ℕ) = z ^ (4 : ℕ) := by
      have eleven_is_seven_plus_four : (11 : ℕ) = 7 + 4 := by norm_num
      rw [eleven_is_seven_plus_four]
      rw [pow_add]
      rw [subprob_z_pow_7_eq_1_proof]
      rw [one_mul]
    rw [h_z_pow_11_simplified]
  letI S₃_complex_num := S₃_complex_num_factor12 * (z ^ (3 : ℕ) + z ^ (4 : ℕ))
  retro' S₃_complex_num_def : S₃_complex_num = S₃_complex_num_factor12 * (z ^ (3 : ℕ) + z ^ (4 : ℕ)) := by funext; rfl
  have subprob_S₃_complex_num_expanded_proof : (z ^ (3 : ℕ) + z ^ (6 : ℕ) + z + z ^ (4 : ℕ)) * (z ^ (3 : ℕ) + z ^ (4 : ℕ)) = (z ^ (6 : ℕ) + z ^ (7 : ℕ)) + (z ^ (9 : ℕ) + z ^ (10 : ℕ)) + (z ^ (4 : ℕ) + z ^ (5 : ℕ)) + (z ^ (7 : ℕ) + z ^ (8 : ℕ)) := by
    mkOpaque
    ring
  have subprob_S₃_complex_num_simplified_proof : (z ^ (6 : ℕ) + z ^ (7 : ℕ)) + (z ^ (9 : ℕ) + z ^ (10 : ℕ)) + (z ^ (4 : ℕ) + z ^ (5 : ℕ)) + (z ^ (7 : ℕ) + z ^ (8 : ℕ)) = (2 : ℂ) + sum_zk_1_to_6 := by
    mkOpaque
    have h_z7 : z ^ (7 : ℕ) = (1 : ℂ) := subprob_z_pow_7_eq_1_proof
    have h_z8 : z ^ (8 : ℕ) = z := by rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, h_z7, one_mul, pow_one]
    have h_z9 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by rw [show (9 : ℕ) = 7 + 2 by norm_num, pow_add, h_z7, one_mul]
    have h_z10 : z ^ (10 : ℕ) = z ^ (3 : ℕ) := by rw [show (10 : ℕ) = 7 + 3 by norm_num, pow_add, h_z7, one_mul]
    rw [h_z7, h_z8, h_z9, h_z10]
    have h_lhs_rearranged : (z ^ (6 : ℕ) + 1) + (z ^ (2 : ℕ) + z ^ (3 : ℕ)) + (z ^ (4 : ℕ) + z ^ (5 : ℕ)) + (1 + z) = (2 : ℂ) + (z + z ^ (2 : ℕ) + z ^ (3 : ℕ) + z ^ (4 : ℕ) + z ^ (5 : ℕ) + z ^ (6 : ℕ)) := by ring
    rw [h_lhs_rearranged]
    congr 1
    rw [← pow_one z]
    rw [sum_zk_1_to_6_def]
    have h_Ioo_0_7_eq_Ico_1_7 : Finset.Ioo (0 : ℕ) (7 : ℕ) = Finset.Ico (1 : ℕ) (7 : ℕ) := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      have h_em := Classical.em (k < 7)
      rcases h_em with h_k_lt_7 | h_k_not_lt_7
      . apply and_congr
        . rw [Nat.lt_iff_add_one_le, Nat.zero_add]
        . rfl
      . simp [propext (iff_false_intro h_k_not_lt_7)]
    rw [h_Ioo_0_7_eq_Ico_1_7]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Nat.Ico_succ_singleton 1]
    rw [Finset.sum_singleton]
    ring
  have subprob_S₃_complex_num_val_proof : S₃_complex_num = (1 : ℂ) := by
    mkOpaque
    rw [S₃_complex_num_def]
    rw [subprob_S₃_complex_num_factor12_calc_proof]
    rw [subprob_S₃_complex_num_expanded_proof]
    rw [subprob_S₃_complex_num_simplified_proof]
    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]
    ring
  letI S₃_complex_repr := S₃_complex_num / (8 : ℂ)
  retro' S₃_complex_repr_def : S₃_complex_repr = S₃_complex_num / (8 : ℂ) := by funext; rfl
  have subprob_S₃_complex_val_proof : S₃_complex_repr = (1 : ℂ) / (8 : ℂ) := by
    mkOpaque
    rw [S₃_complex_repr_def]
    rw [subprob_S₃_complex_num_val_proof]
  have subprob_S₃_val_proof : S₃ = (1 : ℝ) / (8 : ℝ) := by
    mkOpaque
    have h_S3_ofReal_eq_prod_R_complex : ofReal S₃ = R₁_complex * R₂_complex * R₃_complex := by
      rw [S₃_def]
      rw [RingHom.map_mul Complex.ofReal]
      rw [RingHom.map_mul Complex.ofReal]
      rw [subprob_ofReal_r₁_eq_R₁_proof]
      rw [subprob_ofReal_r₂_eq_R₂_proof]
      rw [subprob_ofReal_r₃_eq_R₃_proof]
    have h_prod_R_complex_eq_S3_repr : R₁_complex * R₂_complex * R₃_complex = S₃_complex_repr := by
      rw [R₁_complex_def, R₂_complex_def, R₃_complex_def, S₃_complex_repr_def]
      rw [S₃_complex_num_def, S₃_complex_num_factor12_def]
      field_simp [show (2 : ℂ) ≠ 0 by norm_num]
      rw [show (2 : ℂ) * (2 : ℂ) * (2 : ℂ) = (8 : ℂ) by norm_num]
      simp
    have h_S3_ofReal_eq_1_div_8_complex : ofReal S₃ = (1 : ℂ) / (8 : ℂ) := by rw [h_S3_ofReal_eq_prod_R_complex, h_prod_R_complex_eq_S3_repr, subprob_S₃_complex_val_proof]
    have h_target_complex_form : ofReal ((1 : ℝ) / (8 : ℝ)) = (1 : ℂ) / (8 : ℂ) := by
      rw [Complex.ofReal_eq_coe]
      rw [Complex.ofReal_div]
      simp
    rw [← Complex.ofReal_inj]
    rw [Complex.ofReal_eq_coe] at h_S3_ofReal_eq_1_div_8_complex
    rw [Complex.ofReal_eq_coe] at h_target_complex_form
    rw [h_S3_ofReal_eq_1_div_8_complex, ← h_target_complex_form]
  have subprob_abc_val_S1_S2_proof : S₁ * S₂ = ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ)) := by
    mkOpaque
    rw [subprob_S₁_val_proof]
    rw [subprob_S₂_val_proof]
  have subprob_S1_S2_is_one_fourth_proof : ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (4 : ℝ) := by
    mkOpaque
    norm_num
  have subprob_abc_val_S1S2_S3_proof : (S₁ * S₂) * S₃ = ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ)) := by
    mkOpaque
    have h_S1_mul_S2_eq_one_fourth : S₁ * S₂ = (1 : ℝ) / (4 : ℝ) := by
      rw [subprob_abc_val_S1_S2_proof]
      exact subprob_S1_S2_is_one_fourth_proof
    rw [h_S1_mul_S2_eq_one_fourth]
    rw [subprob_S₃_val_proof]
  have subprob_product_is_one_thirtysecond_proof : ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ)) = (1 : ℝ) / (32 : ℝ) := by
    mkOpaque
    norm_num
  exact
    show a * b * c = (1 : ℝ) / (32 : ℝ) by
      mkOpaque
      rw [subprob_abc_eq_S1S2S3_proof]
      rw [subprob_abc_val_S1S2_S3_proof]
      exact subprob_product_is_one_thirtysecond_proof

#print axioms amc12a_2021_p22

/-Sketch
variable (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x^3 + a * x^2 + b * x + c) (h₁ : f⁻¹' {0} = {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)})

play
  -- Define the roots
  r₁ := Real.cos (2 * Real.pi / 7)
  r₂ := Real.cos (4 * Real.pi / 7)
  r₃ := Real.cos (6 * Real.pi / 7)

  -- Show roots are distinct
  subprob_roots_distinct_aux1 :≡ 2 * Real.pi / 7 < 4 * Real.pi / 7
  subprob_roots_distinct_aux1_proof ⇐ show subprob_roots_distinct_aux1 by sorry
  subprob_roots_distinct_aux2 :≡ 4 * Real.pi / 7 < 6 * Real.pi / 7
  subprob_roots_distinct_aux2_proof ⇐ show subprob_roots_distinct_aux2 by sorry
  subprob_roots_distinct_aux3 :≡ (0 : ℝ) < 2 * Real.pi / 7
  subprob_roots_distinct_aux3_proof ⇐ show subprob_roots_distinct_aux3 by sorry
  subprob_roots_distinct_aux4 :≡ 6 * Real.pi / 7 < Real.pi
  subprob_roots_distinct_aux4_proof ⇐ show subprob_roots_distinct_aux4 by sorry

  subprob_r₁_gt_r₂ :≡ r₁ > r₂
  subprob_r₁_gt_r₂_proof ⇐ show subprob_r₁_gt_r₂ by sorry
  subprob_r₂_gt_r₃ :≡ r₂ > r₃
  subprob_r₂_gt_r₃_proof ⇐ show subprob_r₂_gt_r₃ by sorry

  subprob_r₁_ne_r₂ :≡ r₁ ≠ r₂
  subprob_r₁_ne_r₂_proof ⇐ show subprob_r₁_ne_r₂ by sorry
  subprob_r₁_ne_r₃ :≡ r₁ ≠ r₃
  subprob_r₁_ne_r₃_proof ⇐ show subprob_r₁_ne_r₃ by sorry
  subprob_r₂_ne_r₃ :≡ r₂ ≠ r₃
  subprob_r₂_ne_r₃_proof ⇐ show subprob_r₂_ne_r₃ by sorry

  -- Define the polynomial P corresponding to f x
  P := Polynomial.X^(3:ℕ) + (Polynomial.C a) * Polynomial.X^(2:ℕ) + (Polynomial.C b) * Polynomial.X + (Polynomial.C c)

  -- Show that Polynomial.eval x P = x^3 + a*x^2 + b*x + c
  subprob_P_eval_expr :≡ ∀ x : ℝ, Polynomial.eval x P = x^3 + a * x^2 + b * x + c
  subprob_P_eval_expr_proof ⇐ show subprob_P_eval_expr by sorry

  -- Using h₀, P_eval is f
  subprob_P_eval_eq_f :≡ ∀ x : ℝ, Polynomial.eval x P = f x
  subprob_P_eval_eq_f_proof ⇐ show subprob_P_eval_eq_f by sorry

  -- Properties of P based on its definition
  subprob_P_natDegree :≡ Polynomial.natDegree P = 3
  subprob_P_natDegree_proof ⇐ show subprob_P_natDegree by sorry
  subprob_P_coeff3 :≡ Polynomial.coeff P 3 = (1:ℝ)
  subprob_P_coeff3_proof ⇐ show subprob_P_coeff3 by sorry
  subprob_P_coeff2 :≡ Polynomial.coeff P 2 = a
  subprob_P_coeff2_proof ⇐ show subprob_P_coeff2 by sorry
  subprob_P_coeff1 :≡ Polynomial.coeff P 1 = b
  subprob_P_coeff1_proof ⇐ show subprob_P_coeff1 by sorry
  subprob_P_coeff0 :≡ Polynomial.coeff P 0 = c
  subprob_P_coeff0_proof ⇐ show subprob_P_coeff0 by sorry

  subprob_P_monic :≡ Polynomial.Monic P
  subprob_P_monic_proof ⇐ show subprob_P_monic by sorry

  -- Establish P has roots r₁, r₂, r₃
  subprob_P_is_root_r₁ :≡ Polynomial.IsRoot P r₁
  subprob_P_is_root_r₁_proof ⇐ show subprob_P_is_root_r₁ by sorry
  subprob_P_is_root_r₂ :≡ Polynomial.IsRoot P r₂
  subprob_P_is_root_r₂_proof ⇐ show subprob_P_is_root_r₂ by sorry
  subprob_P_is_root_r₃ :≡ Polynomial.IsRoot P r₃
  subprob_P_is_root_r₃_proof ⇐ show subprob_P_is_root_r₃ by sorry

  Rts_ms := Polynomial.roots P
  subprob_roots_multiset_eq_r1r2r3 :≡ Rts_ms = ({r₁, r₂, r₃} : Multiset ℝ)
  subprob_roots_multiset_eq_r1r2r3_proof ⇐ show subprob_roots_multiset_eq_r1r2r3 by sorry

  -- Establish conditions for Vieta's formulas theorem (Polynomial.coeff_eq_esymm_roots_of_card)
  subprob_card_Rts_ms_eq_3 :≡ Multiset.card Rts_ms = 3
  subprob_card_Rts_ms_eq_3_proof ⇐ show subprob_card_Rts_ms_eq_3 by sorry

  subprob_card_roots_eq_natDegree :≡ Multiset.card Rts_ms = Polynomial.natDegree P
  subprob_card_roots_eq_natDegree_proof ⇐ show subprob_card_roots_eq_natDegree by sorry

  subprob_P_splits :≡ Polynomial.Splits (RingHom.id ℝ) P
  subprob_P_splits_proof ⇐ show subprob_P_splits by sorry

  -- Define S₁, S₂, S₃ (elementary symmetric polynomials of the roots)
  S₁ := r₁ + r₂ + r₃
  S₂ := r₁*r₂ + r₁*r₃ + r₂*r₃
  S₃ := r₁*r₂*r₃

  -- Relate Sᵢ to esymm (Polynomial.roots P)
  subprob_S₁_eq_esymm_roots_1 :≡ S₁ = Multiset.esymm Rts_ms 1
  subprob_S₁_eq_esymm_roots_1_proof ⇐ show subprob_S₁_eq_esymm_roots_1 by sorry
  subprob_S₂_eq_esymm_roots_2 :≡ S₂ = Multiset.esymm Rts_ms 2
  subprob_S₂_eq_esymm_roots_2_proof ⇐ show subprob_S₂_eq_esymm_roots_2 by sorry
  subprob_S₃_eq_esymm_roots_3 :≡ S₃ = Multiset.esymm Rts_ms 3
  subprob_S₃_eq_esymm_roots_3_proof ⇐ show subprob_S₃_eq_esymm_roots_3 by sorry

  -- Vieta's formulas for a (coeff P 2)
  -- Polynomial.coeff P 2 = (-1)^(Polynomial.natDegree P - 2) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 2)
  subprob_natDeg_P_minus_2_is_1 :≡ Polynomial.natDegree P - 2 = 1
  subprob_natDeg_P_minus_2_is_1_proof ⇐ show subprob_natDeg_P_minus_2_is_1 by sorry
  subprob_vieta_coeff2_form :≡ Polynomial.coeff P 2 = (-1 : ℝ) ^ (Polynomial.natDegree P - 2) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 2)
  subprob_vieta_coeff2_form_proof ⇐ show subprob_vieta_coeff2_form by sorry
  subprob_coeff_P_2_eq_neg_S₁ :≡ Polynomial.coeff P 2 = -S₁
  subprob_coeff_P_2_eq_neg_S₁_proof ⇐ show subprob_coeff_P_2_eq_neg_S₁ by sorry
  subprob_vieta_a :≡ a = -S₁
  subprob_vieta_a_proof ⇐ show subprob_vieta_a by sorry

  -- Vieta's formulas for b (coeff P 1)
  -- Polynomial.coeff P 1 = (-1)^(Polynomial.natDegree P - 1) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 1)
  subprob_natDeg_P_minus_1_is_2 :≡ Polynomial.natDegree P - 1 = 2
  subprob_natDeg_P_minus_1_is_2_proof ⇐ show subprob_natDeg_P_minus_1_is_2 by sorry
  subprob_vieta_coeff1_form :≡ Polynomial.coeff P 1 = (-1 : ℝ) ^ (Polynomial.natDegree P - 1) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 1)
  subprob_vieta_coeff1_form_proof ⇐ show subprob_vieta_coeff1_form by sorry
  subprob_coeff_P_1_eq_S₂ :≡ Polynomial.coeff P 1 = S₂
  subprob_coeff_P_1_eq_S₂_proof ⇐ show subprob_coeff_P_1_eq_S₂ by sorry
  subprob_vieta_b :≡ b = S₂
  subprob_vieta_b_proof ⇐ show subprob_vieta_b by sorry

  -- Vieta's formulas for c (coeff P 0)
  -- Polynomial.coeff P 0 = (-1)^(Polynomial.natDegree P - 0) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 0)
  subprob_natDeg_P_minus_0_is_3 :≡ Polynomial.natDegree P - 0 = 3
  subprob_natDeg_P_minus_0_is_3_proof ⇐ show subprob_natDeg_P_minus_0_is_3 by sorry
  subprob_vieta_coeff0_form :≡ Polynomial.coeff P 0 = (-1 : ℝ) ^ (Polynomial.natDegree P - 0) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 0)
  subprob_vieta_coeff0_form_proof ⇐ show subprob_vieta_coeff0_form by sorry
  subprob_coeff_P_0_eq_neg_S₃ :≡ Polynomial.coeff P 0 = -S₃
  subprob_coeff_P_0_eq_neg_S₃_proof ⇐ show subprob_coeff_P_0_eq_neg_S₃ by sorry
  subprob_vieta_c :≡ c = -S₃
  subprob_vieta_c_proof ⇐ show subprob_vieta_c by sorry

  -- Express abc in terms of S₁, S₂, S₃
  subprob_abc_eq_S1S2S3 :≡ a * b * c = S₁ * S₂ * S₃
  subprob_abc_eq_S1S2S3_proof ⇐ show subprob_abc_eq_S1S2S3 by sorry

  -- Calculations using complex numbers
  z := Complex.exp ( (2 * Real.pi / 7) * Complex.I )

  -- Properties of z
  subprob_z_pow_7_eq_1 :≡ z^(7:ℕ) = (1 : ℂ)
  subprob_z_pow_7_eq_1_proof ⇐ show subprob_z_pow_7_eq_1 by sorry
  subprob_z_ne_1 :≡ z ≠ (1 : ℂ)
  subprob_z_ne_1_proof ⇐ show subprob_z_ne_1 by sorry
  subprob_sum_z_k_0_6_eq_0 :≡ ∑ k in Finset.range (7:ℕ), z^k = (0 : ℂ)
  subprob_sum_z_k_0_6_eq_0_proof ⇐ show subprob_sum_z_k_0_6_eq_0 by sorry
  sum_zk_1_to_6 := ∑ k in Finset.Ioo (0:ℕ) (7:ℕ), z^k
  subprob_sum_z_k_1_6_eq_neg_1 :≡ sum_zk_1_to_6 = (-1 : ℂ)
  subprob_sum_z_k_1_6_eq_neg_1_proof ⇐ show subprob_sum_z_k_1_6_eq_neg_1 by sorry

  -- Express roots r₁, r₂, r₃ as complex numbers (which are actually real)
  R₁_complex := (z + z^(6:ℕ)) / (2 : ℂ)
  R₂_complex := (z^(2:ℕ) + z^(5:ℕ)) / (2 : ℂ)
  R₃_complex := (z^(3:ℕ) + z^(4:ℕ)) / (2 : ℂ)

  -- Show these complex numbers are real and equal to r₁, r₂, r₃
  subprob_ofReal_r₁_eq_R₁ :≡ Complex.ofReal r₁ = R₁_complex
  subprob_ofReal_r₁_eq_R₁_proof ⇐ show subprob_ofReal_r₁_eq_R₁ by sorry
  subprob_ofReal_r₂_eq_R₂ :≡ Complex.ofReal r₂ = R₂_complex
  subprob_ofReal_r₂_eq_R₂_proof ⇐ show subprob_ofReal_r₂_eq_R₂ by sorry
  subprob_ofReal_r₃_eq_R₃ :≡ Complex.ofReal r₃ = R₃_complex
  subprob_ofReal_r₃_eq_R₃_proof ⇐ show subprob_ofReal_r₃_eq_R₃ by sorry

  -- Calculate S₁ (as a real number)
  S₁_complex_repr := R₁_complex + R₂_complex + R₃_complex
  subprob_S₁_complex_calc :≡ S₁_complex_repr = sum_zk_1_to_6 / (2 : ℂ)
  subprob_S₁_complex_calc_proof ⇐ show subprob_S₁_complex_calc by sorry
  subprob_S₁_complex_val :≡ S₁_complex_repr = (-1 : ℂ) / (2 : ℂ)
  subprob_S₁_complex_val_proof ⇐ show subprob_S₁_complex_val by sorry
  subprob_S₁_val :≡ S₁ = (-1 : ℝ) / (2 : ℝ)
  subprob_S₁_val_proof ⇐ show subprob_S₁_val by sorry

  -- Calculate S₂ (as a real number)
  S₂_complex_term1 := R₁_complex * R₂_complex
  subprob_S₂_complex_term1_calc :≡ S₂_complex_term1 = (z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term1_calc_proof ⇐ show subprob_S₂_complex_term1_calc by sorry
  S₂_complex_term2 := R₁_complex * R₃_complex
  subprob_S₂_complex_term2_calc :≡ S₂_complex_term2 = (z^(4:ℕ) + z^(5:ℕ) + z^(2:ℕ) + z^(3:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term2_calc_proof ⇐ show subprob_S₂_complex_term2_calc by sorry
  S₂_complex_term3 := R₂_complex * R₃_complex
  subprob_S₂_complex_term3_calc :≡ S₂_complex_term3 = (z^(5:ℕ) + z^(6:ℕ) + z + z^(2:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term3_calc_proof ⇐ show subprob_S₂_complex_term3_calc by sorry

  S₂_complex_repr := S₂_complex_term1 + S₂_complex_term2 + S₂_complex_term3
  subprob_S₂_complex_num_sum :≡ (z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)) + (z^(4:ℕ) + z^(5:ℕ) + z^(2:ℕ) + z^(3:ℕ)) + (z^(5:ℕ) + z^(6:ℕ) + z + z^(2:ℕ)) = (2 : ℂ) * sum_zk_1_to_6
  subprob_S₂_complex_num_sum_proof ⇐ show subprob_S₂_complex_num_sum by sorry
  subprob_S₂_complex_calc :≡ S₂_complex_repr = ((2 : ℂ) * sum_zk_1_to_6) / (4 : ℂ)
  subprob_S₂_complex_calc_proof ⇐ show subprob_S₂_complex_calc by sorry
  subprob_S₂_complex_val :≡ S₂_complex_repr = (-1 : ℂ) / (2 : ℂ)
  subprob_S₂_complex_val_proof ⇐ show subprob_S₂_complex_val by sorry
  subprob_S₂_val :≡ S₂ = (-1 : ℝ) / (2 : ℝ)
  subprob_S₂_val_proof ⇐ show subprob_S₂_val by sorry

  -- Calculate S₃ (as a real number)
  S₃_complex_num_factor12 := (z + z^(6:ℕ)) * (z^(2:ℕ) + z^(5:ℕ))
  subprob_S₃_complex_num_factor12_calc :≡ S₃_complex_num_factor12 = z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)
  subprob_S₃_complex_num_factor12_calc_proof ⇐ show subprob_S₃_complex_num_factor12_calc by sorry
  S₃_complex_num := S₃_complex_num_factor12 * (z^(3:ℕ) + z^(4:ℕ))

  subprob_S₃_complex_num_expanded :≡ (z^(3:ℕ)+z^(6:ℕ)+z+z^(4:ℕ)) * (z^(3:ℕ)+z^(4:ℕ)) = (z^(6:ℕ)+z^(7:ℕ)) + (z^(9:ℕ)+z^(10:ℕ)) + (z^(4:ℕ)+z^(5:ℕ)) + (z^(7:ℕ)+z^(8:ℕ))
  subprob_S₃_complex_num_expanded_proof ⇐ show subprob_S₃_complex_num_expanded by sorry
  subprob_S₃_complex_num_simplified :≡ (z^(6:ℕ)+z^(7:ℕ)) + (z^(9:ℕ)+z^(10:ℕ)) + (z^(4:ℕ)+z^(5:ℕ)) + (z^(7:ℕ)+z^(8:ℕ)) = (2 : ℂ) + sum_zk_1_to_6
  subprob_S₃_complex_num_simplified_proof ⇐ show subprob_S₃_complex_num_simplified by sorry
  subprob_S₃_complex_num_val :≡ S₃_complex_num = (1 : ℂ)
  subprob_S₃_complex_num_val_proof ⇐ show subprob_S₃_complex_num_val by sorry

  S₃_complex_repr := S₃_complex_num / (8 : ℂ)
  subprob_S₃_complex_val :≡ S₃_complex_repr = (1 : ℂ) / (8 : ℂ)
  subprob_S₃_complex_val_proof ⇐ show subprob_S₃_complex_val by sorry
  subprob_S₃_val :≡ S₃ = (1 : ℝ) / (8 : ℝ)
  subprob_S₃_val_proof ⇐ show subprob_S₃_val by sorry

  -- Final calculation
  subprob_abc_val_S1_S2 :≡ S₁ * S₂ = ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ))
  subprob_abc_val_S1_S2_proof ⇐ show subprob_abc_val_S1_S2 by sorry
  subprob_S1_S2_is_one_fourth :≡ ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (4 : ℝ)
  subprob_S1_S2_is_one_fourth_proof ⇐ show subprob_S1_S2_is_one_fourth by sorry
  subprob_abc_val_S1S2_S3 :≡ (S₁ * S₂) * S₃ = ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ))
  subprob_abc_val_S1S2_S3_proof ⇐ show subprob_abc_val_S1S2_S3 by sorry
  subprob_product_is_one_thirtysecond :≡ ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ)) = (1 : ℝ) / (32 : ℝ)
  subprob_product_is_one_thirtysecond_proof ⇐ show subprob_product_is_one_thirtysecond by sorry

  subprob_final_goal :≡ a * b * c = (1 : ℝ) / (32 : ℝ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/-Sketch with proof
variable (a b c : ℝ) (f : ℝ → ℝ) (h₀ : ∀ x, f x = x^3 + a * x^2 + b * x + c) (h₁ : f⁻¹' {0} = {Real.cos (2 * Real.pi / 7), Real.cos (4 * Real.pi / 7), Real.cos (6 * Real.pi / 7)})

play
  r₁ := Real.cos (2 * Real.pi / 7)
  r₂ := Real.cos (4 * Real.pi / 7)
  r₃ := Real.cos (6 * Real.pi / 7)

  subprob_roots_distinct_aux1 :≡ 2 * Real.pi / 7 < 4 * Real.pi / 7
  subprob_roots_distinct_aux1_proof ⇐ show subprob_roots_distinct_aux1 by




    have seven_pos : (7 : ℝ) > 0 := by
      norm_num

    apply ((div_lt_div_iff seven_pos seven_pos).trans (mul_lt_mul_iff_of_pos_right seven_pos)).mpr


    have pi_pos : Real.pi > 0 := by
      exact Real.pi_pos

    apply (mul_lt_mul_right pi_pos).mpr

    norm_num


  subprob_roots_distinct_aux2 :≡ 4 * Real.pi / 7 < 6 * Real.pi / 7
  subprob_roots_distinct_aux2_proof ⇐ show subprob_roots_distinct_aux2 by


    apply (div_lt_div_right (by norm_num : (0 : ℝ) < (7 : ℝ))).mpr
    apply (mul_lt_mul_right Real.pi_pos).mpr
    norm_num

  subprob_roots_distinct_aux3 :≡ (0 : ℝ) < 2 * Real.pi / 7
  subprob_roots_distinct_aux3_proof ⇐ show subprob_roots_distinct_aux3 by


    have h_two_pos : (0 : ℝ) < 2 := by
      norm_num

    have h_pi_pos : 0 < Real.pi := by
      exact Real.pi_pos

    have h_numerator_pos : 0 < 2 * Real.pi := by
      apply mul_pos
      exact h_two_pos
      exact h_pi_pos

    have h_denominator_pos : (0 : ℝ) < 7 := by
      norm_num

    apply div_pos
    exact h_numerator_pos
    exact h_denominator_pos
  subprob_roots_distinct_aux4 :≡ 6 * Real.pi / 7 < Real.pi
  subprob_roots_distinct_aux4_proof ⇐ show subprob_roots_distinct_aux4 by

    have h_seven_pos : (7 : ℝ) > 0 := by
      norm_num

    rw [div_lt_iff h_seven_pos]

    rw [mul_comm Real.pi (7 : ℝ)]

    have h_pi_pos : Real.pi > 0 := by
      exact Real.pi_pos

    rw [mul_lt_mul_iff_of_pos_right h_pi_pos]

    norm_num

  subprob_r₁_gt_r₂ :≡ r₁ > r₂
  subprob_r₁_gt_r₂_proof ⇐ show subprob_r₁_gt_r₂ by

    rw [r₁_def, r₂_def]

    let x₁ := (2 : ℝ) * Real.pi / (7 : ℝ)
    let x₂ := (4 : ℝ) * Real.pi / (7 : ℝ)
    let x₃_arg := (6 : ℝ) * Real.pi / (7 : ℝ)


    have h_0_lt_x₁ : 0 < x₁ := by
      exact subprob_roots_distinct_aux3_proof
    have h_x₁_lt_x₂ : x₁ < x₂ := by
      exact subprob_roots_distinct_aux1_proof
    have h_x₂_lt_x₃_arg : x₂ < x₃_arg := by
      exact subprob_roots_distinct_aux2_proof
    have h_x₃_arg_lt_pi : x₃_arg < Real.pi := by
      exact subprob_roots_distinct_aux4_proof

    have h_x₁_lt_pi : x₁ < Real.pi := by
      apply lt_trans h_x₁_lt_x₂
      apply lt_trans h_x₂_lt_x₃_arg
      exact h_x₃_arg_lt_pi
    have h_x₁_in_Ioo : x₁ ∈ Set.Ioo 0 Real.pi := by
      exact Set.mem_Ioo.mpr ⟨h_0_lt_x₁, h_x₁_lt_pi⟩

    have h_0_lt_x₂ : 0 < x₂ := by
      apply lt_trans h_0_lt_x₁
      exact h_x₁_lt_x₂
    have h_x₂_lt_pi : x₂ < Real.pi := by
      apply lt_trans h_x₂_lt_x₃_arg
      exact h_x₃_arg_lt_pi
    have h_x₂_in_Ioo : x₂ ∈ Set.Ioo 0 Real.pi := by
      exact Set.mem_Ioo.mpr ⟨h_0_lt_x₂, h_x₂_lt_pi⟩


    have cos_strict_anti_on_Icc : StrictAntiOn Real.cos (Set.Icc 0 Real.pi) :=
      Real.strictAntiOn_cos
    have Ioo_subset_Icc_zero_pi : Set.Ioo 0 Real.pi ⊆ Set.Icc 0 Real.pi :=
      Set.Ioo_subset_Icc_self
    have cos_strict_anti_on_Ioo_zero_pi : StrictAntiOn Real.cos (Set.Ioo 0 Real.pi) :=
      StrictAntiOn.mono cos_strict_anti_on_Icc Ioo_subset_Icc_zero_pi
    exact cos_strict_anti_on_Ioo_zero_pi h_x₁_in_Ioo h_x₂_in_Ioo h_x₁_lt_x₂

  subprob_r₂_gt_r₃ :≡ r₂ > r₃
  subprob_r₂_gt_r₃_proof ⇐ show subprob_r₂_gt_r₃ by

    rw [r₂_def, r₃_def]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    . show (0 : ℝ) ≤ (4 : ℝ) * Real.pi / (7 : ℝ)
      exact le_of_lt (lt_trans subprob_roots_distinct_aux3_proof subprob_roots_distinct_aux1_proof)
    . show (6 : ℝ) * Real.pi / (7 : ℝ) ≤ Real.pi
      exact le_of_lt subprob_roots_distinct_aux4_proof
    . show (4 : ℝ) * Real.pi / (7 : ℝ) < (6 : ℝ) * Real.pi / (7 : ℝ)
      exact subprob_roots_distinct_aux2_proof


  subprob_r₁_ne_r₂ :≡ r₁ ≠ r₂
  subprob_r₁_ne_r₂_proof ⇐ show subprob_r₁_ne_r₂ by

    apply @_root_.ne_of_gt
    exact subprob_r₁_gt_r₂_proof

  subprob_r₁_ne_r₃ :≡ r₁ ≠ r₃
  subprob_r₁_ne_r₃_proof ⇐ show subprob_r₁_ne_r₃ by


    have h_r1_gt_r3 : r₁ > r₃ := by
      exact gt_trans subprob_r₁_gt_r₂_proof subprob_r₂_gt_r₃_proof

    apply @_root_.ne_of_gt
    exact h_r1_gt_r3

  subprob_r₂_ne_r₃ :≡ r₂ ≠ r₃
  subprob_r₂_ne_r₃_proof ⇐ show subprob_r₂_ne_r₃ by

    apply @_root_.ne_of_gt
    exact subprob_r₂_gt_r₃_proof


  P := Polynomial.X^(3:ℕ) + (Polynomial.C a) * Polynomial.X^(2:ℕ) + (Polynomial.C b) * Polynomial.X + (Polynomial.C c)

  subprob_P_eval_expr :≡ ∀ x : ℝ, Polynomial.eval x P = x^3 + a * x^2 + b * x + c
  subprob_P_eval_expr_proof ⇐ show subprob_P_eval_expr by

    intro x

    rw [P_def]




    simp

  subprob_P_eval_eq_f :≡ ∀ x : ℝ, Polynomial.eval x P = f x
  subprob_P_eval_eq_f_proof ⇐ show subprob_P_eval_eq_f by

    intro x

    rw [subprob_P_eval_expr_proof x]

    rw [h₀ x]


  subprob_P_natDegree :≡ Polynomial.natDegree P = 3
  subprob_P_natDegree_proof ⇐ show subprob_P_natDegree by


    rw [P_def]

    have h_deg_P₁ : Polynomial.natDegree (X ^ 3 : ℝ[X]) = 3 := by
      exact Polynomial.natDegree_X_pow 3

    have h_deg_P₂_le : Polynomial.natDegree (C a * X ^ 2 + (C b * X + C c) : ℝ[X]) ≤ 2 := by
      apply Nat.le_trans (Polynomial.natDegree_add_le (C a * X ^ 2) (C b * X + C c))
      have h_deg_CaX2 : Polynomial.natDegree (C a * X ^ 2) ≤ 2 := by
        exact Polynomial.natDegree_C_mul_X_pow_le a 2
      have h_deg_CbX_Cc : Polynomial.natDegree (C b * X + C c) ≤ 1 := by
        apply Nat.le_trans (Polynomial.natDegree_add_le (C b * X) (C c))
        apply max_le_iff.mpr
        constructor
        ·
          by_cases h_b_eq_0 : b = 0
          ·
            simp_rw [h_b_eq_0, Polynomial.C_0, zero_mul, Polynomial.natDegree_zero]
            decide
          ·
            rw [Polynomial.natDegree_C_mul_X b h_b_eq_0]
        ·
          apply Nat.le_trans (Polynomial.natDegree_C c).le
          apply Nat.zero_le
      apply max_le h_deg_CaX2
      apply Nat.le_trans h_deg_CbX_Cc
      decide

    have h_deg_P₂_lt_P₁ : Polynomial.natDegree (C a * X ^ 2 + (C b * X + C c) : ℝ[X]) < Polynomial.natDegree (X ^ 3 : ℝ[X]) := by
      rw [h_deg_P₁]
      linarith [h_deg_P₂_le]

    rw [add_assoc ((X ^ 3 : ℝ[X]) + C a * X ^ 2) (C b * X) (C c)]
    rw [add_assoc (X ^ 3 : ℝ[X]) (C a * X ^ 2) (C b * X + C c)]

    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h_deg_P₂_lt_P₁]

    exact h_deg_P₁




















  subprob_P_coeff3 :≡ Polynomial.coeff P 3 = (1:ℝ)
  subprob_P_coeff3_proof ⇐ show subprob_P_coeff3 by







    rw [P_def]
    simp only [Polynomial.coeff_add]

    have h_coeff_X_pow_3 : Polynomial.coeff (X ^ 3) 3 = (1 : ℝ) := by
      rw [Polynomial.coeff_X_pow 3 3]
      rw [if_pos (rfl : 3 = 3)]
    rw [h_coeff_X_pow_3]

    have h_coeff_C_a_X_sq : Polynomial.coeff (Polynomial.C a * X ^ 2) 3 = 0 := by
      rw [Polynomial.coeff_C_mul_X_pow a 2 3]
      rw [if_neg (by norm_num : 3 ≠ 2)]
    rw [h_coeff_C_a_X_sq]

    have h_coeff_C_b_X : Polynomial.coeff (Polynomial.C b * X) 3 = 0 := by
      rw [Polynomial.coeff_C_mul_X b 3]
      rw [if_neg (by norm_num : 3 ≠ 1)]
    rw [h_coeff_C_b_X]

    have h_coeff_C_c : Polynomial.coeff (Polynomial.C c) 3 = 0 := by
      rw [Polynomial.coeff_C]
      rw [if_neg (by norm_num : 3 ≠ 0)]
    rw [h_coeff_C_c]
    norm_num

  subprob_P_coeff2 :≡ Polynomial.coeff P 2 = a
  subprob_P_coeff2_proof ⇐ show subprob_P_coeff2 by








    rw [P_def]

    simp only [coeff_add]

    have h_coeff_X3 : coeff (X ^ (3 : ℕ) : ℝ[X]) 2 = 0 := by
      rw [Polynomial.coeff_X_pow 3 2]
      simp
    rw [h_coeff_X3]

    have h_coeff_CaX2 : coeff (C a * X ^ (2 : ℕ) : ℝ[X]) 2 = a := by
      rw [Polynomial.coeff_C_mul_X_pow a 2 2]
      simp
    rw [h_coeff_CaX2]

    have h_coeff_CbX : coeff (C b * X : ℝ[X]) 2 = 0 := by
      rw [coeff_C_mul_X b 2]
      simp
    rw [h_coeff_CbX]

    have h_coeff_Cc : coeff (C c : ℝ[X]) 2 = 0 := by
      apply Polynomial.coeff_C_ne_zero
      decide
    rw [h_coeff_Cc]

    simp

  subprob_P_coeff1 :≡ Polynomial.coeff P 1 = b
  subprob_P_coeff1_proof ⇐ show subprob_P_coeff1 by

    rw [P_def]


    simp
  subprob_P_coeff0 :≡ Polynomial.coeff P 0 = c
  subprob_P_coeff0_proof ⇐ show subprob_P_coeff0 by




    rw [P_def]

    rw [Polynomial.coeff_add]

    rw [Polynomial.coeff_C_zero]

    rw [add_left_eq_self]

    rw [Polynomial.coeff_add]

    rw [Polynomial.coeff_mul_X_zero]

    rw [add_zero]

    rw [Polynomial.coeff_add]

    rw [Polynomial.coeff_X_pow 3 0]
    rw [if_neg (show (0 : ℕ) ≠ 3 by decide)]

    rw [zero_add]

    rw [Polynomial.coeff_C_mul_X_pow a 2 0]
    rw [if_neg (show (0 : ℕ) ≠ 2 by decide)]

  subprob_P_monic :≡ Polynomial.Monic P
  subprob_P_monic_proof ⇐ show subprob_P_monic by
    rw [Polynomial.Monic]
    rw [Polynomial.leadingCoeff]
    rw [subprob_P_natDegree_proof]
    exact subprob_P_coeff3_proof


  subprob_P_is_root_r₁ :≡ Polynomial.IsRoot P r₁
  subprob_P_is_root_r₁_proof ⇐ show subprob_P_is_root_r₁ by


    rw [Polynomial.IsRoot]

    rw [subprob_P_eval_eq_f_proof r₁]

    rw [← Set.mem_singleton_iff, ← Set.mem_preimage, h₁]

    rw [r₁_def]

    simp

  subprob_P_is_root_r₂ :≡ Polynomial.IsRoot P r₂
  subprob_P_is_root_r₂_proof ⇐ show subprob_P_is_root_r₂ by



    rw [Polynomial.IsRoot.def]
    rw [subprob_P_eval_eq_f_proof]
    rw [← Set.mem_singleton_iff]
    rw [← Set.mem_preimage]
    rw [h₁]
    rw [r₂_def]
    apply Set.mem_insert_of_mem
    apply Set.mem_insert

  subprob_P_is_root_r₃ :≡ Polynomial.IsRoot P r₃
  subprob_P_is_root_r₃_proof ⇐ show subprob_P_is_root_r₃ by

    rw [Polynomial.IsRoot.def]
    rw [subprob_P_eval_eq_f_proof r₃]
    rw [← (Set.mem_preimage.trans Set.mem_singleton_iff)]
    rw [h₁]
    rw [r₃_def]
    simp

  Rts_ms := Polynomial.roots P
  subprob_roots_multiset_eq_r1r2r3 :≡ Rts_ms = ({r₁, r₂, r₃} : Multiset ℝ)
  subprob_roots_multiset_eq_r1r2r3_proof ⇐ show subprob_roots_multiset_eq_r1r2r3 by



    rw [Rts_ms_def]

    let S : Multiset ℝ := {r₁, r₂, r₃}


    have hS_nodup : S.Nodup := by
      dsimp [S]
      rw [Multiset.nodup_cons]
      constructor
      .
        simp only [Multiset.mem_cons, Multiset.mem_singleton, not_or]
        exact ⟨subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof⟩
      .
        dsimp
        rw [Multiset.nodup_cons]
        constructor
        .
          simp only [Multiset.mem_singleton]
          exact subprob_r₂_ne_r₃_proof
        .
          exact Multiset.nodup_singleton _

    have h_all_S_are_roots : ∀ r ∈ S, IsRoot P r := by
      intro r hr_mem
      dsimp [S] at hr_mem
      simp only [Multiset.mem_cons, Multiset.mem_singleton, Multiset.not_mem_zero] at hr_mem
      rcases hr_mem with (h_r_eq_r1 | h_r_eq_r2 | h_r_eq_r3)
      .
        subst h_r_eq_r1
        exact subprob_P_is_root_r₁_proof
      .
        subst h_r_eq_r2
        exact subprob_P_is_root_r₂_proof
      .
        subst h_r_eq_r3
        exact subprob_P_is_root_r₃_proof

    have hS_card_eq_3 : Multiset.card S = 3 := by
      dsimp [S]
      rw [Multiset.card_cons]

      rw [Multiset.card_cons]
      rw [Multiset.card_singleton]

    apply Eq.symm
    apply Multiset.eq_of_le_of_card_le

    .
      apply (Multiset.le_iff_count).mpr
      intro x
      by_cases hxS : x ∈ S
      .
        rw [Multiset.count_eq_one_of_mem hS_nodup hxS]
        rw [Nat.one_le_iff_ne_zero, Multiset.count_ne_zero]
        have hP_ne_0 : P ≠ 0 := Polynomial.Monic.ne_zero subprob_P_monic_proof
        apply (Polynomial.mem_roots hP_ne_0).mpr
        exact h_all_S_are_roots x hxS
      .
        rw [Multiset.count_eq_zero_of_not_mem hxS]
        exact Nat.zero_le _

    .
      rw [hS_card_eq_3]
      have hP_ne_0 : P ≠ 0 := Monic.ne_zero subprob_P_monic_proof
      have h_card_roots_P_le_natDegree_P := Polynomial.card_roots' P
      rw [subprob_P_natDegree_proof] at h_card_roots_P_le_natDegree_P
      exact h_card_roots_P_le_natDegree_P


  subprob_card_Rts_ms_eq_3 :≡ Multiset.card Rts_ms = 3
  subprob_card_Rts_ms_eq_3_proof ⇐ show subprob_card_Rts_ms_eq_3 by

    rw [subprob_roots_multiset_eq_r1r2r3_proof]

    have h_nodup_r123 : Multiset.Nodup ({r₁, r₂, r₃} : Multiset ℝ) := by
      dsimp
      rw [Multiset.nodup_cons]
      constructor
      ·
        simp [subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof]
      ·
        rw [Multiset.nodup_cons]
        constructor
        ·
          simp [subprob_r₂_ne_r₃_proof]
        ·
          rw [(@Multiset.singleton_eq_cons_iff ℝ r₃ r₃ 0).mpr ⟨rfl, rfl⟩]
          rw [Multiset.nodup_cons]
          constructor
          ·
            simp
          ·
            exact Multiset.nodup_zero

    have h_toFinset_eq : ({r₁, r₂, r₃} : Multiset ℝ).toFinset = ({r₁, r₂, r₃} : Finset ℝ) := by
      dsimp
      rw [Multiset.toFinset_cons]
      rw [Multiset.toFinset_cons]
      rw [(@Multiset.singleton_eq_cons_iff ℝ r₃ r₃ (0 : Multiset ℝ)).mpr ⟨rfl, rfl⟩]
      rw [Multiset.toFinset_cons]
      rw [Multiset.toFinset_zero]
      rfl

    have h_val_eq_self_of_nodup : (({r₁, r₂, r₃} : Multiset ℝ).toFinset).val = ({r₁, r₂, r₃} : Multiset ℝ) := by
      rw [Multiset.toFinset_val]
      rw [Multiset.dedup_eq_self]
      exact h_nodup_r123

    rw [← h_val_eq_self_of_nodup, h_toFinset_eq]

    rw [Finset.card_val]

    simp [subprob_r₁_ne_r₂_proof, subprob_r₁_ne_r₃_proof, subprob_r₂_ne_r₃_proof]


  subprob_card_roots_eq_natDegree :≡ Multiset.card Rts_ms = Polynomial.natDegree P
  subprob_card_roots_eq_natDegree_proof ⇐ show subprob_card_roots_eq_natDegree by



    rw [subprob_card_Rts_ms_eq_3_proof]

    rw [subprob_P_natDegree_proof]


  subprob_P_splits :≡ Polynomial.Splits (RingHom.id ℝ) P
  subprob_P_splits_proof ⇐ show subprob_P_splits by
    apply (Polynomial.splits_iff_card_roots (K := ℝ) (p := P)).mpr
    rw [← Rts_ms_def]
    exact subprob_card_roots_eq_natDegree_proof


  S₁ := r₁ + r₂ + r₃
  S₂ := r₁*r₂ + r₁*r₃ + r₂*r₃
  S₃ := r₁*r₂*r₃

  subprob_S₁_eq_esymm_roots_1 :≡ S₁ = Multiset.esymm Rts_ms 1
  subprob_S₁_eq_esymm_roots_1_proof ⇐ show subprob_S₁_eq_esymm_roots_1 by

    rw [S₁_def]

    rw [subprob_roots_multiset_eq_r1r2r3_proof]

    have esymm_eq_sum_for_roots : Multiset.esymm ({r₁, r₂, r₃} : Multiset ℝ) 1 = Multiset.sum ({r₁, r₂, r₃} : Multiset ℝ) := by
      let s_roots := ({r₁, r₂, r₃} : Multiset ℝ)
      unfold Multiset.esymm

      have h_powerset_inst : Multiset.powersetCard 1 s_roots = Multiset.map (fun x => ({x} : Multiset ℝ)) s_roots :=
        Multiset.powersetCard_one s_roots
      rw [h_powerset_inst]

      rw [Multiset.map_map]

      have h_comp_prod_singleton : Multiset.prod ∘ (fun x : ℝ => ({x} : Multiset ℝ)) = id := by
        funext x
        simp only [Function.comp_apply, Multiset.prod_singleton]
        rfl
      rw [h_comp_prod_singleton]

      rw [Multiset.map_id]

    rw [esymm_eq_sum_for_roots]

    simp
    ring

  subprob_S₂_eq_esymm_roots_2 :≡ S₂ = Multiset.esymm Rts_ms 2
  subprob_S₂_eq_esymm_roots_2_proof ⇐ show subprob_S₂_eq_esymm_roots_2 by





    rw [S₂_def]

    rw [subprob_roots_multiset_eq_r1r2r3_proof]

    rw [Multiset.esymm]

    simp [*, Multiset.powersetCard_one, Multiset.map_singleton, Multiset.prod_singleton, Multiset.sum_singleton, add_comm, mul_comm, add_assoc]


  subprob_S₃_eq_esymm_roots_3 :≡ S₃ = Multiset.esymm Rts_ms 3
  subprob_S₃_eq_esymm_roots_3_proof ⇐ show subprob_S₃_eq_esymm_roots_3 by

    rw [S₃_def]

    rw [subprob_roots_multiset_eq_r1r2r3_proof]

    have h_card_eq_k : Multiset.card ({r₁, r₂, r₃} : Multiset ℝ) = 3 := by
      simp

    have h_esymm_rw : Multiset.esymm ({r₁, r₂, r₃} : Multiset ℝ) 3 = Multiset.prod ({r₁, r₂, r₃} : Multiset ℝ) := by
      rw [←h_card_eq_k]
      rw [Multiset.esymm]
      let M_val := ({r₁, r₂, r₃} : Multiset ℝ)
      have H_powerset_card_eq : Multiset.powersetCard (Multiset.card M_val) M_val = {M_val} := by
        rw [(show Multiset.card M_val = 3 from h_card_eq_k)]

        let M0 := (0 : Multiset ℝ)
        let M1 := r₃ ::ₘ M0
        let M2 := r₂ ::ₘ M1
        have H_M0_card : Multiset.card M0 = 0 := Multiset.card_zero
        have H_M1_card : Multiset.card M1 = 1 := by rw [Multiset.card_cons, H_M0_card]
        have H_M2_card : Multiset.card M2 = 2 := by rw [Multiset.card_cons, H_M1_card]

        have h_powerset_M0 : Multiset.powersetCard 0 M0 = {M0} := by
          exact Multiset.powersetCard_zero_left M0

        have h_powerset_M1 : Multiset.powersetCard 1 M1 = {M1} := by
          rw [show M1 = r₃ ::ₘ M0 by rfl, Multiset.powersetCard_cons 0 r₃ M0]
          have h_first_term_zero : Multiset.powersetCard ((0 : ℕ) + 1) M0 = 0 := by
            rw [←H_M0_card]
            exact Multiset.powersetCard_card_add M0 Nat.one_pos
          rw [h_first_term_zero]
          rw [zero_add]
          rw [h_powerset_M0]
          rw [Multiset.map_singleton]

        have h_powerset_M2 : Multiset.powersetCard 2 M2 = {M2} := by
          rw [show M2 = r₂ ::ₘ M1 by rfl]
          rw [Multiset.powersetCard_cons 1 r₂ M1]

          have h_card_M1_lt_2 : Multiset.card M1 < 2 := by (rw [H_M1_card]; norm_num)
          have h_term1_zero : Multiset.powersetCard 2 M1 = 0 :=
            Multiset.powersetCard_eq_empty 2 h_card_M1_lt_2
          rw [h_term1_zero, zero_add]

          rw [h_powerset_M1]
          rw [Multiset.map_singleton]
        rw [show M_val = r₁ ::ₘ M2 by rfl, Multiset.powersetCard_cons 2 r₁ M2]
        have h_first_term_zero' : Multiset.powersetCard ((2 : ℕ) + 1) M2 = 0 := by
          rw [←H_M2_card]
          exact Multiset.powersetCard_card_add M2 Nat.one_pos
        rw [h_first_term_zero']
        rw [zero_add]
        rw [h_powerset_M2]
        rw [Multiset.map_singleton]
      rw [H_powerset_card_eq]
      rw [Multiset.map_singleton]
      rw [Multiset.sum_singleton]
    rw [h_esymm_rw]
    simp
    ring

  subprob_natDeg_P_minus_2_is_1 :≡ Polynomial.natDegree P - 2 = 1
  subprob_natDeg_P_minus_2_is_1_proof ⇐ show subprob_natDeg_P_minus_2_is_1 by

    rw [subprob_P_natDegree_proof]

  subprob_vieta_coeff2_form :≡ Polynomial.coeff P 2 = (-1 : ℝ) ^ (Polynomial.natDegree P - 2) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 2)
  subprob_vieta_coeff2_form_proof ⇐ show subprob_vieta_coeff2_form by





    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof

    let j_for_theorem := Polynomial.natDegree P - 2

    have h_j_le_deg : j_for_theorem ≤ natDegree P := by
      apply Nat.sub_le (natDegree P) 2

    have vieta_result : coeff P (natDegree P - j_for_theorem) =
                         (-1 : ℝ) ^ j_for_theorem * Multiset.esymm (roots P) j_for_theorem := by
      have h_k_idx_le_deg : (natDegree P - j_for_theorem) ≤ natDegree P := by
        apply Nat.sub_le (natDegree P) j_for_theorem

      have h_main_vieta_eq := Polynomial.coeff_eq_esymm_roots_of_card
        h_card_roots_eq_natDegree
        h_k_idx_le_deg


      rw [Nat.sub_sub_self h_j_le_deg] at h_main_vieta_eq

      rw [subprob_P_monic_proof] at h_main_vieta_eq

      rw [one_mul] at h_main_vieta_eq

      exact h_main_vieta_eq

    have h_2_le_natDegree_P : 2 ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num

    have coeff_index_simpl : natDegree P - j_for_theorem = 2 := by
      apply Nat.sub_sub_self h_2_le_natDegree_P

    rw [coeff_index_simpl] at vieta_result

    rw [← Rts_ms_def] at vieta_result

    exact vieta_result
  subprob_coeff_P_2_eq_neg_S₁ :≡ Polynomial.coeff P 2 = -S₁
  subprob_coeff_P_2_eq_neg_S₁_proof ⇐ show subprob_coeff_P_2_eq_neg_S₁ by
    rw [subprob_vieta_coeff2_form_proof]

    rw [subprob_natDeg_P_minus_2_is_1_proof]

    rw [pow_one (-(1 : ℝ))]

    rw [subprob_S₁_eq_esymm_roots_1_proof]

    rw [neg_one_mul]
  subprob_vieta_a :≡ a = -S₁
  subprob_vieta_a_proof ⇐ show subprob_vieta_a by

    have h_a_eq_coeffP2 : a = coeff P (2 : ℕ) := by
      exact subprob_P_coeff2_proof.symm

    have h_coeffP2_eq_negS1 : coeff P (2 : ℕ) = -S₁ := by
      exact subprob_coeff_P_2_eq_neg_S₁_proof

    rw [h_a_eq_coeffP2]
    exact h_coeffP2_eq_negS1

  subprob_natDeg_P_minus_1_is_2 :≡ Polynomial.natDegree P - 1 = 2
  subprob_natDeg_P_minus_1_is_2_proof ⇐ show subprob_natDeg_P_minus_1_is_2 by

    rw [subprob_P_natDegree_proof]

  subprob_vieta_coeff1_form :≡ Polynomial.coeff P 1 = (-1 : ℝ) ^ (Polynomial.natDegree P - 1) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 1)
  subprob_vieta_coeff1_form_proof ⇐ show subprob_vieta_coeff1_form by




    rw [Rts_ms_def]


    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof

    have h_one_le_natDegree : (1 : ℕ) ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num

    rw [Polynomial.coeff_eq_esymm_roots_of_card h_card_roots_eq_natDegree h_one_le_natDegree]

    rw [subprob_P_monic_proof]

    rw [one_mul]

  subprob_coeff_P_1_eq_S₂ :≡ Polynomial.coeff P 1 = S₂
  subprob_coeff_P_1_eq_S₂_proof ⇐ show subprob_coeff_P_1_eq_S₂ by
    rw [subprob_vieta_coeff1_form_proof]

    rw [subprob_natDeg_P_minus_1_is_2_proof]

    simp

    rw [← subprob_S₂_eq_esymm_roots_2_proof]
  subprob_vieta_b :≡ b = S₂
  subprob_vieta_b_proof ⇐ show subprob_vieta_b by


    have h1 : b = coeff P (1 : ℕ) := by
      exact Eq.symm subprob_P_coeff1_proof

    have h2 : coeff P (1 : ℕ) = S₂ := by
      exact subprob_coeff_P_1_eq_S₂_proof

    rw [h1]
    rw [h2]

  subprob_natDeg_P_minus_0_is_3 :≡ Polynomial.natDegree P - 0 = 3
  subprob_natDeg_P_minus_0_is_3_proof ⇐ show subprob_natDeg_P_minus_0_is_3 by


    rw [subprob_P_natDegree_proof]

  subprob_vieta_coeff0_form :≡ Polynomial.coeff P 0 = (-1 : ℝ) ^ (Polynomial.natDegree P - 0) * Multiset.esymm Rts_ms (Polynomial.natDegree P - 0)
  subprob_vieta_coeff0_form_proof ⇐ show subprob_vieta_coeff0_form by




    have h_k_le_natDegree : 0 ≤ natDegree P := by
      rw [subprob_P_natDegree_proof]
      norm_num

    have h_card_roots_eq_natDegree : Multiset.card (roots P) = natDegree P := by
      rw [← Rts_ms_def]
      exact subprob_card_roots_eq_natDegree_proof

    have h_vieta := Polynomial.coeff_eq_esymm_roots_of_card h_card_roots_eq_natDegree h_k_le_natDegree

    rw [Polynomial.leadingCoeff, Monic.coeff_natDegree subprob_P_monic_proof, one_mul] at h_vieta

    rw [← Rts_ms_def] at h_vieta

    exact h_vieta
  subprob_coeff_P_0_eq_neg_S₃ :≡ Polynomial.coeff P 0 = -S₃
  subprob_coeff_P_0_eq_neg_S₃_proof ⇐ show subprob_coeff_P_0_eq_neg_S₃ by


    rw [subprob_vieta_coeff0_form_proof]
    rw [subprob_natDeg_P_minus_0_is_3_proof]
    have h_pow_neg_one_cubed : (-(1 : ℝ)) ^ (3 : ℕ) = -1 := by
      norm_num
    rw [h_pow_neg_one_cubed]
    rw [subprob_S₃_eq_esymm_roots_3_proof]
    rw [neg_mul, one_mul]

  subprob_vieta_c :≡ c = -S₃
  subprob_vieta_c_proof ⇐ show subprob_vieta_c by




    rw [← subprob_P_coeff0_proof]

    exact subprob_coeff_P_0_eq_neg_S₃_proof

  subprob_abc_eq_S1S2S3 :≡ a * b * c = S₁ * S₂ * S₃
  subprob_abc_eq_S1S2S3_proof ⇐ show subprob_abc_eq_S1S2S3 by

    rw [subprob_vieta_a_proof]

    rw [subprob_vieta_b_proof]

    rw [subprob_vieta_c_proof]

    simp

  z := Complex.exp ( (2 * Real.pi / 7) * Complex.I )

  subprob_z_pow_7_eq_1 :≡ z^(7:ℕ) = (1 : ℂ)
  subprob_z_pow_7_eq_1_proof ⇐ show subprob_z_pow_7_eq_1 by



















    rw [z_def]

    have h_arg_coerce : (2 : ℂ) * Complex.ofReal Real.pi / (7 : ℂ) = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) := by
      simp

    change (Complex.exp (((2 : ℂ) * Complex.ofReal Real.pi / (7 : ℂ)) * I)) ^ (7 : ℕ) = (1 : ℂ)

    rw [h_arg_coerce]

    rw [← Complex.exp_nsmul]
    rw [nsmul_eq_mul]

    rw [← mul_assoc]

    have h_complex_coeff_simplify : (↑(7 : ℕ) : ℂ) * Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) = Complex.ofReal ((2 : ℝ) * Real.pi) := by
      rw [← Complex.ofReal_natCast]
      simp only [Complex.ofReal_eq_coe]
      rw [← Complex.ofReal_mul]
      apply congr_arg Complex.ofReal
      norm_cast
      field_simp [(by norm_num : (7 : ℝ) ≠ 0)]
    rw [h_complex_coeff_simplify]

    apply Complex.ext_iff.mpr
    constructor
    .
      rw [Complex.ofReal_eq_coe]
      rw [Complex.exp_ofReal_mul_I_re]
      rw [Complex.one_re]
      rw [Real.cos_two_pi]
    .
      rw [Complex.ofReal_eq_coe]
      rw [Complex.exp_ofReal_mul_I_im]
      rw [Complex.one_im]
      rw [Real.sin_two_pi]

  subprob_z_ne_1 :≡ z ≠ (1 : ℂ)
  subprob_z_ne_1_proof ⇐ show subprob_z_ne_1 by

















    by_contra h_contra
    let θ₀ : ℝ := (2 * Real.pi) / 7
    have h_arg_rewrite : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) * I = (↑θ₀ : ℂ) * I := by
      simp [θ₀]

    rw [z_def, h_arg_rewrite] at h_contra
    rw [mul_comm (↑θ₀ : ℂ) I] at h_contra
    rw [Complex.exp_eq_one_iff] at h_contra
    rcases h_contra with ⟨k, hk_complex_eq⟩
    have hk : θ₀ = (↑(2 * k) : ℝ) * Real.pi := by
      have h_rhs_transformed : ((↑k : ℂ) * ((2 : ℂ) * (ofReal' Real.pi : ℂ))) * I = (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi)) : ℂ) * I := by
        rw [mul_left_inj' Complex.I_ne_zero]
        rw [← Complex.ofReal_intCast k]
        rw [← Complex.ofReal_ofNat 2]
        rw [← Complex.ofReal_mul]
        rw [← Complex.ofReal_mul]
        apply Complex.ofReal_inj.mpr
        apply congr_arg ((↑(k) : ℝ) * ·)
        apply congr_arg (· * Real.pi)
        exact Nat.cast_two

      have h_eq_rewritten : I * (↑θ₀ : ℂ) = (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi)) : ℂ) * I := by
        rw [hk_complex_eq]
        rw [← mul_assoc (↑k : ℂ) ((2 : ℂ) * (ofReal' Real.pi : ℂ)) I]
        rw [h_rhs_transformed]

      rw [mul_comm (Complex.ofReal ((↑k : ℝ) * (2 * Real.pi))) I] at h_eq_rewritten
      replace h_eq_rewritten := (mul_right_inj' Complex.I_ne_zero).mp h_eq_rewritten
      rw [Complex.ofReal_eq_coe] at h_eq_rewritten
      rw [Complex.ofReal_inj] at h_eq_rewritten
      rw [h_eq_rewritten]
      rw [← mul_assoc]
      rw [mul_comm ((k : ℝ) : ℝ) (2 : ℝ)]
      rw [← Int.cast_two]
      rw [← Int.cast_mul]

    have hk_val_subst : (2 * Real.pi) / 7 = (↑(2 * k) : ℝ) * Real.pi := by
      rw [← hk]

    have h_cast_detail : (↑(2 * k) : ℝ) = (2 : ℝ) * (k : ℝ) := by
      rw [Int.cast_mul, Int.cast_two]
    rw [h_cast_detail] at hk_val_subst

    have h_two_pi_ne_zero : 2 * Real.pi ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact Real.pi_ne_zero

    have h_frac_eq_int_real : (1/7 : ℝ) = (k : ℝ) := by
      have h_rhs_rearranged : (2 : ℝ) * (k : ℝ) * Real.pi = (k : ℝ) * (2 * Real.pi) := by
        ac_rfl
      have h_eq_rearranged : (2 * Real.pi) / 7 = (k : ℝ) * (2 * Real.pi) := by
        rw [hk_val_subst, h_rhs_rearranged]
      rw [div_eq_mul_inv] at h_eq_rearranged
      rw [mul_comm ((2 : ℝ) * Real.pi) (7 : ℝ)⁻¹] at h_eq_rearranged
      rw [mul_eq_mul_right_iff] at h_eq_rearranged
      cases h_eq_rearranged with
      | inl h_eq =>
        rw [inv_eq_one_div] at h_eq
        exact h_eq
      | inr h_zero_pi =>
        exfalso; exact h_two_pi_ne_zero h_zero_pi

    have h_k_mul_7_eq_1 : (k : ℤ) * 7 = 1 := by
      rw [← Int.cast_inj (α := ℝ)]
      rw [Int.cast_mul, Int.cast_ofNat 7]
      rw [← h_frac_eq_int_real]
      field_simp

    rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at h_k_mul_7_eq_1
    cases h_k_mul_7_eq_1 with
    | inl h_left =>
      have h_7_eq_1 : (7:ℤ) = 1 := h_left.right
      contradiction
    | inr h_right =>
      have h_7_eq_neg_1 : (7:ℤ) = -1 := h_right.right
      contradiction
  subprob_sum_z_k_0_6_eq_0 :≡ ∑ k in Finset.range (7:ℕ), z^k = (0 : ℂ)
  subprob_sum_z_k_0_6_eq_0_proof ⇐ show subprob_sum_z_k_0_6_eq_0 by



    have h_z_minus_one_ne_zero : z - (1 : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact subprob_z_ne_1_proof


    have h_sum_eq_zero_iff_pow_eq_one : (∑ k in Finset.range (7 : ℕ), z ^ k = 0) ↔ z ^ (7 : ℕ) = 1 := by
      have h_seven_pos : 0 < (7 : ℕ) := by norm_num
      have h_geom_sum_formula : ∑ k in Finset.range (7 : ℕ), z ^ k = (z ^ (7 : ℕ) - 1) / (z - 1) :=
        geom_sum_eq subprob_z_ne_1_proof (7 : ℕ)
      rw [h_geom_sum_formula]
      have h_div_form_equiv : ((z ^ (7 : ℕ) - (1 : ℂ)) / (z - (1 : ℂ)) = (0 : ℂ)) ↔
                              ((z ^ (7 : ℕ) - (1 : ℂ)) = (0 : ℂ) ∨ z - (1 : ℂ) = (0 : ℂ)) :=
        div_eq_zero_iff
      rw [h_div_form_equiv]
      rw [or_iff_left h_z_minus_one_ne_zero]
      rw [sub_eq_zero]

    apply h_sum_eq_zero_iff_pow_eq_one.mpr
    exact subprob_z_pow_7_eq_1_proof
  sum_zk_1_to_6 := ∑ k in Finset.Ioo (0:ℕ) (7:ℕ), z^k
  subprob_sum_z_k_1_6_eq_neg_1 :≡ sum_zk_1_to_6 = (-1 : ℂ)
  subprob_sum_z_k_1_6_eq_neg_1_proof ⇐ show subprob_sum_z_k_1_6_eq_neg_1 by


    have h_sum_total : ∑ k ∈ Finset.range (7 : ℕ), z ^ k = (0 : ℂ) := by
      exact subprob_sum_z_k_0_6_eq_0_proof

    have h_decomp_sum : ∑ k ∈ Finset.range 7, z ^ k = z ^ 0 + ∑ k ∈ Finset.range 6, z ^ (k + 1) := by
      rw [add_comm]
      exact Finset.sum_range_succ' (fun k => z ^ k) 6

    have h_z_pow_0 : z ^ (0 : ℕ) = (1 : ℂ) := by
      exact pow_zero z
    rw [h_z_pow_0] at h_decomp_sum

    rw [h_decomp_sum] at h_sum_total

    have h_sum_shifted_eq_sum_Ioo : ∑ k ∈ Finset.range 6, z ^ (k + 1) = ∑ k ∈ Finset.Ioo 0 7, z ^ k := by
      have h_sum_map : ∑ k ∈ Finset.range 6, z ^ (k + 1) = ∑ k ∈ Finset.Ico 1 (6 + 1), z ^ k := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add' (fun i => z^i) 0 6 1
      rw [h_sum_map]
      rw [Nat.add_one]
      have h_Ico_eq_Ioo : Finset.Ico (1 : ℕ) 7 = Finset.Ioo (0 : ℕ) 7 := by
        rw [← Finset.Ico_erase_left (0 : ℕ) 7]
        ext x
        simp [Nat.one_le_iff_ne_zero, Nat.zero_le]
      rw [h_Ico_eq_Ioo]

    rw [h_sum_shifted_eq_sum_Ioo] at h_sum_total

    rw [← sum_zk_1_to_6_def] at h_sum_total

    rw [add_comm] at h_sum_total
    exact (add_eq_zero_iff_eq_neg.mp h_sum_total)



  R₁_complex := (z + z^(6:ℕ)) / (2 : ℂ)
  R₂_complex := (z^(2:ℕ) + z^(5:ℕ)) / (2 : ℂ)
  R₃_complex := (z^(3:ℕ) + z^(4:ℕ)) / (2 : ℂ)

  subprob_ofReal_r₁_eq_R₁ :≡ Complex.ofReal r₁ = R₁_complex
  subprob_ofReal_r₁_eq_R₁_proof ⇐ show subprob_ofReal_r₁_eq_R₁ by


    rw [r₁_def, R₁_complex_def]

    let θ_real : ℝ := (2 : ℝ) * Real.pi / (7 : ℝ)

    have h_z_arg_eq_ofReal_θ_real : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) = Complex.ofReal θ_real := by
      dsimp only [θ_real]
      simp

    have h_z_alt : z = cexp (Complex.ofReal θ_real * I) := by
      rw [z_def]
      dsimp only [ofReal']
      rw [← Complex.ofReal_def Real.pi]
      apply congr_arg cexp
      apply congr_arg (fun x => x * I)
      exact h_z_arg_eq_ofReal_θ_real

    rw [h_z_alt]

    have hw_pow_7_eq_1 : (cexp (Complex.ofReal θ_real * I)) ^ 7 = 1 := by
      rw [← h_z_alt]
      exact subprob_z_pow_7_eq_1_proof

    have hw_ne_zero : cexp (Complex.ofReal θ_real * I) ≠ 0 := by
      intro hw_eq_zero
      have hw_pow_7_eq_zero : (cexp (Complex.ofReal θ_real * I)) ^ 7 = 0 ^ 7 := by rw [hw_eq_zero]
      rw [zero_pow (by norm_num)] at hw_pow_7_eq_zero
      rw [hw_pow_7_eq_1] at hw_pow_7_eq_zero
      exact one_ne_zero hw_pow_7_eq_zero

    have hw_pow_6_eq_inv_w : (cexp (Complex.ofReal θ_real * I)) ^ 6 = (cexp (Complex.ofReal θ_real * I))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ (cexp (Complex.ofReal θ_real * I)) 6]
      exact hw_pow_7_eq_1

    have h_inv_w_is_exp_neg : (cexp (Complex.ofReal θ_real * I))⁻¹ = cexp (-(Complex.ofReal θ_real * I)) := by
      rw [Complex.exp_neg]

    rw [hw_pow_6_eq_inv_w, h_inv_w_is_exp_neg]

    simp_rw [mul_comm (Complex.ofReal θ_real) I]

    change (Complex.ofReal (Real.cos θ_real) = _)

    have h_cos_def_applied : Complex.cos (Complex.ofReal θ_real) = (cexp (I * Complex.ofReal θ_real) + cexp (-(I * Complex.ofReal θ_real))) / (2 : ℂ) := by
      unfold Complex.cos
      simp_rw [mul_comm (Complex.ofReal θ_real) I]
      ring

    rw [← h_cos_def_applied]
    exact Complex.ofReal_cos θ_real

  subprob_ofReal_r₂_eq_R₂ :≡ Complex.ofReal r₂ = R₂_complex
  subprob_ofReal_r₂_eq_R₂_proof ⇐ show subprob_ofReal_r₂_eq_R₂ by


    rw [r₂_def, R₂_complex_def, z_def]
    have hz_arg_rewrite : (2 : ℂ) * ofReal' Real.pi / (7 : ℂ) * I = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ)) * I := by
      apply congr_arg (fun x => x * I)
      change (Nat.cast 2 : ℂ) * ofReal' Real.pi / (Nat.cast 7 : ℂ) = Complex.ofReal ((2 : ℝ) * Real.pi / (7 : ℝ))
      rw [(Complex.ofReal_natCast (2 : ℕ)).symm, (Complex.ofReal_natCast (7 : ℕ)).symm]
      rw [← Complex.ofReal_mul]
      rw [← Complex.ofReal_div]
      apply congr_arg Complex.ofReal
      simp only [Nat.cast_ofNat]
    rw [hz_arg_rewrite]
    let angle_unit : ℝ := (2 : ℝ) * Real.pi / (7 : ℝ)

    have h_z_pow_2 : cexp (Complex.ofReal angle_unit * I) ^ (2 : ℕ) = cexp (Complex.ofReal (↑(2 : ℕ) * angle_unit) * I) := by
      rw [← Complex.exp_nat_mul (Complex.ofReal angle_unit * I) (2 : ℕ)]
      apply congr_arg Complex.exp
      have h_cast_eq_2 : (Nat.cast 2 : ℂ) = Complex.ofReal (Nat.cast 2 : ℝ) := (Complex.ofReal_natCast 2).symm
      rw [h_cast_eq_2]
      rw [← mul_assoc]
      change (Complex.ofReal (Nat.cast 2 : ℝ) * Complex.ofReal angle_unit) * I = (ofReal' ((Nat.cast 2 : ℝ) * angle_unit)) * I
      rw [Complex.ofReal_mul]
      simp

    have h_z_pow_5 : cexp (Complex.ofReal angle_unit * I) ^ (5 : ℕ) = cexp (Complex.ofReal (↑(5 : ℕ) * angle_unit) * I) := by
      rw [← Complex.exp_nat_mul (Complex.ofReal angle_unit * I) (5 : ℕ)]
      apply congr_arg Complex.exp
      have h_nat_cast_5_eq : (Nat.cast 5 : ℂ) = Complex.ofReal (Nat.cast 5 : ℝ) := (Complex.ofReal_natCast 5).symm
      rw [h_nat_cast_5_eq]
      rw [← mul_assoc]
      change (Complex.ofReal (Nat.cast 5 : ℝ) * Complex.ofReal angle_unit) * I = (ofReal' ((Nat.cast 5 : ℝ) * angle_unit)) * I
      rw [Complex.ofReal_mul]
      simp

    rw [h_z_pow_2, h_z_pow_5]
    have h_2_angle_unit : ↑(2 : ℕ) * angle_unit = (4 : ℝ) * Real.pi / (7 : ℝ) := by
      simp only [angle_unit, Nat.cast_ofNat]
      ring

    have h_5_angle_unit : ↑(5 : ℕ) * angle_unit = (10 : ℝ) * Real.pi / (7 : ℝ) := by
      simp only [angle_unit, Nat.cast_ofNat]
      ring

    rw [h_2_angle_unit, h_5_angle_unit]
    apply Complex.ext_iff.mpr
    constructor

    .
      change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = re ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (2 : ℂ))
      change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = re ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (Nat.cast (2 : ℕ) : ℂ))
      rw [← Complex.ofReal_natCast (2 : ℕ)]
      rw [Complex.div_ofReal_re]
      rw [Complex.add_re]
      change Real.cos ((4 : ℝ) * Real.pi / (7 : ℝ)) = (re (cexp (Complex.ofReal' ((4 : ℝ) * Real.pi / (7 : ℝ)) * I)) + re (cexp (Complex.ofReal' ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (Nat.cast 2 : ℝ)
      rw [Complex.exp_ofReal_mul_I_re]
      rw [Complex.exp_ofReal_mul_I_re]
      field_simp [show (2 : ℝ) ≠ 0 by norm_num]
      rw [mul_comm, ← sub_eq_iff_eq_add]
      have h_angle_equiv : (10 : ℝ) * Real.pi / (7 : ℝ) = 2 * Real.pi - (4 : ℝ) * Real.pi / (7 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        ring
      rw [h_angle_equiv]
      rw [Real.cos_two_pi_sub]
      ring

    .
      change 0 = im ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (2 : ℂ))
      change 0 = im ((cexp (ofReal ((4 : ℝ) * Real.pi / (7 : ℝ)) * I) + cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I)) / (Nat.cast (2 : ℕ) : ℂ))
      rw [← Complex.ofReal_natCast (2 : ℕ)]
      rw [Complex.div_ofReal_im]
      rw [Complex.add_im]

      change (0 : ℝ) = (im (cexp (ofReal' ((4 : ℝ) * Real.pi / (7 : ℝ)) * I)) + im (cexp (ofReal ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (↑((2 : ℕ)) : ℝ)
      rw [Complex.exp_ofReal_mul_I_im ((4 : ℝ) * Real.pi / (7 : ℝ))]

      change (0 : ℝ) = (Real.sin ((4 : ℝ) * Real.pi / (7 : ℝ)) + im (cexp (ofReal' ((10 : ℝ) * Real.pi / (7 : ℝ)) * I))) / (↑((2 : ℕ)) : ℝ)
      rw [Complex.exp_ofReal_mul_I_im ((10 : ℝ) * Real.pi / (7 : ℝ))]

      field_simp [show (2 : ℝ) ≠ 0 by norm_num]
      have h_angle_equiv : (10 : ℝ) * Real.pi / (7 : ℝ) = 2 * Real.pi - (4 : ℝ) * Real.pi / (7 : ℝ) := by
        field_simp [Real.pi_ne_zero]
        ring
      rw [h_angle_equiv]
      rw [Real.sin_two_pi_sub]
      rw [add_neg_self]

  subprob_ofReal_r₃_eq_R₃ :≡ Complex.ofReal r₃ = R₃_complex
  subprob_ofReal_r₃_eq_R₃_proof ⇐ show subprob_ofReal_r₃_eq_R₃ by

    rw [r₃_def]

    rw [R₃_complex_def]

    rw [z_def]

    have hz3 : (cexp ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) ^ (3 : ℕ) =
               cexp (↑(3 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) := by
      rw [(Complex.exp_nat_mul _ _).symm]
    rw [hz3]

    have hz4 : (cexp ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) ^ (4 : ℕ) =
               cexp (↑(4 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I)) := by
      rw [(Complex.exp_nat_mul _ _).symm]
    rw [hz4]

    have exp_arg_3 : ↑(3 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I) = ((6 : ℂ) * ↑(Real.pi) / (7 : ℂ)) * I := by
      simp only [Nat.cast_ofNat]
      ring
    rw [exp_arg_3]

    have exp_arg_4 : ↑(4 : ℕ) * ((2 : ℂ) * ↑(Real.pi) / (7 : ℂ) * I) = ((8 : ℂ) * ↑(Real.pi) / (7 : ℂ)) * I := by
      simp only [Nat.cast_ofNat]
      ring
    rw [exp_arg_4]

    rw [Complex.exp_mul_I, Complex.exp_mul_I]

    rw [Complex.ofReal_eq_coe, Complex.ofReal_cos]

    have arg3_is_real : ((6 : ℂ) * ↑(Real.pi) / (7 : ℂ)) = ↑((6 : ℝ) * Real.pi / (7 : ℝ)) := by
      simp [Complex.ofReal_mul, Complex.ofReal_div]
    rw [arg3_is_real]

    have arg4_is_real : ((8 : ℂ) * ↑(Real.pi) / (7 : ℂ)) = ↑((8 : ℝ) * Real.pi / (7 : ℝ)) := by
      simp [Complex.ofReal_mul, Complex.ofReal_div]
    rw [arg4_is_real]

    apply Complex.ext_iff.mpr
    constructor

    .
      simp only [Complex.cos_ofReal_re, Complex.add_re, Complex.mul_I_re, Complex.sin_ofReal_im, Complex.ofReal_re, Complex.div_re, Complex.ofReal_im, pow_two, Complex.sin_ofReal_re]
      norm_num
      have h_cos_eq : Real.cos ((6 : ℝ) * Real.pi / 7) = Real.cos ((8 : ℝ) * Real.pi / 7) := by
        have h_arg_rel : (8 : ℝ) * Real.pi / 7 = 2 * Real.pi - (6 : ℝ) * Real.pi / 7 := by
          field_simp; ring
        rw [h_arg_rel, Real.cos_two_pi_sub]
      rw [h_cos_eq]
      ring

    .
      simp only [Complex.cos_ofReal_im, Complex.add_im, Complex.mul_I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.ofReal_re, Complex.div_im, Complex.ofReal_im, pow_two, Complex.sin_ofReal_im]
      norm_num
      have h_sin_sum_eq_zero : Real.sin ((6 : ℝ) * Real.pi / 7) + Real.sin ((8 : ℝ) * Real.pi / 7) = 0 := by
        have h_6pi7_eq : (6 : ℝ) * Real.pi / 7 = Real.pi - Real.pi / 7 := by field_simp; ring
        have h_8pi7_eq : (8 : ℝ) * Real.pi / 7 = Real.pi + Real.pi / 7 := by field_simp; ring
        have sin_pi_plus_x (x : ℝ) : Real.sin (Real.pi + x) = - Real.sin x := by
          rw [add_comm, Real.sin_add_pi x]
        rw [h_6pi7_eq, Real.sin_pi_sub, h_8pi7_eq, sin_pi_plus_x (Real.pi/7)]
        ring
      rw [h_sin_sum_eq_zero]
      norm_num


  S₁_complex_repr := R₁_complex + R₂_complex + R₃_complex
  subprob_S₁_complex_calc :≡ S₁_complex_repr = sum_zk_1_to_6 / (2 : ℂ)
  subprob_S₁_complex_calc_proof ⇐ show subprob_S₁_complex_calc by



    rw [S₁_complex_repr_def]
    rw [R₁_complex_def, R₂_complex_def, R₃_complex_def]
    rw [sum_zk_1_to_6_def]

    field_simp

    have h_sum_Ioo_to_Ico : ∑ k ∈ Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k = ∑ k ∈ Finset.Ico (0 + 1) 7, z ^ k := by
      have h_finset_equality : Finset.Ioo (0 : ℕ) (7 : ℕ) = Finset.Ico (0 + 1) 7 := by
        ext k
        simp only [Finset.mem_Ioo, Finset.mem_Ico, Nat.lt_iff_add_one_le]
      rw [h_finset_equality]
    rw [h_sum_Ioo_to_Ico]
    simp only [Nat.zero_add]

    rw [Finset.sum_Ico_eq_sum_range (f := fun k => z ^ k) (m := 1) (n := 7)]

    norm_num

    have h_sum_expanded : ∑ k ∈ Finset.range 6, z ^ (1 + k) =
        z ^ 1 + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 := by
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (1 + k)) 5]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 2)) 4]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 3)) 3]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 4)) 2]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 5)) 1]
      simp only [Nat.add_zero, pow_one, Nat.add_left_comm, Nat.one_add, Nat.add_assoc]
      rw [Finset.sum_range_succ' (fun k ↦ z ^ (k + 6)) 0]
      rw [Finset.sum_range_zero]
      abel
    rw [h_sum_expanded]

    simp only [pow_one]

    abel

  subprob_S₁_complex_val :≡ S₁_complex_repr = (-1 : ℂ) / (2 : ℂ)
  subprob_S₁_complex_val_proof ⇐ show subprob_S₁_complex_val by


    rw [subprob_S₁_complex_calc_proof]

    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]

  subprob_S₁_val :≡ S₁ = (-1 : ℝ) / (2 : ℝ)
  subprob_S₁_val_proof ⇐ show subprob_S₁_val by





    have h_S₁_complex_eq_ofReal_S₁ : S₁_complex_repr = (S₁ : ℂ) := by
      rw [S₁_complex_repr_def]
      rw [← subprob_ofReal_r₁_eq_R₁_proof, ← subprob_ofReal_r₂_eq_R₂_proof, ← subprob_ofReal_r₃_eq_R₃_proof]
      simp only [← map_add Complex.ofReal]
      rw [S₁_def]
      rfl

    have h_ofReal_S₁_val : (S₁ : ℂ) = -(1 : ℂ) / (2 : ℂ) := by
      rw [← h_S₁_complex_eq_ofReal_S₁]
      rw [subprob_S₁_complex_val_proof]

    have h_complex_val_is_ofReal : -(1 : ℂ) / (2 : ℂ) = (((-1 : ℝ) / (2 : ℝ)) : ℂ) := by
      simp [Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div]

    have h_ofReal_S₁_eq_ofReal_val : (S₁ : ℂ) = (((-1 : ℝ) / (2 : ℝ)) : ℂ) := by
      rw [h_ofReal_S₁_val, h_complex_val_is_ofReal]

    exact (Complex.ofReal_inj).mp (h_ofReal_S₁_eq_ofReal_val.trans (Complex.ofReal_div (-1 : ℝ) (2 : ℝ)).symm)

  S₂_complex_term1 := R₁_complex * R₂_complex
  subprob_S₂_complex_term1_calc :≡ S₂_complex_term1 = (z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term1_calc_proof ⇐ show subprob_S₂_complex_term1_calc by



    rw [S₂_complex_term1_def, R₁_complex_def, R₂_complex_def]

    rw [_root_.div_mul_div_comm]

    have h_two_mul_two : (2 : ℂ) * (2 : ℂ) = (4 : ℂ) := by norm_num
    rw [h_two_mul_two]

    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by norm_num
    rw [div_left_inj' h_four_ne_zero]

    have h_z8 : z ^ (8 : ℕ) = z := by
      rw [show (8 : ℕ) = (7 : ℕ) + (1 : ℕ) by norm_num]
      rw [pow_add, subprob_z_pow_7_eq_1_proof, one_mul, pow_one]
    have h_z11 : z ^ (11 : ℕ) = z ^ (4 : ℕ) := by
      rw [show (11 : ℕ) = (7 : ℕ) + (4 : ℕ) by norm_num]
      rw [pow_add, subprob_z_pow_7_eq_1_proof, one_mul]

    ring_nf

    rw [h_z8, h_z11]
    ring
  S₂_complex_term2 := R₁_complex * R₃_complex
  subprob_S₂_complex_term2_calc :≡ S₂_complex_term2 = (z^(4:ℕ) + z^(5:ℕ) + z^(2:ℕ) + z^(3:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term2_calc_proof ⇐ show subprob_S₂_complex_term2_calc by
    rw [S₂_complex_term2_def, R₁_complex_def, R₃_complex_def]

    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by
      norm_num

    field_simp [h_four_ne_zero]

    ring_nf

    have h_z9 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by
      have h9_eq_2_add_7 : (9 : ℕ) = 2 + 7 := by norm_num
      rw [h9_eq_2_add_7, pow_add, subprob_z_pow_7_eq_1_proof, mul_one]

    have h_z10 : z ^ (10 : ℕ) = z ^ (3 : ℕ) := by
      have h10_eq_3_add_7 : (10 : ℕ) = 3 + 7 := by norm_num
      rw [h10_eq_3_add_7, pow_add, subprob_z_pow_7_eq_1_proof, mul_one]

    rw [h_z9, h_z10]

    ring
  S₂_complex_term3 := R₂_complex * R₃_complex
  subprob_S₂_complex_term3_calc :≡ S₂_complex_term3 = (z^(5:ℕ) + z^(6:ℕ) + z + z^(2:ℕ)) / (4 : ℂ)
  subprob_S₂_complex_term3_calc_proof ⇐ show subprob_S₂_complex_term3_calc by
    rw [S₂_complex_term3_def]
    rw [R₂_complex_def, R₃_complex_def]

    field_simp

    have h_lhs_expand : (z ^ 2 + z ^ 5) * (z ^ 3 + z ^ 4) = z ^ 5 + z ^ 6 + z ^ 8 + z ^ 9 := by
      ring
    rw [h_lhs_expand]

    have hz7_eq_1 : z ^ (7 : ℕ) = (1 : ℂ) := subprob_z_pow_7_eq_1_proof

    have hz8_eq_z : z ^ (8 : ℕ) = z := by
      have h_8_is_7_plus_1 : (8 : ℕ) = 7 + 1 := by norm_num
      rw [h_8_is_7_plus_1]
      rw [pow_add z 7 1]
      rw [hz7_eq_1]
      rw [one_mul]
      rw [pow_one]

    have hz9_eq_z2 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by
      have h_9_is_7_plus_2 : (9 : ℕ) = 7 + 2 := by norm_num
      rw [h_9_is_7_plus_2]
      rw [pow_add z 7 2]
      rw [hz7_eq_1]
      rw [one_mul]

    rw [hz8_eq_z, hz9_eq_z2]

    ring

  S₂_complex_repr := S₂_complex_term1 + S₂_complex_term2 + S₂_complex_term3
  subprob_S₂_complex_num_sum :≡ (z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)) + (z^(4:ℕ) + z^(5:ℕ) + z^(2:ℕ) + z^(3:ℕ)) + (z^(5:ℕ) + z^(6:ℕ) + z + z^(2:ℕ)) = (2 : ℂ) * sum_zk_1_to_6
  subprob_S₂_complex_num_sum_proof ⇐ show subprob_S₂_complex_num_sum by

    rw [sum_zk_1_to_6_def]

    have h_0_lt_7 : (0 : ℕ) < (7 : ℕ) := by norm_num
    have h_sum_rewrite : (∑ k ∈ Finset.Ioo (0 : ℕ) (7 : ℕ), z ^ k) = (∑ k ∈ Finset.Ico (0 + 1) 7, z ^ k) := by
      apply congr_arg (fun s : Finset ℕ => ∑ k ∈ s, z ^ k)
      apply Finset.ext
      intro x
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      rw [Nat.lt_iff_add_one_le]
    rw [h_sum_rewrite]
    rw [Finset.sum_Ico_eq_sum_range]

    norm_num

    simp [Finset.sum_range_succ, Finset.sum_range_zero, add_zero, pow_one]

    ring
  subprob_S₂_complex_calc :≡ S₂_complex_repr = ((2 : ℂ) * sum_zk_1_to_6) / (4 : ℂ)
  subprob_S₂_complex_calc_proof ⇐ show subprob_S₂_complex_calc by
    rw [S₂_complex_repr_def]
    rw [subprob_S₂_complex_term1_calc_proof, subprob_S₂_complex_term2_calc_proof, subprob_S₂_complex_term3_calc_proof]
    have h_four_ne_zero : (4 : ℂ) ≠ 0 := by
      norm_num
    field_simp [h_four_ne_zero]
    rw [subprob_S₂_complex_num_sum_proof]

  subprob_S₂_complex_val :≡ S₂_complex_repr = (-1 : ℂ) / (2 : ℂ)
  subprob_S₂_complex_val_proof ⇐ show subprob_S₂_complex_val by



    rw [subprob_S₂_complex_calc_proof]

    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]

    field_simp
    norm_num

  subprob_S₂_val :≡ S₂ = (-1 : ℝ) / (2 : ℝ)
  subprob_S₂_val_proof ⇐ show subprob_S₂_val by



    have h_ofReal_S₂_expanded : ofReal S₂ = (ofReal r₁) * (ofReal r₂) + (ofReal r₁) * (ofReal r₃) + (ofReal r₂) * (ofReal r₃) := by
      rw [S₂_def]
      simp

    have h_S₂_complex_repr_expanded : S₂_complex_repr = R₁_complex * R₂_complex + R₁_complex * R₃_complex + R₂_complex * R₃_complex := by
      rw [S₂_complex_repr_def, S₂_complex_term1_def, S₂_complex_term2_def, S₂_complex_term3_def]

    have h_ofReal_S₂_eq_S₂_complex_repr : ofReal S₂ = S₂_complex_repr := by
      rw [h_ofReal_S₂_expanded]
      rw [subprob_ofReal_r₁_eq_R₁_proof, subprob_ofReal_r₂_eq_R₂_proof, subprob_ofReal_r₃_eq_R₃_proof]
      rw [h_S₂_complex_repr_expanded]

    have h_ofReal_S₂_value : ofReal S₂ = -(1 : ℂ) / (2 : ℂ) := by
      rw [h_ofReal_S₂_eq_S₂_complex_repr]
      exact subprob_S₂_complex_val_proof

    have h_target_val_equiv : -(1 : ℂ) / (2 : ℂ) = ofReal (-(1 : ℝ) / (2 : ℝ)) := by
      simp

    rw [h_target_val_equiv] at h_ofReal_S₂_value
    exact Complex.ofReal_inj.mp h_ofReal_S₂_value








  S₃_complex_num_factor12 := (z + z^(6:ℕ)) * (z^(2:ℕ) + z^(5:ℕ))
  subprob_S₃_complex_num_factor12_calc :≡ S₃_complex_num_factor12 = z^(3:ℕ) + z^(6:ℕ) + z + z^(4:ℕ)
  subprob_S₃_complex_num_factor12_calc_proof ⇐ show subprob_S₃_complex_num_factor12_calc by

    rw [S₃_complex_num_factor12_def]

    have h_expanded_product : (z + z ^ (6 : ℕ)) * (z ^ (2 : ℕ) + z ^ (5 : ℕ)) = z ^ (3 : ℕ) + z ^ (6 : ℕ) + z ^ (8 : ℕ) + z ^ (11 : ℕ) := by
      ring

    rw [h_expanded_product]


    have h_z_pow_8_simplified : z ^ (8 : ℕ) = z := by
      have eight_is_seven_plus_one : (8 : ℕ) = 7 + 1 := by norm_num
      rw [eight_is_seven_plus_one]
      rw [pow_add]
      rw [subprob_z_pow_7_eq_1_proof]
      rw [one_mul]
      rw [pow_one]

    rw [h_z_pow_8_simplified]

    have h_z_pow_11_simplified : z ^ (11 : ℕ) = z ^ (4 : ℕ) := by
      have eleven_is_seven_plus_four : (11 : ℕ) = 7 + 4 := by norm_num
      rw [eleven_is_seven_plus_four]
      rw [pow_add]
      rw [subprob_z_pow_7_eq_1_proof]
      rw [one_mul]

    rw [h_z_pow_11_simplified]

  S₃_complex_num := S₃_complex_num_factor12 * (z^(3:ℕ) + z^(4:ℕ))

  subprob_S₃_complex_num_expanded :≡ (z^(3:ℕ)+z^(6:ℕ)+z+z^(4:ℕ)) * (z^(3:ℕ)+z^(4:ℕ)) = (z^(6:ℕ)+z^(7:ℕ)) + (z^(9:ℕ)+z^(10:ℕ)) + (z^(4:ℕ)+z^(5:ℕ)) + (z^(7:ℕ)+z^(8:ℕ))
  subprob_S₃_complex_num_expanded_proof ⇐ show subprob_S₃_complex_num_expanded by
    ring
  subprob_S₃_complex_num_simplified :≡ (z^(6:ℕ)+z^(7:ℕ)) + (z^(9:ℕ)+z^(10:ℕ)) + (z^(4:ℕ)+z^(5:ℕ)) + (z^(7:ℕ)+z^(8:ℕ)) = (2 : ℂ) + sum_zk_1_to_6
  subprob_S₃_complex_num_simplified_proof ⇐ show subprob_S₃_complex_num_simplified by








    have h_z7 : z ^ (7 : ℕ) = (1 : ℂ) := subprob_z_pow_7_eq_1_proof
    have h_z8 : z ^ (8 : ℕ) = z := by
      rw [show (8 : ℕ) = 7 + 1 by norm_num, pow_add, h_z7, one_mul, pow_one]
    have h_z9 : z ^ (9 : ℕ) = z ^ (2 : ℕ) := by
      rw [show (9 : ℕ) = 7 + 2 by norm_num, pow_add, h_z7, one_mul]
    have h_z10 : z ^ (10 : ℕ) = z ^ (3 : ℕ) := by
      rw [show (10 : ℕ) = 7 + 3 by norm_num, pow_add, h_z7, one_mul]

    rw [h_z7, h_z8, h_z9, h_z10]
    have h_lhs_rearranged : (z ^ (6 : ℕ) + 1) + (z ^ (2 : ℕ) + z ^ (3 : ℕ)) + (z ^ (4 : ℕ) + z ^ (5 : ℕ)) + (1 + z) =
                          (2 : ℂ) + (z + z ^ (2 : ℕ) + z ^ (3 : ℕ) + z ^ (4 : ℕ) + z ^ (5 : ℕ) + z ^ (6 : ℕ)) := by
      ring
    rw [h_lhs_rearranged]
    congr 1
    rw [← pow_one z]
    rw [sum_zk_1_to_6_def]
    have h_Ioo_0_7_eq_Ico_1_7 : Finset.Ioo (0 : ℕ) (7 : ℕ) = Finset.Ico (1 : ℕ) (7 : ℕ) := by
      ext k
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      have h_em := Classical.em (k < 7)
      rcases h_em with h_k_lt_7 | h_k_not_lt_7
      .
        apply and_congr
        . rw [Nat.lt_iff_add_one_le, Nat.zero_add]
        . rfl
      . simp [propext (iff_false_intro h_k_not_lt_7)]
    rw [h_Ioo_0_7_eq_Ico_1_7]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Finset.sum_Ico_succ_top (f := fun k_1 => z ^ k_1) (hab := by norm_num)]
    rw [Nat.Ico_succ_singleton 1]
    rw [Finset.sum_singleton]
    ring


  subprob_S₃_complex_num_val :≡ S₃_complex_num = (1 : ℂ)
  subprob_S₃_complex_num_val_proof ⇐ show subprob_S₃_complex_num_val by


    rw [S₃_complex_num_def]

    rw [subprob_S₃_complex_num_factor12_calc_proof]

    rw [subprob_S₃_complex_num_expanded_proof]

    rw [subprob_S₃_complex_num_simplified_proof]

    rw [subprob_sum_z_k_1_6_eq_neg_1_proof]

    ring


  S₃_complex_repr := S₃_complex_num / (8 : ℂ)
  subprob_S₃_complex_val :≡ S₃_complex_repr = (1 : ℂ) / (8 : ℂ)
  subprob_S₃_complex_val_proof ⇐ show subprob_S₃_complex_val by
    rw [S₃_complex_repr_def]
    rw [subprob_S₃_complex_num_val_proof]
  subprob_S₃_val :≡ S₃ = (1 : ℝ) / (8 : ℝ)
  subprob_S₃_val_proof ⇐ show subprob_S₃_val by

    have h_S3_ofReal_eq_prod_R_complex : ofReal S₃ = R₁_complex * R₂_complex * R₃_complex := by
      rw [S₃_def]
      rw [RingHom.map_mul Complex.ofReal]
      rw [RingHom.map_mul Complex.ofReal]
      rw [subprob_ofReal_r₁_eq_R₁_proof]
      rw [subprob_ofReal_r₂_eq_R₂_proof]
      rw [subprob_ofReal_r₃_eq_R₃_proof]

    have h_prod_R_complex_eq_S3_repr : R₁_complex * R₂_complex * R₃_complex = S₃_complex_repr := by
      rw [R₁_complex_def, R₂_complex_def, R₃_complex_def, S₃_complex_repr_def]
      rw [S₃_complex_num_def, S₃_complex_num_factor12_def]
      field_simp [show (2:ℂ) ≠ 0 by norm_num]
      rw [show (2:ℂ)*(2:ℂ)*(2:ℂ) = (8:ℂ) by norm_num]
      simp

    have h_S3_ofReal_eq_1_div_8_complex : ofReal S₃ = (1 : ℂ) / (8 : ℂ) := by
      rw [h_S3_ofReal_eq_prod_R_complex, h_prod_R_complex_eq_S3_repr, subprob_S₃_complex_val_proof]

    have h_target_complex_form : ofReal ((1 : ℝ) / (8 : ℝ)) = (1 : ℂ) / (8 : ℂ) := by
      rw [Complex.ofReal_eq_coe]
      rw [Complex.ofReal_div]
      simp

    rw [← Complex.ofReal_inj]
    rw [Complex.ofReal_eq_coe] at h_S3_ofReal_eq_1_div_8_complex
    rw [Complex.ofReal_eq_coe] at h_target_complex_form

    rw [h_S3_ofReal_eq_1_div_8_complex, ←h_target_complex_form]


  subprob_abc_val_S1_S2 :≡ S₁ * S₂ = ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ))
  subprob_abc_val_S1_S2_proof ⇐ show subprob_abc_val_S1_S2 by


    rw [subprob_S₁_val_proof]

    rw [subprob_S₂_val_proof]

  subprob_S1_S2_is_one_fourth :≡ ((-1 : ℝ) / (2 : ℝ)) * ((-1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (4 : ℝ)
  subprob_S1_S2_is_one_fourth_proof ⇐ show subprob_S1_S2_is_one_fourth by

    norm_num
  subprob_abc_val_S1S2_S3 :≡ (S₁ * S₂) * S₃ = ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ))
  subprob_abc_val_S1S2_S3_proof ⇐ show subprob_abc_val_S1S2_S3 by


    have h_S1_mul_S2_eq_one_fourth : S₁ * S₂ = (1 : ℝ) / (4 : ℝ) := by
      rw [subprob_abc_val_S1_S2_proof]
      exact subprob_S1_S2_is_one_fourth_proof

    rw [h_S1_mul_S2_eq_one_fourth]

    rw [subprob_S₃_val_proof]

  subprob_product_is_one_thirtysecond :≡ ((1 : ℝ) / (4 : ℝ)) * ((1 : ℝ) / (8 : ℝ)) = (1 : ℝ) / (32 : ℝ)
  subprob_product_is_one_thirtysecond_proof ⇐ show subprob_product_is_one_thirtysecond by



    norm_num

  subprob_final_goal :≡ a * b * c = (1 : ℝ) / (32 : ℝ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    rw [subprob_abc_eq_S1S2S3_proof]
    rw [subprob_abc_val_S1S2_S3_proof]
    exact subprob_product_is_one_thirtysecond_proof
-/
