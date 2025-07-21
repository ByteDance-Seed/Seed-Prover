import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators


theorem amc12b_2020_p21
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt n)) :
  S.card = 6 := by
  letI n_val_from_m_int := fun (m : ℤ) => (70 * m - (1000 : ℤ))
  retro' n_val_from_m_int_def : n_val_from_m_int = fun (m : ℤ) => (70 : ℤ) * m - (1000 : ℤ) := by funext; rfl
  retro' n_val_from_m_int_def' : ∀ (m : ℤ), n_val_from_m_int m = (70 : ℤ) * m - (1000 : ℤ) := by intros; rfl
  letI n_val_from_m_real := fun (m : ℝ) => (70 * m - (1000 : ℝ))
  retro' n_val_from_m_real_def : n_val_from_m_real = fun (m : ℝ) => (70 : ℝ) * m - (1000 : ℝ) := by funext; rfl
  retro' n_val_from_m_real_def' : ∀ (m : ℝ), n_val_from_m_real m = (70 : ℝ) * m - (1000 : ℝ) := by intros; rfl
  letI map_m_to_n := fun (m : ℤ) => (n_val_from_m_int m).toNat
  retro' map_m_to_n_def : map_m_to_n = fun (m : ℤ) => Int.toNat (n_val_from_m_int m) := by funext; rfl
  retro' map_m_to_n_def' : ∀ (m : ℤ), map_m_to_n m = Int.toNat (n_val_from_m_int m) := by intros; rfl
  letI poly1 := fun (x : ℝ) => x ^ 2 - 70 * x + (1000 : ℝ)
  retro' poly1_def : poly1 = fun (x : ℝ) => x ^ (2 : ℕ) - (70 : ℝ) * x + (1000 : ℝ) := by funext; rfl
  retro' poly1_def' : ∀ (x : ℝ), poly1 x = x ^ (2 : ℕ) - (70 : ℝ) * x + (1000 : ℝ) := by intros; rfl
  letI poly2 := fun (x : ℝ) => x ^ 2 - 68 * x + (1001 : ℝ)
  retro' poly2_def : poly2 = fun (x : ℝ) => x ^ (2 : ℕ) - (68 : ℝ) * x + (1001 : ℝ) := by funext; rfl
  retro' poly2_def' : ∀ (x : ℝ), poly2 x = x ^ (2 : ℕ) - (68 : ℝ) * x + (1001 : ℝ) := by intros; rfl
  have subprob_ineq1_form_proof : ∀ (m_real : ℝ), m_real ^ 2 ≤ n_val_from_m_real m_real ↔ poly1 m_real ≤ (0 : ℝ) := by
    mkOpaque
    intro m_real
    rw [n_val_from_m_real_def']
    rw [poly1_def']
    constructor <;> intro h <;> linarith
  have subprob_poly1_sol_proof : ∀ (m_real : ℝ), poly1 m_real ≤ (0 : ℝ) ↔ ((20 : ℝ) ≤ m_real ∧ m_real ≤ (50 : ℝ)) := by
    mkOpaque
    intro m_real
    constructor
    intro h
    have h₁ : m_real ^ 2 - 70 * m_real + 1000 ≤ 0 := by
      rw [poly1_def'] at h
      exact h
    have h₂ : m_real ≥ 20 := by nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    have h₃ : m_real ≤ 50 := by nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    exact ⟨h₂, h₃⟩
    rintro ⟨h₁, h₂⟩
    have h₃ : m_real ^ 2 - 70 * m_real + 1000 ≤ 0 := by nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    rw [poly1_def']
    exact h₃
  have subprob_ineq2_form_proof : ∀ (m_real : ℝ), n_val_from_m_real m_real < (m_real + (1 : ℝ)) ^ 2 ↔ poly2 m_real > (0 : ℝ) := by
    mkOpaque
    intro m_real
    rw [n_val_from_m_real_def', show (m_real + 1) ^ 2 = m_real ^ 2 + 2 * m_real + 1 by ring]
    constructor <;> intro h <;> linarith [poly2_def' m_real]
  have subprob_poly2_sol_int_proof : ∀ (m : ℤ), poly2 ↑m > (0 : ℝ) ↔ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ)) := by
    mkOpaque
    intro m
    let r1 := (68 - Real.sqrt 620) / 2
    let r2 := (68 + Real.sqrt 620) / 2
    have h_r1_lt_r2 : r1 < r2 := by
      simp [r1, r2]
      have h2_pos : (2 : ℝ) > 0 := by norm_num
      apply (div_lt_div_right h2_pos).mp
      have h_sqrt_620_pos : 0 < Real.sqrt (620 : ℝ) := by
        rw [Real.sqrt_pos]
        norm_num
      linarith [h_sqrt_620_pos]
    have h_poly2_eq_prod_roots : poly2 ↑m = (↑m - r1) * (↑m - r2) := by
      rw [poly2_def' ↑m]
      have h_prod_expanded : (↑m - r1) * (↑m - r2) = (↑m) ^ 2 - (r1 + r2) * (↑m) + r1 * r2 := by ring
      rw [h_prod_expanded]
      have h_r1_add_r2 : r1 + r2 = 68 := by field_simp [r1, r2]
      have h_r1_mul_r2 : r1 * r2 = 1001 := by
        field_simp [r1, r2]
        ring
        rw [Real.sq_sqrt (by norm_num : 0 ≤ (620 : ℝ))]
        norm_num
      rw [h_r1_add_r2, h_r1_mul_r2]
    have h_prod_roots_pos_iff_lt_or_gt : ∀ y : ℝ, (y - r1) * (y - r2) > 0 ↔ y < r1 ∨ y > r2 := by
      intro y
      rw [gt_iff_lt]
      rw [mul_pos_iff]
      simp
      have h_and_gt : (y > r1 ∧ y > r2) ↔ y > r2 := by
        constructor
        . exact And.right
        . intro hygt2
          constructor
          . exact gt_trans hygt2 h_r1_lt_r2.gt
          . exact hygt2
      have h_and_lt : (y < r1 ∧ y < r2) ↔ y < r1 := by
        constructor
        . exact And.left
        . intro hylt1
          constructor
          . exact hylt1
          . exact lt_trans hylt1 h_r1_lt_r2
      rw [h_and_gt, h_and_lt]
      rw [or_comm]
    have h_poly2_pos_iff : poly2 ↑m > 0 ↔ (↑m < r1 ∨ ↑m > r2) := by
      rw [h_poly2_eq_prod_roots]
      apply h_prod_roots_pos_iff_lt_or_gt
    have h_sqrt_620 : Real.sqrt (620 : ℝ) = (2 : ℝ) * Real.sqrt (155 : ℝ) := by
      rw [show (620 : ℝ) = (4 * 155 : ℝ) by norm_num]
      rw [Real.sqrt_mul (by norm_num : (4 : ℝ) ≥ 0)]
      have h_sqrt_4_eq_2 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : 0 < (2 : ℝ))]
        norm_num
      rw [h_sqrt_4_eq_2]
    have h_roots_simplify : (68 - Real.sqrt 620) / 2 = 34 - Real.sqrt 155 ∧ (68 + Real.sqrt 620) / 2 = 34 + Real.sqrt 155 := by
      constructor
      . field_simp
        rw [h_sqrt_620]
        ring
      . field_simp
        rw [h_sqrt_620]
        ring
    have h_sqrt_155_bounds : (12 : ℝ) < Real.sqrt (155 : ℝ) ∧ Real.sqrt (155 : ℝ) < (13 : ℝ) := by
      constructor
      . apply (Real.lt_sqrt (by norm_num : 0 ≤ (12 : ℝ))).mpr
        norm_num
      . apply (Real.sqrt_lt (by norm_num : 0 ≤ (155 : ℝ)) (by norm_num : 0 ≤ (13 : ℝ))).mpr
        norm_num
    have h_r1_bounds : (21 : ℝ) < 34 - Real.sqrt (155 : ℝ) ∧ 34 - Real.sqrt (155 : ℝ) < (22 : ℝ) := by
      constructor
      . linarith [h_sqrt_155_bounds.right]
      . linarith [h_sqrt_155_bounds.left]
    have h_r2_bounds : (46 : ℝ) < 34 + Real.sqrt (155 : ℝ) ∧ 34 + Real.sqrt (155 : ℝ) < (47 : ℝ) := by
      constructor
      . linarith [h_sqrt_155_bounds.left]
      . linarith [h_sqrt_155_bounds.right]
    have h_iff_m_real_int : ((↑m : ℝ) < 34 - Real.sqrt 155 ∨ (↑m : ℝ) > 34 + Real.sqrt 155) ↔ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ)) := by
      apply Iff.intro
      . intro hor
        rcases hor with h_lt_r1_simplified | h_gt_r2_simplified
        . left
          have h_m_real_lt_22 : (↑m : ℝ) < 22 := lt_trans h_lt_r1_simplified h_r1_bounds.right
          have h_m_int_lt_22 : m < (22 : ℤ) := Int.cast_lt.mp h_m_real_lt_22
          omega
        . right
          have h_m_real_gt_46 : (↑m : ℝ) > 46 := gt_trans h_gt_r2_simplified h_r2_bounds.left
          have h_m_int_gt_46 : m > (46 : ℤ) := Int.cast_lt.mp (gt_iff_lt.mp h_m_real_gt_46)
          omega
      . intro hor
        rcases hor with h_le_21 | h_ge_47
        . left
          have h_m_real_le_21 : (↑m : ℝ) ≤ 21 := by norm_cast
          exact lt_of_le_of_lt h_m_real_le_21 h_r1_bounds.left
        . right
          have h_m_real_ge_47 : (↑m : ℝ) ≥ 47 := by norm_cast
          have h_47_gt_r2_simplified : (47 : ℝ) > 34 + Real.sqrt (155 : ℝ) := gt_iff_lt.mpr h_r2_bounds.right
          exact gt_of_ge_of_gt h_m_real_ge_47 h_47_gt_r2_simplified
    rw [h_poly2_pos_iff]
    dsimp [r1, r2]
    rw [h_roots_simplify.left, h_roots_simplify.right]
    rw [h_iff_m_real_int]
  letI M_conditions := fun (m : ℤ) => m ≥ (15 : ℤ) ∧ ((20 : ℤ) ≤ m ∧ m ≤ (50 : ℤ)) ∧ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))
  retro' M_conditions_def : M_conditions = fun (m : ℤ) => m ≥ (15 : ℤ) ∧ ((20 : ℤ) ≤ m ∧ m ≤ (50 : ℤ)) ∧ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ)) := by funext; rfl
  retro' M_conditions_def' : ∀ (m : ℤ), M_conditions m = (m ≥ (15 : ℤ) ∧ ((20 : ℤ) ≤ m ∧ m ≤ (50 : ℤ)) ∧ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))) := by intros; rfl
  letI M_finset_part1 := Finset.Icc (20 : ℤ) (21 : ℤ)
  retro' M_finset_part1_def : M_finset_part1 = Finset.Icc (20 : ℤ) (21 : ℤ) := by funext; rfl
  retro' M_finset_part1_inh_1 : Finset.card M_finset_part1 = (2 : ℕ) := by have this := Leansim.Tactic.inh_card M_finset_part1_def; simp at this; exact this
  retro' M_finset_part1_inh_2 : True := by have this := Leansim.Tactic.powerset_finset M_finset_part1_def; simp at this; exact this
  letI M_finset_part2 := Finset.Icc (47 : ℤ) (50 : ℤ)
  retro' M_finset_part2_def : M_finset_part2 = Finset.Icc (47 : ℤ) (50 : ℤ) := by funext; rfl
  retro' M_finset_part2_inh_1 : Finset.card M_finset_part2 = (4 : ℕ) := by have this := Leansim.Tactic.inh_card M_finset_part2_def; simp at this; exact this
  retro' M_finset_part2_inh_2 : True := by have this := Leansim.Tactic.powerset_finset M_finset_part2_def; simp at this; exact this
  have subprob_M_conditions_equiv_M_parts_proof : ∀ (m : ℤ), M_conditions m ↔ (m ∈ M_finset_part1 ∨ m ∈ M_finset_part2) := by
    mkOpaque
    intro m
    simp only [M_conditions_def', M_finset_part1_def, M_finset_part2_def, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      cases' le_total 21 m with h₄ h₄ <;> cases' le_total 47 m with h₅ h₅ <;> simp_all <;> omega
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> constructor <;> omega
  have subprob_M_finset_part1_card_proof : M_finset_part1.card = (2 : ℕ) := by
    mkOpaque
    simp [M_finset_part1_def] <;> decide <;> rfl <;> simp <;> linarith
  have subprob_M_finset_part2_card_proof : M_finset_part2.card = (4 : ℕ) := by
    mkOpaque
    rw [M_finset_part2_def]
    decide
  have subprob_n_val_positive_on_M_parts_proof : (∀ m ∈ M_finset_part1, n_val_from_m_int m > (0 : ℤ)) ∧ (∀ m ∈ M_finset_part2, n_val_from_m_int m > (0 : ℤ)) := by
    mkOpaque
    constructor
    intro m hm
    simp_all only [Finset.mem_Icc, ge_iff_le, gt_iff_lt, le_refl, and_true]
    linarith
    intro m hm
    simp_all only [Finset.mem_Icc, ge_iff_le, gt_iff_lt, le_refl, and_true]
    linarith
  letI S1 := Finset.image map_m_to_n M_finset_part1
  retro' S1_def : S1 = Finset.image map_m_to_n M_finset_part1 := by funext; rfl
  retro' S1_inh_1 : True := by have this := Leansim.Tactic.inh_card S1_def; simp at this; exact this
  retro' S1_inh_2 : True := by have this := Leansim.Tactic.powerset_finset S1_def; simp at this; exact this
  letI S2 := Finset.image map_m_to_n M_finset_part2
  retro' S2_def : S2 = Finset.image map_m_to_n M_finset_part2 := by funext; rfl
  retro' S2_inh_1 : True := by have this := Leansim.Tactic.inh_card S2_def; simp at this; exact this
  retro' S2_inh_2 : True := by have this := Leansim.Tactic.powerset_finset S2_def; simp at this; exact this
  have subprob_n_in_S_iff_image_union_proof : ∀ (n : ℕ), n ∈ S ↔ (n ∈ S1 ∨ n ∈ S2) := by
    mkOpaque
    intro n
    rw [h₀]
    constructor
    intro h_n_in_S
    rcases h_n_in_S with ⟨h_n_pos, h_n_eq_sqrt_floor⟩
    let m_real := ((n : ℝ) + 1000) / 70
    simp at m_real
    have h_m_real_eq_sqrt_floor : m_real = (⌊√(n : ℝ)⌋ : ℝ) := by exact h_n_eq_sqrt_floor
    let m := ⌊√(n : ℝ)⌋
    have h_m_real_eq_m_cast : m_real = (m : ℝ) := by exact h_n_eq_sqrt_floor
    have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
      have h_eq1 : ((n : ℝ) + 1000) / 70 = (m : ℝ) := h_m_real_eq_m_cast
      have h_70_ne_0 : (70 : ℝ) ≠ 0 := by norm_num
      have h_eq_mul_70 : (n : ℝ) + 1000 = (m : ℝ) * 70 := by field_simp [h_70_ne_0] at h_eq1; exact h_eq1
      have h_n_real_eq_expr : (n : ℝ) = (m : ℝ) * (70 : ℝ) - (1000 : ℝ) := by
        rw [eq_sub_iff_add_eq.symm] at h_eq_mul_70
        exact h_eq_mul_70
      have h_n_val_int_real_eq_expr_cast : (n_val_from_m_int m : ℝ) = (70 * m - 1000 : ℝ) := by
        rw [n_val_from_m_int_def' m]
        norm_cast
      have h_int_expr_real_eq_real_expr : (70 * m - 1000 : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := by norm_cast
      have h_n_val_int_real_eq_expr : (n_val_from_m_int m : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := Eq.trans h_n_val_int_real_eq_expr_cast h_int_expr_real_eq_real_expr
      have h_comm_mul_sub : (m : ℝ) * (70 : ℝ) - (1000 : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := by rw [mul_comm (m : ℝ) (70 : ℝ)]
      have h_n_real_eq_expr' : (n : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := Eq.trans h_n_real_eq_expr h_comm_mul_sub
      exact Eq.trans h_n_real_eq_expr' h_n_val_int_real_eq_expr.symm
    have h_n_val_int_pos : n_val_from_m_int m > 0 := by
      have h_n_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr h_n_pos
      rw [h_n_real_eq_n_val_int_real] at h_n_real_pos
      exact Int.cast_pos.mp h_n_real_pos
    have h_n_eq_map_m_to_n : n = map_m_to_n m := by
      rw [map_m_to_n_def' m]
      have h_z_nonneg : (n_val_from_m_int m : ℤ) ≥ 0 := Int.le_of_lt h_n_val_int_pos
      have h_int_to_nat_z_eq_z : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg h_z_nonneg
      have h_n_int_eq_z_int : (n : ℤ) = n_val_from_m_int m := (Int.cast_inj (α := ℝ)).mp h_n_real_eq_n_val_int_real
      have h_n_int_eq_int_to_nat_z_int : (n : ℤ) = (Int.toNat (n_val_from_m_int m) : ℤ) := by exact Eq.trans h_n_int_eq_z_int h_int_to_nat_z_eq_z.symm
      apply (Nat.cast_inj (R := ℤ)).mp
      exact h_n_int_eq_int_to_nat_z_int
    have h_m_ge_15 : m ≥ 15 := by
      rw [n_val_from_m_int_def' m] at h_n_val_int_pos
      have h_70m_gt_1000 : 70 * m > 1000 := by linarith [h_n_val_int_pos]
      by_contra h_contra
      have h_m_lt_15 : m < 15 := Int.lt_of_not_ge h_contra
      have h_m_le_14 : m ≤ 14 := Int.le_of_lt_add_one h_m_lt_15
      have h_70_nonneg : (70 : ℤ) ≥ (0 : ℤ) := by norm_num
      have h_70m_le_980 : (70 : ℤ) * m ≤ (70 : ℤ) * (14 : ℤ) := Int.mul_le_mul_of_nonneg_left h_m_le_14 h_70_nonneg
      norm_num at h_70m_le_980
      linarith [h_70m_gt_1000, h_70m_le_980]
    have h_outer_m_real_ge_0 : (m : ℝ) ≥ 0 := by
      have h_m_real_ge_15_real : (m : ℝ) ≥ 15 := Int.cast_le.mpr h_m_ge_15
      have h_15_real_ge_0_real : (15 : ℝ) ≥ 0 := by norm_num
      exact ge_trans h_m_real_ge_15_real h_15_real_ge_0_real
    have h_outer_m_plus_1_ge_0 : (m : ℝ) + 1 ≥ 0 := by
      have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_outer_m_real_ge_0
      have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
      exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
    have h_outer_n_real_ge_0 : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    have h_n_real_bounds : (m : ℝ) ^ 2 ≤ (n : ℝ) ∧ (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by
      have h_floor_def_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by apply (Int.floor_eq_iff (α := ℝ)).mp rfl
      constructor
      . apply (Real.le_sqrt h_outer_m_real_ge_0 h_outer_n_real_ge_0).mp h_floor_def_bounds.left
      . have h_sqrt_lt_inst : √(n : ℝ) < ((m : ℝ) + 1) ↔ (n : ℝ) < ((m : ℝ) + 1) ^ 2 := Real.sqrt_lt h_outer_n_real_ge_0 h_outer_m_plus_1_ge_0
        exact h_sqrt_lt_inst.mp h_floor_def_bounds.right
    have h_n_val_int_real_eq_n_val_from_m_real : (n_val_from_m_int m : ℝ) = n_val_from_m_real (m : ℝ) := by
      rw [n_val_from_m_int_def' m, n_val_from_m_real_def' (m : ℝ)]
      norm_cast
    have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) := Eq.trans h_n_real_eq_n_val_int_real h_n_val_int_real_eq_n_val_from_m_real
    rw [h_n_real_eq_n_val_from_m_real] at h_n_real_bounds
    have h_n_val_real_lt_m_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 := h_n_real_bounds.right
    have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by exact (subprob_ineq1_form_proof (m : ℝ)).mp h_n_real_bounds.left
    have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
      apply (subprob_ineq2_form_proof (m : ℝ)).mp
      exact h_n_val_real_lt_m_plus_1_sq
    have h_m_real_range1 : 20 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by exact (subprob_poly1_sol_proof (m : ℝ)).mp h_poly1_le_0
    have h_m_int_range1 : 20 ≤ m ∧ m ≤ 50 := by
      constructor
      . exact Int.cast_le.mp h_m_real_range1.left
      . by_contra h_contra
        have h_50_lt_m_int : 50 < m := by
          have h_le_or_lt : m ≤ 50 ∨ 50 < m := Int.le_or_lt m 50
          apply Or.resolve_left h_le_or_lt h_contra
        have h_50_lt_m_real : (50 : ℝ) < (m : ℝ) := Int.cast_lt.mpr h_50_lt_m_int
        have h_50_lt_50 : (50 : ℝ) < (50 : ℝ) := lt_of_lt_of_le h_50_lt_m_real h_m_real_range1.right
        exact lt_irrefl (50 : ℝ) h_50_lt_50
    have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by exact (subprob_poly2_sol_int_proof m).mp h_poly2_gt_0
    have h_M_conditions : M_conditions m := by
      rw [M_conditions_def' m]
      exact ⟨h_m_ge_15, ⟨h_m_int_range1, h_m_range2_or⟩⟩
    have h_m_in_M1_or_M2 : m ∈ M_finset_part1 ∨ m ∈ M_finset_part2 := by exact (subprob_M_conditions_equiv_M_parts_proof m).mp h_M_conditions
    cases h_m_in_M1_or_M2 with
    | inl h_m_in_M1 =>
      left
      rw [S1_def]
      rw [Finset.mem_image]
      exists m
      exact ⟨h_m_in_M1, h_n_eq_map_m_to_n.symm⟩
    | inr h_m_in_M2 =>
      right
      rw [S2_def]
      rw [Finset.mem_image]
      exists m
      exact ⟨h_m_in_M2, h_n_eq_map_m_to_n.symm⟩
    intro h_n_in_S1_or_S2
    rcases h_n_in_S1_or_S2 with h_n_in_S1 | h_n_in_S2
    case inl =>
      simp [S1_def] at h_n_in_S1
      rcases h_n_in_S1 with ⟨m, h_m_in_M1, h_n_eq⟩
      have h_n_val_pos : n_val_from_m_int m > 0 := (subprob_n_val_positive_on_M_parts_proof.left) m h_m_in_M1
      have h_n_pos : 0 < n := by
        rw [h_n_eq.symm]
        simp only [map_m_to_n_def']
        rw [Nat.pos_iff_ne_zero]
        apply (Iff.not Int.toNat_eq_zero).mpr
        exact not_le_of_gt h_n_val_pos
      have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
        rw [h_n_eq.symm]
        rw [map_m_to_n_def']
        norm_cast
        have h_int_eq : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg (Int.le_of_lt h_n_val_pos)
        norm_cast at h_int_eq
      have h_n_val_int_eq_def : n_val_from_m_int m = 70 * m - 1000 := n_val_from_m_int_def' m
      have h_n_val_real_eq_def : (n_val_from_m_int m : ℝ) = 70 * (m : ℝ) - 1000 := by
        rw [h_n_val_int_eq_def]
        norm_cast
      have h_lhs : ((n : ℝ) + 1000) / 70 = (m : ℝ) := by
        rw [h_n_real_eq_n_val_int_real, h_n_val_real_eq_def]
        field_simp
      have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_bounds : 20 ≤ m ∧ m ≤ 21 := h_m_in_M1
        have h_m_real_bounds : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 21 := by norm_cast
        have h_m_real_bounds_poly1 : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by
          constructor
          . exact h_m_real_bounds.left
          . have h_21_le_50 : (21 : ℝ) ≤ 50 := by norm_num
            linarith [h_m_real_bounds.right, h_21_le_50]
        exact (subprob_poly1_sol_proof (m : ℝ)).mpr h_m_real_bounds_poly1
      have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_bounds : 20 ≤ m ∧ m ≤ 21 := h_m_in_M1
        have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by left; exact h_m_bounds.right
        exact (subprob_poly2_sol_int_proof m).mpr h_m_range2_or
      have h_m_real_sq_le_n_val_real : (m : ℝ) ^ 2 ≤ n_val_from_m_real (m : ℝ) := by exact (subprob_ineq1_form_proof (m : ℝ)).mpr h_poly1_le_0
      have h_n_val_real_lt_m_real_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 := (subprob_ineq2_form_proof (m : ℝ)).mpr h_poly2_gt_0
      have h_m_real_nonneg : (m : ℝ) ≥ 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_ge_20_int : 20 ≤ m := h_m_in_M1.left
        have h_m_real_ge_20_real : (m : ℝ) ≥ 20 := Int.cast_le.mpr h_m_ge_20_int
        have h_20_real_ge_0_real : (20 : ℝ) ≥ 0 := by norm_num
        exact ge_trans h_m_real_ge_20_real h_20_real_ge_0_real
      have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) := by
        apply Eq.trans h_n_real_eq_n_val_int_real
        rw [n_val_from_m_real_def' (m : ℝ)]
        norm_cast
      have h_n_real_nonneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
      have h_m_real_sq_le_n_real : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
        rw [h_n_real_eq_n_val_from_m_real]
        exact h_m_real_sq_le_n_val_real
      have h_n_real_lt_m_real_plus_1_sq : (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by exact lt_of_eq_of_lt h_n_real_eq_n_val_from_m_real h_n_val_real_lt_m_real_plus_1_sq
      have h_sqrt_n_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by
        constructor
        . apply (Real.le_sqrt h_m_real_nonneg h_n_real_nonneg).mpr h_m_real_sq_le_n_real
        . have h_m_plus_1_real_nonneg : (m : ℝ) + 1 ≥ 0 := by
            have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_m_real_nonneg
            have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
            exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
          apply (Real.sqrt_lt h_n_real_nonneg h_m_plus_1_real_nonneg).mpr h_n_real_lt_m_real_plus_1_sq
      have h_floor_sqrt_n_eq_m : ⌊√(n : ℝ)⌋ = m := Int.floor_eq_iff.mpr h_sqrt_n_bounds
      have h_rhs : (⌊√(n : ℝ)⌋ : ℝ) = (m : ℝ) := by norm_cast
      constructor
      . exact h_n_pos
      . rw [h_lhs, h_rhs.symm]
    case inr =>
      simp [S2_def] at h_n_in_S2
      rcases h_n_in_S2 with ⟨m, h_m_in_M2, h_n_eq⟩
      have h_n_val_pos : n_val_from_m_int m > 0 := (subprob_n_val_positive_on_M_parts_proof.right) m h_m_in_M2
      have h_n_pos : 0 < n := by
        rw [h_n_eq.symm]
        simp only [map_m_to_n_def']
        rw [Nat.pos_iff_ne_zero]
        apply (Iff.not Int.toNat_eq_zero).mpr
        exact not_le_of_gt h_n_val_pos
      have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
        rw [h_n_eq.symm]
        rw [map_m_to_n_def']
        norm_cast
        have h_int_eq : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg (Int.le_of_lt h_n_val_pos)
        norm_cast at h_int_eq
      have h_n_val_int_eq_def : n_val_from_m_int m = 70 * m - 1000 := n_val_from_m_int_def' m
      have h_n_val_real_eq_def : (n_val_from_m_int m : ℝ) = 70 * (m : ℝ) - 1000 := by
        rw [h_n_val_int_eq_def]
        norm_cast
      have h_lhs : ((n : ℝ) + 1000) / 70 = (m : ℝ) := by
        rw [h_n_real_eq_n_val_int_real, h_n_val_real_eq_def]
        field_simp
      have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_bounds : 47 ≤ m ∧ m ≤ 50 := h_m_in_M2
        have h_m_real_bounds : (47 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by norm_cast
        have h_m_real_bounds_poly1 : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by
          constructor
          . have h_20_le_47 : (20 : ℝ) ≤ 47 := by norm_num
            linarith [h_m_real_bounds.left, h_20_le_47]
          . exact h_m_real_bounds.right
        exact (subprob_poly1_sol_proof (m : ℝ)).mpr h_m_real_bounds_poly1
      have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_bounds : 47 ≤ m ∧ m ≤ 50 := h_m_in_M2
        have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by right; exact h_m_bounds.left
        exact (subprob_poly2_sol_int_proof m).mpr h_m_range2_or
      have h_m_real_sq_le_n_val_real : (m : ℝ) ^ 2 ≤ n_val_from_m_real (m : ℝ) := by exact (subprob_ineq1_form_proof (m : ℝ)).mpr h_poly1_le_0
      have h_n_val_real_lt_m_real_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 := (subprob_ineq2_form_proof (m : ℝ)).mpr h_poly2_gt_0
      have h_m_real_nonneg : (m : ℝ) ≥ 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_ge_47_int : 47 ≤ m := h_m_in_M2.left
        have h_m_real_ge_47_real : (m : ℝ) ≥ 47 := Int.cast_le.mpr h_m_ge_47_int
        have h_47_real_ge_0_real : (47 : ℝ) ≥ 0 := by norm_num
        exact ge_trans h_m_real_ge_47_real h_47_real_ge_0_real
      have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) := by
        apply Eq.trans h_n_real_eq_n_val_int_real
        rw [n_val_from_m_real_def' (m : ℝ)]
        norm_cast
      have h_n_real_nonneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
      have h_m_real_sq_le_n_real : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
        rw [h_n_real_eq_n_val_from_m_real]
        exact h_m_real_sq_le_n_val_real
      have h_n_real_lt_m_real_plus_1_sq : (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by exact lt_of_eq_of_lt h_n_real_eq_n_val_from_m_real h_n_val_real_lt_m_real_plus_1_sq
      have h_sqrt_n_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by
        constructor
        . apply (Real.le_sqrt h_m_real_nonneg h_n_real_nonneg).mpr h_m_real_sq_le_n_real
        . have h_m_plus_1_real_nonneg : (m : ℝ) + 1 ≥ 0 := by
            have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_m_real_nonneg
            have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
            exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
          apply (Real.sqrt_lt h_n_real_nonneg h_m_plus_1_real_nonneg).mpr h_n_real_lt_m_real_plus_1_sq
      have h_floor_sqrt_n_eq_m : ⌊√(n : ℝ)⌋ = m := Int.floor_eq_iff.mpr h_sqrt_n_bounds
      have h_rhs : (⌊√(n : ℝ)⌋ : ℝ) = (m : ℝ) := by norm_cast
      constructor
      . exact h_n_pos
      . rw [h_lhs, h_rhs.symm]
  have subprob_map_m_to_n_inj_on_M1_def_proof : ∀ (x y : ℤ), x ∈ M_finset_part1 → y ∈ M_finset_part1 → map_m_to_n x = map_m_to_n y → x = y := by
    mkOpaque
    intro x y hx hy heq
    rw [map_m_to_n_def', map_m_to_n_def' y] at heq
    have heq_int_cast : (Int.toNat (n_val_from_m_int x) : ℤ) = (Int.toNat (n_val_from_m_int y) : ℤ) := Nat.cast_inj.mpr heq
    have h_pos_part1 := subprob_n_val_positive_on_M_parts_proof.left
    have hx_pos : n_val_from_m_int x > 0 := h_pos_part1 x hx
    have hy_pos : n_val_from_m_int y > 0 := h_pos_part1 y hy
    have hx_nonneg : n_val_from_m_int x ≥ 0 := le_of_lt hx_pos
    have hy_nonneg : n_val_from_m_int y ≥ 0 := le_of_lt hy_pos
    rw [Int.toNat_of_nonneg hx_nonneg] at heq_int_cast
    rw [Int.toNat_of_nonneg hy_nonneg] at heq_int_cast
    have heq_int : (n_val_from_m_int x : ℤ) = (n_val_from_m_int y : ℤ) := heq_int_cast
    rw [n_val_from_m_int_def' x] at heq_int
    rw [n_val_from_m_int_def' y] at heq_int
    have h_add_1000 : (70 : ℤ) * x = (70 : ℤ) * y := by linarith [heq_int]
    have h_70_nonzero : (70 : ℤ) ≠ 0 := by norm_num
    have h_cancel : x = y := (Int.mul_eq_mul_left_iff h_70_nonzero).mp h_add_1000
    exact h_cancel
  have subprob_map_m_to_n_inj_on_M2_def_proof : ∀ (x y : ℤ), x ∈ M_finset_part2 → y ∈ M_finset_part2 → map_m_to_n x = map_m_to_n y → x = y := by
    mkOpaque
    intros x y hx hy heq
    rw [map_m_to_n_def', map_m_to_n_def'] at heq
    rw [n_val_from_m_int_def', n_val_from_m_int_def'] at heq
    have h_pos_x := subprob_n_val_positive_on_M_parts_proof.right x hx
    rw [n_val_from_m_int_def'] at h_pos_x
    have h_nonneg_x : 0 ≤ (70 : ℤ) * x - (1000 : ℤ) := by linarith [h_pos_x]
    have h_pos_y := subprob_n_val_positive_on_M_parts_proof.right y hy
    rw [n_val_from_m_int_def'] at h_pos_y
    have h_nonneg_y : 0 ≤ (70 : ℤ) * y - (1000 : ℤ) := by linarith [h_pos_y]
    have h_zx_eq_cast_toNat : (70 : ℤ) * x - (1000 : ℤ) = ↑(Int.toNat ((70 : ℤ) * x - (1000 : ℤ))) := by
      symm
      apply Int.toNat_of_nonneg
      exact h_nonneg_x
    have h_zy_eq_cast_toNat : (70 : ℤ) * y - (1000 : ℤ) = ↑(Int.toNat ((70 : ℤ) * y - (1000 : ℤ))) := by
      symm
      apply Int.toNat_of_nonneg
      exact h_nonneg_y
    have h_cast_eq : (↑(Int.toNat ((70 : ℤ) * x - (1000 : ℤ))) : ℤ) = (↑(Int.toNat ((70 : ℤ) * y - (1000 : ℤ))) : ℤ) := by rw [heq]
    have heq_int : (70 : ℤ) * x - (1000 : ℤ) = (70 : ℤ) * y - (1000 : ℤ) := by
      rw [h_zx_eq_cast_toNat]
      rw [h_cast_eq]
      rw [← h_zy_eq_cast_toNat]
    have h_eq_add_1000 : (70 : ℤ) * x = (70 : ℤ) * y := by linarith [heq_int]
    rw [Int.mul_comm (70 : ℤ) x, Int.mul_comm (70 : ℤ) y] at h_eq_add_1000
    exact Int.eq_of_mul_eq_mul_right (by norm_num : (70 : ℤ) ≠ 0) h_eq_add_1000
  have subprob_card_S1_eq_card_M1_proof : S1.card = M_finset_part1.card := by
    mkOpaque
    rw [S1_def]
    apply Finset.card_image_of_injOn
    exact fun x hx y hy hxy => subprob_map_m_to_n_inj_on_M1_def_proof x y hx hy hxy
  have subprob_card_S2_eq_card_M2_proof : S2.card = M_finset_part2.card := by
    mkOpaque
    rw [S2_def]
    apply Finset.card_image_of_injOn
    exact fun x hx y hy hxy => subprob_map_m_to_n_inj_on_M2_def_proof x y hx hy hxy
  have subprob_S1_card_val_proof : S1.card = (2 : ℕ) := by
    mkOpaque
    rw [subprob_card_S1_eq_card_M1_proof]
    rw [subprob_M_finset_part1_card_proof]
  have subprob_S2_card_val_proof : S2.card = (4 : ℕ) := by
    mkOpaque
    rw [subprob_card_S2_eq_card_M2_proof]
    rw [subprob_M_finset_part2_card_proof]
  have subprob_map_m1_neq_map_m2_for_disjoint_M_parts_proof : ∀ (m1 : ℤ) (m2 : ℤ), m1 ∈ M_finset_part1 → m2 ∈ M_finset_part2 → map_m_to_n m1 ≠ map_m_to_n m2 := by
    mkOpaque
    intro m1 m2 hm1 hm2
    intro heq
    rw [map_m_to_n_def' m1, map_m_to_n_def' m2] at heq
    have hm1_pos : n_val_from_m_int m1 > 0 := by
      rcases subprob_n_val_positive_on_M_parts_proof with ⟨hpos1, hpos2⟩
      exact hpos1 m1 hm1
    have hm2_pos : n_val_from_m_int m2 > 0 := by
      rcases subprob_n_val_positive_on_M_parts_proof with ⟨hpos1, hpos2⟩
      exact hpos2 m2 hm2
    have hm1_nonneg : n_val_from_m_int m1 ≥ 0 := le_of_lt hm1_pos
    have hm2_nonneg : n_val_from_m_int m2 ≥ 0 := le_of_lt hm2_pos
    have h_m1_eq_int : n_val_from_m_int m1 = ↑(Int.toNat (n_val_from_m_int m1)) := (Int.toNat_of_nonneg hm1_nonneg).symm
    have h_m2_eq_int : n_val_from_m_int m2 = ↑(Int.toNat (n_val_from_m_int m2)) := (Int.toNat_of_nonneg hm2_nonneg).symm
    have h_int_eq : n_val_from_m_int m1 = n_val_from_m_int m2 := by
      rw [h_m1_eq_int]
      rw [heq]
      rw [← h_m2_eq_int]
    rw [n_val_from_m_int_def' m1] at h_int_eq
    rw [n_val_from_m_int_def' m2] at h_int_eq
    have h_add_1000 : (70 : ℤ) * m1 = (70 : ℤ) * m2 := by linarith [h_int_eq]
    have h_70_ne_zero : (70 : ℤ) ≠ 0 := by norm_num
    have H_iff_general : (70 : ℤ) * m1 = (70 : ℤ) * m2 ↔ m1 = m2 ∨ (70 : ℤ) = 0 := mul_eq_mul_left_iff
    have H_or : m1 = m2 ∨ (70 : ℤ) = 0 := H_iff_general.mp h_add_1000
    have hm_eq : m1 = m2 := Or.resolve_right H_or h_70_ne_zero
    have hm1_in_M2 : m1 ∈ M_finset_part2 := hm_eq ▸ hm2
    rw [M_finset_part1_def] at hm1
    rw [M_finset_part2_def] at hm1_in_M2
    have hm1_bounds1 : (20 : ℤ) ≤ m1 ∧ m1 ≤ (21 : ℤ) := by exact Finset.mem_Icc.mp hm1
    have hm1_bounds2 : (47 : ℤ) ≤ m1 ∧ m1 ≤ (50 : ℤ) := by exact Finset.mem_Icc.mp hm1_in_M2
    have contra : (47 : ℤ) ≤ (21 : ℤ) := by linarith [hm1_bounds1.right, hm1_bounds2.left]
    norm_num at contra
  have subprob_S1_S2_disjoint_def_proof : ∀ (x : ℕ), x ∈ S1 → x ∈ S2 → False := by
    mkOpaque
    intro x hxS1 hxS2
    rw [S1_def] at hxS1
    rw [S2_def] at hxS2
    rw [Finset.mem_image] at hxS1
    rw [Finset.mem_image] at hxS2
    rcases hxS1 with ⟨m1, hm1_in_M1, heq1⟩
    rcases hxS2 with ⟨m2, hm2_in_M2, heq2⟩
    have : map_m_to_n m1 = map_m_to_n m2 := by rw [heq1, heq2]
    have h_neq : map_m_to_n m1 ≠ map_m_to_n m2 := subprob_map_m1_neq_map_m2_for_disjoint_M_parts_proof m1 m2 hm1_in_M1 hm2_in_M2
    exact h_neq this
  have subprob_card_S_eq_sum_cards_from_disjoint_union_proof : S.card = S1.card + S2.card := by
    mkOpaque
    have h₁ : S = S1 ∪ S2 := by
      ext n
      simp [subprob_n_in_S_iff_image_union_proof]
    have h₂ : Disjoint S1 S2 := by
      simp [Finset.disjoint_iff_ne]
      intro x hm xm
      apply subprob_S1_S2_disjoint_def_proof x hm xm
    simp [h₁, h₂, Finset.card_union_eq, subprob_S1_card_val_proof, subprob_S2_card_val_proof]
  have subprob_final_goal_proof : S.card = (6 : ℕ) := by
    mkOpaque
    have h₁ : Finset.card S1 = 2 := subprob_S1_card_val_proof
    have h₂ : Finset.card S2 = 4 := subprob_S2_card_val_proof
    have h₃ : Finset.card S = Finset.card S1 + Finset.card S2 := subprob_card_S_eq_sum_cards_from_disjoint_union_proof
    rw [h₁, h₂] at h₃
    norm_num at h₃
    exact h₃
  exact
    show Finset.card S = (6 : ℕ) by
      mkOpaque
      simpa [subprob_S1_card_val_proof, subprob_S2_card_val_proof] using subprob_card_S_eq_sum_cards_from_disjoint_union_proof

#print axioms amc12b_2020_p21

/- Sketch
variable (S : Finset ℕ) (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ (↑n + (1000 : ℝ)) / 70 = Int.floor (Real.sqrt ↑n))
play
  n_val_from_m_int := fun (m : ℤ) => (70 * m - (1000 : ℤ))
  n_val_from_m_real := fun (m : ℝ) => (70 * m - (1000 : ℝ))
  map_m_to_n := fun (m : ℤ) => (n_val_from_m_int m).toNat

  poly1 := fun (x : ℝ) => x^2 - 70 * x + (1000 : ℝ)
  poly2 := fun (x : ℝ) => x^2 - 68 * x + (1001 : ℝ)

  subprob_ineq1_form :≡ ∀ (m_real : ℝ), m_real^2 ≤ n_val_from_m_real m_real ↔ poly1 m_real ≤ (0 : ℝ)
  subprob_ineq1_form_proof ⇐ show subprob_ineq1_form by sorry
  subprob_poly1_sol :≡ ∀ (m_real : ℝ), poly1 m_real ≤ (0 : ℝ) ↔ ((20 : ℝ) ≤ m_real ∧ m_real ≤ (50 : ℝ))
  subprob_poly1_sol_proof ⇐ show subprob_poly1_sol by sorry

  subprob_ineq2_form :≡ ∀ (m_real : ℝ), n_val_from_m_real m_real < (m_real + (1 : ℝ))^2 ↔ poly2 m_real > (0 : ℝ)
  subprob_ineq2_form_proof ⇐ show subprob_ineq2_form by sorry

  subprob_poly2_sol_int :≡ ∀ (m : ℤ), poly2 ↑m > (0 : ℝ) ↔ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))
  subprob_poly2_sol_int_proof ⇐ show subprob_poly2_sol_int by sorry

  M_conditions := fun (m : ℤ) => m ≥ (15 : ℤ) ∧ ((20 : ℤ) ≤ m ∧ m ≤ (50 : ℤ)) ∧ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))

  M_finset_part1 := Finset.Icc (20:ℤ) (21:ℤ)
  M_finset_part2 := Finset.Icc (47:ℤ) (50:ℤ)

  subprob_M_conditions_equiv_M_parts :≡ ∀ (m : ℤ), M_conditions m ↔ (m ∈ M_finset_part1 ∨ m ∈ M_finset_part2)
  subprob_M_conditions_equiv_M_parts_proof ⇐ show subprob_M_conditions_equiv_M_parts by sorry

  subprob_M_finset_part1_card :≡ M_finset_part1.card = (2 : ℕ)
  subprob_M_finset_part1_card_proof ⇐ show subprob_M_finset_part1_card by sorry
  subprob_M_finset_part2_card :≡ M_finset_part2.card = (4 : ℕ)
  subprob_M_finset_part2_card_proof ⇐ show subprob_M_finset_part2_card by sorry

  subprob_n_val_positive_on_M_parts :≡ (∀ m ∈ M_finset_part1, n_val_from_m_int m > (0 : ℤ)) ∧ (∀ m ∈ M_finset_part2, n_val_from_m_int m > (0 : ℤ))
  subprob_n_val_positive_on_M_parts_proof ⇐ show subprob_n_val_positive_on_M_parts by sorry

  S1 := Finset.image map_m_to_n M_finset_part1
  S2 := Finset.image map_m_to_n M_finset_part2

  subprob_n_in_S_iff_image_union :≡ ∀ (n : ℕ), n ∈ S ↔ (n ∈ S1 ∨ n ∈ S2)
  subprob_n_in_S_iff_image_union_proof ⇐ show subprob_n_in_S_iff_image_union by sorry

  subprob_map_m_to_n_inj_on_M1_def :≡ ∀ (x y : ℤ), x ∈ M_finset_part1 → y ∈ M_finset_part1 → map_m_to_n x = map_m_to_n y → x = y
  subprob_map_m_to_n_inj_on_M1_def_proof ⇐ show subprob_map_m_to_n_inj_on_M1_def by sorry
  subprob_map_m_to_n_inj_on_M2_def :≡ ∀ (x y : ℤ), x ∈ M_finset_part2 → y ∈ M_finset_part2 → map_m_to_n x = map_m_to_n y → x = y
  subprob_map_m_to_n_inj_on_M2_def_proof ⇐ show subprob_map_m_to_n_inj_on_M2_def by sorry

  subprob_card_S1_eq_card_M1 :≡ S1.card = M_finset_part1.card
  subprob_card_S1_eq_card_M1_proof ⇐ show subprob_card_S1_eq_card_M1 by sorry
  subprob_card_S2_eq_card_M2 :≡ S2.card = M_finset_part2.card
  subprob_card_S2_eq_card_M2_proof ⇐ show subprob_card_S2_eq_card_M2 by sorry

  subprob_S1_card_val :≡ S1.card = (2 : ℕ)
  subprob_S1_card_val_proof ⇐ show subprob_S1_card_val by sorry
  subprob_S2_card_val :≡ S2.card = (4 : ℕ)
  subprob_S2_card_val_proof ⇐ show subprob_S2_card_val by sorry

  subprob_map_m1_neq_map_m2_for_disjoint_M_parts :≡ ∀ (m1 : ℤ) (m2 : ℤ), m1 ∈ M_finset_part1 → m2 ∈ M_finset_part2 → map_m_to_n m1 ≠ map_m_to_n m2
  subprob_map_m1_neq_map_m2_for_disjoint_M_parts_proof ⇐ show subprob_map_m1_neq_map_m2_for_disjoint_M_parts by sorry

  -- Definition of S1 and S2 being disjoint: S1 ∩ S2 = ∅, or ∀ x, x ∈ S1 → x ∈ S2 → False
  subprob_S1_S2_disjoint_def :≡ ∀ (x : ℕ), x ∈ S1 → x ∈ S2 → False
  subprob_S1_S2_disjoint_def_proof ⇐ show subprob_S1_S2_disjoint_def by sorry

  -- The fact that S is the union of S1 and S2 is already established by subprob_n_in_S_iff_image_union.
  -- We need to use this fact along with disjointness to find the card.
  -- This step relies on the prover having access to Finset.card_union_eq or similar.
  subprob_card_S_eq_sum_cards_from_disjoint_union :≡ S.card = S1.card + S2.card
  subprob_card_S_eq_sum_cards_from_disjoint_union_proof ⇐ show subprob_card_S_eq_sum_cards_from_disjoint_union by sorry

  subprob_final_goal :≡ S.card = (6 : ℕ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/

/- Sketch with proof
:variable (S: Finset ℕ) (h₀: ∀ (n : ℕ), n ∈ S ↔ (0 : ℕ) < n ∧ ((↑(n) : ℝ) + (1000 : ℝ)) / (70 : ℝ) = (↑(⌊√(↑(n) : ℝ)⌋) : ℝ))
play
  n_val_from_m_int := fun (m : ℤ) => (70 * m - (1000 : ℤ))
  n_val_from_m_real := fun (m : ℝ) => (70 * m - (1000 : ℝ))
  map_m_to_n := fun (m : ℤ) => (n_val_from_m_int m).toNat
  poly1 := fun (x : ℝ) => x^2 - 70 * x + (1000 : ℝ)
  poly2 := fun (x : ℝ) => x^2 - 68 * x + (1001 : ℝ)
  subprob_ineq1_form :≡ ∀ (m_real : ℝ), m_real^2 ≤ n_val_from_m_real m_real ↔ poly1 m_real ≤ (0 : ℝ)
  subprob_ineq1_form_proof ⇐ show subprob_ineq1_form by
    intro m_real
    rw [n_val_from_m_real_def']
    rw [poly1_def']
    constructor <;> intro h <;> linarith
  subprob_poly1_sol :≡ ∀ (m_real : ℝ), poly1 m_real ≤ (0 : ℝ) ↔ ((20 : ℝ) ≤ m_real ∧ m_real ≤ (50 : ℝ))
  subprob_poly1_sol_proof ⇐ show subprob_poly1_sol by
    intro m_real
    constructor
    intro h
    have h₁ : m_real ^ 2 - 70 * m_real + 1000 ≤ 0 := by
      rw [poly1_def'] at h
      exact h
    have h₂ : m_real ≥ 20 := by
      nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    have h₃ : m_real ≤ 50 := by
      nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    exact ⟨h₂, h₃⟩
    rintro ⟨h₁, h₂⟩
    have h₃ : m_real ^ 2 - 70 * m_real + 1000 ≤ 0 := by
      nlinarith [sq_nonneg (m_real - 20), sq_nonneg (m_real - 50)]
    rw [poly1_def']
    exact h₃
  subprob_ineq2_form :≡ ∀ (m_real : ℝ), n_val_from_m_real m_real < (m_real + (1 : ℝ))^2 ↔ poly2 m_real > (0 : ℝ)
  subprob_ineq2_form_proof ⇐ show subprob_ineq2_form by
    intro m_real
    rw [n_val_from_m_real_def', show (m_real + 1) ^ 2 = m_real ^ 2 + 2 * m_real + 1 by ring]
    constructor <;> intro h <;> linarith [poly2_def' m_real]
  subprob_poly2_sol_int :≡ ∀ (m : ℤ), poly2 ↑m > (0 : ℝ) ↔ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))
  subprob_poly2_sol_int_proof ⇐ show subprob_poly2_sol_int by
    intro m
    let r1 := (68 - Real.sqrt 620) / 2
    let r2 := (68 + Real.sqrt 620) / 2
    have h_r1_lt_r2 : r1 < r2 := by
      simp [r1, r2]
      have h2_pos : (2 : ℝ) > 0 := by norm_num
      apply (div_lt_div_right h2_pos).mp
      have h_sqrt_620_pos : 0 < Real.sqrt (620 : ℝ) := by
        rw [Real.sqrt_pos]
        norm_num
      linarith [h_sqrt_620_pos]
    have h_poly2_eq_prod_roots : poly2 ↑m = (↑m - r1) * (↑m - r2) := by
      rw [poly2_def' ↑m]
      have h_prod_expanded : (↑m - r1) * (↑m - r2) = (↑m)^2 - (r1 + r2) * (↑m) + r1 * r2 := by ring
      rw [h_prod_expanded]
      have h_r1_add_r2 : r1 + r2 = 68 := by
        field_simp [r1, r2]
      have h_r1_mul_r2 : r1 * r2 = 1001 := by
        field_simp [r1, r2]
        ring
        rw [Real.sq_sqrt (by norm_num : 0 ≤ (620 : ℝ))]
        norm_num
      rw [h_r1_add_r2, h_r1_mul_r2]
    have h_prod_roots_pos_iff_lt_or_gt : ∀ y : ℝ, (y - r1) * (y - r2) > 0 ↔ y < r1 ∨ y > r2 := by
      intro y
      rw [gt_iff_lt]
      rw [mul_pos_iff]
      simp
      have h_and_gt : (y > r1 ∧ y > r2) ↔ y > r2 := by
        constructor
        .
          exact And.right
        .
          intro hygt2
          constructor
          .
            exact gt_trans hygt2 h_r1_lt_r2.gt
          .
            exact hygt2
      have h_and_lt : (y < r1 ∧ y < r2) ↔ y < r1 := by
        constructor
        .
          exact And.left
        .
          intro hylt1
          constructor
          .
            exact hylt1
          .
            exact lt_trans hylt1 h_r1_lt_r2
      rw [h_and_gt, h_and_lt]
      rw [or_comm]
    have h_poly2_pos_iff : poly2 ↑m > 0 ↔ (↑m < r1 ∨ ↑m > r2) := by
      rw [h_poly2_eq_prod_roots]
      apply h_prod_roots_pos_iff_lt_or_gt
    have h_sqrt_620 : Real.sqrt (620 : ℝ) = (2 : ℝ) * Real.sqrt (155 : ℝ) := by
      rw [show (620 : ℝ) = (4 * 155 : ℝ) by norm_num]
      rw [Real.sqrt_mul (by norm_num : (4 : ℝ) ≥ 0)]
      have h_sqrt_4_eq_2 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : 0 < (2 : ℝ))]
        norm_num
      rw [h_sqrt_4_eq_2]
    have h_roots_simplify : (68 - Real.sqrt 620) / 2 = 34 - Real.sqrt 155 ∧ (68 + Real.sqrt 620) / 2 = 34 + Real.sqrt 155 := by
      constructor
      .
        field_simp
        rw [h_sqrt_620]
        ring
      .
        field_simp
        rw [h_sqrt_620]
        ring
    have h_sqrt_155_bounds : (12 : ℝ) < Real.sqrt (155 : ℝ) ∧ Real.sqrt (155 : ℝ) < (13 : ℝ) := by
      constructor
      .
        apply (Real.lt_sqrt (by norm_num : 0 ≤ (12 : ℝ))).mpr
        norm_num
      .
        apply (Real.sqrt_lt (by norm_num : 0 ≤ (155 : ℝ)) (by norm_num : 0 ≤ (13 : ℝ))).mpr
        norm_num
    have h_r1_bounds : (21 : ℝ) < 34 - Real.sqrt (155 : ℝ) ∧ 34 - Real.sqrt (155 : ℝ) < (22 : ℝ) := by
      constructor
      .
        linarith [h_sqrt_155_bounds.right]
      .
        linarith [h_sqrt_155_bounds.left]
    have h_r2_bounds : (46 : ℝ) < 34 + Real.sqrt (155 : ℝ) ∧ 34 + Real.sqrt (155 : ℝ) < (47 : ℝ) := by
      constructor
      .
        linarith [h_sqrt_155_bounds.left]
      .
        linarith [h_sqrt_155_bounds.right]
    have h_iff_m_real_int : ((↑m : ℝ) < 34 - Real.sqrt 155 ∨ (↑m : ℝ) > 34 + Real.sqrt 155) ↔ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ)) := by
      apply Iff.intro
      .
        intro hor
        rcases hor with h_lt_r1_simplified | h_gt_r2_simplified
        .
          left
          have h_m_real_lt_22 : (↑m : ℝ) < 22 := lt_trans h_lt_r1_simplified h_r1_bounds.right
          have h_m_int_lt_22 : m < (22 : ℤ) := Int.cast_lt.mp h_m_real_lt_22
          omega
        .
          right
          have h_m_real_gt_46 : (↑m : ℝ) > 46 := gt_trans h_gt_r2_simplified h_r2_bounds.left
          have h_m_int_gt_46 : m > (46 : ℤ) := Int.cast_lt.mp (gt_iff_lt.mp h_m_real_gt_46)
          omega
      .
        intro hor
        rcases hor with h_le_21 | h_ge_47
        .
          left
          have h_m_real_le_21 : (↑m : ℝ) ≤ 21 := by norm_cast
          exact lt_of_le_of_lt h_m_real_le_21 h_r1_bounds.left
        .
          right
          have h_m_real_ge_47 : (↑m : ℝ) ≥ 47 := by norm_cast
          have h_47_gt_r2_simplified : (47 : ℝ) > 34 + Real.sqrt (155 : ℝ) := gt_iff_lt.mpr h_r2_bounds.right
          exact gt_of_ge_of_gt h_m_real_ge_47 h_47_gt_r2_simplified
    rw [h_poly2_pos_iff]
    dsimp [r1, r2]
    rw [h_roots_simplify.left, h_roots_simplify.right]
    rw [h_iff_m_real_int]
  M_conditions := fun (m : ℤ) => m ≥ (15 : ℤ) ∧ ((20 : ℤ) ≤ m ∧ m ≤ (50 : ℤ)) ∧ (m ≤ (21 : ℤ) ∨ m ≥ (47 : ℤ))
  M_finset_part1 := Finset.Icc (20:ℤ) (21:ℤ)
  M_finset_part2 := Finset.Icc (47:ℤ) (50:ℤ)
  subprob_M_conditions_equiv_M_parts :≡ ∀ (m : ℤ), M_conditions m ↔ (m ∈ M_finset_part1 ∨ m ∈ M_finset_part2)
  subprob_M_conditions_equiv_M_parts_proof ⇐ show subprob_M_conditions_equiv_M_parts by
    intro m
    simp only [M_conditions_def', M_finset_part1_def, M_finset_part2_def, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      cases' le_total 21 m with h₄ h₄ <;> cases' le_total 47 m with h₅ h₅ <;> simp_all
      <;> omega
    · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> constructor <;> omega
  subprob_M_finset_part1_card :≡ M_finset_part1.card = (2 : ℕ)
  subprob_M_finset_part1_card_proof ⇐ show subprob_M_finset_part1_card by
    simp [M_finset_part1_def]
    <;> decide
    <;> rfl
    <;> simp
    <;> linarith
  subprob_M_finset_part2_card :≡ M_finset_part2.card = (4 : ℕ)
  subprob_M_finset_part2_card_proof ⇐ show subprob_M_finset_part2_card by
    rw [M_finset_part2_def]
    decide
  subprob_n_val_positive_on_M_parts :≡ (∀ m ∈ M_finset_part1, n_val_from_m_int m > (0 : ℤ)) ∧ (∀ m ∈ M_finset_part2, n_val_from_m_int m > (0 : ℤ))
  subprob_n_val_positive_on_M_parts_proof ⇐ show subprob_n_val_positive_on_M_parts by
    constructor
    intro m hm
    simp_all only [Finset.mem_Icc, ge_iff_le, gt_iff_lt, le_refl, and_true]
    linarith
    intro m hm
    simp_all only [Finset.mem_Icc, ge_iff_le, gt_iff_lt, le_refl, and_true]
    linarith
  S1 := Finset.image map_m_to_n M_finset_part1
  S2 := Finset.image map_m_to_n M_finset_part2
  subprob_n_in_S_iff_image_union :≡ ∀ (n : ℕ), n ∈ S ↔ (n ∈ S1 ∨ n ∈ S2)
  subprob_n_in_S_iff_image_union_proof ⇐ show subprob_n_in_S_iff_image_union by
    intro n
    rw [h₀]
    constructor
    intro h_n_in_S
    rcases h_n_in_S with ⟨h_n_pos, h_n_eq_sqrt_floor⟩
    let m_real := ((n : ℝ) + 1000) / 70
    simp at m_real
    have h_m_real_eq_sqrt_floor : m_real = (⌊√(n : ℝ)⌋ : ℝ) := by
      exact h_n_eq_sqrt_floor
    let m := ⌊√(n : ℝ)⌋
    have h_m_real_eq_m_cast : m_real = (m : ℝ) := by
      exact h_n_eq_sqrt_floor
    have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
      have h_eq1 : ((n : ℝ) + 1000) / 70 = (m : ℝ) := h_m_real_eq_m_cast
      have h_70_ne_0 : (70 : ℝ) ≠ 0 := by norm_num
      have h_eq_mul_70 : (n : ℝ) + 1000 = (m : ℝ) * 70 := by field_simp [h_70_ne_0] at h_eq1; exact h_eq1
      have h_n_real_eq_expr : (n : ℝ) = (m : ℝ) * (70 : ℝ) - (1000 : ℝ) := by
        rw [eq_sub_iff_add_eq.symm] at h_eq_mul_70
        exact h_eq_mul_70
      have h_n_val_int_real_eq_expr_cast : (n_val_from_m_int m : ℝ) = (70 * m - 1000 : ℝ) := by
        rw [n_val_from_m_int_def' m]
        norm_cast
      have h_int_expr_real_eq_real_expr : (70 * m - 1000 : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := by
        norm_cast
      have h_n_val_int_real_eq_expr : (n_val_from_m_int m : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := Eq.trans h_n_val_int_real_eq_expr_cast h_int_expr_real_eq_real_expr
      have h_comm_mul_sub : (m : ℝ) * (70 : ℝ) - (1000 : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := by
        rw [mul_comm (m : ℝ) (70 : ℝ)]
      have h_n_real_eq_expr' : (n : ℝ) = (70 : ℝ) * (m : ℝ) - (1000 : ℝ) := Eq.trans h_n_real_eq_expr h_comm_mul_sub
      exact Eq.trans h_n_real_eq_expr' h_n_val_int_real_eq_expr.symm
    have h_n_val_int_pos : n_val_from_m_int m > 0 := by
      have h_n_real_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr h_n_pos
      rw [h_n_real_eq_n_val_int_real] at h_n_real_pos
      exact Int.cast_pos.mp h_n_real_pos
    have h_n_eq_map_m_to_n : n = map_m_to_n m := by
      rw [map_m_to_n_def' m]
      have h_z_nonneg : (n_val_from_m_int m : ℤ) ≥ 0 := Int.le_of_lt h_n_val_int_pos
      have h_int_to_nat_z_eq_z : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg h_z_nonneg
      have h_n_int_eq_z_int : (n : ℤ) = n_val_from_m_int m := (Int.cast_inj (α := ℝ)).mp h_n_real_eq_n_val_int_real
      have h_n_int_eq_int_to_nat_z_int : (n : ℤ) = (Int.toNat (n_val_from_m_int m) : ℤ) := by
        exact Eq.trans h_n_int_eq_z_int h_int_to_nat_z_eq_z.symm
      apply (Nat.cast_inj (R := ℤ)).mp
      exact h_n_int_eq_int_to_nat_z_int
    have h_m_ge_15 : m ≥ 15 := by
      rw [n_val_from_m_int_def' m] at h_n_val_int_pos
      have h_70m_gt_1000 : 70 * m > 1000 := by linarith [h_n_val_int_pos]
      by_contra h_contra
      have h_m_lt_15 : m < 15 := Int.lt_of_not_ge h_contra
      have h_m_le_14 : m ≤ 14 := Int.le_of_lt_add_one h_m_lt_15
      have h_70_nonneg : (70 : ℤ) ≥ (0 : ℤ) := by norm_num
      have h_70m_le_980 : (70 : ℤ) * m ≤ (70 : ℤ) * (14 : ℤ) := Int.mul_le_mul_of_nonneg_left h_m_le_14 h_70_nonneg
      norm_num at h_70m_le_980
      linarith [h_70m_gt_1000, h_70m_le_980]
    have h_outer_m_real_ge_0 : (m : ℝ) ≥ 0 := by
      have h_m_real_ge_15_real : (m : ℝ) ≥ 15 := Int.cast_le.mpr h_m_ge_15
      have h_15_real_ge_0_real : (15 : ℝ) ≥ 0 := by norm_num
      exact ge_trans h_m_real_ge_15_real h_15_real_ge_0_real
    have h_outer_m_plus_1_ge_0 : (m : ℝ) + 1 ≥ 0 := by
      have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_outer_m_real_ge_0
      have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
      exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
    have h_outer_n_real_ge_0 : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    have h_n_real_bounds : (m : ℝ) ^ 2 ≤ (n : ℝ) ∧ (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by
      have h_floor_def_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by
        apply (Int.floor_eq_iff (α := ℝ)).mp rfl
      constructor
      .
        apply (Real.le_sqrt h_outer_m_real_ge_0 h_outer_n_real_ge_0).mp h_floor_def_bounds.left
      .
        have h_sqrt_lt_inst : √(n : ℝ) < ((m : ℝ) + 1) ↔ (n : ℝ) < ((m : ℝ) + 1) ^ 2 := Real.sqrt_lt h_outer_n_real_ge_0 h_outer_m_plus_1_ge_0
        exact h_sqrt_lt_inst.mp h_floor_def_bounds.right
    have h_n_val_int_real_eq_n_val_from_m_real : (n_val_from_m_int m : ℝ) = n_val_from_m_real (m : ℝ) := by
      rw [n_val_from_m_int_def' m, n_val_from_m_real_def' (m : ℝ)]
      norm_cast
    have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) :=
      Eq.trans h_n_real_eq_n_val_int_real h_n_val_int_real_eq_n_val_from_m_real
    rw [h_n_real_eq_n_val_from_m_real] at h_n_real_bounds
    have h_n_val_real_lt_m_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 := h_n_real_bounds.right
    have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by
      exact (subprob_ineq1_form_proof (m : ℝ)).mp h_n_real_bounds.left
    have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
      apply (subprob_ineq2_form_proof (m : ℝ)).mp
      exact h_n_val_real_lt_m_plus_1_sq
    have h_m_real_range1 : 20 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by
      exact (subprob_poly1_sol_proof (m : ℝ)).mp h_poly1_le_0
    have h_m_int_range1 : 20 ≤ m ∧ m ≤ 50 := by
      constructor
      .
        exact Int.cast_le.mp h_m_real_range1.left
      .
        by_contra h_contra
        have h_50_lt_m_int : 50 < m := by
          have h_le_or_lt : m ≤ 50 ∨ 50 < m := Int.le_or_lt m 50
          apply Or.resolve_left h_le_or_lt h_contra
        have h_50_lt_m_real : (50 : ℝ) < (m : ℝ) := Int.cast_lt.mpr h_50_lt_m_int
        have h_50_lt_50 : (50 : ℝ) < (50 : ℝ) := lt_of_lt_of_le h_50_lt_m_real h_m_real_range1.right
        exact lt_irrefl (50 : ℝ) h_50_lt_50
    have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by
      exact (subprob_poly2_sol_int_proof m).mp h_poly2_gt_0
    have h_M_conditions : M_conditions m := by
      rw [M_conditions_def' m]
      exact ⟨h_m_ge_15, ⟨h_m_int_range1, h_m_range2_or⟩⟩
    have h_m_in_M1_or_M2 : m ∈ M_finset_part1 ∨ m ∈ M_finset_part2 := by
      exact (subprob_M_conditions_equiv_M_parts_proof m).mp h_M_conditions
    cases h_m_in_M1_or_M2 with
    | inl h_m_in_M1 =>
      left
      rw [S1_def]
      rw [Finset.mem_image]
      exists m
      exact ⟨h_m_in_M1, h_n_eq_map_m_to_n.symm⟩
    | inr h_m_in_M2 =>
      right
      rw [S2_def]
      rw [Finset.mem_image]
      exists m
      exact ⟨h_m_in_M2, h_n_eq_map_m_to_n.symm⟩
    intro h_n_in_S1_or_S2
    rcases h_n_in_S1_or_S2 with h_n_in_S1 | h_n_in_S2
    case inl =>
      simp [S1_def] at h_n_in_S1
      rcases h_n_in_S1 with ⟨m, h_m_in_M1, h_n_eq⟩
      have h_n_val_pos : n_val_from_m_int m > 0 := (subprob_n_val_positive_on_M_parts_proof.left) m h_m_in_M1
      have h_n_pos : 0 < n := by
        rw [h_n_eq.symm]
        simp only [map_m_to_n_def']
        rw [Nat.pos_iff_ne_zero]
        apply (Iff.not Int.toNat_eq_zero).mpr
        exact not_le_of_gt h_n_val_pos
      have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
        rw [h_n_eq.symm]
        rw [map_m_to_n_def']
        norm_cast
        have h_int_eq : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg (Int.le_of_lt h_n_val_pos)
        norm_cast at h_int_eq
      have h_n_val_int_eq_def : n_val_from_m_int m = 70 * m - 1000 := n_val_from_m_int_def' m
      have h_n_val_real_eq_def : (n_val_from_m_int m : ℝ) = 70 * (m : ℝ) - 1000 := by
        rw [h_n_val_int_eq_def]
        norm_cast
      have h_lhs : ((n : ℝ) + 1000) / 70 = (m : ℝ) := by
        rw [h_n_real_eq_n_val_int_real, h_n_val_real_eq_def]
        field_simp
      have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_bounds : 20 ≤ m ∧ m ≤ 21 := h_m_in_M1
        have h_m_real_bounds : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 21 := by norm_cast
        have h_m_real_bounds_poly1 : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by
          constructor
          .
            exact h_m_real_bounds.left
          .
            have h_21_le_50 : (21 : ℝ) ≤ 50 := by norm_num
            linarith [h_m_real_bounds.right, h_21_le_50]
        exact (subprob_poly1_sol_proof (m : ℝ)).mpr h_m_real_bounds_poly1
      have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_bounds : 20 ≤ m ∧ m ≤ 21 := h_m_in_M1
        have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by left; exact h_m_bounds.right
        exact (subprob_poly2_sol_int_proof m).mpr h_m_range2_or
      have h_m_real_sq_le_n_val_real : (m : ℝ) ^ 2 ≤ n_val_from_m_real (m : ℝ) := by
        exact (subprob_ineq1_form_proof (m : ℝ)).mpr h_poly1_le_0
      have h_n_val_real_lt_m_real_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 :=
        (subprob_ineq2_form_proof (m : ℝ)).mpr h_poly2_gt_0
      have h_m_real_nonneg : (m : ℝ) ≥ 0 := by
        simp [M_finset_part1_def] at h_m_in_M1
        have h_m_ge_20_int : 20 ≤ m := h_m_in_M1.left
        have h_m_real_ge_20_real : (m : ℝ) ≥ 20 := Int.cast_le.mpr h_m_ge_20_int
        have h_20_real_ge_0_real : (20 : ℝ) ≥ 0 := by norm_num
        exact ge_trans h_m_real_ge_20_real h_20_real_ge_0_real
      have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) := by
        apply Eq.trans h_n_real_eq_n_val_int_real
        rw [n_val_from_m_real_def' (m : ℝ)]
        norm_cast
      have h_n_real_nonneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
      have h_m_real_sq_le_n_real : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
        rw [h_n_real_eq_n_val_from_m_real]
        exact h_m_real_sq_le_n_val_real
      have h_n_real_lt_m_real_plus_1_sq : (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by
        exact lt_of_eq_of_lt h_n_real_eq_n_val_from_m_real h_n_val_real_lt_m_real_plus_1_sq
      have h_sqrt_n_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by
        constructor
        .
          apply (Real.le_sqrt h_m_real_nonneg h_n_real_nonneg).mpr h_m_real_sq_le_n_real
        .
          have h_m_plus_1_real_nonneg : (m : ℝ) + 1 ≥ 0 := by
            have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_m_real_nonneg
            have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
            exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
          apply (Real.sqrt_lt h_n_real_nonneg h_m_plus_1_real_nonneg).mpr h_n_real_lt_m_real_plus_1_sq
      have h_floor_sqrt_n_eq_m : ⌊√(n : ℝ)⌋ = m := Int.floor_eq_iff.mpr h_sqrt_n_bounds
      have h_rhs : (⌊√(n : ℝ)⌋ : ℝ) = (m : ℝ) := by norm_cast
      constructor
      . exact h_n_pos
      . rw [h_lhs, h_rhs.symm]
    case inr =>
      simp [S2_def] at h_n_in_S2
      rcases h_n_in_S2 with ⟨m, h_m_in_M2, h_n_eq⟩
      have h_n_val_pos : n_val_from_m_int m > 0 := (subprob_n_val_positive_on_M_parts_proof.right) m h_m_in_M2
      have h_n_pos : 0 < n := by
        rw [h_n_eq.symm]
        simp only [map_m_to_n_def']
        rw [Nat.pos_iff_ne_zero]
        apply (Iff.not Int.toNat_eq_zero).mpr
        exact not_le_of_gt h_n_val_pos
      have h_n_real_eq_n_val_int_real : (n : ℝ) = (n_val_from_m_int m : ℝ) := by
        rw [h_n_eq.symm]
        rw [map_m_to_n_def']
        norm_cast
        have h_int_eq : (Int.toNat (n_val_from_m_int m) : ℤ) = n_val_from_m_int m := Int.toNat_of_nonneg (Int.le_of_lt h_n_val_pos)
        norm_cast at h_int_eq
      have h_n_val_int_eq_def : n_val_from_m_int m = 70 * m - 1000 := n_val_from_m_int_def' m
      have h_n_val_real_eq_def : (n_val_from_m_int m : ℝ) = 70 * (m : ℝ) - 1000 := by
        rw [h_n_val_int_eq_def]
        norm_cast
      have h_lhs : ((n : ℝ) + 1000) / 70 = (m : ℝ) := by
        rw [h_n_real_eq_n_val_int_real, h_n_val_real_eq_def]
        field_simp
      have h_poly1_le_0 : poly1 (m : ℝ) ≤ 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_bounds : 47 ≤ m ∧ m ≤ 50 := h_m_in_M2
        have h_m_real_bounds : (47 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by norm_cast
        have h_m_real_bounds_poly1 : (20 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 50 := by
          constructor
          .
            have h_20_le_47 : (20 : ℝ) ≤ 47 := by norm_num
            linarith [h_m_real_bounds.left, h_20_le_47]
          .
            exact h_m_real_bounds.right
        exact (subprob_poly1_sol_proof (m : ℝ)).mpr h_m_real_bounds_poly1
      have h_poly2_gt_0 : poly2 (m : ℝ) > 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_bounds : 47 ≤ m ∧ m ≤ 50 := h_m_in_M2
        have h_m_range2_or : m ≤ 21 ∨ m ≥ 47 := by right; exact h_m_bounds.left
        exact (subprob_poly2_sol_int_proof m).mpr h_m_range2_or
      have h_m_real_sq_le_n_val_real : (m : ℝ) ^ 2 ≤ n_val_from_m_real (m : ℝ) := by
        exact (subprob_ineq1_form_proof (m : ℝ)).mpr h_poly1_le_0
      have h_n_val_real_lt_m_real_plus_1_sq : n_val_from_m_real (m : ℝ) < ((m : ℝ) + 1) ^ 2 :=
        (subprob_ineq2_form_proof (m : ℝ)).mpr h_poly2_gt_0
      have h_m_real_nonneg : (m : ℝ) ≥ 0 := by
        simp [M_finset_part2_def] at h_m_in_M2
        have h_m_ge_47_int : 47 ≤ m := h_m_in_M2.left
        have h_m_real_ge_47_real : (m : ℝ) ≥ 47 := Int.cast_le.mpr h_m_ge_47_int
        have h_47_real_ge_0_real : (47 : ℝ) ≥ 0 := by norm_num
        exact ge_trans h_m_real_ge_47_real h_47_real_ge_0_real
      have h_n_real_eq_n_val_from_m_real : (n : ℝ) = n_val_from_m_real (m : ℝ) := by
        apply Eq.trans h_n_real_eq_n_val_int_real
        rw [n_val_from_m_real_def' (m : ℝ)]
        norm_cast
      have h_n_real_nonneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
      have h_m_real_sq_le_n_real : (m : ℝ) ^ 2 ≤ (n : ℝ) := by
        rw [h_n_real_eq_n_val_from_m_real]
        exact h_m_real_sq_le_n_val_real
      have h_n_real_lt_m_real_plus_1_sq : (n : ℝ) < ((m : ℝ) + 1) ^ 2 := by
        exact lt_of_eq_of_lt h_n_real_eq_n_val_from_m_real h_n_val_real_lt_m_real_plus_1_sq
      have h_sqrt_n_bounds : (m : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) < (m : ℝ) + 1 := by
        constructor
        .
          apply (Real.le_sqrt h_m_real_nonneg h_n_real_nonneg).mpr h_m_real_sq_le_n_real
        .
          have h_m_plus_1_real_nonneg : (m : ℝ) + 1 ≥ 0 := by
            have h_m_real_ge_0_real : (m : ℝ) ≥ 0 := h_m_real_nonneg
            have h_1_real_ge_0_real : (1 : ℝ) ≥ 0 := by norm_num
            exact add_nonneg h_m_real_ge_0_real h_1_real_ge_0_real
          apply (Real.sqrt_lt h_n_real_nonneg h_m_plus_1_real_nonneg).mpr h_n_real_lt_m_real_plus_1_sq
      have h_floor_sqrt_n_eq_m : ⌊√(n : ℝ)⌋ = m := Int.floor_eq_iff.mpr h_sqrt_n_bounds
      have h_rhs : (⌊√(n : ℝ)⌋ : ℝ) = (m : ℝ) := by norm_cast
      constructor
      . exact h_n_pos
      . rw [h_lhs, h_rhs.symm]
  subprob_map_m_to_n_inj_on_M1_def :≡ ∀ (x y : ℤ), x ∈ M_finset_part1 → y ∈ M_finset_part1 → map_m_to_n x = map_m_to_n y → x = y
  subprob_map_m_to_n_inj_on_M1_def_proof ⇐ show subprob_map_m_to_n_inj_on_M1_def by
    intro x y hx hy heq
    rw [map_m_to_n_def', map_m_to_n_def' y] at heq
    have heq_int_cast : (Int.toNat (n_val_from_m_int x) : ℤ) = (Int.toNat (n_val_from_m_int y) : ℤ) := Nat.cast_inj.mpr heq
    have h_pos_part1 := subprob_n_val_positive_on_M_parts_proof.left
    have hx_pos : n_val_from_m_int x > 0 := h_pos_part1 x hx
    have hy_pos : n_val_from_m_int y > 0 := h_pos_part1 y hy
    have hx_nonneg : n_val_from_m_int x ≥ 0 := le_of_lt hx_pos
    have hy_nonneg : n_val_from_m_int y ≥ 0 := le_of_lt hy_pos
    rw [Int.toNat_of_nonneg hx_nonneg] at heq_int_cast
    rw [Int.toNat_of_nonneg hy_nonneg] at heq_int_cast
    have heq_int : (n_val_from_m_int x : ℤ) = (n_val_from_m_int y : ℤ) := heq_int_cast
    rw [n_val_from_m_int_def' x] at heq_int
    rw [n_val_from_m_int_def' y] at heq_int
    have h_add_1000 : (70 : ℤ) * x = (70 : ℤ) * y := by linarith [heq_int]
    have h_70_nonzero : (70 : ℤ) ≠ 0 := by norm_num
    have h_cancel : x = y := (Int.mul_eq_mul_left_iff h_70_nonzero).mp h_add_1000
    exact h_cancel
  subprob_map_m_to_n_inj_on_M2_def :≡ ∀ (x y : ℤ), x ∈ M_finset_part2 → y ∈ M_finset_part2 → map_m_to_n x = map_m_to_n y → x = y
  subprob_map_m_to_n_inj_on_M2_def_proof ⇐ show subprob_map_m_to_n_inj_on_M2_def by
    intros x y hx hy heq
    rw [map_m_to_n_def', map_m_to_n_def'] at heq
    rw [n_val_from_m_int_def', n_val_from_m_int_def'] at heq
    have h_pos_x := subprob_n_val_positive_on_M_parts_proof.right x hx
    rw [n_val_from_m_int_def'] at h_pos_x
    have h_nonneg_x : 0 ≤ (70 : ℤ) * x - (1000 : ℤ) := by linarith [h_pos_x]
    have h_pos_y := subprob_n_val_positive_on_M_parts_proof.right y hy
    rw [n_val_from_m_int_def'] at h_pos_y
    have h_nonneg_y : 0 ≤ (70 : ℤ) * y - (1000 : ℤ) := by linarith [h_pos_y]
    have h_zx_eq_cast_toNat : (70 : ℤ) * x - (1000 : ℤ) = ↑(Int.toNat ((70 : ℤ) * x - (1000 : ℤ))) := by
      symm
      apply Int.toNat_of_nonneg
      exact h_nonneg_x
    have h_zy_eq_cast_toNat : (70 : ℤ) * y - (1000 : ℤ) = ↑(Int.toNat ((70 : ℤ) * y - (1000 : ℤ))) := by
      symm
      apply Int.toNat_of_nonneg
      exact h_nonneg_y
    have h_cast_eq : (↑(Int.toNat ((70 : ℤ) * x - (1000 : ℤ))) : ℤ) = (↑(Int.toNat ((70 : ℤ) * y - (1000 : ℤ))) : ℤ) := by
      rw [heq]
    have heq_int : (70 : ℤ) * x - (1000 : ℤ) = (70 : ℤ) * y - (1000 : ℤ) := by
      rw [h_zx_eq_cast_toNat]
      rw [h_cast_eq]
      rw [← h_zy_eq_cast_toNat]
    have h_eq_add_1000 : (70 : ℤ) * x = (70 : ℤ) * y := by linarith [heq_int]
    rw [Int.mul_comm (70 : ℤ) x, Int.mul_comm (70 : ℤ) y] at h_eq_add_1000
    exact Int.eq_of_mul_eq_mul_right (by norm_num : (70 : ℤ) ≠ 0) h_eq_add_1000
  subprob_card_S1_eq_card_M1 :≡ S1.card = M_finset_part1.card
  subprob_card_S1_eq_card_M1_proof ⇐ show subprob_card_S1_eq_card_M1 by
    rw [S1_def]
    apply Finset.card_image_of_injOn
    exact fun x hx y hy hxy => subprob_map_m_to_n_inj_on_M1_def_proof x y hx hy hxy
  subprob_card_S2_eq_card_M2 :≡ S2.card = M_finset_part2.card
  subprob_card_S2_eq_card_M2_proof ⇐ show subprob_card_S2_eq_card_M2 by
    rw [S2_def]
    apply Finset.card_image_of_injOn
    exact fun x hx y hy hxy => subprob_map_m_to_n_inj_on_M2_def_proof x y hx hy hxy
  subprob_S1_card_val :≡ S1.card = (2 : ℕ)
  subprob_S1_card_val_proof ⇐ show subprob_S1_card_val by
    rw [subprob_card_S1_eq_card_M1_proof]
    rw [subprob_M_finset_part1_card_proof]
  subprob_S2_card_val :≡ S2.card = (4 : ℕ)
  subprob_S2_card_val_proof ⇐ show subprob_S2_card_val by
    rw [subprob_card_S2_eq_card_M2_proof]
    rw [subprob_M_finset_part2_card_proof]
  subprob_map_m1_neq_map_m2_for_disjoint_M_parts :≡ ∀ (m1 : ℤ) (m2 : ℤ), m1 ∈ M_finset_part1 → m2 ∈ M_finset_part2 → map_m_to_n m1 ≠ map_m_to_n m2
  subprob_map_m1_neq_map_m2_for_disjoint_M_parts_proof ⇐ show subprob_map_m1_neq_map_m2_for_disjoint_M_parts by
    intro m1 m2 hm1 hm2
    intro heq
    rw [map_m_to_n_def' m1, map_m_to_n_def' m2] at heq
    have hm1_pos : n_val_from_m_int m1 > 0 := by
      rcases subprob_n_val_positive_on_M_parts_proof with ⟨hpos1, hpos2⟩
      exact hpos1 m1 hm1
    have hm2_pos : n_val_from_m_int m2 > 0 := by
      rcases subprob_n_val_positive_on_M_parts_proof with ⟨hpos1, hpos2⟩
      exact hpos2 m2 hm2
    have hm1_nonneg : n_val_from_m_int m1 ≥ 0 := le_of_lt hm1_pos
    have hm2_nonneg : n_val_from_m_int m2 ≥ 0 := le_of_lt hm2_pos
    have h_m1_eq_int : n_val_from_m_int m1 = ↑(Int.toNat (n_val_from_m_int m1)) := (Int.toNat_of_nonneg hm1_nonneg).symm
    have h_m2_eq_int : n_val_from_m_int m2 = ↑(Int.toNat (n_val_from_m_int m2)) := (Int.toNat_of_nonneg hm2_nonneg).symm
    have h_int_eq : n_val_from_m_int m1 = n_val_from_m_int m2 := by
      rw [h_m1_eq_int]
      rw [heq]
      rw [← h_m2_eq_int]
    rw [n_val_from_m_int_def' m1] at h_int_eq
    rw [n_val_from_m_int_def' m2] at h_int_eq
    have h_add_1000 : (70 : ℤ) * m1 = (70 : ℤ) * m2 := by linarith [h_int_eq]
    have h_70_ne_zero : (70 : ℤ) ≠ 0 := by norm_num
    have H_iff_general : (70 : ℤ) * m1 = (70 : ℤ) * m2 ↔ m1 = m2 ∨ (70 : ℤ) = 0 := mul_eq_mul_left_iff
    have H_or : m1 = m2 ∨ (70 : ℤ) = 0 := H_iff_general.mp h_add_1000
    have hm_eq : m1 = m2 := Or.resolve_right H_or h_70_ne_zero
    have hm1_in_M2 : m1 ∈ M_finset_part2 := hm_eq ▸ hm2
    rw [M_finset_part1_def] at hm1
    rw [M_finset_part2_def] at hm1_in_M2
    have hm1_bounds1 : (20 : ℤ) ≤ m1 ∧ m1 ≤ (21 : ℤ) := by exact Finset.mem_Icc.mp hm1
    have hm1_bounds2 : (47 : ℤ) ≤ m1 ∧ m1 ≤ (50 : ℤ) := by exact Finset.mem_Icc.mp hm1_in_M2
    have contra : (47 : ℤ) ≤ (21 : ℤ) := by linarith [hm1_bounds1.right, hm1_bounds2.left]
    norm_num at contra
  subprob_S1_S2_disjoint_def :≡ ∀ (x : ℕ), x ∈ S1 → x ∈ S2 → False
  subprob_S1_S2_disjoint_def_proof ⇐ show subprob_S1_S2_disjoint_def by
    intro x hxS1 hxS2
    rw [S1_def] at hxS1
    rw [S2_def] at hxS2
    rw [Finset.mem_image] at hxS1
    rw [Finset.mem_image] at hxS2
    rcases hxS1 with ⟨m1, hm1_in_M1, heq1⟩
    rcases hxS2 with ⟨m2, hm2_in_M2, heq2⟩
    have : map_m_to_n m1 = map_m_to_n m2 := by
      rw [heq1, heq2]
    have h_neq : map_m_to_n m1 ≠ map_m_to_n m2 :=
      subprob_map_m1_neq_map_m2_for_disjoint_M_parts_proof m1 m2 hm1_in_M1 hm2_in_M2
    exact h_neq this
  subprob_card_S_eq_sum_cards_from_disjoint_union :≡ S.card = S1.card + S2.card
  subprob_card_S_eq_sum_cards_from_disjoint_union_proof ⇐ show subprob_card_S_eq_sum_cards_from_disjoint_union by
    have h₁ : S = S1 ∪ S2 := by
      ext n
      simp [subprob_n_in_S_iff_image_union_proof]
    have h₂ : Disjoint S1 S2 := by
      simp [Finset.disjoint_iff_ne]
      intro x hm xm
      apply subprob_S1_S2_disjoint_def_proof x hm xm
    simp [h₁, h₂, Finset.card_union_eq, subprob_S1_card_val_proof, subprob_S2_card_val_proof]
  subprob_final_goal :≡ S.card = (6 : ℕ)
  subprob_final_goal_proof ⇐ show subprob_final_goal by
    have h₁ : Finset.card S1 = 2 := subprob_S1_card_val_proof
    have h₂ : Finset.card S2 = 4 := subprob_S2_card_val_proof
    have h₃ : Finset.card S = Finset.card S1 + Finset.card S2 := subprob_card_S_eq_sum_cards_from_disjoint_union_proof
    rw [h₁, h₂] at h₃
    norm_num at h₃
    exact h₃
  original_target :≡ Finset.card S = (6 : ℕ)
  original_target_proof ⇐ show original_target by
    simpa [subprob_S1_card_val_proof, subprob_S2_card_val_proof] using subprob_card_S_eq_sum_cards_from_disjoint_union_proof
-/
