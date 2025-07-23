-- In carleson/Carleson/ToMathlib/RealInterpolation.lean

import Carleson.ToMathlib.WeakType
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! This file contains a proof of the Marcinkiewisz real interpolation theorem.
    The proof roughly follows Folland, Real Analysis. Modern Techniques and Their Applications,
    section 6.4, theorem 6.28, but a different truncation is used, and some estimates instead
    follow the technique as e.g. described in [Duoandikoetxea, Fourier Analysis, 2000].

    The file consists of the following sections:
    - Convenience results for working with (interpolated) exponents
    - Results about the particular choice of exponent
    - Interface for using cutoff functions
    - Results about the particular choice of scale
    - Some tools for measure theory computations
    - Results about truncations of a function
    - Measurability properties of truncations
    - Truncations and Lp spaces
    - Some results about the integrals of truncations
    - Minkowski's integral inequality
    - Apply Minkowski's integral inequality to truncations
    - Weaktype estimates applied to truncations
    - Definitions
    - Proof of the real interpolation theorem
-/

noncomputable section

open ENNReal Real Set MeasureTheory

-- Note (F): can we make `t : ℝ≥0∞` for a large part of the proof?
variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ}

/-! ## Convenience results for working with (interpolated) exponents
-/
namespace ComputationsInterpolatedExponents

-- unused
lemma ofReal_mem_Ioo_0_1 (h : t ∈ Ioo 0 1) : ENNReal.ofReal t ∈ Ioo 0 1 :=
  ⟨ofReal_pos.mpr h.1, ofReal_lt_one.mpr h.2⟩

lemma ENNReal_preservation_positivity₀ (ht : t ∈ Ioo 0 1) (hpq : p ≠ ⊤ ∨ q ≠ ⊤) :
    0 < (1 - ENNReal.ofReal t) * p⁻¹ + ENNReal.ofReal t * q⁻¹ := by
  have t_mem : ENNReal.ofReal t ∈ Ioo 0 1 :=
    ⟨ofReal_pos.mpr ht.1, ENNReal.ofReal_one ▸ (ofReal_lt_ofReal_iff zero_lt_one).mpr ht.2⟩
  obtain dir|dir := hpq
  · exact Left.add_pos_of_pos_of_nonneg (mul_pos ((tsub_pos_of_lt t_mem.2).ne')
      (ENNReal.inv_ne_zero.mpr dir)) (zero_le _)
  · exact Right.add_pos_of_nonneg_of_pos (zero_le _)
      (mul_pos ((ofReal_pos.mpr ht.1).ne') (ENNReal.inv_ne_zero.mpr dir))

lemma ENNReal_preservation_positivity (ht : t ∈ Ioo 0 1) (hpq : p ≠ q) :
    0 < (1 - ENNReal.ofReal t) * p⁻¹ + ENNReal.ofReal t * q⁻¹ := by
  apply ENNReal_preservation_positivity₀ ht
  cases (lt_or_gt_of_ne hpq) <;> exact Ne.ne_or_ne ⊤ hpq

lemma ENNReal_preservation_positivity' (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p > 0 := by
  rw [← inv_inv p, hp]
  simp [ENNReal.mul_eq_top, sub_eq_zero, hp₀.ne', hp₁.ne']

lemma interp_exp_ne_top (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ≠ ⊤ :=
  ENNReal.inv_ne_zero.mp <| hp ▸ (ENNReal_preservation_positivity ht hp₀p₁).ne'

lemma interp_exp_ne_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ≠ ⊤ :=
  ENNReal.inv_ne_zero.mp (hp ▸ (ENNReal_preservation_positivity₀ ht hp₀p₁).ne')

lemma interp_exp_eq (hp₀p₁ : p₀ = p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ = p := by
  rw [← inv_inv (a := p), hp, ← hp₀p₁, ← add_mul,
    tsub_add_cancel_of_le <| ofReal_lt_one.mpr ht.2 |>.le, one_mul, inv_inv]

lemma interp_exp_lt_top (hp₀p₁ : p₀ ≠ p₁)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top hp₀p₁ ht hp

lemma interp_exp_lt_top' (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p < ⊤ :=
  Ne.lt_top <| interp_exp_ne_top' hp₀p₁ ht hp

lemma interp_exp_between (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ∈ Ioo p₀ p₁ := by
  refine ⟨?_, ?_⟩ <;> apply ENNReal.inv_lt_inv.mp
  · rw [hp]
    have : p₀⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₀⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ofReal_lt_one.mpr ht.2
    nth_rw 2 [this]
    gcongr
    · exact mul_ne_top (sub_ne_top top_ne_one.symm) (inv_ne_top.mpr hp₀.ne')
    · exact (ofReal_pos.mpr ht.1).ne'
    · exact coe_ne_top
  · rw [hp]
    have : p₁⁻¹ = (1 - ENNReal.ofReal t) * p₁⁻¹ + ENNReal.ofReal t * p₁⁻¹ := by
      rw [← add_mul, tsub_add_eq_max, max_eq_left_of_lt, one_mul]
      exact ofReal_lt_one.mpr ht.2
    nth_rw 1 [this]
    gcongr
    · exact mul_ne_top coe_ne_top (inv_ne_top.mpr hp₁.ne')
    · exact (tsub_pos_iff_lt.mpr (ofReal_lt_one.mpr ht.2)).ne'
    · exact coe_ne_top

lemma one_le_interp_exp_aux (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁) (hp₀p₁ : p₀ < p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p :=
  hp₀.trans_lt
    (interp_exp_between (zero_lt_one.trans_le hp₀) (zero_lt_one.trans_le hp₁) hp₀p₁ ht hp).1 |>.le

lemma switch_exponents (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p⁻¹ = (1 - ENNReal.ofReal (1 - t)) * p₁⁻¹ + ENNReal.ofReal (1 - t) * p₀⁻¹ := by
  rw [add_comm, ← ofReal_one, ← ofReal_sub, _root_.sub_sub_cancel, ofReal_sub _ ht.1.le, ofReal_one]
  · exact hp
  · exact (Ioo.one_sub_mem ht).1.le

lemma one_le_toReal {a : ℝ≥0∞} (ha₁ : 1 ≤ a) (ha₂ : a < ⊤) : 1 ≤ a.toReal :=
  toReal_mono ha₂.ne_top ha₁

lemma one_le_interp (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p := by
  rcases (lt_or_gt_of_ne hp₀p₁) with p₀lt_p₁ | p₁lt_p₀
  · exact one_le_interp_exp_aux hp₀ hp₁ p₀lt_p₁ ht hp
  · exact one_le_interp_exp_aux hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)

lemma one_le_interp_toReal (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 1 ≤ p.toReal :=
  one_le_toReal (one_le_interp hp₀ hp₁ hp₀p₁ ht hp) (Ne.lt_top (interp_exp_ne_top hp₀p₁ ht hp))

lemma coe_rpow_ne_top {a : ℝ} {q : ℝ} (hq : q ≥ 0): ENNReal.ofReal a ^ q ≠ ⊤ :=
  rpow_ne_top_of_nonneg hq coe_ne_top

-- Note this lemma can directly be applied to elements of `ℝ≥0` as well
lemma coe_rpow_ne_top' {a : ℝ} {q : ℝ} (hq : 0 < q): ENNReal.ofReal a ^ q ≠ ⊤ :=
  coe_rpow_ne_top hq.le

lemma coe_pow_pos {a : ℝ} {q : ℝ} (ha : a > 0) : ENNReal.ofReal a ^ q > 0 :=
  ENNReal.rpow_pos (ofReal_pos.mpr ha) coe_ne_top

lemma rpow_ne_top' {a : ℝ≥0∞} {q : ℝ} (ha : a ≠ 0) (ha' : a ≠ ⊤)  : a ^ q ≠ ⊤ := by
  intro h
  rcases ENNReal.rpow_eq_top_iff.mp h with ⟨a_zero, _⟩ | ⟨a_top, _⟩
  · exact (ha a_zero).elim
  · exact (ha' a_top).elim

lemma exp_toReal_pos' {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : q.toReal > 0 :=
  toReal_pos (lt_of_lt_of_le zero_lt_one hq).ne' hq'.ne_top

lemma ne_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ico {p q r : ℝ≥0∞} (hq : q ∈ Ico p r) : q < ⊤ := (ne_top_of_Ico hq).lt_top

lemma ne_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ ⊤ := hq.2.ne_top

lemma lt_top_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q < ⊤ := (ne_top_of_Ioo hq).lt_top

lemma ne_top_of_Ioc {p q r : ℝ≥0∞} (hq : q ∈ Ioc p r) (hr : r < ⊤) : q ≠ ⊤ :=
  hq.2.trans_lt hr |>.ne_top

lemma pos_of_rb_Ioc {p q r : ℝ≥0∞} (hr : q ∈ Ioc p r) : 0 < r :=
  zero_le p |>.trans_lt hr.1 |>.trans_le hr.2

lemma exp_toReal_ne_zero {q : ℝ≥0∞} (hq : q ≥ 1) (hq' : q < ⊤) : q.toReal ≠ 0 :=
  (exp_toReal_pos' hq hq').ne'

-- TODO: remove the top one?
lemma exp_toReal_ne_zero' {q : ℝ≥0∞} (hq : q > 0) (hq' : q ≠ ⊤) : q.toReal ≠ 0 :=
  (toReal_pos hq.ne' hq').ne'

lemma exp_toReal_ne_zero_of_Ico {q p : ℝ≥0∞} (hq : q ∈ Ico 1 p) : q.toReal ≠ 0 :=
  exp_toReal_ne_zero hq.1 (lt_top_of_Ico hq)

lemma pos_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q > 0 := pos_of_gt hq.1

lemma ne_zero_of_Ioo {p q r : ℝ≥0∞} (hq : q ∈ Ioo p r) : q ≠ 0 := (pos_of_gt hq.1).ne'

lemma pos_of_Icc_1 {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : p > 0 := lt_of_lt_of_le zero_lt_one hp.1

lemma pos_of_ge_1 {p : ℝ≥0∞} (hp : 1 ≤ p) : p > 0 := lt_of_lt_of_le zero_lt_one hp

lemma pos_rb_of_Icc_1_inh {p q : ℝ≥0∞} (hp : p ∈ Icc 1 q) : q > 0 :=
  lt_of_lt_of_le zero_lt_one (le_trans hp.1 hp.2)

lemma toReal_pos_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : p.toReal > 0 :=
  toReal_pos (ne_zero_of_lt hp.1) hp.2.ne_top

lemma toReal_ne_zero_of_Ioo {q p r : ℝ≥0∞} (hp : p ∈ Ioo q r) : p.toReal ≠ 0 :=
  toReal_ne_zero.mpr ⟨ne_zero_of_lt hp.1, hp.2.ne_top⟩

-- TODO: check which ones are actually used
lemma eq_of_rpow_eq (a b: ℝ≥0∞) (c : ℝ) (hc : c ≠ 0) (h : a ^ c = b ^ c) : a = b := by
  rw [← ENNReal.rpow_rpow_inv hc a, ← ENNReal.rpow_rpow_inv hc b]
  exact congrFun (congrArg HPow.hPow h) c⁻¹

lemma le_of_rpow_le {a b: ℝ≥0∞} {c : ℝ} (hc : c > 0) (h : a ^ c ≤ b ^ c) : a ≤ b := by
  rw [← ENNReal.rpow_rpow_inv hc.ne' a, ← ENNReal.rpow_rpow_inv hc.ne' b]
  exact (ENNReal.rpow_le_rpow_iff (inv_pos_of_pos hc)).mpr h

-- TODO : decide if this is wanted
-- local instance : Coe ℝ ℝ≥0∞ where
--   coe x := ENNReal.ofReal x

lemma coe_inv_exponent (hp₀ : p₀ > 0) : ENNReal.ofReal (p₀⁻¹.toReal) = p₀⁻¹ :=
  ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne')

lemma inv_of_interpolated_pos' (hp₀p₁ : p₀ ≠ p₁) (ht : t ∈ Ioo 0 1)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : 0 < p⁻¹ :=
  ENNReal.inv_pos.mpr (interp_exp_ne_top hp₀p₁ ht hp)

-- TODO: remove, this is redundant, but for now mirror the development for reals...
lemma interpolated_pos' (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹): 0 < p :=
  ENNReal_preservation_positivity' hp₀ hp₁ hp

lemma exp_toReal_pos (hp₀ : p₀ > 0) (hp₀' : p₀ ≠ ⊤) : 0 < p₀.toReal :=
  toReal_pos hp₀.ne' hp₀'

lemma interp_exp_in_Ioo_zero_top (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p ∈ Ioo 0 ⊤ :=
  ⟨interpolated_pos' hp₀ hp₁ hp, interp_exp_lt_top' hp₀p₁ ht hp⟩

lemma inv_toReal_pos_of_ne_top (hp₀ : p₀ > 0) (hp' : p₀ ≠ ⊤) : p₀⁻¹.toReal > 0 :=
  toReal_inv _ ▸ inv_pos_of_pos (exp_toReal_pos hp₀ hp')

lemma inv_toReal_ne_zero_of_ne_top (hp₀ : p₀ > 0) (hp' : p₀ ≠ ⊤) : p₀⁻¹.toReal ≠ 0 :=
  (inv_toReal_pos_of_ne_top hp₀ hp').ne'

lemma interp_exp_toReal_pos (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ hp).ne' (interp_exp_ne_top hp₀p₁ ht hp)

lemma interp_exp_toReal_pos' (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hp₀p₁ : p₀ ≠ ⊤ ∨ p₁ ≠ ⊤) : 0 < p.toReal :=
  toReal_pos (interpolated_pos' hp₀ hp₁ hp).ne' (interp_exp_ne_top' hp₀p₁ ht hp)

lemma interp_exp_inv_pos (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0)
    (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    0 < p⁻¹.toReal :=
  toReal_inv _ ▸ inv_pos_of_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)

lemma interp_exp_inv_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0)
    (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) : p⁻¹.toReal ≠ 0 :=
  (interp_exp_inv_pos ht hp₀ hp₁ hp₀p₁ hp).ne'

lemma preservation_interpolation (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0)
    (hp₁ : p₁ > 0) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p⁻¹.toReal = (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rw [← one_toReal, ← toReal_ofReal ht.1.le, ← ENNReal.toReal_sub_of_le]
  · rw [← toReal_mul, ← toReal_mul, ← toReal_add]
    · exact congrArg ENNReal.toReal hp
    · exact mul_ne_top (sub_ne_top (top_ne_one.symm)) (inv_ne_top.mpr hp₀.ne')
    · exact mul_ne_top coe_ne_top (inv_ne_top.mpr hp₁.ne')
  · exact ofReal_le_one.mpr ht.2.le
  · exact top_ne_one.symm

lemma preservation_positivity_inv_toReal (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) :
    0 < (1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal := by
  rcases (eq_or_ne p₀ ⊤) with p₀eq_top | p₀ne_top
  · rw [p₀eq_top]
    simp only [inv_top, zero_toReal, mul_zero, zero_add]
    apply mul_pos ht.1
    rw [toReal_inv]
    refine inv_pos_of_pos (exp_toReal_pos hp₁ ?_)
    rw [p₀eq_top] at hp₀p₁
    exact hp₀p₁.symm
  · exact add_pos_of_pos_of_nonneg (mul_pos (Ioo.one_sub_mem ht).1 (toReal_inv _ ▸ inv_pos_of_pos
      (exp_toReal_pos hp₀ p₀ne_top))) (mul_nonneg ht.1.le toReal_nonneg)

lemma ne_inv_toReal_exponents (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁) :
    (p₀⁻¹.toReal ≠ p₁⁻¹.toReal) := by
  refine fun h ↦ hp₀p₁ ?_
  rw [← inv_inv p₀, ← inv_inv p₁]
  apply congrArg Inv.inv
  rw [← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₀.ne'),
    ← ofReal_toReal_eq_iff.mpr (inv_ne_top.mpr hp₁.ne')]
  exact congrArg ENNReal.ofReal h

lemma ne_inv_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0)
  (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    (p₀⁻¹.toReal ≠ p⁻¹.toReal) := by
  rw [preservation_interpolation ht hp₀ hp₁ hp,
    ← sub_ne_zero, _root_.sub_mul, one_mul, add_comm_sub, sub_add_eq_sub_sub, sub_self, zero_sub,
    neg_sub, ← _root_.mul_sub]
  exact mul_ne_zero ht.1.ne' (sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁))

lemma ne_sub_toReal_exp (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁) :
    p₁⁻¹.toReal - p₀⁻¹.toReal ≠ 0 :=
  sub_ne_zero_of_ne (ne_inv_toReal_exponents hp₀ hp₁ hp₀p₁).symm

lemma ne_toReal_exp_interp_exp (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀.toReal ≠ p.toReal := by
  refine fun h ↦ ne_inv_toReal_exp_interp_exp ht hp₀ hp₁ hp₀p₁ hp ?_
  repeat rw [toReal_inv _]
  exact congrArg Inv.inv h

lemma ne_toReal_exp_interp_exp₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p.toReal ≠ p₁.toReal :=
  (ne_toReal_exp_interp_exp (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)).symm

lemma ofReal_inv_interp_sub_exp_pos₁ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0)
    (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₁.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr (ne_toReal_exp_interp_exp₁ ht hq₀ hq₁ hq₀q₁ hq)))

lemma ofReal_inv_interp_sub_exp_pos₀ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0)
    (hq₀q₁ : q₀ ≠ q₁) (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    ENNReal.ofReal |q.toReal - q₀.toReal|⁻¹ > 0 :=
  ofReal_pos.mpr (inv_pos_of_pos (abs_sub_pos.mpr (Ne.symm
    (ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq))))

lemma exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p₀ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun h ↦ (not_le_of_gt h (le_of_lt (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1)).elim,
      fun h ↦ (not_le_of_gt h p₀lt_p₁.le).elim⟩
  · exact ⟨fun _ ↦ p₁lt_p₀,
      fun _ ↦ (interp_exp_between hp₁ hp₀ p₁lt_p₀ (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2⟩

lemma exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ < p ↔ p₀ < p₁ := by
  rcases lt_or_gt_of_ne hp₀p₁ with p₀lt_p₁ | p₁lt_p₀
  · exact ⟨fun _ ↦ p₀lt_p₁, fun _ ↦ (interp_exp_between hp₀ hp₁ p₀lt_p₁ ht hp).1⟩
  · exact ⟨fun h ↦ (not_le_of_gt h (interp_exp_between hp₁ hp₀ p₁lt_p₀
      (Ioo.one_sub_mem ht) (switch_exponents ht hp)).2.le).elim,
      fun h ↦ (not_le_of_gt h p₁lt_p₀.le).elim⟩

lemma exp_lt_exp_gt_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₀ ↔ p₁ < p := by
  rw [exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)]

lemma exp_gt_exp_lt_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₀ < p ↔ p < p₁ := by
  rw [exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff (Ioo.one_sub_mem ht) hp₁ hp₀ (Ne.symm hp₀p₁)
    (switch_exponents ht hp)]

lemma exp_lt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p < p₁ ↔ p₀ < p₁ := by
  rw [← exp_gt_exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp

lemma exp_gt_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) :
    p₁ < p ↔ p₁ < p₀ := by
  rw [← exp_lt_exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp]
  exact exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp

end ComputationsInterpolatedExponents

end

noncomputable section

/-! ## Results about the particular choice of exponent

    The proof of the real interpolation theorem will estimate
    `distribution (trunc f A(t)) t` and `distribution (trunc_compl f A(t)) t` for a
    function `A`. The function `A` can be given a closed-form expression that works for
    _all_ cases in the real interpolation theorem, because of the computation rules available
    for elements in `ℝ≥0∞` that avoid the need for a limiting procedure, e.g. `⊤⁻¹ = 0`.

    The function `A` will be of the form `A(t) = (t / d) ^ σ` for particular choices of `d` and
    `σ`. This section contatins results about the exponents `σ`.
-/
namespace ComputationsChoiceExponent

open ENNReal Real Set ComputationsInterpolatedExponents

variable {p₀ q₀ p₁ q₁ p q : ℝ≥0∞} {t : ℝ}

def ζ := (((1 - t) * (p₀⁻¹).toReal + t * (p₁⁻¹).toReal) * ((q₁⁻¹).toReal - (q₀⁻¹).toReal)) /
        (((1 - t) * (q₀⁻¹).toReal + t * (q₁⁻¹).toReal) * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))

lemma ζ_equality₁ (ht : t ∈ Ioo 0 1) :
    @ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) *
    ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) *
    ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₀⁻¹.toReal)) := by
  unfold ζ
  rw [← mul_div_mul_right _ _ ht.1.ne', mul_assoc _ _ t, mul_assoc _ _ t]
  congr <;> ring

lemma ζ_equality₂ (ht : t ∈ Ioo 0 1) :
    @ζ p₀ q₀ p₁ q₁ t =
    (((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal) *
    ((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal - q₁⁻¹.toReal)) /
    (((1 - t) * q₀⁻¹.toReal + t * q₁⁻¹.toReal) *
    ((1 - t) * p₀⁻¹.toReal + t * p₁⁻¹.toReal - p₁⁻¹.toReal)) := by
  unfold ζ
  have : - (1 - t) < 0 := neg_neg_iff_pos.mpr (sub_pos.mpr ht.2)
  rw [← mul_div_mul_right _ _ this.ne, mul_assoc _ _ (-(1 - t)), mul_assoc _ _ (-(1 - t))]
  congr <;> ring

lemma ζ_symm :
    @ζ p₀ q₀ p₁ q₁ t = @ζ p₁ q₁ p₀ q₀ (1 - t) := by
  unfold ζ
  rw [← mul_div_mul_right (c := - 1), mul_assoc _ _ (-1), mul_assoc _ _ (-1)]; on_goal 2 => positivity
  simp only [mul_neg, mul_one, neg_sub, _root_.sub_sub_cancel]
  nth_rewrite 1 [add_comm]; nth_rw 2 [add_comm]

set_option linter.style.multiGoal false in
set_option linter.flexible false in
lemma ζ_equality₃ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    @ζ p₀ q₀ p₁ q₁ t = (p₀.toReal * (q₀.toReal - q.toReal))  / (q₀.toReal * (p₀.toReal - p.toReal))
    := by
  rw [ζ_equality₁ ht, ← preservation_interpolation, ← preservation_interpolation]
  have q_pos : 0 < q := interpolated_pos' hq₀ hq₁ hq
  have p_pos : 0 < p := interpolated_pos' hp₀ hp₁ hp
  have hne : p.toReal * q.toReal * p₀.toReal * q₀.toReal > 0 :=
    mul_pos (mul_pos (mul_pos (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp)
    (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)) (exp_toReal_pos hp₀ hp₀'))
    (exp_toReal_pos hq₀ hq₀')
  rw [← mul_div_mul_right _ _ hne.ne']
  have eq₁ : p⁻¹.toReal * (q⁻¹.toReal - q₀⁻¹.toReal) *
      (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      p₀.toReal * (p⁻¹.toReal * p.toReal) * ((q⁻¹.toReal * q.toReal) * q₀.toReal -
      (q₀⁻¹.toReal * q₀.toReal) * q.toReal) := by ring
  have eq₂ : q⁻¹.toReal * (p⁻¹.toReal - p₀⁻¹.toReal) *
      (p.toReal * q.toReal * p₀.toReal * q₀.toReal) =
      q₀.toReal * (q⁻¹.toReal * q.toReal) * ((p⁻¹.toReal * p.toReal) * p₀.toReal -
      (p₀⁻¹.toReal * p₀.toReal) * p.toReal) := by ring
  rw [eq₁, eq₂, ← @toReal_mul q⁻¹ q, ← @toReal_mul p⁻¹ p, ← @toReal_mul p₀⁻¹ p₀,
      ← @toReal_mul q₀⁻¹ q₀]
  all_goals try assumption
  -- TODO: why can below goals not be discharged?
  repeat rw [ENNReal.inv_mul_cancel] <;> try positivity
  all_goals simp <;> try assumption
  · apply interp_exp_ne_top hq₀q₁ ht hq
  · apply interp_exp_ne_top hp₀p₁ ht hp

lemma one_sub_coe_one_sub (ht : t ∈ Ioo 0 1) :
    (1 - ENNReal.ofReal (1 - t)) = ENNReal.ofReal t := by
  have := ht.2
  rw [← ofReal_one, ← ENNReal.ofReal_sub] <;> congr
  · linarith
  · linarith

lemma coe_one_sub (ht : t ∈ Ioo 0 1) :
    ENNReal.ofReal (1 - t) = 1 - ENNReal.ofReal t := by
  rw [← ofReal_one, ← ENNReal.ofReal_sub]; exact ht.1.le

lemma ζ_equality₄ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    @ζ p₀ q₀ p₁ q₁ t =
    (p₁.toReal * (q₁.toReal - q.toReal)) / (q₁.toReal * (p₁.toReal - p.toReal)) := by
  rw [ζ_symm]
  have one_sub_mem : 1 - t ∈ Ioo 0 1 := Ioo.one_sub_mem ht
  rw [ζ_equality₃ one_sub_mem] <;> try assumption
  · exact hp₀p₁.symm
  · exact hq₀q₁.symm
  · rw [hp, one_sub_coe_one_sub ht, coe_one_sub ht]; ring
  · rw [hq, one_sub_coe_one_sub ht, coe_one_sub ht]; ring

lemma ζ_equality₅ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    p₀.toReal + (@ζ p₀ q₀ p₁ q₁ t)⁻¹ * (q.toReal - q₀.toReal) * (p₀.toReal / q₀.toReal) = p.toReal
    := by
  rw [ζ_equality₃ ht] <;> try assumption
  simp only [inv_div]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  calc
  _ = p₀.toReal - (q₀.toReal⁻¹ * q₀.toReal) * (p₀.toReal - p.toReal) * (p₀.toReal⁻¹ * p₀.toReal) *
      ((q₀.toReal - q.toReal)⁻¹ * (q₀.toReal - q.toReal)) := by ring
  _ = _ := by
    rw [inv_mul_cancel₀, inv_mul_cancel₀, inv_mul_cancel₀]
    · simp only [one_mul, mul_one, _root_.sub_sub_cancel]
    · exact sub_ne_zero_of_ne (ne_toReal_exp_interp_exp ht hq₀ hq₁ hq₀q₁ hq)
    · exact (exp_toReal_pos hp₀ hp₀').ne'
    · exact (exp_toReal_pos hq₀ hq₀').ne'

lemma ζ_equality₆ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    p₁.toReal + (@ζ p₀ q₀ p₁ q₁ t)⁻¹ * (q.toReal - q₁.toReal) * (p₁.toReal / q₁.toReal) = p.toReal
    := by
  rw [ζ_symm]
  exact ζ_equality₅ (Ioo.one_sub_mem ht) hp₁ hq₁ hp₀ hq₀ hp₀p₁.symm hq₀q₁.symm
    (switch_exponents ht hp) (switch_exponents ht hq) hp₁' hq₁'

lemma ζ_equality₇ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ = ⊤) :
    @ζ p₀ q₀ p₁ q₁ t = p₀.toReal / (p₀.toReal - p.toReal) := by
  rw [ζ_equality₁ ht, ← preservation_interpolation ht hp₀ hp₁ hp,
    ← preservation_interpolation ht hq₀ hq₁ hq, hq₀']
  simp only [inv_top, zero_toReal, sub_zero, mul_zero, zero_add]
  have obs : p₀.toReal * p.toReal * q.toReal > 0 :=
    mul_pos (mul_pos (toReal_pos hp₀.ne' hp₀') (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp))
    (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq)
  rw [← mul_div_mul_right _ _ obs.ne']
  congr
  · calc
    _ = (p.toReal⁻¹ * p.toReal) * (q.toReal⁻¹ * q.toReal) * p₀.toReal := by
      rw [toReal_inv, toReal_inv]
      ring
    _ = _ := by
      rw [inv_mul_cancel₀, inv_mul_cancel₀, one_mul, one_mul]
      · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
      · exact (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp).ne'
  · calc
    _ = (q.toReal⁻¹ * q.toReal) * (p.toReal⁻¹ * p.toReal * p₀.toReal - p₀.toReal⁻¹ *
        p₀.toReal * p.toReal) := by
      rw [toReal_inv, toReal_inv, toReal_inv]
      ring
    _ = _ := by
      repeat rw [inv_mul_cancel₀, one_mul]
      · exact (toReal_pos hp₀.ne' hp₀').ne'
      · exact (interp_exp_toReal_pos ht hp₀ hp₁ hp₀p₁ hp).ne'
      · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'

lemma ζ_equality₈ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ = ⊤) :
    @ζ p₀ q₀ p₁ q₁ t = p₁.toReal / (p₁.toReal - p.toReal) :=
  ζ_symm ▸ ζ_equality₇ (Ioo.one_sub_mem ht) hp₁ hq₁ hp₀ hq₀ (Ne.symm hp₀p₁) (Ne.symm hq₀q₁)
    (switch_exponents ht hp) (switch_exponents ht hq) hp₁' hq₁'

lemma ζ_eq_top_top (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
    (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ = ⊤)
    (hq₁' : q₁ = ⊤) :
    @ζ p₀ q₀ p₁ q₁ t = 1 := by
  rw [ζ_equality₂ ht, ← preservation_interpolation ht hp₀ hp₁ hp,
    ← preservation_interpolation ht hq₀ hq₁ hq, hp₁', hq₁']
  simp only [inv_top, zero_toReal, sub_zero]
  rw [mul_comm, div_eq_mul_inv, mul_inv_cancel₀]
  exact (mul_pos (interp_exp_inv_pos ht hq₀ hq₁ hq₀q₁ hq)
    (interp_exp_inv_pos ht hp₀ hp₁ hp₀p₁ hp)).ne'

lemma ζ_pos_iff_aux (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ ≠ ⊤) :
    ( 0 < p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal))) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma preservation_inequality (ht : t ∈ Ioo 0 1) (hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p.toReal < p₀.toReal ↔ p < p₀ :=
  toReal_lt_toReal (interp_exp_ne_top hp₀p₁ ht hp) hp₀'

lemma preservation_inequality' (ht : t ∈ Ioo 0 1)(hp₀p₁ : p₀ ≠ p₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹) (hp₀' : p₀ ≠ ⊤) :
    p₀.toReal < p.toReal ↔ p₀ < p :=
  toReal_lt_toReal hp₀' (interp_exp_ne_top hp₀p₁ ht hp)

lemma preservation_inequality_of_lt₀ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀q₁ : q₀ < q₁) :
    q₀.toReal < q.toReal :=
  (toReal_lt_toReal hq₀q₁.ne_top (interp_exp_ne_top hq₀q₁.ne ht hq)).mpr
    ((exp_gt_iff ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma preservation_inequality_of_lt₁ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀q₁ : q₀ < q₁)
    (hq₁' : q₁ ≠ ⊤):
    q.toReal < q₁.toReal :=
  (toReal_lt_toReal (interp_exp_ne_top hq₀q₁.ne ht hq) hq₁').mpr
    ((exp_lt_iff₁ ht hq₀ hq₁ hq₀q₁.ne hq).mpr hq₀q₁)

lemma ζ_pos_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) : (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₀.toReal) ∧ (p.toReal < p₀.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p₀.toReal < p.toReal)) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_pos_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_pos_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q.toReal < q₁.toReal) ∧ (p.toReal < p₁.toReal)) ∨
    ((q₁.toReal < q.toReal) ∧ (p₁.toReal < p.toReal)) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_pos_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_pos_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
    (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal ∨
    q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal := by
  unfold ζ
  rw [_root_.div_pos_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg,
      neg_mul_eq_mul_neg, mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma inv_toReal_iff (hp₀ : p₀ > 0) (hp₁ : p₁ > 0) :
    p₀⁻¹.toReal < p₁⁻¹.toReal ↔ p₁ < p₀ :=
  Iff.trans (toReal_lt_toReal (ne_of_lt (inv_lt_top.mpr hp₀))
    (ne_of_lt (inv_lt_top.mpr hp₁))) ENNReal.inv_lt_inv

lemma ζ_pos_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q₁ < q₀) ∧ (p₁ < p₀)) ∨ ((q₀ < q₁) ∧ (p₀ < p₁)) := by
  rw [ζ_pos_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_pos_iff' (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
    (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    ((q < q₀) ∧ (p < p₀)) ∨ ((q₀ < q) ∧ (p₀ < p)) := by
  rw [ζ_pos_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁,
    ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq,
    ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp, ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_pos_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
    (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁)  :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    (q₀ < q) := by
  rw [ζ_pos_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_pos_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0)
  (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    (0 < @ζ p₀ q₀ p₁ q₁ t) ↔
    (q < q₁) := by
  rw [← exp_gt_exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_neg_iff_aux₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
    q₀⁻¹.toReal < q₁⁻¹.toReal ∧ p₁⁻¹.toReal < p₀⁻¹.toReal ∨
    q₁⁻¹.toReal < q₀⁻¹.toReal ∧ p₀⁻¹.toReal < p₁⁻¹.toReal := by
  unfold ζ
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg]
  rw [mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
      mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁
  · exact preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁
  · exact preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁

lemma ζ_neg_iff (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
    q₁ < q₀ ∧ p₀ < p₁ ∨ q₀ < q₁ ∧ p₁ < p₀ := by
  rw [ζ_neg_iff_aux₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, inv_toReal_iff hq₀ hq₁, inv_toReal_iff hp₀ hp₁,
    inv_toReal_iff hq₁ hq₀, inv_toReal_iff hp₁ hp₀]

lemma ζ_neg_iff' (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) :
    (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔
    ((q < q₀) ∧ (p₀ < p)) ∨ ((q₀ < q) ∧ (p < p₀)) := by
  rw [ζ_neg_iff ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁, ← exp_lt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_lt_iff ht hq₀ hq₁ hq₀q₁ hq, ← exp_gt_iff ht hp₀ hp₁ hp₀p₁ hp,
    ← exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]

lemma ζ_neg_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔ q < q₀ := by
  rw [ζ_neg_iff' ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁ hp hq]
  rw [← exp_gt_iff (p := p) ht hp₀ hp₁ hp₀p₁'.ne hp] at hp₀p₁'
  have : ¬ (p < p₀) := not_lt_of_gt hp₀p₁'
  tauto

lemma ζ_neg_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    (@ζ p₀ q₀ p₁ q₁ t) < 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma ζ_neg_iff_aux (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    (p₀.toReal * (q₀.toReal - q.toReal) / (q₀.toReal * (p₀.toReal - p.toReal)) < 0) ↔
    ((q.toReal < q₀.toReal) ∧ (p₀.toReal < p.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p.toReal < p₀.toReal)) := by
  rw [div_neg_iff, ← Left.neg_pos_iff, ← Left.neg_pos_iff, neg_mul_eq_mul_neg, neg_mul_eq_mul_neg,
    mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left,
    mul_pos_iff_of_pos_left, mul_pos_iff_of_pos_left, neg_sub, neg_sub]
  · simp only [sub_pos, sub_neg]
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'
  · exact exp_toReal_pos hq₀ hq₀'
  · exact exp_toReal_pos hp₀ hp₀'

lemma ζ_neg_toReal_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) :
    (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q.toReal < q₀.toReal) ∧ (p₀.toReal < p.toReal)) ∨
    ((q₀.toReal < q.toReal) ∧ (p.toReal < p₀.toReal)) := by
  rw [ζ_equality₃ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀']
  exact ζ_neg_iff_aux hp₀ hq₀ hp₀' hq₀'

lemma ζ_neg_toReal_iff₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₁' : p₁ ≠ ⊤)
    (hq₁' : q₁ ≠ ⊤) :
    (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q.toReal < q₁.toReal) ∧ (p₁.toReal < p.toReal)) ∨ ((q₁.toReal < q.toReal) ∧
    (p.toReal < p₁.toReal)) := by
  rw [ζ_equality₄ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₁' hq₁']
  exact ζ_neg_iff_aux hp₁ hq₁ hp₁' hq₁'

lemma ζ_neg_iff₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀' : p₀ ≠ ⊤)
    (hq₀' : q₀ ≠ ⊤) : (@ζ p₀ q₀ p₁ q₁ t < 0) ↔
    ((q < q₀) ∧ (p₀ < p)) ∨ ((q₀ < q) ∧ (p < p₀)) := by
  rw [ζ_neg_toReal_iff₀ ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁ hp hq hp₀' hq₀',
    preservation_inequality ht hq₀q₁ hq hq₀', preservation_inequality ht hp₀p₁ hp hp₀',
    preservation_inequality' ht hq₀q₁ hq hq₀', preservation_inequality' ht hp₀p₁ hp hp₀']

lemma ζ_ne_zero (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0)
    (hp₀p₁ : p₀ ≠ p₁) (hq₀q₁ : q₀ ≠ q₁) :
    (@ζ p₀ q₀ p₁ q₁ t ≠ 0) := by
  refine div_ne_zero ?_ ?_
  · apply mul_ne_zero (preservation_positivity_inv_toReal ht hp₀ hp₁ hp₀p₁).ne'
    refine sub_ne_zero_of_ne (Ne.symm fun h ↦ hq₀q₁ ?_)
    rw [← inv_inv q₀, ← inv_inv q₁, ← coe_inv_exponent hq₀, ← coe_inv_exponent hq₁]
    exact congrArg Inv.inv (congrArg ENNReal.ofReal h)
  · apply mul_ne_zero (preservation_positivity_inv_toReal ht hq₀ hq₁ hq₀q₁).ne'
    refine sub_ne_zero_of_ne (Ne.symm fun h ↦ hp₀p₁ ?_)
    rw [← inv_inv p₀, ← inv_inv p₁, ← coe_inv_exponent hp₀, ← coe_inv_exponent hp₁]
    exact congrArg Inv.inv (congrArg ENNReal.ofReal h)

lemma ζ_le_zero_iff_of_lt₀ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    (@ζ p₀ q₀ p₁ q₁ t ≤ 0) ↔ q < q₀ := by
  constructor <;> intro h
  · rcases (Decidable.lt_or_eq_of_le h) with ζ_lt_0 | ζ_eq_0
    · exact (ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mp ζ_lt_0
    · exact False.elim <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ hp₀p₁'.ne hq₀q₁) ζ_eq_0
  · exact ((ζ_neg_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁').mpr h).le

lemma ζ_le_zero_iff_of_lt₁ (ht : t ∈ Ioo 0 1) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0)
    (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hp₀p₁' : p₀ < p₁) :
    (@ζ p₀ q₀ p₁ q₁ t) ≤ 0 ↔ q₁ < q := by
  rw [← exp_lt_exp_gt_iff ht hq₀ hq₁ hq₀q₁ hq]
  exact ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁'

lemma eq_exponents₀ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal + q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₀.toReal)) = (1 - t) * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t) * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
      calc
      _ = q₀.toReal * q₁⁻¹.toReal - q₀.toReal * q₀⁻¹.toReal +
          q₁⁻¹.toReal * q.toReal - q₁⁻¹.toReal *  q₀.toReal := by
        ring
      _ = q₁⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal := by
        rw [toReal_inv, toReal_inv, toReal_inv, mul_inv_cancel₀, inv_mul_cancel₀]
        · ring
        · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
        · exact (toReal_pos hq₀.ne' hq₀').ne'
      _ = q.toReal * (q₁⁻¹.toReal - q⁻¹.toReal) := by ring
      _ = _ := by
        rw [preservation_interpolation ht hq₀ hq₁ hq]
        congr
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₂ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀.toReal / p₀.toReal + p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₀.toReal)) = (1 - t) * p₀⁻¹.toReal * q.toReal := by
  rw [div_eq_inv_mul, mul_div_assoc, mul_assoc, toReal_inv, ← mul_add, mul_comm_div,
    ← mul_div_assoc, add_div']
  · have : q₀.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) + q₁⁻¹.toReal * (q.toReal - q₀.toReal) =
        q.toReal * ((1 - t) * (q₁⁻¹.toReal - q₀⁻¹.toReal)) := by
      calc
      _ = q₀.toReal * q₁⁻¹.toReal - q₀.toReal * q₀⁻¹.toReal +
          q₁⁻¹.toReal * q.toReal - q₁⁻¹.toReal *  q₀.toReal := by
        ring
      _ = q₁⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal := by
        rw [toReal_inv, toReal_inv, toReal_inv, mul_inv_cancel₀, inv_mul_cancel₀]
        · ring
        · exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
        · exact (toReal_pos hq₀.ne' hq₀').ne'
      _ = q.toReal * (q₁⁻¹.toReal - q⁻¹.toReal) := by ring
      _ = _ := by
        rw [preservation_interpolation ht hq₀ hq₁ hq]
        congr
        ring
    rw [this, mul_div_assoc, mul_div_cancel_right₀]
    · ring
    · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁
  · exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₁ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) = - t * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : q₀⁻¹.toReal * (q.toReal - q₀.toReal) = - t * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
    calc
    _ = (q₀⁻¹.toReal * q.toReal - q₀⁻¹.toReal * q₀.toReal) := by ring
    _ = (q₀⁻¹.toReal * q.toReal - 1) := by
      rw [toReal_inv, inv_mul_cancel₀]
      exact (exp_toReal_pos hq₀ hq₀').ne'
    _ = (q₀⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal) := by
      rw [toReal_inv, toReal_inv, inv_mul_cancel₀]
      exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
    _ = q.toReal * (q₀⁻¹.toReal - q⁻¹.toReal) := by ring
    _ = _ := by
      rw [preservation_interpolation ht hq₀ hq₁ hq]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

-- TODO: simplify these proofs with statements above
lemma eq_exponents₃ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₀' : q₀ ≠ ⊤) :
    (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (q.toReal - q₀.toReal) =
    - t * p₁⁻¹.toReal * q.toReal := by
  rw [mul_comm_div, ← mul_div_assoc]
  have : (p₁⁻¹.toReal * q₀⁻¹.toReal) * (q.toReal - q₀.toReal) =
      - t * p₁⁻¹.toReal * q.toReal * (q₁⁻¹.toReal - q₀⁻¹.toReal) := by
    calc
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q₀⁻¹.toReal * q₀.toReal) := by ring
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - 1) := by
      rw [toReal_inv, toReal_inv, inv_mul_cancel₀]
      apply (exp_toReal_pos hq₀ hq₀').ne'
    _ = p₁⁻¹.toReal * (q₀⁻¹.toReal * q.toReal - q⁻¹.toReal * q.toReal) := by
      rw [toReal_inv, toReal_inv, toReal_inv, inv_mul_cancel₀]
      exact (interp_exp_toReal_pos ht hq₀ hq₁ hq₀q₁ hq).ne'
    _ = p₁⁻¹.toReal * q.toReal * (q₀⁻¹.toReal - q⁻¹.toReal) := by ring
    _ = _ := by
      rw [preservation_interpolation ht hq₀ hq₁ hq]
      ring
  rw [this, mul_div_cancel_right₀]
  exact ne_sub_toReal_exp hq₀ hq₁ hq₀q₁

lemma eq_exponents₄  :
    (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) =
    - (q₀⁻¹.toReal / (q₀⁻¹.toReal - q₁⁻¹.toReal)) := calc
  _ = - (q₀⁻¹.toReal * (-(q₁⁻¹.toReal - q₀⁻¹.toReal)⁻¹)) := by
    rw [div_eq_mul_inv]; ring
  _ = _ := by congr; rw [neg_inv, neg_sub]

lemma eq_exponents₅ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤):
    (q₁.toReal + -(q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)))
    = t * q.toReal := by
  rw [eq_exponents₄, neg_mul, neg_neg, eq_exponents₀ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁)
    (switch_exponents ht hq) hq₁']
  ring

lemma eq_exponents₆ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) = (1 - t) * q.toReal := by
  rw [← neg_neg (a := q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)), ← eq_exponents₄, neg_mul,
    eq_exponents₁ (Ioo.one_sub_mem ht) hq₁ hq₀ (Ne.symm hq₀q₁) (switch_exponents ht hq) hq₁']
  ring

lemma eq_exponents₇ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    q₁.toReal / p₁.toReal + -(p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
    (q.toReal - q₁.toReal)) =
    t * p₁⁻¹.toReal * q.toReal := by
  rw [div_eq_mul_inv, toReal_inv]
  calc
  _ = p₁.toReal⁻¹ * (q₁.toReal + - (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) *
      (q.toReal - q₁.toReal))) := by ring
  _ = _ := by
    rw [eq_exponents₅ (ht := ht)] <;> try assumption
    ring

lemma eq_exponents₈ (ht : t ∈ Ioo 0 1) (hq₀ : q₀ > 0) (hq₁ : q₁ > 0) (hq₀q₁ : q₀ ≠ q₁)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹) (hq₁' : q₁ ≠ ⊤) :
    p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal) =
    (1 - t) * p₀⁻¹.toReal * q.toReal := calc
  _ = p₀⁻¹.toReal * (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal) * (q.toReal - q₁.toReal)) := by ring
  _ = _ := by
    rw [eq_exponents₆] <;> try assumption
    ring

end ComputationsChoiceExponent

end

/-! ## Interface for using cutoff functions
-/
noncomputable section

open Real Set

/-- A ScaledPowerFunction is meant to represent a function of the form `t ↦ (t / d)^σ`,
    where `d` is strictly positive and either `σ > 0` or `σ < 0`. -/
structure ScaledPowerFunction where
  σ : ℝ
  d : ℝ
  hd : d > 0
  hσ : (σ > 0) ∨ (σ < 0)

/-- A ToneCouple is an couple of two monotone functions that are practically inverses of each
    other. It is used in the proof of the real interpolation theorem.

    Note: originally it seemed useful to make the possible choice of this function general
    in the proof of the real inteprolation theorem. However, in the end really only one
    function works for all the different cases. This infrastructure, however, could potentially
    still be useful, if one would like to try to improve the constant. -/
structure ToneCouple where
  ton : ℝ → ℝ
  inv : ℝ → ℝ
  mon : Bool
  ton_is_ton : if mon then StrictMonoOn ton (Ioi 0) else StrictAntiOn ton (Ioi 0)
  ran_ton : ∀ t ∈ Ioi (0 : ℝ), ton t ∈ Ioi 0
  ran_inv : ∀ t ∈ Ioi (0 : ℝ), inv t ∈ Ioi 0
  inv_pf : if mon
      then ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ s < inv t) ∧ (t < ton s ↔ inv t < s)
      else ∀ s ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), (ton s < t ↔ inv t < s) ∧ (t < ton s ↔ s < inv t)

/-- A scaled power function gives rise to a ToneCouple. -/
def spf_to_tc (spf : ScaledPowerFunction) : ToneCouple where
  ton := fun s : ℝ ↦ (s / spf.d) ^ spf.σ
  inv := fun t : ℝ ↦ spf.d * t ^ spf.σ⁻¹
  mon := if spf.σ > 0 then true else false
  ran_ton := fun t ht ↦ rpow_pos_of_pos (div_pos ht spf.hd) _
  ran_inv := fun t ht ↦ mul_pos spf.hd (rpow_pos_of_pos ht spf.σ⁻¹)
  ton_is_ton := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      refine (rpow_lt_rpow_iff ?_ ?_ sgn_σ).mpr ?_
      · exact (div_pos hs spf.hd).le
      · exact (div_pos ht spf.hd).le
      · exact div_lt_div_of_pos_right hst spf.hd
    · simp only [Bool.false_eq_true, ↓reduceIte]
      intro s (hs : s > 0) t (ht : t > 0) hst
      rcases spf.hσ with σ_pos | σ_neg
      · exact (sgn_σ σ_pos).elim
      · simp only
        exact (Real.rpow_lt_rpow_iff_of_neg (div_pos ht spf.hd)
          (div_pos hs spf.hd) σ_neg).mpr (div_lt_div_of_pos_right hst spf.hd)
  inv_pf := by
    split <;> rename_i sgn_σ
    · simp only [↓reduceIte, mem_Ioi]
      refine fun s hs t ht => ⟨?_, ?_⟩
      · rw [← Real.lt_rpow_inv_iff_of_pos (div_nonneg hs.le spf.hd.le) ht.le sgn_σ,
        ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
      · rw [← Real.rpow_inv_lt_iff_of_pos ht.le (div_nonneg hs.le spf.hd.le)
          sgn_σ, ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
    · simp only [↓reduceIte, mem_Ioi]
      intro s hs t ht
      rcases spf.hσ with σ_pos | σ_neg
      · contradiction
      · constructor
        · rw [← Real.rpow_inv_lt_iff_of_neg ht (div_pos hs spf.hd) σ_neg,
            ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']
        · rw [← Real.lt_rpow_inv_iff_of_neg (div_pos hs spf.hd) ht σ_neg,
            ← _root_.mul_lt_mul_left spf.hd, mul_div_cancel₀ _ spf.hd.ne']

end

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [NormedAddCommGroup E]
  [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂]
  [NormedAddCommGroup E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E₁} {t : ℝ}

/-! ## Results about the particular choice of scale

    The proof of the real interpolation theorem will estimate
    `distribution (trunc f A(t)) t` and `distribution (trunc_compl f A(t)) t` for a
    function `A`. The function `A` can be given a closed-form expression that works for
    _all_ cases in the real interpolation theorem, because of the computation rules available
    for elements in `ℝ≥0∞` that avoid the need for a limiting procedure, e.g. `⊤⁻¹ = 0`.

    The function `A` will be of the form `A(t) = (t / d) ^ σ` for particular choices of `d` and
    `σ`. This section contatins results about the scale `d`.
-/
namespace ChoiceScale

def d := ENNReal.toReal
    (C₀ ^ (q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₀⁻¹.toReal * q₁⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) /
    (C₁ ^ (q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal)) * (eLpNorm f p μ ^ p.toReal) ^
      (p₁⁻¹.toReal * q₀⁻¹.toReal / (q₁⁻¹.toReal - q₀⁻¹.toReal))))

lemma d_pos_aux₀ (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    0 < eLpNorm f p μ ^ p.toReal :=
  ENNReal.rpow_pos (pos_of_Ioo hF) (ne_top_of_Ioo hF)

lemma d_ne_top_aux₀ {b : ℝ} {F : ℝ≥0∞} (hF : F ∈ Ioo 0 ⊤) : F ^ b ≠ ⊤ :=
  rpow_ne_top' (ne_zero_of_Ioo hF) (ne_top_of_Ioo hF)

lemma d_ne_zero_aux₀ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.rpow_pos (d_pos_aux₀ hF) (d_ne_top_aux₀ hF)).ne'

lemma d_ne_zero_aux₁ {C : ℝ≥0} {c : ℝ} (hC : C > 0) :
    (ENNReal.ofNNReal C) ^ c ≠ 0 :=
  (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hC) coe_ne_top).ne'

lemma d_ne_zero_aux₂ {C : ℝ≥0} {b c : ℝ} (hC : C > 0)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ 0 :=
  (ENNReal.mul_pos (d_ne_zero_aux₁ hC) (d_ne_zero_aux₀ hF)).ne'

lemma d_ne_top_aux₁ {C : ℝ≥0} {c : ℝ} (hC : C > 0) :
    (ENNReal.ofNNReal C) ^ c ≠ ⊤ :=
  rpow_ne_top' (ENNReal.coe_pos.mpr hC).ne' coe_ne_top

lemma d_ne_top_aux₂ {b : ℝ} (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  rpow_ne_top' (d_pos_aux₀ hF).ne' (d_ne_top_aux₀ hF)

lemma d_ne_top_aux₃ {C : ℝ≥0} {b c : ℝ} (hC : C > 0)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    C ^ c * (eLpNorm f p μ ^ p.toReal) ^ b ≠ ⊤ :=
  mul_ne_top (d_ne_top_aux₁ hC) (d_ne_top_aux₂ hF)

lemma d_ne_zero_aux₃ {b₀ c₀ b₁ c₁ : ℝ} (hC₀ : C₀ > 0) (hC₁ : C₁ > 0) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (C₀ ^ c₀ * (eLpNorm f p μ ^ p.toReal) ^ b₀) /
    (C₁ ^ c₁ * (eLpNorm f p μ ^ p.toReal) ^ b₁) ≠ 0 := by
  refine ENNReal.div_ne_zero.mpr ⟨?_, ?_⟩
  · apply d_ne_zero_aux₂ <;> try assumption
  · apply d_ne_top_aux₃ <;> try assumption

lemma d_ne_top_aux₄ {b₀ c₀ b₁ c₁ : ℝ} (hC₀ : C₀ > 0) (hC₁ : C₁ > 0) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    (C₀ ^ c₀ * (eLpNorm f p μ ^ p.toReal) ^ b₀) /
    (C₁ ^ c₁ * (eLpNorm f p μ ^ p.toReal) ^ b₁) ≠ ⊤ := by
  refine (div_lt_top ?_ ?_).ne
  · apply d_ne_top_aux₃ <;> assumption
  · apply d_ne_zero_aux₂ <;> assumption

-- If the `p`-norm of `f` is positive and finite, then `d` is positive
lemma d_pos (hC₀ : C₀ > 0) (hC₁ : C₁ > 0) (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
  @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f > 0 :=
toReal_pos (d_ne_zero_aux₃ hC₀ hC₁ hF) (d_ne_top_aux₄ hC₀ hC₁ hF)

lemma d_eq_top₀ (hp₀ : p₀ > 0) (hq₁ : q₁ > 0) (hp₀' : p₀ ≠ ⊤) (hq₀' : q₀ = ⊤) (hq₀q₁ : q₀ ≠ q₁):
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f =
    (↑C₀ ^ p₀.toReal * eLpNorm f p μ ^ p.toReal).toReal ^ p₀.toReal⁻¹ := by
  unfold d
  rw [hq₀']
  simp only [inv_top, zero_toReal, sub_zero, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    div_one]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_one]
    · rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg]
      · rw [ENNReal.rpow_rpow_inv, toReal_inv]
        exact (exp_toReal_pos hp₀ hp₀').ne'
      · positivity
    · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₁ ((hq₀' ▸ hq₀q₁).symm)).ne'

lemma d_eq_top₁ (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hp₁' : p₁ ≠ ⊤) (hq₁' : q₁ = ⊤)
    (hq₀q₁ : q₀ ≠ q₁) (hC₁ : C₁ > 0) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f =
    (↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal).toReal ^ p₁.toReal⁻¹ := by
  unfold d
  rw [hq₁']
  simp only [inv_top, zero_toReal, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    one_div]
  rw [div_neg, div_neg]
  rw [mul_div_cancel_right₀]
  · rw [div_eq_mul_inv, mul_inv_cancel₀, ENNReal.rpow_neg_one]
    · rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg]
      · rw [ENNReal.rpow_rpow_inv, ← toReal_inv, ENNReal.mul_inv, inv_inv]
        · rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_mul, toReal_inv, mul_neg, mul_one, neg_neg,
            toReal_mul, coe_toReal]
        · left; exact ENNReal.inv_ne_zero.mpr coe_ne_top
        · left; exact inv_ne_top.mpr <| (ENNReal.coe_pos.mpr hC₁).ne'
        · exact (exp_toReal_pos hp₁ hp₁').ne'
      · positivity
    · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'
  · exact (inv_toReal_pos_of_ne_top hq₀ (hq₁' ▸ hq₀q₁)).ne'

lemma d_eq_top_of_eq (hC₁ : C₁ > 0) (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hq₀' : q₀ ≠ ⊤)
(hp₀': p₀ ≠ ⊤) (hp₁ : p₁ > 0) (hp₀p₁ : p₀ = p₁) (hpp₀: p = p₀) (hq₁' : q₁ = ⊤) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f = (C₁ * eLpNorm f p μ).toReal := by
  rw [d_eq_top₁, ← hp₀p₁, hpp₀] <;> try assumption
  on_goal 1 => rw [toReal_rpow, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_rpow_inv, ENNReal.rpow_rpow_inv]
  · exact exp_toReal_ne_zero' hp₀ hp₀'
  · exact exp_toReal_ne_zero' hp₀ hp₀'
  · positivity
  · exact hp₀p₁ ▸ hp₀'
  · exact hq₁' ▸ hq₀'

lemma d_eq_top_top (hq₀ : q₀ > 0) (hq₀q₁ : q₀ ≠ q₁) (hp₁' : p₁ = ⊤) (hq₁' : q₁ = ⊤) :
    @d α E₁ m p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f = C₁ := by
  unfold d
  rw [hp₁', hq₁']
  simp only [inv_top, zero_toReal, zero_sub, zero_div, ENNReal.rpow_zero, mul_zero, mul_one,
    zero_mul, one_div]
  rw [div_neg, div_eq_mul_inv, mul_inv_cancel₀]
  · rw [ENNReal.rpow_neg, ENNReal.rpow_one, inv_inv, coe_toReal]
  · exact (toReal_pos (ENNReal.inv_ne_zero.mpr (hq₁' ▸ hq₀q₁)) (ENNReal.inv_ne_top.mpr hq₀.ne')).ne'

/-- The particular choice of scaled power function that works in the proof of the
    real interpolation theorem. -/
def spf_ch (ht : t ∈ Ioo 0 1) (hq₀q₁ : q₀ ≠ q₁) (hp₀ : 0 < p₀) (hq₀ : 0 < q₀)
    (hp₁ : 0 < p₁) (hq₁ : 0 < q₁) (hp₀p₁ : p₀ ≠ p₁) (hC₀ : C₀ > 0) (hC₁ : C₁ > 0)
    (hF : eLpNorm f p μ ∈ Ioo 0 ⊤) :
    ScaledPowerFunction where
  σ := @ζ p₀ q₀ p₁ q₁ t
  d := @d _ E₁ _ p p₀ q₀ p₁ q₁ C₀ C₁ μ _ f
  hσ := lt_or_gt_of_ne <| Ne.symm <| (ζ_ne_zero ht hp₀ hq₀ hp₁ hq₁ hp₀p₁ hq₀q₁)
  hd := d_pos hC₀ hC₁ hF

end ChoiceScale

end

noncomputable section

open NNReal ENNReal MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  {f : α → E₁} {t : ℝ}

/-! ## Some tools for measure theory computations
    A collection of small lemmas to help with integral manipulations.
-/
namespace MeasureTheory

-- TODO: change lhs and rhs?
-- TODO: rewrite the condition in filter form?
lemma lintegral_double_restrict_set {A B: Set α} {f : α → ℝ≥0∞} (hA : MeasurableSet A)
  (hB : MeasurableSet B) (hf : ∀ᵐ (x : α) ∂μ, x ∈ A \ B → f x ≤ 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A ∩ B, f x ∂μ := by
  have h₀ := setLIntegral_mono_ae' (MeasurableSet.diff hA hB) hf; rw [lintegral_zero] at h₀
  rw [← lintegral_inter_add_diff (hB := hB), nonpos_iff_eq_zero.mp h₀, add_zero]

lemma measure_preserving_shift {a : ℝ} :
    MeasurePreserving (fun x ↦ a + x) volume volume :=
  measurePreserving_add_left volume a

lemma measureable_embedding_shift {a : ℝ} : MeasurableEmbedding (fun x ↦ a + x) :=
  measurableEmbedding_addLeft a

lemma measure_preserving_scaling {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun x ↦ a * x) volume ((ENNReal.ofReal |a⁻¹|) • volume) :=
  { measurable := measurable_const_mul a, map_eq := Real.map_volume_mul_left ha }

lemma lintegral_shift (f : ℝ → ENNReal) {a : ℝ} :
    ∫⁻ x : ℝ, (f (x + a)) = ∫⁻ x : ℝ, f x :=
  lintegral_add_right_eq_self f a

lemma lintegral_shift' (f : ℝ → ENNReal) {a : ℝ} {s : Set ℝ}:
    ∫⁻ (x : ℝ) in (fun z : ℝ ↦ z + a)⁻¹' s, f (x + a) = ∫⁻ (x : ℝ) in s, f x := by
  rw [(measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight a)]

lemma lintegral_add_right_Ioi (f : ℝ → ENNReal) {a b : ℝ} :
    ∫⁻ (x : ℝ) in Ioi (b - a), f (x + a) = ∫⁻ (x : ℝ) in Ioi b, f x := by
  nth_rewrite 2 [← lintegral_shift' (a := a)]
  simp

lemma lintegral_scale_constant (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0):
    ∫⁻ x : ℝ, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, f x := by
  rw [← @lintegral_smul_measure, MeasurePreserving.lintegral_comp_emb]
  · exact measure_preserving_scaling h
  · exact measurableEmbedding_mulLeft₀ h

lemma lintegral_scale_constant_preimage (f: ℝ → ENNReal) {a : ℝ} (h : a ≠ 0)
    {s : Set ℝ}:
    ∫⁻ x : ℝ in (fun z : ℝ ↦ a * z)⁻¹' s, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in s, f x
    := by
  rw [← lintegral_smul_measure,
    (measure_preserving_scaling h).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft₀ h),
    Measure.restrict_smul]

lemma lintegral_scale_constant_halfspace (f: ℝ → ENNReal) {a : ℝ} (h : 0 < a) :
    ∫⁻ x : ℝ in Ioi 0, f (a*x) = ENNReal.ofReal |a⁻¹| * ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [← lintegral_scale_constant_preimage f h.ne']
  have h₀ : (fun z ↦ a * z) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x
    simp [mul_pos_iff_of_pos_left h]
  rw [h₀]

lemma lintegral_scale_constant_halfspace' {f: ℝ → ENNReal} {a : ℝ} (h : 0 < a) :
    ENNReal.ofReal |a| * ∫⁻ x : ℝ in Ioi 0, f (a*x) = ∫⁻ x : ℝ in Ioi 0, f x := by
  rw [lintegral_scale_constant_halfspace f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a),
    abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h.ne')]
  simp

lemma lintegral_scale_constant' {f: ℝ → ENNReal} {a : ℝ} (h : a ≠ 0):
    ENNReal.ofReal |a| * ∫⁻ x : ℝ, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_scale_constant f h, ← mul_assoc, ← ofReal_mul (abs_nonneg a), abs_inv,
      mul_inv_cancel₀ (abs_ne_zero.mpr h)]
  simp

-- local convenience function
lemma lintegral_rw_aux {g : ℝ → ℝ≥0∞} {f₁ f₂ : ℝ → ℝ≥0∞} {A : Set ℝ}
    (heq : f₁ =ᶠ[ae (volume.restrict A)] f₂) :
    ∫⁻ s in A, g s * f₁ s = ∫⁻ s in A, g s * f₂ s :=
  (lintegral_rw₂ (Filter.EventuallyEq.refl (ae (volume.restrict A)) g) heq HMul.hMul)

lemma power_aux {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ (p + q)) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal s ^ p * ENNReal.ofReal s ^ q ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : s > 0)
  rw [ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs, ofReal_rpow_of_pos hs,
    ← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma power_aux_2 {p q : ℝ} :
    (fun s ↦ ENNReal.ofReal (s ^ (p + q))) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p) * ENNReal.ofReal (s ^ q) ) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s (hs : s > 0)
  rw [← ofReal_mul (by positivity), ← Real.rpow_add hs]

lemma ofReal_rpow_of_pos_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : s > 0) using ofReal_rpow_of_pos hs

lemma extract_constant_double_integral_rpow {f : ℝ → ℝ → ℝ≥0∞} {q : ℝ} (hq : q ≥ 0) {a : ℝ≥0∞}
    (ha : a ≠ ⊤):
    ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, a * f s t) ^ q =
    a ^ q * ∫⁻ (s : ℝ) in Ioi 0, (∫⁻ (t : ℝ) in Ioi 0, f s t) ^ q := by
  simp_rw [← lintegral_const_mul' _ _ (rpow_ne_top_of_nonneg hq ha),
    ← ENNReal.mul_rpow_of_nonneg _ _ hq, lintegral_const_mul' a _ ha]

lemma ofReal_rpow_rpow_aux {p : ℝ} :
    (fun s ↦ ENNReal.ofReal s ^ p) =ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
    (fun s ↦ ENNReal.ofReal (s ^ p)) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    with s (hs : s > 0) using ofReal_rpow_of_pos hs

lemma lintegral_rpow_of_gt {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / (γ + 1)) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hβ.le, integral_rpow]
    · rw [Real.zero_rpow hγ2.ne', sub_zero]
    · exact Or.inl hγ
  · apply (@intervalIntegral.intervalIntegrable_rpow' 0 β γ ?_).1
    linarith
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc]
      with s hs using Real.rpow_nonneg hs.1.le γ

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞} {c : ℝ≥0} {a : ℝ}
  {μ : Measure α} {ν : Measure α'}
  {f : α → E₁} {t : ℝ}

/-! ## Results about truncations of a function
-/
namespace MeasureTheory

/-- The `t`-truncation of a function `f`. -/
def trunc [NormedAddCommGroup E₁] (f : α → E₁) (t : ℝ) (x : α) : E₁ := if ‖f x‖ ≤ t then f x else 0

/-- The complement of a `t`-truncation of a function `f`. -/
def trunc_compl [NormedAddCommGroup E₁] (f : α → E₁) (t : ℝ) : α → E₁ := f - trunc f t

lemma trunc_compl_eq [NormedAddCommGroup E₁] {a : ℝ} {f : α → E₁} :
    f - trunc f a = fun x ↦ if a < ‖f x‖ then f x else 0 := by
  ext x
  simp_rw [Pi.sub_apply, trunc, ← not_lt, ite_not, apply_ite (f x - ·), sub_zero, sub_self]

/-- A function to deal with truncations and complement of truncations in one go. -/
def trnc [NormedAddCommGroup E₁] (j : Bool) (f : α → E₁) (t : ℝ)  : α → E₁ :=
  match j with
  | false => f - trunc f t
  | true => trunc f t

/-- A function is the complement if its truncation and the complement of the truncation. -/
lemma trunc_buildup [NormedAddCommGroup E₁] : f = trunc f t + trunc_compl f t := by
  ext x; simp [trunc, trunc_compl]

/-- If the truncation parameter is non-positive, the truncation vanishes. -/
lemma trunc_of_nonpos {f : α → E₁} {a : ℝ} [NormedAddCommGroup E₁] (ha : a ≤ 0) :
    trunc f a = 0 := by
  unfold trunc
  ext x
  split_ifs
  · dsimp only [Pi.zero_apply]
    apply norm_eq_zero.mp
    · have : ‖f x‖ ≥ 0 := norm_nonneg _
      linarith []
  · rfl

/-- If the truncation parameter is non-positive, the complement of the truncation is the
    function itself. -/
lemma trunc_compl_of_nonpos {f : α → E₁} {a : ℝ} [NormedAddCommGroup E₁] (ha : a ≤ 0) :
    trunc_compl f a = f := by
  unfold trunc_compl
  rw [trunc_compl_eq]
  ext x
  dsimp only [Pi.zero_apply]
  split_ifs
  · rfl
  · apply (norm_eq_zero.mp ?_).symm
    have : ‖f x‖ ≥ 0 := norm_nonneg _
    linarith

/-! ## Measurability properties of truncations -/

-- @[measurability, fun_prop]
-- lemma _root_.Measurable.trunc [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : Measurable f) : Measurable (trunc f t) := by
--   refine hf.ite (measurableSet_le ?_ ?_) measurable_const <;> fun_prop

-- @[measurability, fun_prop]
-- lemma _root_.Measurable.trunc_compl [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : Measurable f) :
--     Measurable (f - trunc f t) := by
--   rw [trunc_compl_eq]
--   apply Measurable.ite ?_ hf measurable_const
--   exact measurableSet_lt measurable_const hf.norm

@[measurability]
protected lemma StronglyMeasurable.trunc [NormedAddCommGroup E₁]
    (hf : StronglyMeasurable f) : StronglyMeasurable (trunc f t) :=
  StronglyMeasurable.ite (measurableSet_le hf.norm stronglyMeasurable_const) hf
    stronglyMeasurable_const

@[measurability]
protected lemma StronglyMeasurable.trunc_compl [NormedAddCommGroup E₁]
    (hf : StronglyMeasurable f) : StronglyMeasurable (f - trunc f t) := by
  rw [trunc_compl_eq]
  exact hf.ite (measurableSet_lt stronglyMeasurable_const hf.norm) stronglyMeasurable_const

-- @[measurability, fun_prop]
-- lemma aemeasurable_trunc [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : AEMeasurable f μ) :
--     AEMeasurable (trunc f t) μ := by
--   rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
--   exists (trunc g t)
--   constructor
--   · apply wg1.indicator (s := {x | ‖g x‖ ≤ t}) (measurableSet_le wg1.norm measurable_const)
--   apply measure_mono_null ?_ wg2
--   intro x
--   contrapose
--   simp only [mem_compl_iff, mem_setOf_eq, not_not]
--   intro h₂
--   unfold trunc
--   rewrite [h₂]
--   rfl

-- @[measurability, fun_prop]
-- lemma aeMeasurable_trunc_compl [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
--     (hf : AEMeasurable f μ) :
--     AEMeasurable (trunc_compl f t) μ := by
--   rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
--   exists (trunc_compl g t)
--   constructor
--   · unfold trunc_compl
--     rw [trunc_compl_eq]
--     exact wg1.indicator (s := {x | t < ‖g x‖}) (measurableSet_lt measurable_const wg1.norm)
--   · apply measure_mono_null ?_ wg2
--     intro x
--     contrapose
--     simp only [mem_compl_iff, mem_setOf_eq, not_not]
--     intro f_eq_g; unfold trunc_compl; unfold trunc; dsimp only [Pi.sub_apply]; rw [f_eq_g]

@[measurability]
lemma aestronglyMeasurable_trunc [NormedAddCommGroup E₁]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (trunc g t)
  constructor
  · exact wg1.indicator (s := {x | ‖g x‖ ≤ t}) (wg1.norm.measurableSet_le stronglyMeasurable_const)
  · refine measure_mono_null (fun x ↦ ?_) wg2
    contrapose
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    intro h₂
    unfold trunc
    rw [h₂]

@[measurability]
lemma aestronglyMeasurable_trunc_compl [NormedAddCommGroup E₁]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (f - trunc f t) μ := by
  rcases hf with ⟨g, ⟨wg1, wg2⟩⟩
  exists (g - trunc g t)
  constructor
  · rw [trunc_compl_eq]
    exact wg1.indicator (s := {x | t < ‖g x‖}) (stronglyMeasurable_const.measurableSet_lt wg1.norm)
  · apply measure_mono_null ?_ wg2
    intro x
    contrapose
    simp only [mem_compl_iff, mem_setOf_eq, not_not]
    intro h₂
    rw [trunc_compl_eq, trunc_compl_eq]
    simp only
    rw [h₂]

@[measurability]
lemma aestronglyMeasurable_trnc {j : Bool} [NormedAddCommGroup E₁]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trnc j f t) μ := by
  rcases j
  · exact aestronglyMeasurable_trunc_compl hf
  · exact aestronglyMeasurable_trunc hf

lemma trunc_le {f : α → E₁} {a : ℝ} [NormedAddCommGroup E₁] (x : α) :
    ‖trunc f a x‖ ≤ max 0 a := by
  unfold trunc
  split_ifs with h
  · rcases (lt_or_le a 0) with a_lt_0 | _
    · exact Trans.trans (Trans.trans h a_lt_0.le) (le_max_left 0 a)
    · exact Trans.trans h (le_max_right 0 a)
  · simp

/-- A small lemma that is helpful for rewriting -/
lemma coe_coe_eq_ofReal (a : ℝ) : ofNNReal a.toNNReal = ENNReal.ofReal a := by rfl

lemma trunc_eLpNormEssSup_le {f : α → E₁} {a : ℝ} [NormedAddCommGroup E₁] :
    eLpNormEssSup (trunc f a) μ ≤ ENNReal.ofReal (max 0 a) := by
  refine essSup_le_of_ae_le _ (ae_of_all _ fun x ↦ ?_)
  simp only [enorm_eq_nnnorm, ← norm_toNNReal, coe_coe_eq_ofReal]
  exact ofReal_le_ofReal (trunc_le x)

lemma trunc_mono {f : α → E₁} {a b : ℝ} [NormedAddCommGroup E₁]
    (hab : a ≤ b) {x : α} : ‖trunc f a x‖ ≤ ‖trunc f b x‖ := by
  unfold trunc
  split_ifs
  · rfl
  · linarith
  · rw [norm_zero]; exact norm_nonneg _
  · exact le_refl _

/-- The norm of the truncation is monotone in the truncation parameter -/
lemma norm_trunc_mono {f : α → E₁} [NormedAddCommGroup E₁] :
    Monotone fun s ↦ eLpNorm (trunc f s) p μ :=
  fun _a _b hab ↦ eLpNorm_mono fun _x ↦ trunc_mono hab

lemma trunc_buildup_norm {f : α → E₁} {a : ℝ} {x : α} [NormedAddCommGroup E₁] :
    ‖trunc f a x‖ + ‖(f - trunc f a) x‖ = ‖f x‖ := by
  simp only [trunc, Pi.sub_apply]; split_ifs with h <;> simp

lemma trunc_le_func {f : α → E₁} {a : ℝ} {x : α} [NormedAddCommGroup E₁] :
    ‖trunc f a x‖ ≤ ‖f x‖ := by
  unfold trunc; split_ifs <;> simp

lemma trunc_compl_le_func {f : α → E₁} {a : ℝ} {x : α} [NormedAddCommGroup E₁] :
    ‖(f - trunc f a) x‖ ≤ ‖f x‖ := by
  rw [trunc_compl_eq]; dsimp only; split_ifs <;> simp

lemma trunc_compl_anti {f : α → E₁} {a b : ℝ} {x : α} [NormedAddCommGroup E₁] (hab : a ≤ b) :
    ‖(f - trunc f b) x‖ ≤ ‖(f - trunc f a) x‖ := by
  have obs : ‖trunc f a x‖ + ‖(f - trunc f a) x‖ = ‖trunc f b x‖ + ‖(f - trunc f b) x‖ := by
    rw [trunc_buildup_norm, trunc_buildup_norm]
  have : ‖trunc f a x‖ ≤ ‖trunc f b x‖ := trunc_mono hab
  linarith

/-- The norm of the complement of the truncation is antitone in the truncation parameter -/
lemma norm_trunc_compl_anti {f : α → E₁} [NormedAddCommGroup E₁] :
    Antitone (fun s ↦ eLpNorm (f - trunc f s) p μ) :=
  fun _a _b hab ↦ eLpNorm_mono (fun _ ↦ trunc_compl_anti hab)

/-- The norm of the truncation is meaurable in the truncation parameter -/
@[measurability, fun_prop]
lemma norm_trunc_measurable [NormedAddCommGroup E₁] :
    Measurable (fun s ↦ eLpNorm (trunc f s) p μ) :=
  norm_trunc_mono.measurable

/-- The norm of the complement of the truncation is measurable in the truncation parameter -/
@[measurability, fun_prop]
lemma norm_trunc_compl_measurable [NormedAddCommGroup E₁] :
    Measurable (fun s ↦ eLpNorm (f - trunc f s) p μ) :=
  norm_trunc_compl_anti.measurable

lemma trnc_le_func {j : Bool} {f : α → E₁} {a : ℝ} {x : α} [NormedAddCommGroup E₁] :
    ‖trnc j f a x‖ ≤ ‖f x‖ := by
  unfold trnc trunc
  rcases j
  · dsimp only [Pi.sub_apply]
    split_ifs <;> simp
  · dsimp only
    split_ifs <;> simp

-- /-- ## Distribution functions of truncations -/

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

/-! ## Truncations and L-p spaces -/

lemma power_estimate {a b t γ : ℝ} (hγ : γ > 0) (htγ : γ ≤ t) (hab : a ≤ b) :
    (t / γ) ^ a ≤ (t / γ) ^ b := by
  gcongr
  exact (one_le_div hγ).mpr htγ

lemma power_estimate' {a b t γ : ℝ} (ht : t > 0) (htγ : t ≤ γ) (hab: a ≤ b) :
    (t / γ) ^ b ≤ (t / γ) ^ a := by
  have γ_pos : γ > 0 := lt_of_lt_of_le ht htγ
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos ht (γ_pos)) (div_le_one_of_le₀ htγ γ_pos.le) hab

lemma rpow_le_rpow_of_exponent_le_base_le {a b t γ : ℝ} (ht : t > 0) (htγ : t ≤ γ) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ b) ≤ ENNReal.ofReal (t ^ a) * ENNReal.ofReal (γ ^ (b - a)) := by
  rw [mul_comm]
  have γ_pos : 0 < γ := lt_of_lt_of_le ht htγ
  rw [Real.rpow_sub γ_pos]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-b) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos γ_pos (-b))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (power_estimate' ht htγ hab)

-- TODO: there is a lot of overlap between above proof and below
lemma rpow_le_rpow_of_exponent_le_base_ge {a b t γ : ℝ} (hγ : γ > 0) (htγ : γ ≤ t) (hab : a ≤ b) :
    ENNReal.ofReal (t ^ a) ≤ ENNReal.ofReal (t ^ b) * ENNReal.ofReal (γ ^ (a - b)) := by
  rw [mul_comm]
  have t_pos : 0 < t := gt_of_ge_of_gt htγ hγ
  rw [Real.rpow_sub hγ]
  refine (ENNReal.mul_le_mul_left (a := ENNReal.ofReal (γ ^ (-a) )) ?_ coe_ne_top).mp ?_
  · exact (ofReal_pos.mpr (Real.rpow_pos_of_pos hγ (-a))).ne'
  · rw [← ofReal_mul, ← mul_assoc, ← ofReal_mul, ← mul_div_assoc, ← Real.rpow_add, neg_add_cancel,
        Real.rpow_zero, ← ofReal_mul, mul_comm] <;> try positivity
    nth_rw 2 [mul_comm]
    rw [← neg_one_mul, Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow] <;> try positivity
    rw [one_div]
    nth_rw 2 [← Real.rpow_neg_one]
    rw [← Real.rpow_mul (by positivity)]
    nth_rw 3 [mul_comm]
    rw [Real.rpow_mul, Real.rpow_neg_one, ← Real.mul_rpow, ← div_eq_mul_inv] <;> try positivity
    exact ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le ((one_le_div hγ).mpr htγ) hab)

lemma trunc_preserves_Lp {p : ℝ≥0∞} {a : ℝ} [NormedAddCommGroup E₁]
    (hf : Memℒp f p μ) :
    Memℒp (trunc f a) p μ := by
  refine ⟨aestronglyMeasurable_trunc hf.1, lt_of_le_of_lt (eLpNorm_mono_ae (ae_of_all _ ?_)) hf.2⟩
  intro x
  unfold trunc
  split_ifs with is_fx_le_a <;> simp

-- lemma snorm_trunc_compl_le {p : ℝ≥0∞} {a : ℝ} [NormedAddCommGroup E₁] :
--     eLpNorm (f - trunc f a) p μ ≤ eLpNorm f p μ :=
--   eLpNorm_mono (fun _ ↦ trunc_compl_le_func)

lemma trunc_compl_preserves_Lp {p : ℝ≥0∞} {a : ℝ} [NormedAddCommGroup E₁] (hf : Memℒp f p μ) :
    Memℒp (f - trunc f a) p μ :=
  Memℒp.sub hf (trunc_preserves_Lp hf)

lemma estimate_eLpNorm_trunc_compl {p q : ℝ≥0∞} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] (hp : p ≠ ⊤) (hpq : q ∈ Ioo 0 p) (hf : AEMeasurable f μ) (ha : a > 0) :
    eLpNorm ((f - trunc f a)) q μ ^ q.toReal ≤
    ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
    eLpNorm f p μ ^ p.toReal := by
  unfold eLpNorm eLpNorm'
  have q_ne_top: q ≠ ⊤ := hpq.2.ne_top
  have p_ne_zero : p ≠ 0 := (lt_trans hpq.1 hpq.2).ne'
  have q_ne_zero : q ≠ 0 := hpq.1.ne'
  have q_toReal_pos : q.toReal > 0 := exp_toReal_pos hpq.1 q_ne_top
  split_ifs
  · contradiction
  · calc
    _ = ∫⁻ x : α in {x | a < ‖f x‖}, ‖(f - trunc f a) x‖ₑ ^ q.toReal ∂μ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      · apply (setLIntegral_eq_of_support_subset _).symm
        unfold Function.support
        intro x
        rw [trunc_compl_eq]
        dsimp only [Pi.sub_apply, mem_setOf_eq]
        split_ifs with is_a_lt_fx
        · exact fun _ => is_a_lt_fx
        · contrapose; intro _; simpa [enorm_eq_nnnorm]
      · exact exp_toReal_ne_zero' hpq.1 q_ne_top
    _ ≤ ∫⁻ x : α in {x | a < ‖f x‖}, ‖f x‖ₑ ^ q.toReal ∂μ := by
      apply lintegral_mono_ae
      apply ae_of_all
      intro x
      gcongr
      rw [enorm_eq_nnnorm, ← norm_toNNReal, enorm_eq_nnnorm, ← norm_toNNReal]
      simp only [Pi.sub_apply, ENNReal.coe_le_coe, norm_nonneg, Real.toNNReal_le_toNNReal_iff]
      apply trnc_le_func (j := ⊥)
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * ∫⁻ x : α in {x | a < ‖f x‖},
        ‖f x‖ₑ ^ p.toReal ∂μ := by
      rw [← lintegral_const_mul']; swap; · exact coe_ne_top
      simp only [enorm_eq_nnnorm]
      apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
      · apply ae_of_all
        intro x (hx : a < ‖f x‖)
        rw [mul_comm]
        rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm (f x), ENNReal.ofReal_rpow_of_nonneg,
          ENNReal.ofReal_rpow_of_nonneg]
          <;> try positivity
        exact rpow_le_rpow_of_exponent_le_base_ge ha hx.le (toReal_mono hp hpq.2.le)
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * ∫⁻ x : α,
        ↑‖f x‖₊ ^ p.toReal ∂μ := by
      gcongr
      exact setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      · simp only [enorm_eq_nnnorm]
      · exact exp_toReal_ne_zero' (lt_trans hpq.1 hpq.2) hp

lemma estimate_eLpNorm_trunc {p q : ℝ≥0∞}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hq : q ≠ ⊤)
    (hpq : p ∈ Ioo 0 q) (hf : AEMeasurable f μ) :
    eLpNorm (trunc f a) q μ ^ q.toReal ≤
    ENNReal.ofReal (a ^ (q.toReal - p.toReal)) * eLpNorm f p μ ^ p.toReal := by
  unfold eLpNorm eLpNorm'
  have p_ne_top : p ≠ ⊤ := hpq.2.ne_top
  have : p ≠ 0 := hpq.1.ne'
  have : q ≠ 0 := (lt_trans hpq.1 hpq.2).ne'
  split_ifs
  · contradiction
  · calc
    _ = ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ↑‖trunc f a x‖₊ ^ q.toReal ∂μ := by
      rw [one_div, ENNReal.rpow_inv_rpow]
      · apply Eq.symm
        apply setLIntegral_eq_of_support_subset
        unfold Function.support
        intro x
        dsimp only [Pi.sub_apply, mem_setOf_eq]
        unfold trunc
        split_ifs with is_fx_le_a
        · intro fx_rpow_ne_zero
          refine ⟨?_, is_fx_le_a⟩
          contrapose! fx_rpow_ne_zero
          rw [norm_le_zero_iff.mp fx_rpow_ne_zero]
          simpa using toReal_pos this hq
        · contrapose; intro _; simpa using toReal_pos this hq
      · exact exp_toReal_ne_zero' (lt_trans hpq.1 hpq.2) hq
    _ ≤ ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ‖f x‖₊ ^ q.toReal ∂ μ := by
      apply lintegral_mono_ae
      apply ae_of_all
      intro x
      gcongr
      rw [← norm_toNNReal, ← norm_toNNReal]
      exact Real.toNNReal_mono (trnc_le_func (j := ⊤))
    _ ≤ ENNReal.ofReal (a ^ (q.toReal - p.toReal)) *
        ∫⁻ (x : α) in {x | 0 < ‖f x‖ ∧ ‖f x‖ ≤ a}, ‖f x‖₊ ^ p.toReal ∂ μ := by
      rw [← lintegral_const_mul']
      · apply setLIntegral_mono_ae (AEMeasurable.restrict (by fun_prop))
        · apply ae_of_all
          intro x hx
          rw [mul_comm]
          rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm (f x), ENNReal.ofReal_rpow_of_nonneg,
            ENNReal.ofReal_rpow_of_nonneg] <;> try positivity
          apply rpow_le_rpow_of_exponent_le_base_le hx.1 hx.2
          exact toReal_mono hq hpq.2.le
      · exact coe_ne_top
    _ ≤ _ := by
      gcongr
      rw [one_div, ENNReal.rpow_inv_rpow]
      · exact setLIntegral_le_lintegral _ _
      · exact exp_toReal_ne_zero' hpq.1 p_ne_top

/-- If `f` is in `Lp`, the truncation is element of `Lq` for `q > p`. -/
lemma trunc_Lp_Lq_higher [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hpq : p ∈ Ioo 0 q) (hf : Memℒp f p μ) :
    Memℒp (trnc ⊤ f a) q μ := by
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  rcases (eq_or_ne q ⊤) with q_eq_top | q_ne_top
  · rw [q_eq_top, eLpNorm_exponent_top]
    exact Trans.trans trunc_eLpNormEssSup_le coe_lt_top
  · rw [← rpow_lt_top_iff_of_pos (toReal_pos (lt_trans hpq.1 hpq.2).ne' q_ne_top)]
    apply lt_of_le_of_lt (estimate_eLpNorm_trunc q_ne_top hpq hf.1.aemeasurable)
    apply mul_lt_top coe_lt_top
    refine (rpow_lt_top_iff_of_pos ?_).mpr hf.2
    exact toReal_pos hpq.1.ne' hpq.2.ne_top

/-- If `f` is in `Lp`, the complement of the truncation is in `Lq` for `q < p`. -/
lemma trunc_compl_Lp_Lq_lower [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hp : p ≠ ⊤)
    (hpq : q ∈ Ioo 0 p) (ha : a > 0) (hf : Memℒp f p μ) :
    Memℒp (trnc ⊥ f a) q μ := by
  refine ⟨aestronglyMeasurable_trnc hf.1, ?_⟩
  have : q.toReal > 0 := toReal_pos hpq.left.ne' hpq.right.ne_top
  refine (rpow_lt_top_iff_of_pos this).mp ?_
  refine lt_of_le_of_lt
    (estimate_eLpNorm_trunc_compl hp hpq hf.1.aemeasurable ha) ?_
  apply mul_lt_top coe_lt_top
  refine (rpow_lt_top_iff_of_pos ?_).mpr hf.2
  exact toReal_pos (lt_trans hpq.left hpq.right).ne' hp

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [NormedAddCommGroup E]
  [NormedAddCommGroup E₁]
  [NormedAddCommGroup E₂]
  [MeasurableSpace E] [BorelSpace E]
  {f : α → E₁} {t : ℝ}

/-! ## Some results about the integrals of truncations

-/
namespace MeasureTheory

def res (j : Bool) (β : ℝ) : Set ℝ :=
  if j then Ioo (0 : ℝ) β else Ioi β

lemma measurableSet_res {j : Bool} {β : ℝ} : MeasurableSet (res j β) := by
  unfold res
  split
  · exact measurableSet_Ioo
  · exact measurableSet_Ioi

lemma res_subset_Ioi {j : Bool} {β : ℝ} (hβ : β > 0) : res j β ⊆ Ioi 0 := by
  unfold res
  split
  · exact Ioo_subset_Ioi_self
  · simp only [Ioi, setOf_subset_setOf]
    intro s hs
    linarith

instance decidableMemRes {j : Bool} {β : ℝ} : Decidable (t ∈ res j β) := by
  exact Classical.propDecidable (t ∈ res j β)

def res' (j : Bool) (β : ℝ) : Set ℝ :=
  if j then Ioc (0 : ℝ) β else Ici β

lemma res'comp (j : Bool) (β : ℝ) (hβ : β > 0) :
    Ioi (0 : ℝ) \ res' j β = res (¬j) β := by
  unfold res' res
  split_ifs with h₀ h₁ h₂
  · rw [h₀] at h₁; simp at h₁
  · ext x
    simp only [mem_diff, mem_Ioi, mem_Ioc, not_and, not_le]
    constructor
    · tauto
    · intro h
      exact ⟨lt_trans hβ h, fun _ ↦ h⟩
  · ext x
    simp only [Ioi_diff_Ici, mem_Ioo]
  · have : j = false := eq_false_of_ne_true h₀
    rw [this] at h₂
    simp at h₂

lemma measurableSet_res' {j : Bool} {β : ℝ} : MeasurableSet (res' j β) := by
  unfold res'
  measurability

lemma res'subset_Ioi {j : Bool} {β : ℝ} (hβ : β > 0) : res' j β ⊆ Ioi 0 := by
  unfold res'
  split
  · exact Ioc_subset_Ioi_self
  · exact Ici_subset_Ioi.mpr hβ

lemma lintegral_trunc_mul₀ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ} (hp : p > 0)
    (hfx : ‖f x‖₊ > 0) :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p =
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p := by
  rw [lintegral_double_restrict_set (B := res' (xor j tc.mon) (tc.inv ‖f x‖))
      measurableSet_Ioi measurableSet_res']
  · have : Ioi 0 ∩ res' (xor j tc.mon) (tc.inv ‖f x‖) = res' (xor j tc.mon) (tc.inv ‖f x‖) := by
      refine inter_eq_self_of_subset_right (res'subset_Ioi (tc.ran_inv (‖f x‖) hfx))
    rw [this]
  · apply ae_of_all
    rw [res'comp]
    · intro s
      unfold res trnc trunc
      have mon_pf := tc.inv_pf
      split_ifs at mon_pf with mon
      · rw [mon]
        rcases j
        · simp only [Bool.bne_true, Bool.not_false, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
          intro (hs : s > tc.inv ‖f x‖)
          split_ifs with h
          · simp [hp]
          · have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).2.mpr hs
            contrapose! h; linarith
        · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true]
          intro hs
          split_ifs with h
          · have := (mon_pf s hs.1 (‖f x‖) hfx).1.mpr hs.2
            linarith
          · simp [hp]
      · rw [Bool.not_eq_true] at mon
        rw [mon]
        rcases j
        · simp only [bne_self_eq_false, Bool.false_eq_true, not_false_eq_true, decide_true,
          ↓reduceIte, Pi.sub_apply]
          intro hs
          split_ifs with h
          · simp [hp]
          · have := (mon_pf s hs.1 (‖f x‖) hfx).2.mpr hs.2
            linarith
        · simp only [Bool.bne_false, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          intro (hs : tc.inv ‖f x‖ < s)
          have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).1.mpr hs
          split_ifs with h
          · linarith
          · simp [hp]
    · exact tc.ran_inv ‖f x‖ hfx

lemma lintegral_trunc_mul₁ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple} :
    ∫⁻ s : ℝ in res' (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p := by
  apply setLIntegral_congr
  unfold res res'
  split_ifs
  · exact Ioo_ae_eq_Ioc.symm
  · exact Ioi_ae_eq_Ici.symm

lemma lintegral_trunc_mul₂ {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {p : ℝ} {tc : ToneCouple}
    (hfx : ‖f x‖ > 0) :
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p =
    ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s) * ‖f x‖₊ ^ p := by
  apply setLIntegral_congr_fun measurableSet_res
  · apply ae_of_all
    unfold res trnc trunc
    have mon_pf := tc.inv_pf
    split_ifs at mon_pf with mon
    · rw [mon]
      rcases j
      · simp only [Bool.bne_true, Bool.not_false, ↓reduceIte, Pi.sub_apply]
        intro s hs
        split_ifs with h
        · have := (mon_pf s hs.1 (‖f x‖) hfx).1.mpr hs.2
          contrapose! h; linarith
        · simp
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        intro s (hs : s > tc.inv ‖f x‖)
        split_ifs with h
        · rfl
        · have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).2.mpr hs
          contrapose! h; linarith
    · rw [Bool.not_eq_true] at mon
      rw [mon]
      rcases j
      · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
        intro s (hs : tc.inv ‖f x‖ < s)
        have := (mon_pf s (lt_trans (tc.ran_inv ‖f x‖ hfx) hs) (‖f x‖) hfx).1.mpr hs
        split_ifs with h
        · linarith
        · simp
      · simp only [Bool.bne_false, ↓reduceIte]
        intro s hs
        have := (mon_pf s hs.1 (‖f x‖) hfx).2.mpr hs.2
        split_ifs with h
        · rfl
        · linarith

lemma lintegral_trunc_mul {g : ℝ → ℝ≥0∞} {j : Bool} {x : α} {tc : ToneCouple} {p : ℝ}
    (hp : p > 0) (hfx : ‖f x‖₊ > 0) :
    ∫⁻ s : ℝ in Ioi 0, (g s) * ‖trnc j f (tc.ton s) x‖₊ ^ p =
    (∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv ‖f x‖), (g s)) * ‖f x‖₊ ^ p := by
  rw [lintegral_trunc_mul₀ hp hfx, lintegral_trunc_mul₁, lintegral_trunc_mul₂ hfx,
    lintegral_mul_const']
  exact ((rpow_lt_top_iff_of_pos hp).mpr coe_lt_top).ne

/-! Extract expressions for the lower Lebesgue integral of power functions -/

lemma lintegral_rpow_of_gt_abs {β γ : ℝ} (hβ : β > 0) (hγ : γ > -1) :
    ∫⁻ s : ℝ in Ioo 0 β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  have hγ2 : γ + 1 > 0 := by linarith
  rw [abs_of_nonneg hγ2.le]
  exact lintegral_rpow_of_gt hβ hγ

-- TODO: treat symmetrically to Ioo case?
lemma lintegral_Ioi_rpow_of_lt_abs {β σ : ℝ} (hβ : β > 0) (hσ : σ < -1):
    ∫⁻ s : ℝ in Ioi β, ENNReal.ofReal (s ^ σ) =
    ENNReal.ofReal (β ^ (σ + 1) / |σ + 1|) := by
  have hσ2 : σ + 1 < 0 := by linarith
  rw [abs_of_neg hσ2, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioi_rpow_of_lt hσ hβ, div_neg, neg_div]
  · apply integrableOn_Ioi_rpow_of_lt hσ hβ
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi]
    exact fun s hs ↦ Real.rpow_nonneg (lt_trans hβ hs).le σ

lemma lintegral_rpow_abs {j : Bool} {tc : ToneCouple} {γ : ℝ} {t : ℝ}
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) (ht : t > 0) :
  ∫⁻ s : ℝ in res (xor j tc.mon) (tc.inv t), ENNReal.ofReal s ^ γ =
    ENNReal.ofReal ((tc.inv t) ^ (γ + 1) / |γ + 1|) := by
  rw [← lintegral_congr_ae (Filter.mp_mem (self_mem_ae_restrict measurableSet_res)
      (Filter.univ_mem'
      (fun s hs ↦ (ofReal_rpow_of_pos (res_subset_Ioi (tc.ran_inv t ht) hs)).symm)))]
  unfold res
  split at hγ <;> rename_i xor_split
  · rw [xor_split]
    simp only [↓reduceIte]
    rw [lintegral_rpow_of_gt_abs (tc.ran_inv t ht) hγ]
  · rw [eq_false_of_ne_true xor_split]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lintegral_Ioi_rpow_of_lt_abs (tc.ran_inv t ht) hγ]

lemma value_lintegral_res₀ {j : Bool} {β γ : ℝ} {tc : ToneCouple} (hβ : β > 0)
    (hγ : if xor j tc.mon then γ > -1 else γ < -1 ) :
    ∫⁻ s : ℝ in res (xor j tc.mon) β, ENNReal.ofReal (s ^ γ) =
    ENNReal.ofReal (β ^ (γ + 1) / |γ + 1|) := by
  unfold res
  split_ifs at hγ with h
  · rw [h]
    simp only [↓reduceIte]
    rw [lintegral_rpow_of_gt_abs hβ hγ]
  · have : xor j tc.mon = false := by
      contrapose! h; exact eq_true_of_ne_false h
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [lintegral_Ioi_rpow_of_lt_abs hβ hγ]

lemma value_lintegral_res₁ {t γ p': ℝ} {spf : ScaledPowerFunction} (ht : t > 0) :
    ENNReal.ofReal (((spf_to_tc spf).inv t) ^ (γ + 1) / |γ + 1| ) * ENNReal.ofReal (t ^ p') =
    ENNReal.ofReal (spf.d ^ (γ + 1) * t ^ (spf.σ⁻¹ * (γ + 1) + p') / |γ + 1|) := by
  have := spf.hd
  unfold spf_to_tc
  dsimp only
  rw [← ENNReal.ofReal_mul, ← mul_div_right_comm, Real.mul_rpow, mul_assoc, ← Real.rpow_mul,
      ← Real.rpow_add] <;> positivity

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set ComputationsInterpolatedExponents
    ComputationsChoiceExponent

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}
  {f : α → E₁} {t : ℝ}

/-! ## Minkowski's integral inequality -/
namespace MeasureTheory

lemma rpow_add_of_pos (a : ℝ≥0∞) (c d : ℝ) (hc : c > 0) (hd : d > 0):
    a ^ (c + d) = a ^ c * a ^ d := by
  have hcd : c + d  > 0 := by linarith
  rcases (eq_or_ne a 0) with a_eq_zero | a_ne_zero
  · rw [a_eq_zero, zero_rpow_of_pos hcd, zero_rpow_of_pos hc, zero_rpow_of_pos hd, mul_zero]
  · rcases (eq_or_ne a ⊤) with a_eq_top | a_ne_top
    · rw [a_eq_top, top_rpow_of_pos hcd, top_rpow_of_pos hc, top_rpow_of_pos hd, top_mul_top]
    · rw [ENNReal.rpow_add c d a_ne_zero a_ne_top]

lemma eq_of_le_of_le (a b : ℝ≥0∞) (hab : a ≤ b) (hab': b ≤ a) : a = b := by
  rcases (eq_or_ne a b) with a_eq_b | a_ne_b
  · exact a_eq_b
  · rcases lt_or_gt_of_ne a_ne_b with a_lt_b | b_lt_a
    · contrapose! a_lt_b; exact hab'
    · contrapose! b_lt_a; exact hab

def trunc_cut (f : α → ℝ≥0∞) (μ : Measure α) [SigmaFinite μ] :=
  fun n : ℕ ↦ indicator (spanningSets μ n) (fun x ↦ min (f x) n)

lemma trunc_cut_mono {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∀ x : α, Monotone (fun n ↦ trunc_cut f μ n x) := by
  intro x m n hmn; simp only [trunc_cut, indicator]
  split_ifs with is_fx_le_m is_fx_le_n
  · refine min_le_min_left (f x) (Nat.cast_le.mpr hmn)
  · contrapose! is_fx_le_n
    apply monotone_spanningSets _ hmn is_fx_le_m
  · exact zero_le _
  · exact zero_le _

lemma trunc_cut_mono₀ {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    Monotone (trunc_cut f μ) := by
  intro m n hmn x; apply trunc_cut_mono
  exact hmn

lemma trunc_cut_sup {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞} :
    ∀ x : α, ⨆ n : ℕ, trunc_cut f μ n x = f x := by
  intro x; refine iSup_eq_of_forall_le_of_forall_lt_exists_gt ?h₁ ?h₂
  · intro n; unfold trunc_cut indicator
    split_ifs
    · exact min_le_left (f x) ↑n
    · exact zero_le _
  · intro w hw
    unfold trunc_cut
    have : ∃ m : ℕ, x ∈ spanningSets μ m := by
      have obs := iUnion_spanningSets μ
      refine mem_iUnion.mp ?_
      rw [obs]
      exact trivial
    rcases this with ⟨m, wm⟩
    rcases ENNReal.exists_nat_gt hw.ne_top with ⟨n, wn⟩
    use (m + n)
    simp only [indicator]
    split_ifs with is_x_in_Ampn
    · refine lt_min hw ?_
      calc
      w < n := wn
      _ ≤ m + n := le_add_self
      _ = _ := (Nat.cast_add m n).symm
    · contrapose! is_x_in_Ampn
      exact monotone_spanningSets _ (Nat.le_add_right m n) wm

set_option linter.flexible false in
/-- Characterization of `∫⁻ x : α, f x ^ p ∂μ` by a duality argument. -/
lemma representationLp {μ : Measure α} [SigmaFinite μ] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {p q : ℝ} (hp : p > 1) (hq : q ≥ 1)
    (hpq : p⁻¹ + q⁻¹ = 1) :
    (∫⁻ x : α, (f x) ^ p ∂μ) ^ (1 / p) =
    ⨆ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ x : α, (g' x) ^ q ∂μ ≤ 1},
    ∫⁻ x : α, (f x) * g x ∂μ := by
  let A := spanningSets μ
  let g := trunc_cut f μ
  have hpq' : p.IsConjExponent q := Real.IsConjExponent.mk hp hpq
  have f_mul : ∀ n : ℕ, (g n) ^ p ≤ f * (g n) ^ (p - 1) := by
    intro n x
    simp only [g, Pi.pow_apply, Pi.mul_apply, trunc_cut, indicator]
    split_ifs
    · refine le_trans (b := (min (f x) ↑n) * min (f x) ↑n ^ (p - 1)) ?_ ?_
      · nth_rewrite 1 [← add_sub_cancel 1 p]
        rw [rpow_add_of_pos, ENNReal.rpow_one] <;> try linarith
      · exact mul_le_mul_right' (min_le_left (f x) ↑n) (min (f x) ↑n ^ (p - 1))
    · rw [ENNReal.zero_rpow_of_pos] <;> positivity
  have g_lim : ∀ x : α, Filter.Tendsto (fun n ↦ g n x) Filter.atTop (nhds (f x)) := by
    intro x
    apply tendsto_atTop_isLUB (trunc_cut_mono _)
    exact isLUB_iff_sSup_eq.mpr (trunc_cut_sup _)
  have g_sup' : (fun x ↦ ⨆ n : ℕ, (g n x) ^ p) = fun x ↦ (f x) ^ p := by
    ext x
    apply iSup_eq_of_tendsto
    · intro m n hmn
      dsimp only
      gcongr
      exact trunc_cut_mono _ hmn
    · exact (g_lim x).ennrpow_const p
  have g_meas (n : ℕ): AEMeasurable (g n) μ := by
    exact AEMeasurable.indicator (by fun_prop) (measurableSet_spanningSets μ n)
  have g_fin (n : ℕ): ∫⁻ (z : α), g n z ^ p ∂μ < ⊤ := by
    calc
    _ = ∫⁻ (z : α) in A n, g n z ^ p ∂μ := by
      unfold g trunc_cut
      rw [← lintegral_indicator]; swap; exact measurableSet_spanningSets μ n
      congr 1
      ext x
      dsimp only [indicator]
      split_ifs
      · rfl
      · simp only [ENNReal.rpow_eq_zero_iff, true_and, zero_ne_top, false_and, or_false]; positivity
    _ ≤ ∫⁻ (_x : α) in A n, n ^ p ∂μ := by
      apply setLIntegral_mono measurable_const
      · intro x hx
        gcongr
        unfold g trunc_cut indicator
        split_ifs
        · exact min_le_right (f x) ↑n
        · contradiction
    _ = n ^ p * μ (A n) := setLIntegral_const (A n) (↑n ^ p)
    _ < ⊤ := mul_lt_top (rpow_lt_top_of_nonneg (by linarith) coe_ne_top)
              (measure_spanningSets_lt_top μ n)
  have obs : ∀ n : ℕ, ∫⁻ x : α, (f x) * ((g n x) ^ (p - 1) /
      (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹) ∂μ ≥
      (∫⁻ x : α, (g n x) ^ p ∂μ) ^ p⁻¹ := by
    intro n
    rcases eq_or_ne (∫⁻ x : α, (g n x) ^ p ∂μ) 0  with int_eq_zero | int_ne_zero
    · rw [int_eq_zero, ENNReal.zero_rpow_of_pos]
      · exact zero_le _
      · refine inv_pos_of_pos (by positivity)
    · calc
      _ = (∫⁻ x : α, (f x) * (g n x) ^ (p - 1) ∂μ) * (
          (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ := by
        simp_rw [div_eq_mul_inv, ← mul_assoc]
        rw [lintegral_mul_const'' _ (by fun_prop)]
      _ ≥ (∫⁻ x : α, (g n x) ^ (p) ∂μ) * ((∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ := by
        gcongr
        apply f_mul
      _ = (∫⁻ x : α, (g n x) ^ (p) ∂μ) * ((∫⁻ y : α, (g n y) ^ p ∂μ) ^ q⁻¹)⁻¹ := by
        congr
        ext x
        rw [← ENNReal.rpow_mul]
        congr
        refine Real.IsConjExponent.sub_one_mul_conj ?_
        exact Real.IsConjExponent.mk hp hpq
      _ = (∫⁻ x : α, (g n x) ^ p ∂μ) ^ p⁻¹ := by
        rw [← ENNReal.rpow_neg]
        nth_rw 1 [← ENNReal.rpow_one (x := (∫⁻ x : α, (g n x) ^ (p) ∂μ))]
        rw [← ENNReal.rpow_add _ _ int_ne_zero (g_fin n).ne]
        congr
        exact add_neg_eq_of_eq_add hpq.symm
  have int_fg : ∫⁻ (x : α), f x ^ p ∂μ = ⨆ n : ℕ, ∫⁻ x : α, g n x ^ p ∂μ := by
    rw [← g_sup']
    apply lintegral_iSup' (fun n ↦ by fun_prop) (ae_of_all _ fun x m n hmn ↦ ?_)
    dsimp only
    gcongr
    exact trunc_cut_mono _ hmn
  have sup_rpow : (⨆ n : ℕ, ∫⁻ x : α, g n x ^ p ∂μ) ^ (1 / p) =
      ⨆ n : ℕ, (∫⁻ x : α, g n x ^ p ∂μ) ^ (1 / p) := by
    apply Monotone.map_iSup_of_continuousAt (f := fun (x : ℝ≥0∞) ↦ x ^ (1 / p))
    · fun_prop
    · apply ENNReal.monotone_rpow_of_nonneg (by positivity)
    · simp; positivity
  let h := fun n : ℕ ↦ (fun x ↦ g n x ^ (p - 1) / (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)
  have comp_sup : (⨆ n : ℕ, ∫⁻ (x : α), f x * h n x ∂μ) ≤
      ⨆ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ (z : α), (g' z) ^ q ∂μ ≤ 1},
      ∫⁻ (x : α), f x * g x ∂μ := by
    nth_rw 1 [← iSup_range (f := fun n : ℕ ↦ h n) (g := fun r ↦ ∫⁻ x : α, f x * r x ∂μ)]
    apply iSup_le_iSup_of_subset fun r exists_n ↦ ?_
    rcases exists_n with ⟨n, wn⟩
    simp_rw [← wn]
    unfold h
    refine ⟨by fun_prop, ?_⟩
    simp_rw [div_eq_mul_inv]
    calc
    _ = ∫⁻ (z : α), ((g n z ^ (p - 1)) ^ q) *
        ((∫⁻ (y : α), (g n y ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ ^ q ∂μ := by
      congr 1
      ext z
      rw [ENNReal.mul_rpow_of_nonneg]
      linarith
    _ = (∫⁻ (z : α), ((g n z ^ (p - 1)) ^ q) ∂μ) *
        ((∫⁻ (y : α), (g n y ^ (p - 1)) ^ q ∂μ) ^ q⁻¹)⁻¹ ^ q := by
      rw [lintegral_mul_const'' _ (by fun_prop)]
    _ ≤ _ := by
      rcases eq_or_ne (∫⁻ x : α, ((g n x) ^ (p - 1)) ^ q ∂μ) 0 with int_eq_zero | int_ne_zero
      · rw [int_eq_zero]
        simp
      · rw [ENNReal.inv_rpow, ENNReal.rpow_inv_rpow]
        apply le_of_eq
        refine ENNReal.mul_inv_cancel int_ne_zero ?inr.a.ht
        · apply ne_of_lt
          calc
          _ = ∫⁻ (z : α), g n z ^ p ∂μ := by
            congr 1
            ext z
            rw [← ENNReal.rpow_mul]
            congr
            exact Real.IsConjExponent.sub_one_mul_conj hpq'
          _ < ⊤ := g_fin n
        · linarith
  apply eq_of_le_of_le
  · rw [int_fg, sup_rpow]
    calc
    _ ≤ ⨆ n : ℕ, ∫⁻ x : α, (f x) * ((g n x) ^ (p - 1) /
        (∫⁻ y : α, ((g n y) ^ (p - 1)) ^ q ∂μ) ^ q⁻¹) ∂μ := by
      gcongr
      rw [one_div]
      apply obs
    _ ≤ _ := comp_sup
  · refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
    calc
    _ ≤ (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) * (∫⁻ x : α, r x ^ q ∂μ) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq' hf hr.1
    _ ≤ (∫⁻ x : α, f x ^ p ∂μ) ^ (1 / p) * (1) ^ (1 / q) := by
      gcongr
      exact hr.2
    _ = _ := by simp

lemma aemeasurability_prod₁ {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x : α ∂μ, AEMeasurable (f ∘ (Prod.mk x)) ν := by
  rcases hf with ⟨g, hg⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hg.2] with x h
  exact ⟨g ∘ Prod.mk x, hg.1.comp (measurable_prod_mk_left), h⟩

lemma aemeasurability_prod₂ {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SFinite μ] ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ y : β ∂ν, AEMeasurable (f ∘ (fun x ↦ Prod.mk x y)) μ := by
  have : AEMeasurable (f ∘ Prod.swap) (ν.prod μ) := by
    refine AEMeasurable.comp_measurable ?_ measurable_swap
    rw [Measure.prod_swap]
    assumption
  exact aemeasurability_prod₁ this

lemma aemeasurability_integral_component {α : Type u_1} {β : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    ⦃f : α × β → ENNReal⦄
    (hf : AEMeasurable f (μ.prod ν)) :
    AEMeasurable (fun x ↦ ∫⁻ (y : β), f (x, y) ∂ν) μ := by
  rcases hf with ⟨g, hg⟩
  refine ⟨fun x ↦ ∫⁻ y : β, g (x, y) ∂ν, Measurable.lintegral_prod_right hg.1, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hg.2] with x h using lintegral_congr_ae h

/-- Minkowsi's integral inequality -/
-- TODO: the condition on `μ` can probably be weakened to `SFinite μ`, by using a limit
-- argument
lemma lintegral_lintegral_pow_swap {α : Type u_1} {β : Type u_3} {p : ℝ} (hp : 1 ≤ p)
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SigmaFinite μ] ⦃f : α → β → ENNReal⦄
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ν)) :
    (∫⁻ (x : α), (∫⁻ (y : β), f x y ∂ν) ^ p ∂μ) ^ p⁻¹ ≤
    ∫⁻ (y : β), (∫⁻ (x : α), (f x y) ^ p ∂μ) ^ p⁻¹ ∂ν := by
  rcases Decidable.lt_or_eq_of_le hp with one_lt_p | one_eq_p
  · let q := Real.conjExponent p
    have hpq' : p.IsConjExponent q := Real.IsConjExponent.conjExponent one_lt_p
    have one_lt_q : 1 < q := (Real.IsConjExponent.symm hpq').one_lt
    have ineq : ∀ g ∈ {g' : α → ℝ≥0∞ | AEMeasurable g' μ ∧ ∫⁻ (z : α), (g' z) ^ q ∂μ ≤ 1},
        ∫⁻ x : α, (∫⁻ y : β, f x y ∂ν) * g x ∂μ ≤
        ∫⁻ (y : β), (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ ∂ν := by
      intro g ⟨hg1, hg2⟩
      have ae_meas₁ : ∀ᵐ x : α ∂μ, AEMeasurable (f x) ν :=
        aemeasurability_prod₁ (f := Function.uncurry f) hf
      calc
      _ = ∫⁻ x : α, (∫⁻ y : β, f x y * g x ∂ν) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [ae_meas₁] with a ha using (lintegral_mul_const'' _ ha).symm
      _ = ∫⁻ y : β, (∫⁻ x : α, f x y * g x ∂μ) ∂ν := lintegral_lintegral_swap (hf.mul hg1.fst)
      _ ≤ ∫⁻ (y : β), (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [aemeasurability_prod₂ hf] with y hy
        calc
        _ ≤ (∫⁻ (x : α), f x y ^ p ∂μ) ^ (1 / p) * (∫⁻ (x : α), g x ^ q ∂μ) ^ (1 / q) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq' hy hg1
        _ ≤ (∫⁻ (x : α), f x y ^ p ∂μ) ^ (1 / p) * 1 ^ (1 / q) := by
          gcongr
        _ = (∫⁻ (x : α), f x y ^ p ∂μ) ^ p⁻¹ := by
          simp [one_div]
    nth_rw 1 [← one_div]
    rw [representationLp (hp := one_lt_p) (hq := one_lt_q.le) (hpq := hpq'.inv_add_inv_conj)]
    · exact (iSup_le fun g ↦ iSup_le fun hg ↦ ineq g hg)
    · exact (aemeasurability_integral_component hf)
  · rw [← one_eq_p]
    simp only [ENNReal.rpow_one, inv_one]
    exact (lintegral_lintegral_swap hf).le

lemma lintegral_lintegral_pow_swap_rpow {α : Type u_1} {β : Type u_3} {p : ℝ} (hp : p ≥ 1)
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SigmaFinite μ] ⦃f : α → β → ENNReal⦄
    (hf : AEMeasurable (Function.uncurry f) (μ.prod ν)) :
    (∫⁻ (x : α), (∫⁻ (y : β), f x y ∂ν) ^ p ∂μ) ≤
    (∫⁻ (y : β), (∫⁻ (x : α), (f x y) ^ p ∂μ) ^ p⁻¹ ∂ν) ^ p := by
  have p_pos : p > 0 := lt_of_lt_of_le zero_lt_one hp
  refine le_of_rpow_le (inv_pos_of_pos p_pos) ?_
  rw [ENNReal.rpow_rpow_inv p_pos.ne']
  exact lintegral_lintegral_pow_swap hp hf

/-! ## Apply Minkowski's integral inequality to truncations
-/

@[measurability, fun_prop]
theorem ton_aeMeasurable (tc : ToneCouple) : AEMeasurable tc.ton (volume.restrict (Ioi 0)) := by
  -- ton is either increasing or decreasing
  have mono_or_anti := tc.ton_is_ton
  split_ifs at mono_or_anti
  · exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioi mono_or_anti.monotoneOn
  · exact aemeasurable_restrict_of_antitoneOn measurableSet_Ioi mono_or_anti.antitoneOn

@[measurability]
lemma indicator_ton_measurable {g : α → E₁} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] [SigmaFinite μ] (hg : AEMeasurable g μ) (tc : ToneCouple) :
    NullMeasurableSet {(s, x) : ℝ × α | ‖g x‖₊ ≤ tc.ton s }
        ((volume.restrict (Ioi 0)).prod μ) :=
  nullMeasurableSet_le hg.snd.norm (ton_aeMeasurable tc).fst

@[measurability]
lemma indicator_ton_measurable_lt {g : α → E₁} [MeasurableSpace E₁] [NormedAddCommGroup E₁]
    [BorelSpace E₁] [SigmaFinite μ] (hg : AEMeasurable g μ) (tc : ToneCouple) :
    NullMeasurableSet {(s, x) : ℝ × α | tc.ton s < ‖g x‖₊ }
        ((volume.restrict (Ioi 0)).prod μ) :=
  nullMeasurableSet_lt (ton_aeMeasurable tc).fst hg.snd.norm

@[measurability]
lemma truncation_ton_measurable {f : α → E₁}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [SigmaFinite (μ.restrict (Function.support f))] -- TODO: TypeClass or implicit variable?
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a : ℝ × α ↦ (trunc f (tc.ton a.1)) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | ‖f x‖₊ ≤ tc.ton s}
  have : (fun z : ℝ × α ↦ (trunc f (tc.ton z.1)) z.2) =
      Set.indicator A (fun z : ℝ × α ↦ f z.2) := by
    ext z; simp [trunc, indicator, A]
  rw [this]
  exact (aemeasurable_indicator_iff₀ (indicator_ton_measurable hf.restrict _)).mpr
    hf.restrict.snd.restrict

@[measurability]
lemma truncation_compl_ton_measurable {f : α → E₁}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    [SigmaFinite (μ.restrict (Function.support f))] -- TODO: TypeClass or implicit variable?
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a : ℝ × α ↦ ((f - trunc f (tc.ton a.1))) a.2)
    ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f) )) := by
  let A := {(s, x) : ℝ × α | tc.ton s < ‖f x‖₊}
  have : (fun z : ℝ × α ↦ (f - trunc f (tc.ton z.1)) z.2) = Set.indicator A (fun z : ℝ × α ↦ f z.2) := by
    ext z; rw [trunc_compl_eq]; simp [A, indicator]
  rw [this]
  refine (aemeasurable_indicator_iff₀ (indicator_ton_measurable_lt hf.restrict _)).mpr
    hf.restrict.snd.restrict

lemma restrict_to_support {a : ℝ} {p : ℝ} (hp : p > 0) [NormedAddCommGroup E₁] (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖trunc f a x‖₊ ^ p ∂ μ = ∫⁻ x : α, ‖trunc f a x‖₊ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support trunc
  rw [setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  simp_rw [f_zero]; simp [hp]

lemma restrict_to_support_trunc_compl {a : ℝ} {p : ℝ} [NormedAddCommGroup E₁] (hp : p > 0)
    (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖(f - trunc f a) x‖₊ ^ p ∂μ =
    ∫⁻ x : α, ‖(f - trunc f a) x‖₊ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support trunc
  rw [setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  rw [Pi.sub_apply, f_zero]
  simp [hp]

lemma restrict_to_support_trnc {a : ℝ} {p : ℝ} {j : Bool} [NormedAddCommGroup E₁] (hp : p > 0)
    (f : α → E₁) :
    ∫⁻ x : α in Function.support f, ‖trnc j f a x‖₊ ^ p ∂μ =
    ∫⁻ x : α, ‖trnc j f a x‖₊ ^ p ∂μ := by
  apply setLIntegral_eq_of_support_subset
  unfold Function.support trnc trunc
  rw [setOf_subset_setOf]
  intro x
  contrapose!
  intro f_zero
  rcases j
  · dsimp only [Pi.sub_apply]; simp_rw [f_zero]; simp [hp]
  · simp_rw [f_zero]; simp [hp]

@[fun_prop]
theorem aeMeasurable_trunc_restrict
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] {j : Bool}
    {hμ : SigmaFinite (μ.restrict (Function.support f))} (hf : AEMeasurable f μ) (tc : ToneCouple) :
    AEMeasurable (fun a ↦ trnc j f (tc.ton a.1) a.2)
      ((volume.restrict (Ioi 0)).prod (μ.restrict (Function.support f))) := by
  rcases j
  · exact truncation_compl_ton_measurable hf _
  · exact truncation_ton_measurable hf _

lemma lintegral_lintegral_pow_swap_trunc_compl {q q₀ p₀ : ℝ} [MeasurableSpace E₁]
    [NormedAddCommGroup E₁]
    [BorelSpace E₁] {j : Bool} {hμ : SigmaFinite (μ.restrict (Function.support f))}
    (hp₀ : p₀ > 0) (hp₀q₀ : p₀ ≤ q₀)
    (hf : AEMeasurable f μ) (tc : ToneCouple) :
    ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f, ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ↑‖trnc j f (tc.ton s) a‖₊ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀) ≤
    (∫⁻ a : α in Function.support f,
      (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ↑‖trnc j f (tc.ton s) a‖₊  ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
  apply lintegral_lintegral_pow_swap_rpow
  · apply le_of_mul_le_mul_left _ hp₀
    field_simp [hp₀q₀]
  · unfold Function.uncurry
    simp only [Pi.sub_apply]
    fun_prop

lemma lintegral_congr_support {f : α → E₁} {g h: α → ENNReal}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hf : AEMeasurable f μ) (hgh : ∀ x ∈ Function.support f, g x = h x) :
    ∫⁻ x : α in Function.support f, g x ∂μ = ∫⁻ x : α in Function.support f, h x ∂μ := by
  refine lintegral_congr_ae (ae_iff.mpr ?_)
  rw [Measure.restrict_apply₀']
  · refine measure_mono_null (fun x h₀ ↦ ?_) measure_empty
    have : g x = h x := hgh _ (mem_of_mem_inter_right h₀)
    have : x ∈ {a | ¬g a = h a} := mem_of_mem_diff h₀
    change ¬ (g x = h x) at this
    contradiction
  · have : (Function.support f) = (Function.support (fun x ↦ ‖f x‖)) := by
      unfold Function.support
      ext x
      simp only [ne_eq, mem_setOf_eq, norm_eq_zero]
    rw [this]
    exact (aestronglyMeasurable_iff_aemeasurable.mpr hf.norm).nullMeasurableSet_support

/-- One of the key estimates for the real interpolation theorem, not yet using
    the particular choice of exponent and scale in the `ScaledPowerFunction`. -/
lemma estimate_trnc {p₀ q₀ q : ℝ} {spf : ScaledPowerFunction} {j : Bool}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁]
    (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₀q₀ : p₀ ≤ q₀)
    (hf : AEMeasurable f μ) (hf₂ : SigmaFinite (μ.restrict (Function.support f)))
    (hpowers : if xor j (spf_to_tc spf).mon = true then q₀ < q else q < q₀) :
    ∫⁻ s : ℝ in Ioi 0,
    eLpNorm (trnc j f ((spf_to_tc spf).ton s)) (ENNReal.ofReal p₀) μ ^ q₀ *
    ENNReal.ofReal (s ^ (q - q₀ - 1)) ≤
    ENNReal.ofReal (spf.d ^ (q - q₀)) * ENNReal.ofReal |q - q₀|⁻¹ *
    (∫⁻ (a : α) in Function.support f,
    ENNReal.ofReal (‖f a‖ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀))) ∂μ) ^
    (p₀⁻¹ * q₀) := by
  have := spf.hd
  unfold eLpNorm eLpNorm'
  set tc := spf_to_tc spf
  split_ifs with is_p₀pos is_p₀top
  · have : p₀ ≤ 0 := ofReal_eq_zero.mp is_p₀pos
    contrapose! this; exact hp₀
  · contrapose! is_p₀top; exact coe_ne_top
  · rw [toReal_ofReal hp₀.le]
    calc
    _ = ∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (s ^ (q - q₀ - 1)) *
    ((∫⁻ (a : α), ↑‖trnc j f ((spf_to_tc spf).ton s) a‖₊ ^ p₀ ∂μ) ^ (1 / p₀)) ^ q₀  := by
      simp only [enorm_eq_nnnorm]
      congr 1
      ext x
      rw [mul_comm]
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹) ^ (p₀⁻¹ * q₀) *
        (∫⁻ (a : α) in Function.support f, ↑‖trnc j f (tc.ton s) a‖₊ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀)
        := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [ENNReal.rpow_inv_rpow]
      · rw [one_div, ← ENNReal.rpow_mul, restrict_to_support_trnc hp₀]
      · positivity
    _ = ∫⁻ (s : ℝ) in Ioi 0,
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ↑‖trnc j f (tc.ton s) a‖₊ ^ p₀ ∂μ) ^ (p₀⁻¹ * q₀)
        := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [lintegral_const_mul', ENNReal.mul_rpow_of_nonneg]
      · positivity
      · exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) coe_ne_top).ne
    _ ≤ (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ↑‖trnc j f (tc.ton s) a‖₊  ^ p₀) ^ (p₀⁻¹ * q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      -- This is a consequence of Minkowski's integral inequality
      apply lintegral_lintegral_pow_swap_trunc_compl hp₀ hp₀q₀ hf tc; assumption
    _ = (∫⁻ a : α in Function.support f,
        (∫⁻ (s : ℝ) in Ioi 0,
        (ENNReal.ofReal (s ^ (q - q₀ - 1)) *
        ↑‖trnc j f (tc.ton s) a‖₊ ^ q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x _
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      filter_upwards with s _
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_inv_rpow, ← ENNReal.rpow_mul] <;> try positivity
      congr
      field_simp
    _ = (∫⁻ a : α in Function.support f,
        ((∫⁻ (s : ℝ) in res (xor j tc.mon) (tc.inv ‖f a‖),
        (ENNReal.ofReal (s ^ (q - q₀ - 1))))*
        ↑‖f a‖₊ ^ q₀) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      apply lintegral_trunc_mul hq₀ (nnnorm_pos.mpr hfx)
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal (tc.inv ‖f a‖ ^ (q - q₀ - 1 + 1) / |q - q₀ - 1 + 1|)) *
        ENNReal.ofReal (‖f a‖ ^ q₀)) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 2
      · apply value_lintegral_res₀
        · apply tc.ran_inv
          exact norm_pos_iff.mpr hfx
        · split_ifs with h
          · simp only [h, ↓reduceIte] at hpowers; linarith
          · simp only [h, Bool.false_eq_true, ↓reduceIte] at hpowers; linarith
      · rw [← ofReal_rpow_of_nonneg] <;> try positivity
        congr
        exact norm_toNNReal.symm
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal
        (spf.d ^ (q - q₀ - 1 + 1) * ‖f a‖ ^ (spf.σ⁻¹ * (q - q₀ - 1 + 1) + q₀) /
      |q - q₀ - 1 + 1|))) ^ (p₀⁻¹ * q₀)⁻¹ ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x hfx
      congr 1
      apply value_lintegral_res₁
      exact norm_pos_iff.mpr hfx
    _ = (∫⁻ a : α in Function.support f,
        ((ENNReal.ofReal (spf.d ^ (q - q₀)) ^ (p₀⁻¹ * q₀)⁻¹ *
        ENNReal.ofReal (‖f a‖ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹)) *
    ENNReal.ofReal |q - q₀|⁻¹ ^ (p₀⁻¹ * q₀)⁻¹))  ∂μ) ^ (p₀⁻¹ * q₀) := by
      congr 1
      apply lintegral_congr_support hf
      intro x _
      rw [div_eq_mul_inv, ENNReal.ofReal_mul, sub_add_cancel, ENNReal.ofReal_mul,
          ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg] <;> try positivity
      nth_rw 2 [ENNReal.ofReal_rpow_of_nonneg] <;> try positivity
      rw [← Real.rpow_mul] ; try positivity
    _ = ENNReal.ofReal (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ ((spf.σ⁻¹ * (q - q₀) + q₀) * (p₀⁻¹ * q₀)⁻¹)) ∂μ) ^
        (p₀⁻¹ * q₀) *
        ENNReal.ofReal |q - q₀|⁻¹ := by
      rw [lintegral_mul_const', lintegral_const_mul', ENNReal.mul_rpow_of_nonneg,
          ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_inv_rpow, ENNReal.rpow_inv_rpow] <;>
          try positivity
      · exact rpow_ne_top_of_nonneg (by positivity) coe_ne_top
      · exact rpow_ne_top_of_nonneg (by positivity) coe_ne_top
    _ = ENNReal.ofReal (spf.d ^ (q - q₀)) *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ (p₀ + spf.σ⁻¹ * (q - q₀) * (p₀ / q₀))) ∂μ) ^
        (p₀⁻¹ * q₀) *
        ENNReal.ofReal |q - q₀|⁻¹ := by
      congr
      ext x
      congr
      ring_nf
      rw [inv_inv]
      field_simp
    _ = _ := by ring

def sel (j : Bool) (p₀ p₁ : ℝ≥0∞) := match j with | true => p₁ | false => p₀

/-- One of the key estimates for the real interpolation theorem, now using
    the particular choice of exponent, but not yet using the
    particular choice of scale in the `ScaledPowerFunction`. -/
lemma estimate_trnc₁ {spf : ScaledPowerFunction} {j : Bool}
    [MeasurableSpace E₁] [NormedAddCommGroup E₁] [BorelSpace E₁] (ht : t ∈ Ioo 0 1)
    (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp₁ : p₁ > 0) (hq₁ : q₁ > 0) (hpq : sel j p₀ p₁ ≤ sel j q₀ q₁)
    (hp' : sel j p₀ p₁ ≠ ⊤) (hq' : sel j q₀ q₁ ≠ ⊤)  (hp₀p₁ : p₀ < p₁)
    (hq₀q₁ : q₀ ≠ q₁) (hp : p⁻¹ = (1 - ENNReal.ofReal t) * p₀⁻¹ + ENNReal.ofReal t * p₁⁻¹)
    (hq : q⁻¹ = (1 - ENNReal.ofReal t) * q₀⁻¹ + ENNReal.ofReal t * q₁⁻¹)
    (hf : AEMeasurable f μ) (hf₂ : SigmaFinite (μ.restrict (Function.support f)))
    (hspf : spf.σ = @ζ p₀ q₀ p₁ q₁ t) :
    ∫⁻ s : ℝ in Ioi 0,
    eLpNorm (trnc j f ((spf_to_tc spf).ton s)) (sel j p₀ p₁) μ ^ (sel j q₀ q₁).toReal *
    ENNReal.ofReal (s ^ (q.toReal - (sel j q₀ q₁).toReal - 1)) ≤
    ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
    ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
    ((eLpNorm f p μ) ^ p.toReal) ^ ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
  have p_toReal_pos : p.toReal > 0 :=
    interp_exp_toReal_pos' ht hp₀ hp₁ hp (Or.inl hp₀p₁.ne_top)
  calc
  _ ≤ ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α) in Function.support f,
      ENNReal.ofReal (‖f a‖ ^ ((sel j p₀ p₁).toReal + spf.σ⁻¹ * (q.toReal - (sel j q₀ q₁).toReal) *
      ((sel j p₀ p₁).toReal / (sel j q₀ q₁).toReal))) ∂μ) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    have coe_p' : ENNReal.ofReal (sel j p₀ p₁).toReal = (sel j p₀ p₁) := ofReal_toReal_eq_iff.mpr hp'
    nth_rw 1 [← coe_p']
    apply estimate_trnc
    · apply toReal_pos
      · cases j
        · exact hp₀.ne'
        · exact hp₁.ne'
      · exact hp'
    · apply toReal_pos
      · cases j
        · exact hq₀.ne'
        · exact hq₁.ne'
      · exact hq'
    · exact toReal_mono hq' hpq
    · exact hf
    · exact hf₂
    · unfold spf_to_tc
      cases j
      · unfold sel
        dsimp only
        rw [hspf]
        simp only [Bool.if_false_right, Bool.and_true, Bool.false_bne, decide_eq_true_eq]
        split_ifs with is_ζ_pos
        · apply toReal_strict_mono
          · exact interp_exp_ne_top hq₀q₁ ht hq
          · exact (ζ_pos_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_le_zero_iff_of_lt₀ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
            (le_of_not_lt is_ζ_pos)
      · unfold sel
        dsimp only
        rw [hspf]
        simp only [Bool.if_false_right, Bool.and_true, Bool.true_bne, Bool.not_eq_true',
            decide_eq_false_iff_not]
        split_ifs with is_ζ_pos
        · apply toReal_strict_mono hq'
          exact (ζ_pos_iff_of_lt₁ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp is_ζ_pos
        · apply toReal_strict_mono
          · exact interp_exp_ne_top hq₀q₁ ht hq
          · exact (ζ_le_zero_iff_of_lt₁ ht hp₀ hq₀ hp₁ hq₁ hq₀q₁ hp hq hp₀p₁).mp
                (le_of_not_lt is_ζ_pos)
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
        ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
        (∫⁻ (a : α) in Function.support f,
        ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ) ^
        ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    ext x
    congr
    rcases j
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₅ (hp₀p₁ := hp₀p₁.ne) <;> assumption
    · dsimp only [sel]
      rw [hspf]
      apply ζ_equality₆ (hp₀p₁ := hp₀p₁.ne) <;> assumption
  _ ≤ ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (∫⁻ (a : α),
      ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    gcongr
    exact setLIntegral_le_lintegral _ _
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      (((∫⁻ (a : α), ‖f a‖₊ ^ p.toReal ∂μ) ^ p.toReal⁻¹ ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [ENNReal.rpow_inv_rpow] <;> try positivity
    congr
    ext x
    rw [← ofReal_rpow_of_nonneg] <;> try positivity
    congr
    exact ofReal_norm_eq_enorm (f x)
  _ = ENNReal.ofReal (spf.d ^ (q.toReal - (sel j q₀ q₁).toReal)) *
      ENNReal.ofReal |q.toReal - (sel j q₀ q₁).toReal|⁻¹ *
      ((eLpNorm f p μ) ^ p.toReal) ^
      ((sel j p₀ p₁).toReal ⁻¹ * (sel j q₀ q₁).toReal) := by
    congr
    rw [← one_div]
    refine (eLpNorm_eq_lintegral_rpow_enorm ?_ ?_).symm
    · exact (interpolated_pos' hp₀ hp₁ hp).ne'
    · exact interp_exp_ne_top hp₀p₁.ne ht hp

-- TODO: move this to Weaktype.lean?
lemma wnorm_eq_zero_iff {f : α → E₁} {p : ℝ≥0∞} [NormedAddCommGroup E₁] (hp : p ≠ 0) :
    wnorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  unfold wnorm
  split_ifs with h₀
  · exact eLpNormEssSup_eq_zero_iff
  · refine Iff.trans ⟨?_, ?_⟩ eLpNormEssSup_eq_zero_iff <;> intro h
    · have iSup_wnorm := iSup_eq_zero.mp h
      by_contra h₁
      have : eLpNormEssSup f μ > 0 := pos_iff_ne_zero.mpr h₁
      unfold eLpNormEssSup at this
      rw [essSup_eq_sInf] at this
      let b := (min (sInf {a : ℝ≥0∞ | μ {x | a < ↑‖f x‖₊} = 0}) 1) / 2
      have b_lt_inf : b < min (sInf {a : ℝ≥0∞ | μ {x | a < ↑‖f x‖₊} = 0}) 1 :=
        ENNReal.half_lt_self (lt_min this zero_lt_one).ne'
          (lt_of_le_of_lt (min_le_right _ 1) one_lt_top).ne
      have meas_ne_zero : μ {x | b < ↑‖f x‖₊} ≠ 0 := by
        intro h
        have obs : sInf {a | μ {x | a < ↑‖f x‖₊} = 0} ≤ b := csInf_le' h
        contrapose! obs
        calc
        _ < _ := b_lt_inf
        _ ≤ _ := min_le_left ..
      have b_ne_0 : b ≠ 0 := (ENNReal.half_pos (lt_min this zero_lt_one).ne').ne'
      have p_toReal_inv_pos : p.toReal⁻¹ > 0 := inv_pos_of_pos (toReal_pos hp h₀)
      have coe_b : ENNReal.ofNNReal b.toNNReal = b := coe_toNNReal b_lt_inf.ne_top
      have : distribution f b μ = 0 := by
        refine (rpow_eq_zero_iff_of_pos p_toReal_inv_pos).mp ?_
        refine eq_zero_of_ne_zero_of_mul_left_eq_zero b_ne_0 ?_
        rw [← coe_b]
        exact iSup_wnorm b.toNNReal
      exact meas_ne_zero this
    · refine iSup_eq_zero.mpr fun t ↦ mul_eq_zero.mpr
        (Or.inr ((rpow_eq_zero_iff_of_pos (inv_pos_of_pos (toReal_pos hp h₀))).mpr (nonpos_iff_eq_zero.mp ?_)))
      calc
        _ ≤ distribution f 0 μ := by gcongr; exact zero_le _
        _ = distribution f (eLpNormEssSup f μ) μ := by congr; exact h.symm
        _ = 0 := distribution_snormEssSup

/-! ## Weaktype estimates applied to truncations -/

variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]

lemma eLpNorm_trnc_est {f : α → E₁} {j : Bool} {a : ℝ} :
    eLpNorm (trnc j f a) p μ ≤ eLpNorm f p μ := eLpNorm_mono fun _x ↦ trnc_le_func

variable [ContinuousENorm ε] {T : (α → E₁) → (α' → ε)} in
-- TODO: remove the subindex 0 here
lemma weaktype_estimate {C₀ : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞} {f : α → E₁}
      (hq : 0 < q) (hq' : q < ⊤) (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p q μ ν C₀) {t : ℝ} (ht : t > 0) :
    distribution (T f) (ENNReal.ofReal t) ν ≤ C₀ ^ q.toReal *
        eLpNorm f p μ ^ q.toReal * ENNReal.ofReal (t ^ (-q.toReal)) := by
  have wt_est := (h₀T f hf).2 -- the weaktype estimate
  have q_pos : q.toReal > 0 := toReal_pos hq.ne' hq'.ne_top
  have tq_pos : ENNReal.ofReal t ^ q.toReal > 0 := coe_pow_pos ht
  have tq_ne_top : (ENNReal.ofReal t) ^ q.toReal ≠ ⊤ := coe_rpow_ne_top' q_pos
  -- have hq₁ : q.toReal = q := by exact toReal_ofReal q_nonneg
  simp only [wnorm, wnorm', hq'.ne_top, ↓reduceIte, iSup_le_iff] at wt_est
  have wt_est_t := wt_est t.toNNReal -- this is the weaktype estimate applied to t
  rw [← ENNReal.mul_le_mul_right (c := (ENNReal.ofReal t) ^ q.toReal) _ tq_ne_top,
      ofReal_rpow_of_pos, mul_assoc _ _ (ENNReal.ofReal (t ^ q.toReal)), ← ofReal_mul',
      ← Real.rpow_add, neg_add_cancel, Real.rpow_zero, ofReal_one, mul_one, mul_comm,
      ← ENNReal.mul_rpow_of_nonneg] <;> try positivity
  refine (ENNReal.rpow_inv_le_iff q_pos).mp ?_
  rw [ENNReal.mul_rpow_of_nonneg, ENNReal.ofReal_rpow_of_pos,
      Real.rpow_rpow_inv] <;> try positivity
  rwa [← coe_coe_eq_ofReal]

variable [ContinuousENorm ε] {T : (α → E₁) → (α' → ε)} in
lemma weaktype_estimate_top {C : ℝ≥0} {p : ℝ≥0∞} {q : ℝ≥0∞}
    (hq' : q = ⊤) {f : α → E₁} (hf : Memℒp f p μ)
    (hT : HasWeakType T p q μ ν C) {t : ℝ} (ht : C * eLpNorm f p μ ≤ ENNReal.ofReal t) :
    distribution (T f) (ENNReal.ofReal t) ν = 0 := by
  have wt_est := (hT f hf).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T f) (eLpNormEssSup (T f) ν) ν := distribution_mono_right (le_trans wt_est ht)
  _ = _ := meas_essSup_lt -- meas_eLpNormEssSup_lt

-- for the remaining lemmas we use too much measure theory that is just for normed spaces
-- try to generalize to ENorm-classes after Mathlib refactor
variable {T : (α → E₁) → (α' → E₂)}

/-- If `T` has weaktype `p₀`-`p₁`, `f` is `AEStronglyMeasurable` and the `p`-norm of `f`
    vanishes, then the `q`-norm of `T f` vanishes.
    -/
lemma weaktype_aux₀ {p₀ q₀ p q : ℝ≥0∞}
    (hp₀ : p₀ > 0) (hq₀ : q₀ > 0) (hp : p > 0) (hq : q > 0)
    {C₀ : ℝ≥0}
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (hf : AEStronglyMeasurable f μ)
    (hF : eLpNorm f p μ = 0) :
    eLpNorm (T f) q ν = 0 := by
  have f_ae_0 : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hf hp.ne').mp hF
  have hf₂ : eLpNorm f p₀ μ = 0 := (eLpNorm_eq_zero_iff hf hp₀.ne').mpr f_ae_0
  have hf₁ : Memℒp f p₀ μ := ⟨hf, by rw [hf₂]; exact zero_lt_top⟩
  have := (h₀T f hf₁).2
  rw [hf₂, mul_zero] at this
  have wnorm_0 : wnorm (T f) q₀ ν = 0 := nonpos_iff_eq_zero.mp this
  have : (T f) =ᵐ[ν] 0 := (wnorm_eq_zero_iff hq₀.ne').mp wnorm_0
  exact (eLpNorm_eq_zero_iff (h₀T _ hf₁).1 hq.ne').mpr this

variable [MeasurableSpace E₁] [BorelSpace E₁]

lemma weaktype_estimate_trunc_compl {C₀ : ℝ≥0} {p p₀: ℝ≥0∞} {f : α → E₁}
    (hp₀ : 0 < p₀) {q₀ : ℝ≥0∞} (hp : p ≠ ⊤) (hq₀ : 0 < q₀) (hq₀' : q₀ < ⊤)
    (hp₀p : p₀ < p) (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : t > 0) {a : ℝ} (ha : a > 0) :
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν ≤ C₀ ^ q₀.toReal *
        eLpNorm (f - trunc f a) p₀ μ ^ q₀.toReal * (ENNReal.ofReal (t ^ (-q₀.toReal))) := by
  apply weaktype_estimate hq₀ hq₀' ?_ h₀T ht
  exact trunc_compl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ ha hf

lemma weaktype_estimate_trunc {C₁ : ℝ≥0} {p p₁ q₁: ℝ≥0∞} {f : α → E₁}
    (hp : 0 < p)
    (hq₁ : 0 < q₁) (hq₁' : q₁ < ⊤) (hp₁p : p < p₁)
    (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) {a : ℝ} :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν ≤ C₁ ^ q₁.toReal *
      eLpNorm (trunc f a) p₁ μ ^ q₁.toReal * ENNReal.ofReal (t ^ (-q₁.toReal)) :=
  weaktype_estimate hq₁ hq₁' (trunc_Lp_Lq_higher (p := p) ⟨hp, hp₁p⟩ hf) h₁T ht

lemma weaktype_estimate_trunc_top_top {a : ℝ} {C₁ : ℝ≥0}
    (hC₁ : C₁ > 0) {p p₁ q₁ : ℝ≥0∞} (hp : 0 < p)
    (hp₁ : p₁ = ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) (ha : a = t / C₁) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  rw [ha]
  have obs : Memℒp (trunc f (t / C₁)) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf
  have wt_est := (h₁T (trunc f (t / C₁)) obs).2
  simp only [wnorm, eLpNorm, hq₁, ↓reduceIte, hp₁, top_ne_zero] at wt_est
  apply nonpos_iff_eq_zero.mp
  have ineq : eLpNormEssSup (T (trunc f (t / C₁))) ν ≤ ENNReal.ofReal t := calc
    _ ≤ C₁ * eLpNormEssSup (trunc f (t / C₁)) μ := wt_est
    _ ≤ C₁ * ENNReal.ofReal (max 0 (t / C₁)) := by
      gcongr
      exact trunc_eLpNormEssSup_le
    _ ≤ _ := by
      let C := C₁.toReal
      have coe_C : C.toNNReal = C₁ := Real.toNNReal_coe
      rw [← coe_C, coe_coe_eq_ofReal, ← ENNReal.ofReal_mul, max_eq_right, congrArg toReal coe_C,
        mul_div_cancel₀]
      · exact Ne.symm (ne_of_lt hC₁)
      · positivity
      · positivity
  calc
  _ ≤ distribution (T (trunc f (t / C₁))) (eLpNormEssSup (T (trunc f (t / C₁))) ν) ν :=
      distribution_mono_right ineq
  _ = 0 := distribution_snormEssSup

lemma weaktype_estimate_trunc_compl_top {C₀ : ℝ≥0} (hC₀ : C₀ > 0) {p p₀ q₀ : ℝ≥0∞}
    (hp₀ : 0 < p₀) (hq₀ : q₀ = ⊤) (hp₀p : p₀ < p) (hp : p ≠ ⊤) {f : α → E₁} (hf : Memℒp f p μ)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) {t : ℝ} (ht : t > 0) {a : ℝ} {d : ℝ} -- (hd : d > 0)
    (ha : a = (t / d) ^ (p₀.toReal / (p₀.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₀) ^ p₀.toReal *
        eLpNorm f p μ ^ p.toReal).toReal ^ p₀.toReal⁻¹) :
    distribution (T (f - trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  rcases (eq_zero_or_pos (eLpNormEssSup f μ)) with snorm_zero | snorm_pos
  · have : eLpNorm (trnc ⊥ f a) ⊤ μ = 0 := by
      apply nonpos_iff_eq_zero.mp
      rw [← snorm_zero]
      exact eLpNorm_trnc_est (p := ⊤)
    have obs : eLpNorm (T (trnc ⊥ f a)) ⊤ ν = 0 :=
      weaktype_aux₀ hp₀ (hq₀ ▸ zero_lt_top) zero_lt_top zero_lt_top h₀T
        (aestronglyMeasurable_trunc_compl hf.1) this
    exact nonpos_iff_eq_zero.mp (Trans.trans (distribution_mono_right (Trans.trans obs
      (zero_le (ENNReal.ofReal t)))) meas_eLpNormEssSup_lt)
  · have p_pos : p > 0 := lt_trans hp₀ hp₀p
    have snorm_p_pos : eLpNorm f p μ ≠ 0 := fun snorm_0 ↦ snorm_pos.ne' <|
      eLpNormEssSup_eq_zero_iff.mpr <| (eLpNorm_eq_zero_iff hf.1 p_pos.ne').mp snorm_0
    have term_pos : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
      apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
    have term_ne_top : (ENNReal.ofNNReal C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤
        := mul_ne_top (rpow_ne_top' (ENNReal.coe_ne_zero.mpr hC₀.ne') coe_ne_top)
          (rpow_ne_top' snorm_p_pos (Memℒp.eLpNorm_ne_top hf))
    have d_pos : d > 0 := hdeq ▸ Real.rpow_pos_of_pos (zero_toReal ▸
      toReal_strict_mono term_ne_top term_pos) _
    have a_pos : a > 0 := by rw [ha]; positivity
    have obs : Memℒp (f - trunc f a) p₀ μ := trunc_compl_Lp_Lq_lower hp ⟨hp₀, hp₀p⟩ a_pos hf
    have wt_est := (h₀T (f - trunc f a) obs).2
    unfold wnorm at wt_est
    split_ifs at wt_est
    have snorm_est : eLpNormEssSup (T (f - trunc f a)) ν ≤ ENNReal.ofReal t := by
      apply le_of_rpow_le (exp_toReal_pos hp₀ hp₀p.ne_top)
      calc
      _ ≤ (↑C₀ * eLpNorm (f - trunc f a) p₀ μ) ^ p₀.toReal := by gcongr
      _ ≤ (↑C₀) ^ p₀.toReal * (ENNReal.ofReal (a ^ (p₀.toReal - p.toReal)) *
          eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ toReal_nonneg]
        gcongr
        exact estimate_eLpNorm_trunc_compl hp ⟨hp₀, hp₀p⟩ hf.1.aemeasurable a_pos
      _ = (↑C₀) ^ p₀.toReal * eLpNorm f p μ ^ p.toReal *
          (ENNReal.ofReal (d ^ p₀.toReal))⁻¹ * ENNReal.ofReal (t ^ p₀.toReal) := by
        rw [ha, ← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring
        · exact (sub_neg.mpr (toReal_strict_mono hp hp₀p)).ne
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top]
        exact toReal_ne_zero.mpr ⟨hp₀.ne', hp₀p.ne_top⟩
    apply nonpos_iff_eq_zero.mp
    calc
    _ ≤ distribution (T (f - trunc f a)) (eLpNormEssSup (T (f - trunc f a)) ν) ν :=
      distribution_mono_right snorm_est
    _ = _ := meas_eLpNormEssSup_lt

lemma weaktype_estimate_trunc_top {C₁ : ℝ≥0} (hC₁ : C₁ > 0) {p p₁ q₁ : ℝ≥0∞}
    (hp : 0 < p)
    (hp₁ : p₁ < ⊤) (hq₁ : q₁ = ⊤) (hp₁p : p < p₁) {f : α → E₁} (hf : Memℒp f p μ)
    (h₁T : HasWeakType T p₁ q₁ μ ν C₁) {t : ℝ} (ht : t > 0) {a : ℝ} {d : ℝ} -- (hd : d > 0)
    (ha : a = (t / d) ^ (p₁.toReal / (p₁.toReal - p.toReal)))
    (hdeq : d = ((ENNReal.ofNNReal C₁) ^ p₁.toReal *
        eLpNorm f p μ ^ p.toReal).toReal ^ p₁.toReal⁻¹) :
    distribution (T (trunc f a)) (ENNReal.ofReal t) ν = 0 := by
  have obs : Memℒp (trunc f a) p₁ μ := trunc_Lp_Lq_higher ⟨hp, hp₁p⟩ hf
  have wt_est := (h₁T (trunc f a) obs).2
  unfold wnorm at wt_est
  split_ifs at wt_est
  have : p₁.toReal ≠ 0 := exp_toReal_ne_zero' (lt_trans hp hp₁p) hp₁.ne_top
  have : eLpNormEssSup (T (trunc f a)) ν ^ p₁.toReal ≤ (↑C₁ * eLpNorm (trunc f a) p₁ μ) ^ p₁.toReal
      := by gcongr
  have snorm_est : eLpNormEssSup (T (trunc f a)) ν ≤ ENNReal.ofReal t := by
    apply le_of_rpow_le (exp_toReal_pos (lt_trans hp hp₁p) hp₁.ne_top)
    refine le_trans this ?_
    rcases (eq_zero_or_pos (eLpNormEssSup f μ)) with snorm_zero | snorm_pos
    · gcongr
      calc
      _ ≤ (ENNReal.ofNNReal C₁) * eLpNorm f p₁ μ := by
        gcongr
        apply eLpNorm_mono (fun x ↦ trunc_le_func)
      _ ≤ _ := by
        have : eLpNorm f p₁ μ = 0 := Trans.trans (eLpNorm_congr_ae
            (eLpNormEssSup_eq_zero_iff.mp snorm_zero)) eLpNorm_zero
        simp only [this, mul_zero, zero_le]
    · have snorm_p_pos : eLpNorm f p μ ≠ 0 := by
        intro snorm_0
        apply Ne.symm (ne_of_lt snorm_pos)
        apply eLpNormEssSup_eq_zero_iff.mpr
        exact (eLpNorm_eq_zero_iff hf.1 hp.ne').mp snorm_0
      have term_pos : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal > 0 := by
        apply ENNReal.mul_pos <;> exact (rpow_pos_of_nonneg (by positivity) (by positivity)).ne'
      have term_ne_top : (ENNReal.ofNNReal C₁) ^ p₁.toReal * eLpNorm f p μ ^ p.toReal ≠ ⊤ :=
        mul_ne_top (rpow_ne_top' (ENNReal.coe_ne_zero.mpr hC₁.ne') coe_ne_top)
          (rpow_ne_top' snorm_p_pos (Memℒp.eLpNorm_ne_top hf))
      have d_pos : d > 0 := hdeq ▸ Real.rpow_pos_of_pos (zero_toReal ▸
        toReal_strict_mono term_ne_top term_pos) _
      calc
      _ ≤ ↑C₁ ^ p₁.toReal * ((ENNReal.ofReal (a ^ (p₁.toReal - p.toReal))) * eLpNorm f p μ ^ p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg]
        gcongr
        · exact estimate_eLpNorm_trunc hp₁.ne_top ⟨hp, hp₁p⟩ hf.1.aemeasurable
        · exact toReal_nonneg
      _ = ↑C₁ ^ p₁.toReal * eLpNorm f p μ ^ p.toReal * (ENNReal.ofReal (d ^ p₁.toReal))⁻¹ *
          ENNReal.ofReal (t ^ p₁.toReal) := by
        rw [ha, ← Real.rpow_mul, div_mul_cancel₀]
        · rw [Real.div_rpow] <;> try positivity
          rw [ENNReal.ofReal_div_of_pos] <;> try positivity
          rw [div_eq_mul_inv]
          ring
        · exact (sub_pos.mpr (toReal_strict_mono hp₁.ne_top hp₁p)).ne'
        · positivity
      _ = _ := by
        rw [ofReal_rpow_of_pos ht]
        nth_rw 3 [← one_mul (ENNReal.ofReal _)]
        rw [hdeq]
        rw [Real.rpow_inv_rpow] <;> try positivity
        rw [ofReal_toReal term_ne_top, ENNReal.mul_inv_cancel (by positivity) term_ne_top]
  apply nonpos_iff_eq_zero.mp
  calc
  _ ≤ distribution (T (trunc f a)) (eLpNormEssSup (T (trunc f a)) ν) ν := by gcongr
  _ = _ := meas_eLpNormEssSup_lt

end MeasureTheory

end

noncomputable section

open NNReal ENNReal MeasureTheory Set Pointwise

variable {α α' ε E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m' : MeasurableSpace α'}
  {p p' q p₀ q₀ p₁ q₁: ℝ≥0∞}
  {C₀ C₁ : ℝ≥0} {μ : Measure α} {ν : Measure α'}
  {a : ℝ}-- truncation parameter
  [NormedAddCommGroup E] [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₃] [BorelSpace E₃]
  {f : α → E₁} {t : ℝ}
  {T : (α → E₁) → (α' → E₂)}
namespace MeasureTheory

-- /-- # The real interpolation theorem

-- ## Definitions-/

def Subadditive [ENorm ε] (T : (α → E₁) → α' → ε) : Prop :=
  ∃ A ≠ ⊤, ∀ (f g : α → E₁) (x : α'), ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

def Subadditive_trunc [ENorm ε] (T : (α → E₁) → α' → ε) (A : ℝ≥0∞) (f : α → E₁) (ν : Measure α') :
    Prop :=
  ∀ a : ℝ, a > 0 → ∀ᵐ y ∂ν,
  ‖T (trunc f a + trunc_compl f a) y‖ₑ ≤ A * (‖T (trunc f a) y‖ₑ + ‖T (trunc_compl f a) y‖ₑ)

/-- The operator is subadditive on functions satisfying `P` with constant `A`
(this is almost vacuous if `A = ⊤`). -/
def AESubadditiveOn [ENorm ε] (T : (α → E₁) → α' → ε) (P : (α → E₁) → Prop) (A : ℝ≥0∞)
    (ν : Measure α') : Prop :=
  ∀ (f g : α → E₁), P f → P g → ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ)

namespace AESubadditiveOn

variable [ENormedAddMonoid ε] {ν : Measure α'}

lemma antitone {T : (α → E₁) → α' → ε} {P P' : (α → E₁) → Prop}
    (h : ∀ {u : α → E₁}, P u → P' u) {A : ℝ≥0∞} (sa : AESubadditiveOn T P' A ν) :
    AESubadditiveOn T P A ν :=
  fun f g hf hg ↦ sa f g (h hf) (h hg)

/- Start of proof attempt -/
lemma round1_zero {P : (α → E₁) → Prop} (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (A : ℝ≥0∞) (h : ∀ u, P u → T u =ᵐ[ν] 0) :
    AESubadditiveOn T P A ν := by
  intro f g hf hg
  have h1 : P (f + g) := hP hf hg
  have h2 : T (f + g) =ᵐ[ν] 0 := h (f + g) h1
  have h3 : T f =ᵐ[ν] 0 := h f hf
  have h4 : T g =ᵐ[ν] 0 := h g hg
  have h5 : ∀ᵐ x ∂ν, T (f + g) x = 0 := h2
  have h6 : ∀ᵐ x ∂ν, T f x = 0 := h3
  have h7 : ∀ᵐ x ∂ν, T g x = 0 := h4
  have h_final : ∀ᵐ x ∂ν, ‖T (f + g) x‖ₑ ≤ A * (‖T f x‖ₑ + ‖T g x‖ₑ) := by
    filter_upwards [h5, h6, h7] with x hx1 hx2 hx3
    simp [hx1, hx2, hx3]
    <;> norm_num
  exact h_final

theorem zero {P : (α → E₁) → Prop} (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (A : ℝ≥0∞) (h : ∀ u, P u → T u =ᵐ[ν] 0) : AESubadditiveOn T P A ν  := by

  exact round1_zero hP A h
