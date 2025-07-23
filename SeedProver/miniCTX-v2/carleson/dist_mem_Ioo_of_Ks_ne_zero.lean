-- In carleson/Carleson/Psi.lean

import Carleson.Defs
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Topology.EMetricSpace.Paracompact

open MeasureTheory Measure NNReal Metric Set TopologicalSpace Function DoublingMeasure Bornology
open scoped ENNReal
noncomputable section

/-! The function `ψ` -/

section D
variable {D : ℕ} {x : ℝ} {s : ℤ} (hD : 1 < (D : ℝ))

open Real

section -- We record here some trivial inequalities that are used repeatedly below.
private lemma fourD0' (hD : 1 ≤ D) : 0 < (4 * D : ℝ) := by positivity
private lemma four_x0 {x : ℝ} (hx : 0 < x) : 0 < 4 * x := mul_pos four_pos hx
include hD
private lemma D0 : 0 < (D : ℝ) := one_pos.trans hD
private lemma D2 : 2 ≤ (D : ℝ) := by exact_mod_cast hD
private lemma twoD0 : 0 < (2 * D : ℝ) := by linarith
private lemma fourD0 : 0 < (4 * D : ℝ) := by linarith
private lemma D_pow0 (r : ℝ) : 0 < (D : ℝ) ^ r := by positivity
private lemma D_pow0' (r : ℤ) : 0 < (D : ℝ) ^ r := by positivity
private lemma cDx0 {c x : ℝ} (hc : c > 0) (hx : 0 < x) : c * D * x > 0 := by positivity
end

def ψ (D : ℕ) (x : ℝ) : ℝ :=
  max 0 <| min 1 <| min (4 * D * x - 1) (2 - 4 * x)

set_option hygiene false
scoped[ShortVariables] notation "ψ" => ψ (defaultD a)

lemma zero_le_ψ (D : ℕ) (x : ℝ) : 0 ≤ ψ D x :=
  le_max_left 0 _

lemma ψ_le_one (D : ℕ) (x : ℝ) : ψ D x ≤ 1 :=
  max_le (one_pos.le) (min_le_left 1 _)

lemma abs_ψ_le_one (D : ℕ) (x : ℝ) : |ψ D x| ≤ 1 :=
  abs_le.2 ⟨by linarith [zero_le_ψ D x], ψ_le_one D x⟩

---------------------------------------------
/- `ψ_formula₀` through `ψ_formula₄` establish the piecewise formula for `ψ`. -/

lemma ψ_formula₀ {x : ℝ} (hx : x ≤ 1 / (4 * D : ℝ)) : ψ D x = 0 := by
  by_cases hD : D = 0
  · simp [ψ, hD]
  · exact max_eq_left <| (min_le_right 1 _).trans <| (min_le_left _ _).trans <|
      tsub_nonpos.2 <| (le_div_iff₀' (mul_pos four_pos
      (by exact_mod_cast Nat.zero_lt_of_ne_zero hD))).1 hx

include hD in
lemma ψ_formula₁ {x : ℝ} (hx : 1 / (4 * D) ≤ x ∧ x ≤ 1 / (2 * D)) :
    ψ D x = 4 * D * x - 1 := by
  have : x ≥ 0 := le_trans (one_div_nonneg.2 (fourD0 hD).le) hx.1
  have hx1 := (div_le_iff₀' (fourD0 hD)).1 hx.1
  have hx2 := (le_div_iff₀' (twoD0 hD)).1 hx.2
  have ineq₀ : 4 * D * x - 1 ≤ 2 - 4 * x := by
    suffices (2 * D + 2 * D + 4) * x ≤ 3 by linarith
    exact le_trans (by gcongr; linarith [D2 hD]) (by linarith: (2 * D + 2 * D + 2 * D) * x ≤ 3)
  have ineq₁ : 4 * D * x - 1 ≤ 1 := by linarith
  have ineq₂ : 0 ≤ 4 * D * x - 1 := by linarith
  rw [ψ, min_eq_left ineq₀, min_eq_right ineq₁, max_eq_right ineq₂]

include hD in
lemma ψ_formula₂ {x : ℝ} (hx : 1 / (2 * D) ≤ x ∧ x ≤ 1 / 4) : ψ D x = 1 := by
  unfold ψ
  suffices min 1 (min (4 * D * x - 1) (2 - 4 * x)) = 1 from this.symm ▸ max_eq_right_of_lt one_pos
  have := (div_le_iff₀' (twoD0 hD)).1 hx.1
  exact min_eq_left (le_min (by linarith) (by linarith))

include hD in
lemma ψ_formula₃ {x : ℝ} (hx : 1 / 4 ≤ x ∧ x ≤ 1 / 2) : ψ D x = 2 - 4 * x := by
  have ineq₀ : 2 - 4 * x ≤ 4 * D * x - 1 := by nlinarith [D2 hD]
  have ineq₁ : 2 - 4 * x ≤ 1 := by linarith
  have ineq₂ : 2 - 4 * x ≥ 0 := by linarith
  rw [ψ, min_eq_right ineq₀, min_eq_right ineq₁, max_eq_right ineq₂]

lemma ψ_formula₄ {x : ℝ} (hx : x ≥ 1 / 2) : ψ D x = 0 :=
  max_eq_left <| (min_le_right _ _).trans <| (min_le_right _ _).trans (by linarith)
---------------------------------------------

lemma psi_zero : ψ D 0 = 0 := ψ_formula₀ (by positivity)

lemma continuous_ψ : Continuous (ψ D) := by
  unfold ψ; fun_prop

include hD in
lemma support_ψ : support (ψ D) = Ioo (4 * D : ℝ)⁻¹ 2⁻¹ := by
  ext x
  by_cases hx₀ : x ≤ 1 / (4 * D)
  · suffices x ≤ (D : ℝ)⁻¹ * 4⁻¹ by simp [ψ_formula₀ hx₀, this]
    rwa [one_div, mul_inv_rev] at hx₀
  push_neg at hx₀
  have hx₀_inv : (D : ℝ)⁻¹ * 4⁻¹ < x := by convert hx₀ using 1; simp
  have ne₀ : 4 * D * x - 1 ≠ 0 := ne_of_gt (by rwa [sub_pos, ← div_lt_iff₀' (fourD0 hD)])
  by_cases hx₁ : x ≤ 1 / (2 * D)
  · suffices (D : ℝ)⁻¹ * 4⁻¹ < x ∧ x < 2⁻¹ by simpa [ne₀, ψ_formula₁ hD ⟨hx₀.le, hx₁⟩]
    exact ⟨hx₀_inv, lt_of_le_of_lt hx₁ (by simp [_root_.inv_lt_one_iff₀, hD])⟩
  push_neg at hx₁
  by_cases hx₂ : x ≤ 1 / 4
  · simpa [ψ_formula₂ hD ⟨hx₁.le, hx₂⟩, hx₀_inv] using lt_of_le_of_lt hx₂ (by norm_num)
  push_neg at hx₂
  by_cases hx₃ : x < 1 / 2
  · have : ¬ 2 - 4 * x = 0 := by linarith
    simpa [ψ_formula₃ hD ⟨hx₂.le, hx₃.le⟩, hx₀, hx₃, ← one_div]
  · rw [mem_support, ψ_formula₄ (not_lt.1 hx₃), ne_self_iff_false, false_iff, mem_Ioo, not_and,
      inv_eq_one_div 2]
    exact fun _ ↦ hx₃

lemma lipschitzWith_ψ (hD : 1 ≤ D) : LipschitzWith (4 * D) (ψ D) := by
  have max_eq_4D : max 0 (4 * D : ℝ≥0) = 4 * D := max_eq_right (fourD0' hD).le
  have max_eq_4D' : max (4 * D) 4 = 4 * D := by apply max_eq_left; linarith
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min 1 <| min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 0).max this
  suffices LipschitzWith (4 * D) (fun (x : ℝ) ↦ min (4 * D * x - 1) (2 - 4 * x)) from
    max_eq_4D ▸ (LipschitzWith.const 1).min this
  have lw1 : LipschitzWith (4 * D) (fun (x : ℝ) ↦ 4 * D * x - 1) := by
    refine LipschitzWith.of_le_add_mul (4 * D) (fun x y ↦ ?_)
    suffices 4 * D * (x - y) ≤ 4 * D * dist x y by norm_cast at this ⊢; linarith
    exact (mul_le_mul_left (fourD0' hD)).2 <| sub_le_dist x y
  have lw2 : LipschitzWith 4 (fun (x : ℝ) ↦ 2 - 4 * x) := by
    refine LipschitzWith.of_le_add_mul 4 (fun x y ↦ ?_)
    suffices 4 * (y - x) ≤ 4 * dist x y by norm_cast at this ⊢; linarith
    gcongr
    exact dist_comm x y ▸ sub_le_dist y x
  have := lw1.min lw2
  norm_cast at this ⊢
  convert max_eq_4D' ▸ this

-- Alternate version of `lipschitzWith_ψ` that avoids using `ENNReal`.
lemma lipschitzWith_ψ' (hD : 1 ≤ D) (a b : ℝ) : ‖ψ D a - ψ D b‖ ≤ 4 * D * dist a b := by
  have lipschitz := lipschitzWith_ψ hD a b
  rw [edist_dist, edist_dist, dist_eq_norm_sub] at lipschitz
  norm_cast at lipschitz
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by exact_mod_cast (fourD0' hD).le),
    ← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top] at lipschitz
  repeat rw [ENNReal.toReal_ofReal (by positivity)] at lipschitz
  norm_cast

/- the one or two numbers `s` where `ψ (D ^ (-s) * x)` is possibly nonzero -/
variable (D) in def nonzeroS (x : ℝ) : Finset ℤ :=
  Finset.Icc ⌊(1 + logb D (2 * x))⌋ ⌈logb D (4 * x)⌉

---------------------------------------------

section include_hD

/- The goal of the next several lemmas is to prove `sum_ψ`, which says that
`∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1`.

The first four lemmas prove some properties of the endpoints of `nonzeroS D x`, and in particular
show that `nonzeroS D x` has either 1 or 2 elements. The next two lemmas prove `sum_ψ` in the
1-element and 2-element cases, respectively, and then `sum_ψ` follows immediately.
-/

include hD

private lemma le_div_ceil_mul (hx : 0 < x) : 1 / (4 * D) ≤ D ^ (-⌈logb D (4 * x)⌉) * x := by
  rw [← div_le_iff₀ hx, div_div, ← rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD four_pos hx),
    ← inv_eq_one_div, (by norm_cast : (D : ℝ) ^ (-⌈logb D (4 * x)⌉) = D ^ (-⌈logb D (4 * x)⌉ : ℝ)),
    ← rpow_neg (D0 hD).le, rpow_le_rpow_left_iff hD, neg_le_neg_iff]
  apply le_of_le_of_eq <| calc
    (⌈logb D (4 * x)⌉ : ℝ) ≤ ⌊logb D (4 * x)⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one _
    _                     ≤ logb D (4 * x) + 1   := by gcongr; exact Int.floor_le (logb D (4 * x))
  rw [← logb_self_eq_one hD, ← logb_mul (mul_pos four_pos hx).ne.symm (ne_of_gt (D0 hD)),
    mul_assoc, mul_assoc, mul_comm _ x]

private lemma one_add_logb (hx : x > 0) : 1 + logb D (2 * x) = logb D (2 * D * x) := by
  rw [← logb_self_eq_one hD, ← logb_mul (D0 hD).ne.symm (mul_pos two_pos hx).ne.symm,
    ← mul_assoc, mul_comm (D : ℝ) 2]

-- If `D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)`, then the endpoints of `nonzeroS x` are equal.
private lemma eq_endpoints (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)) :
    ⌊(1 + logb D (2 * x))⌋ = ⌈logb D (4 * x)⌉ := by
  rw [Int.floor_eq_iff, one_add_logb hD hx]
  constructor
  · rw [← rpow_le_rpow_left_iff hD, ← inv_le_inv₀ (D_pow0 hD _) (D_pow0 hD _),
      rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD two_pos hx),
      ← rpow_neg (D0 hD).le, inv_eq_one_div]
    exact_mod_cast h.le
  · have : logb D (2 * D * x) < logb D (4 * D * x) := by
      refine (strictMonoOn_logb hD) ?_ ?_ (by linarith [(cDx0 hD two_pos hx)]) <;>
        exact mem_Ioi.2 (cDx0 hD (by norm_num) hx)
    apply lt_of_lt_of_le this
    rw [mul_comm, ← mul_assoc, mul_comm x 4, logb_mul (mul_pos four_pos hx).ne.symm (D0 hD).ne.symm,
      logb_self_eq_one hD, add_le_add_iff_right, mul_comm]
    exact Int.le_ceil _

-- If `D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)`, then the endpoints of `nonzeroS x` differ by 1.
private lemma endpoint_sub_one (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)) :
    ⌊1 + logb D (2 * x)⌋ = ⌈logb D (4 * x)⌉ - 1 := by
  rw [one_add_logb hD hx]
  apply le_antisymm
  · rw [← inv_eq_one_div, zpow_neg, inv_lt_inv₀ (D_pow0' hD _) (cDx0 hD two_pos hx)] at h
    rw [Int.floor_le_sub_one_iff, ← rpow_lt_rpow_left_iff hD,
      rpow_logb (D0 hD) (ne_of_gt hD) (cDx0 hD two_pos hx)]
    exact_mod_cast h
  · apply sub_le_iff_le_add.2 ∘ Int.ceil_le.2
    suffices logb D (4 * x) ≤ logb D (2 * D * x) by
      exact_mod_cast (lt_of_le_of_lt this (Int.lt_floor_add_one _)).le
    have : 4 * x ≤ 2 * D * x := (mul_le_mul_right hx).2 (by linarith [D2 hD])
    refine (strictMonoOn_logb hD).monotoneOn ?_ ?_ this <;> exact mem_Ioi.2 (by positivity)

-- Special case of `sum_ψ`, for the case where `nonzeroS D x` has one element.
private lemma sum_ψ₁ (hx : 0 < x) (h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)) :
    ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  rw [nonzeroS, eq_endpoints hD hx h, Finset.Icc_self, Finset.sum_singleton]
  refine ψ_formula₂ hD ⟨le_of_eq_of_le (by field_simp) ((mul_le_mul_right hx).2 h), ?_⟩
  calc
    D ^ (-⌈logb D (4 * x)⌉) * x
      = D ^ (-⌈logb D (4 * x)⌉ : ℝ) * x := by norm_cast
    _ ≤ D ^ (-logb D (4 * x)) * x      := by
      gcongr
      · exact hD.le
      · exact Int.le_ceil (logb D (4 * x))
    _ = 1 / (4 * x) * x                := by
      rw [rpow_neg (D0 hD).le, inv_eq_one_div, rpow_logb (D0 hD) hD.ne.symm (by linarith)]
    _ = 1 / 4                          := by field_simp; exact mul_comm x 4

-- Special case of `sum_ψ`, for the case where `nonzeroS D x` has two elements.
private lemma sum_ψ₂ (hx : 0 < x)
    (h : D ^ (-⌈logb D (4 * x)⌉) < 1 / (2 * D * x)) :
    ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  -- Replace `nonzeroS D x` with `{s₀ - 1, s₀}`, where `s₀ := ⌈logb D (4 * x)⌉`
  have endpts := endpoint_sub_one hD hx h
  have ne : ⌈logb D (4 * x)⌉ - 1 ≠ ⌈logb D (4 * x)⌉ := pred_ne_self _
  have : nonzeroS D x = {⌈logb D (4 * x)⌉ - 1, ⌈logb D (4 * x)⌉} := by
    rw [nonzeroS, ← endpts]
    have Icc_of_eq_add_one {a b : ℤ} (h : a + 1 = b) : Finset.Icc a b = {a, b} := by
      subst h; exact Int.Icc_eq_pair a
    exact Icc_of_eq_add_one (add_eq_of_eq_sub endpts)
  set s₀ := ⌈logb D (4 * x)⌉
  rw [this, Finset.sum_insert ((Finset.not_mem_singleton).2 ne), Finset.sum_singleton]
  -- Now calculate the sum
  have Ds₀x_lt := (mul_lt_mul_right hx).2 h
  rw [← div_div, div_mul_cancel₀ _ (ne_of_gt hx)] at Ds₀x_lt
  have hs₀ := And.intro (le_div_ceil_mul hD hx) Ds₀x_lt.le
  suffices 1 / 4 ≤ D ^ (-(s₀ - 1)) * x ∧ D ^ (-(s₀ - 1)) * x ≤ 1 / 2 by
    rw [ψ_formula₁ hD hs₀, ψ_formula₃ hD this]
    suffices (D : ℝ) ^ (1 - s₀) = D * D ^ (-s₀) by rw [neg_sub, this]; ring
    rw [zpow_sub₀ (ne_of_gt (D0 hD)), zpow_neg, zpow_one, div_eq_mul_inv]
  rw [neg_sub, sub_eq_add_neg, zpow_add₀ (ne_of_gt (D0 hD)), zpow_one, mul_assoc]
  constructor
  · rw [← div_le_iff₀' (D0 hD), div_div]; exact hs₀.1
  · rw [← le_div_iff₀' (D0 hD), div_div]; exact hs₀.2

-- See `finsum_ψ` for the version that doesn't explicitly restrict to the support.
lemma sum_ψ (hx : 0 < x) : ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) = 1 := by
  by_cases h : D ^ (-⌈logb D (4 * x)⌉) ≥ 1 / (2 * D * x)
  · exact sum_ψ₁ hD hx h
  · exact sum_ψ₂ hD hx (lt_of_not_ge h)

--------------------------------------------------
/- Now we prove that `nonzeroS D x` is the support of `s ↦ ψ D (D ^ (-s) * x)`. This converts
`sum_ψ` into `finsum_ψ`, which states that `∑ᶠ s : ℤ, ψ D (D ^ (-s) * x) = 1`. -/

lemma mem_nonzeroS_iff {i : ℤ} {x : ℝ} (hx : 0 < x) :
    i ∈ nonzeroS D x ↔ (D ^ (-i) * x) ∈ Ioo (4 * D : ℝ)⁻¹ 2⁻¹ := by
  rw [mem_Ioo, nonzeroS, Finset.mem_Icc, Int.floor_le_iff, Int.le_ceil_iff, mul_inv_rev,
    add_comm _ 1, Real.add_lt_add_iff_left, ← lt_div_iff₀ hx, mul_comm (D : ℝ)⁻¹,
    ← div_lt_div_iff₀ hx (inv_pos.2 (D0 hD)), div_inv_eq_mul, ← zpow_add_one₀ ((D0 hD).ne.symm),
    zpow_neg, ← Real.rpow_intCast, ← Real.rpow_intCast, lt_logb_iff_rpow_lt hD (four_x0 hx),
    logb_lt_iff_lt_rpow hD (mul_pos two_pos hx), ← sub_eq_neg_add, ← neg_sub i 1, ← inv_mul',
    ← inv_mul', inv_lt_inv₀ (D_pow0 hD _) (mul_pos two_pos hx), Int.cast_neg, Int.cast_sub,
    Int.cast_one, rpow_neg (D0 hD).le, inv_lt_inv₀ (four_x0 hx) (D_pow0 hD _), and_comm]

lemma psi_ne_zero_iff {x : ℝ} (hx : 0 < x) :
    ψ D (D ^ (-s) * x) ≠ 0 ↔ s ∈ nonzeroS D x := by
  rw [← mem_support, support_ψ (by exact_mod_cast hD), mem_nonzeroS_iff hD hx]

lemma psi_eq_zero_iff {x : ℝ} (hx : 0 < x) : ψ D (D ^ (-s) * x) = 0 ↔ s ∉ nonzeroS D x := by
  rw [← iff_not_comm, ← psi_ne_zero_iff hD hx]

lemma support_ψS (hx : 0 < x) : support (fun (s : ℤ) ↦ ψ D (D ^ (-s) * x)) = nonzeroS D x := by
  ext; rw [mem_support]; exact psi_ne_zero_iff hD hx

lemma support_ψS_subset_Icc {b c : ℤ} {x : ℝ}
    (h : x ∈ Icc ((D : ℝ) ^ (b - 1) / 2) (D ^ c / 4)) :
    support (fun (s : ℤ) ↦ ψ D (D ^ (-s) * x)) ⊆ Icc b c := by
  intro i hi
  have hx : x > 0 := lt_of_lt_of_le (by positivity) h.1
  simp only [support_ψS hD hx, nonzeroS, Finset.coe_Icc, mem_Icc] at hi
  simp only [toFinset_Icc, Finset.coe_Icc, mem_Icc]
  refine ⟨le_trans ?_ hi.1, le_trans hi.2 ?_⟩
  · rw [← Nat.cast_one, Int.floor_nat_add, Nat.cast_one, ← sub_le_iff_le_add', Int.le_floor,
      Real.le_logb_iff_rpow_le hD (mul_pos two_pos hx), mul_comm]
    exact_mod_cast (div_le_iff₀ two_pos).mp h.1
  · rw [Int.ceil_le, Real.logb_le_iff_le_rpow hD (mul_pos four_pos hx), mul_comm]
    exact_mod_cast (le_div_iff₀ four_pos).mp h.2

lemma finsum_ψ (hx : 0 < x) : ∑ᶠ s : ℤ, ψ D (D ^ (-s) * x) = 1 := by
  refine Eq.trans ?_ (sum_ψ hD hx)
  apply Eq.trans <| finsum_eq_sum _ <| support_ψS hD hx ▸ Finset.finite_toSet (nonzeroS D x)
  congr
  ext
  rw [Finite.mem_toFinset, support_ψS hD hx, Finset.mem_coe]

lemma sum_ψ_le (S : Finset ℤ) (hx : 0 < x) : ∑ s ∈ S, ψ D (D ^ (-s) * x) ≤ 1 := calc
  _ = ∑ s ∈ S ∩ (nonzeroS D x), ψ D (D ^ (-s) * x) := by
    refine (Finset.sum_subset Finset.inter_subset_left (fun s sS hs ↦ ?_)).symm
    exact (psi_eq_zero_iff hD hx).mpr (fun h ↦ hs <| Finset.mem_inter.mpr ⟨sS, h⟩)
  _ ≤ ∑ s ∈ nonzeroS D x, ψ D (D ^ (-s) * x) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ ↦ zero_le_ψ ..)
  _ = 1 := sum_ψ hD hx

end include_hD

end D

open Complex

open scoped ShortVariables
variable (X : Type*) {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [ProofData a q K σ₁ σ₂ F G]
variable {s : ℤ} {x y : X}

section -- Again, we start by recording some trivial inequalities that will be needed repeatedly.
include q K σ₁ σ₂ F G
private lemma a0' : a > 0 := by linarith [four_le_a X]
private lemma a0 : (a : ℝ) > 0 := by exact_mod_cast (a0' X)
private lemma D1 : (D : ℝ) > 1 := by norm_cast; norm_num; exact (a0' X).ne.symm
private lemma D0' : (D : ℝ) > 0 := one_pos.trans (D1 X)
private lemma D0'' : D > 0 := by exact_mod_cast (D0' X)
private lemma Ds0 (s : ℤ) : (D : ℝ) ^ s > 0 := have := D0' X; by positivity
end

variable {X}

/-- K_s in the blueprint -/
@[nolint unusedArguments]
def Ks [ProofData a q K σ₁ σ₂ F G] (s : ℤ) (x y : X) : ℂ :=
  K x y * ψ (D ^ (-s) * dist x y)

lemma Ks_def (s : ℤ) (x y : X) : Ks s x y = K x y * ψ (D ^ (-s) * dist x y) := rfl

lemma sum_Ks {t : Finset ℤ} (hs : nonzeroS D (dist x y) ⊆ t) (hD : 1 < (D : ℝ)) (h : 0 < dist x y) :
    ∑ i ∈ t, Ks i x y = K x y := by
  simp_rw [Ks, ← Finset.mul_sum]
  norm_cast
  suffices ∑ i ∈ t, ψ (D ^ (-i) * dist x y) = 1 by rw [this, ofReal_one, mul_one]
  rw [← Finset.sum_subset hs, sum_ψ hD h]
  intros
  rwa [psi_eq_zero_iff hD h]

-- maybe this version is also useful?
-- lemma sum_Ks' {t : Finset ℤ}
--     (hs : ∀ i : ℤ, (D ^ i * dist x y) ∈ Ioo (4 * D)⁻¹ 2⁻¹ → i ∈ t)
--     (hD : 1 < D) (h : x ≠ y) : ∑ i ∈ t, Ks i x y = K x y := by
--   sorry

/- Start of proof attempt -/
lemma round1_h1 (X : Type*) 
  [PseudoMetricSpace X]
  {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G]
  {s : ℤ} {x y : X}
  (h : Ks s x y ≠ 0):
  ψ ((D : ℝ) ^ (-s) * dist x y) ≠ 0 := by
  by_contra h10
  have h11 : Ks s x y = 0 := by
    rw [Ks_def]
    rw [h10]
    simp
  contradiction

lemma round1_h31 (X : Type*) 
  [PseudoMetricSpace X]
  {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G]
  {s : ℤ} {x y : X}
  (h1 : ψ ((D : ℝ) ^ (-s) * dist x y) ≠ 0):
  (4 * (D : ℝ))⁻¹ < (D : ℝ) ^ (-s) * dist x y := by
  by_contra h31
  have h311 : (D : ℝ) ^ (-s) * dist x y ≤ (4 * (D : ℝ))⁻¹ := by linarith
  have h312 : (D : ℝ) ^ (-s) * dist x y ≤ 1 / (4 * (D : ℝ)) := by
    have h101 : (4 * (D : ℝ))⁻¹ = 1 / (4 * (D : ℝ)) := by ring
    linarith
  have h313 : ψ ((D : ℝ) ^ (-s) * dist x y) = 0 := by
    apply ψ_formula₀
    linarith
  contradiction

lemma round1_h32 (X : Type*) 
  [PseudoMetricSpace X]
  {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G]
  {s : ℤ} {x y : X}
  (h1 : ψ ((D : ℝ) ^ (-s) * dist x y) ≠ 0):
  (D : ℝ) ^ (-s) * dist x y < (2 : ℝ)⁻¹ := by
  by_contra h32
  have h321 : (D : ℝ) ^ (-s) * dist x y ≥ (2 : ℝ)⁻¹ := by linarith
  have h322 : ψ ((D : ℝ) ^ (-s) * dist x y) = 0 := by
    apply ψ_formula₄
    linarith
  contradiction

lemma round1_h_ineq1 (X : Type*) 
  [PseudoMetricSpace X]
  {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G]
  {s : ℤ} {x y : X}
  (h31 : (4 * (D : ℝ))⁻¹ < (D : ℝ) ^ (-s) * dist x y)
  (h32 : (D : ℝ) ^ (-s) * dist x y < (2 : ℝ)⁻¹):
  dist x y < (D : ℝ) ^ s / 2 := by
  have h_pos1 : 0 < (D : ℝ) := by linarith [D1 X]
  have h_pos2 : 0 < (D : ℝ) ^ s := by positivity
  have h5 : (D : ℝ) ^ (-s) * dist x y < (2 : ℝ)⁻¹ := h32
  have h51 : (D : ℝ) ^ (-s) * dist x y < 1 / 2 := by
    norm_num at h5 ⊢ <;> linarith
  have h52 : 0 < (D : ℝ) ^ s := by positivity
  have h : ((D : ℝ) ^ (-s) * dist x y) * ((D : ℝ) ^ s) < (1 / 2) * ((D : ℝ) ^ s) := by
    nlinarith
  have h53 : ((D : ℝ) ^ (-s) * dist x y) * ((D : ℝ) ^ s) = dist x y := by
    have h531 : (D : ℝ) ^ (-s) * (D : ℝ) ^ s = 1 := by
      have h5311 : (D : ℝ) ^ (-s) * (D : ℝ) ^ s = (D : ℝ) ^ (-s + s) := by
        rw [← zpow_add₀ (by linarith : (D : ℝ) ≠ 0)]
        <;> ring
      have h5312 : -s + s = (0 : ℤ) := by ring
      rw [h5311, h5312]
      norm_num
    calc
      ((D : ℝ) ^ (-s) * dist x y) * ((D : ℝ) ^ s) = ((D : ℝ) ^ (-s) * (D : ℝ) ^ s) * dist x y := by ring
      _ = 1 * dist x y := by rw [h531]
      _ = dist x y := by ring
  have h54 : dist x y < (1 / 2) * ((D : ℝ) ^ s) := by linarith
  have h55 : (1 / 2) * ((D : ℝ) ^ s) = (D : ℝ) ^ s / 2 := by ring
  linarith

lemma round1_h_ineq2 (X : Type*) 
  [PseudoMetricSpace X]
  {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [ProofData a q K σ₁ σ₂ F G]
  {s : ℤ} {x y : X}
  (h31 : (4 * (D : ℝ))⁻¹ < (D : ℝ) ^ (-s) * dist x y)
  (h32 : (D : ℝ) ^ (-s) * dist x y < (2 : ℝ)⁻¹):
  (D : ℝ) ^ (s - 1) / 4 < dist x y := by
  have hD_pos : 0 < (D : ℝ) := by linarith [D1 X]
  have h4 : 0 < 4 * (D : ℝ) ^ s := by positivity
  have h9 : (4 * (D : ℝ))⁻¹ * (4 * (D : ℝ) ^ s) < ((D : ℝ) ^ (-s) * dist x y) * (4 * (D : ℝ) ^ s) := by
    have h91 : 0 < 4 * (D : ℝ) ^ s := by positivity
    nlinarith
  have h10 : (4 * (D : ℝ))⁻¹ * (4 * (D : ℝ) ^ s) = (D : ℝ) ^ (s - 1) := by
    have h101 : (4 * (D : ℝ))⁻¹ * (4 * (D : ℝ) ^ s) = (D : ℝ) ^ s / (D : ℝ) := by
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring
    have h102 : (D : ℝ) ^ (s - 1) = (D : ℝ) ^ s / (D : ℝ) := by
      have h1021 : (D : ℝ) ≠ 0 := by linarith
      have h : (D : ℝ) ^ (s - 1) = (D : ℝ) ^ s / (D : ℝ) := by
        rw [show s - 1 = s + (-1 : ℤ) by ring]
        rw [zpow_add₀ h1021]
        simp [zpow_neg, zpow_one]
        <;> field_simp
        <;> ring
      linarith
    linarith
  have h11 : ((D : ℝ) ^ (-s) * dist x y) * (4 * (D : ℝ) ^ s) = 4 * dist x y := by
    have h111 : (D : ℝ) ^ (-s) * (D : ℝ) ^ s = 1 := by
      have h1111 : (D : ℝ) ≠ 0 := by linarith
      have h : (D : ℝ) ^ (-s) * (D : ℝ) ^ s = (D : ℝ) ^ (-s + s) := by
        rw [← zpow_add₀ h1111]
        <;> ring
      have h2 : -s + s = (0 : ℤ) := by ring
      rw [h, h2]
      norm_num
    have h112 : ((D : ℝ) ^ (-s) * dist x y) * (4 * (D : ℝ) ^ s) = 4 * dist x y * ((D : ℝ) ^ (-s) * (D : ℝ) ^ s) := by
      ring
    rw [h112, h111]
    <;> ring
  have h12 : (D : ℝ) ^ (s - 1) < 4 * dist x y := by linarith
  have h13 : (D : ℝ) ^ (s - 1) / 4 < dist x y := by linarith
  linarith

theorem dist_mem_Ioo_of_Ks_ne_zero {s : ℤ} {x y : X} (h : Ks s x y ≠ 0) :
    dist x y ∈ Ioo ((D ^ (s - 1) : ℝ) / 4) (D ^ s / 2)  := by

  have h1 : ψ ((D : ℝ) ^ (-s) * dist x y) ≠ 0 := by
    exact round1_h1 X h

  have h31 : (4 * (D : ℝ))⁻¹ < (D : ℝ) ^ (-s) * dist x y := by
    exact round1_h31 X h1

  have h32 : (D : ℝ) ^ (-s) * dist x y < (2 : ℝ)⁻¹ := by
    exact round1_h32 X h1

  have h_ineq1 : dist x y < (D : ℝ) ^ s / 2 := by
    exact round1_h_ineq1 X h31 h32

  have h_ineq2 : (D : ℝ) ^ (s - 1) / 4 < dist x y := by
    exact round1_h_ineq2 X h31 h32

  exact ⟨h_ineq2, h_ineq1⟩
