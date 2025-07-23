-- In carleson/Carleson/ToMathlib/HardyLittlewood.lean

import Carleson.ToMathlib.DoublingMeasure
import Carleson.ToMathlib.RealInterpolation
import Mathlib.MeasureTheory.Covering.Vitali

open MeasureTheory Metric Bornology Set TopologicalSpace Vitali Filter ENNReal Pointwise
open scoped NNReal
noncomputable section

/-! This should roughly contain the contents of chapter 9. -/

section Prelude

variable {X : Type*} [PseudoMetricSpace X] [SeparableSpace X]

variable (X) in
/-- Lemma 9.0.2 -/
lemma covering_separable_space :
    ∃ C : Set X, C.Countable ∧ ∀ r > 0, ⋃ c ∈ C, ball c r = univ := by
  simp_rw [← Metric.dense_iff_iUnion_ball, exists_countable_dense]

lemma countable_globalMaximalFunction :
    (covering_separable_space X).choose ×ˢ (univ : Set ℤ) |>.Countable :=
  (covering_separable_space X).choose_spec.1.prod countable_univ

lemma exists_ball_subset_ball_two (c : X) {r : ℝ} (hr : 0 < r) :
    ∃ c' ∈ (covering_separable_space X).choose,
      ∃ m : ℤ, ball c r ⊆ ball c' (2 ^ m) ∧ 2 ^ m ≤ 2 * r ∧ ball c' (2 ^ m) ⊆ ball c (4 * r) := by
  obtain ⟨_, hCr⟩ := (covering_separable_space X).choose_spec
  let m := ⌊Real.logb 2 r⌋
  have hm : 2 ^ m ≤ r := by
    calc _ ≤ (2 : ℝ) ^ (Real.logb 2 r) := by
          convert Real.monotone_rpow_of_base_ge_one one_le_two (Int.floor_le _)
          exact (Real.rpow_intCast 2 m).symm
      _ = _ := Real.rpow_logb zero_lt_two (OfNat.one_ne_ofNat 2).symm hr
  have hm' : r < 2 ^ (m + 1) := by
    calc _ = (2 : ℝ) ^ Real.logb 2 r := (Real.rpow_logb zero_lt_two (OfNat.one_ne_ofNat 2).symm hr).symm
      _ < _ := by
        rw [← Real.rpow_intCast 2 (m + 1)]
        refine Real.strictMono_rpow_of_base_gt_one one_lt_two ?_
        simp [m]
  let a := ((2 : ℝ) ^ (m + 1) - r) / 2
  have h_univ := hCr a (by simp [a, hm'])
  obtain ⟨c', hc', hcc'⟩ := mem_iUnion₂.mp <| h_univ ▸ Set.mem_univ c
  refine ⟨c', hc', m + 1, ball_subset_ball_of_le ?_, ?_, ?_⟩
  · calc
      _ ≤ a + r := by gcongr; exact (dist_comm c c' ▸ mem_ball.mp hcc').le
      _ ≤ _ := by simp only [a, sub_div]; linarith
  · rw [← Real.rpow_intCast 2 (m + 1)]
    push_cast
    rw [Real.rpow_add_one two_ne_zero m, mul_comm]
    gcongr
    exact_mod_cast hm
  · refine ball_subset_ball_of_le ?_
    calc
      _ ≤ a + 2 ^ (m + 1) := by gcongr; exact (mem_ball.mp hcc').le
      _ ≤ 2 ^ (m + 1) + 2 ^ (m + 1) := by
        gcongr
        simp only [a]
        linarith
      _ ≤ 2 * r + 2 * r := by
        rw [← Real.rpow_intCast 2 (m + 1)]
        push_cast
        rw [Real.rpow_add_one two_ne_zero m, mul_comm]
        gcongr <;> simp [hm]
      _ = 4 * r := by ring

end Prelude

variable {X E : Type*} {A : ℝ≥0} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsDoubling A] [NormedAddCommGroup E]
  {f : X → E} {x : X} {ι : Type*} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ}
  -- feel free to assume `A ≥ 16` or similar

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑.
M_{𝓑, p} in the blueprint. -/
def maximalFunction (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ)
    (p : ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  (⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
    fun _ ↦ ⨍⁻ y in ball (c i) (r i), ‖u y‖₊ ^ p ∂μ) ^ p⁻¹

/-- The Hardy-Littlewood maximal function w.r.t. a collection of balls 𝓑 with exponent 1.
M_𝓑 in the blueprint. -/
abbrev MB (μ : Measure X) (𝓑 : Set ι) (c : ι → X) (r : ι → ℝ) (u : X → E) (x : X) : ℝ≥0∞ :=
  maximalFunction μ 𝓑 c r 1 u x

lemma maximalFunction_eq_MB
    {μ : Measure X} {𝓑 : Set ι} {c : ι → X} {r : ι → ℝ} {p : ℝ} {u : X → E} {x : X} (hp : 0 ≤ p) :
    maximalFunction μ 𝓑 c r p u x = (MB μ 𝓑 c r (‖u ·‖ ^ p) x) ^ p⁻¹ := by
  unfold MB maximalFunction; rw [← ENNReal.rpow_mul, inv_one, one_mul]; congr! 8
  rw [ENNReal.rpow_one, ← ENNReal.coe_rpow_of_nonneg _ hp, ENNReal.coe_inj,
    Real.nnnorm_rpow_of_nonneg (by simp), nnnorm_norm]

-- We will replace the criterion `P` used in `MeasureTheory.AESublinearOn.maximalFunction` with the
-- weaker criterion `LocallyIntegrable` that is closed under addition and scalar multiplication.

-- The average that appears in the definition of `MB`
variable (μ c r) in
private def T (i : ι) (u : X → E) := ⨍⁻ (y : X) in ball (c i) (r i), ‖u y‖₊ ∂μ

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_of_isBounded [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {s : Set X}
    (hs : IsBounded s) : IntegrableOn f s μ :=
  hf.integrableOn_isCompact hs.isCompact_closure |>.mono_set subset_closure

-- move
lemma MeasureTheory.LocallyIntegrable.integrableOn_ball [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ) {x : X} {r : ℝ} : IntegrableOn f (ball x r) μ :=
  hf.integrableOn_of_isBounded isBounded_ball

-- move
lemma MeasureTheory.LocallyIntegrable.laverage_ball_lt_top [ProperSpace X]
    {f : X → E} (hf : LocallyIntegrable f μ)
    {x₀ : X} {r : ℝ} :
    ⨍⁻ x in ball x₀ r, ‖f x‖₊ ∂μ < ⊤ :=
  laverage_lt_top hf.integrableOn_ball.2.ne

private lemma T.add_le [MeasurableSpace E] [BorelSpace E] [BorelSpace X] [ProperSpace X]
    (i : ι) {f g : X → E} (hf : LocallyIntegrable f μ) :
    ‖T μ c r i (f + g)‖ₑ ≤ ‖T μ c r i f‖ₑ + ‖T μ c r i g‖ₑ := by
  simp only [T, Pi.add_apply, enorm_eq_self, ← enorm_eq_nnnorm]
  rw [← laverage_add_left hf.integrableOn_ball.aemeasurable.enorm]
  exact laverage_mono (fun x ↦ ENNNorm_add_le (f x) (g x))

-- move
lemma NNReal.smul_ennreal_eq_mul (x : ℝ≥0) (y : ℝ≥0∞) : x • y = x * y := rfl

private lemma T.smul [NormedSpace ℝ E] (i : ι) : ∀ {f : X → E} {d : ℝ≥0}, LocallyIntegrable f μ →
    T μ c r i (d • f) = d • T μ c r i f := by
  intro f d _
  simp_rw [T, Pi.smul_apply, NNReal.smul_def, NNReal.smul_ennreal_eq_mul,
    laverage_const_mul ENNReal.coe_ne_top]
  simp [nnnorm_smul]

-- todo: move
-- slightly more general than the Mathlib version
-- the extra conclusion says that if there is a nonnegative radius, then we can choose `r b` to be
-- larger than `r a` (up to a constant)
theorem exists_disjoint_subfamily_covering_enlargement_closedBall' {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => closedBall (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
        (∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b) := by
  rcases eq_empty_or_nonempty t with (rfl | _)
  · exact ⟨∅, Subset.refl _, pairwiseDisjoint_empty, by simp⟩
  by_cases ht : ∀ a ∈ t, r a < 0
  · refine ⟨t, .rfl, fun a ha b _ _ ↦ by
      simp only [Function.onFun, closedBall_eq_empty.2 (ht a ha), empty_disjoint],
      fun a ha => ⟨a, ha, by simp only [closedBall_eq_empty.2 (ht a ha), empty_subset],
      fun u hut hu ↦ (ht u hut).not_le hu |>.elim⟩⟩
  push_neg at ht
  let t' := { a ∈ t | 0 ≤ r a }
  have h2τ : 1 < (τ - 1) / 2 := by linarith
  rcases exists_disjoint_subfamily_covering_enlargement (fun a => closedBall (x a) (r a)) t' r
      ((τ - 1) / 2) h2τ (fun a ha => ha.2) R (fun a ha => hr a ha.1) fun a ha =>
      ⟨x a, mem_closedBall_self ha.2⟩ with
    ⟨u, ut', u_disj, hu⟩
  have A : ∀ a ∈ t', ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (τ * r b) ∧
    ∀ u ∈ t, 0 ≤ r u → r a ≤ (τ - 1) / 2 * r b := by
    intro a ha
    rcases hu a ha with ⟨b, bu, hb, rb⟩
    refine ⟨b, bu, ?_⟩
    have : dist (x a) (x b) ≤ r a + r b := dist_le_add_of_nonempty_closedBall_inter_closedBall hb
    exact ⟨closedBall_subset_closedBall' <| by linarith, fun _ _ _ ↦ rb⟩
  refine ⟨u, ut'.trans fun a ha => ha.1, u_disj, fun a ha => ?_⟩
  rcases le_or_lt 0 (r a) with (h'a | h'a)
  · exact A a ⟨ha, h'a⟩
  · rcases ht with ⟨b, rb⟩
    rcases A b ⟨rb.1, rb.2⟩ with ⟨c, cu, _, hc⟩
    refine ⟨c, cu, by simp only [closedBall_eq_empty.2 h'a, empty_subset], fun _ _ _ ↦ ?_⟩
    have : 0 ≤ r c := nonneg_of_mul_nonneg_right (rb.2.trans <| hc b rb.1 rb.2) (by positivity)
    exact h'a.le.trans <| by positivity

-- move to Vitali
theorem Vitali.exists_disjoint_subfamily_covering_enlargement_ball {α} [MetricSpace α] (t : Set ι)
    (x : ι → α) (r : ι → ℝ) (R : ℝ) (hr : ∀ a ∈ t, r a ≤ R) (τ : ℝ) (hτ : 3 < τ) :
    ∃ u ⊆ t,
      (u.PairwiseDisjoint fun a => ball (x a) (r a)) ∧
        ∀ a ∈ t, ∃ b ∈ u, ball (x a) (r a) ⊆ ball (x b) (τ * r b) := by
  obtain ⟨σ, hσ, hστ⟩ := exists_between hτ
  obtain ⟨u, hut, hux, hu⟩ :=
    exists_disjoint_subfamily_covering_enlargement_closedBall' t x r R hr σ hσ
  refine ⟨u, hut, fun i hi j hj hij ↦ ?_, fun a ha => ?_⟩
  · exact (hux hi hj hij).mono ball_subset_closedBall ball_subset_closedBall
  obtain ⟨b, hbu, hb⟩ := hu a ha
  refine ⟨b, hbu, ?_⟩
  obtain h2a|h2a := le_or_lt (r a) 0
  · simp_rw [ball_eq_empty.mpr h2a, empty_subset]
  refine ball_subset_closedBall.trans hb.1 |>.trans <| closedBall_subset_ball ?_
  gcongr
  apply pos_of_mul_pos_right <| h2a.trans_le <| hb.2 a ha h2a.le
  linarith

-- move next to Finset.exists_le
lemma Finset.exists_image_le {α β} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)]
    (s : Finset α) (f : α → β) : ∃ b : β, ∀ a ∈ s, f a ≤ b := by
  classical
  simpa using s.image f |>.exists_le

-- move
lemma Set.Finite.exists_image_le {α β} [Nonempty β] [Preorder β] [IsDirected β (· ≤ ·)]
    {s : Set α} (hs : s.Finite) (f : α → β) : ∃ b : β, ∀ a ∈ s, f a ≤ b := by
  simpa using hs.toFinset.exists_image_le f

theorem Set.Countable.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (h𝓑 : 𝓑.Countable)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞) (R : ℝ) (hR : ∀ a ∈ 𝓑, r a ≤ R)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  := by
  obtain ⟨B, hB𝓑, hB, h2B⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    𝓑 c r R hR (2 ^ 2) (by norm_num)
  have : Countable B := h𝓑.mono hB𝓑
  have disj := fun i j hij ↦
    hB (Subtype.coe_prop i) (Subtype.coe_prop j) (Subtype.coe_ne_coe.mpr hij)
  calc
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ l * μ (⋃ i ∈ B, ball (c i) (2 ^ 2 * r i)) := by
          refine mul_left_mono (μ.mono fun x hx ↦ ?_)
          simp only [mem_iUnion, mem_ball, exists_prop] at hx
          rcases hx with ⟨i, i𝓑, hi⟩
          obtain ⟨b, bB, hb⟩ := h2B i i𝓑
          refine mem_iUnion₂.mpr ⟨b, bB, hb <| mem_ball.mpr hi⟩
    _ ≤ l * ∑' i : B, μ (ball (c i) (2 ^ 2 * r i)) :=
          mul_left_mono <| measure_biUnion_le μ (h𝓑.mono hB𝓑) fun i ↦ ball (c i) (2 ^ 2 * r i)
    _ ≤ l * ∑' i : B, A ^ 2 * μ (ball (c i) (r i)) := by
          refine mul_left_mono <| ENNReal.tsum_le_tsum (fun i ↦ ?_)
          rw [sq, sq, mul_assoc, mul_assoc]
          apply (measure_ball_two_le_same (c i) (2 * r i)).trans
          exact mul_left_mono (measure_ball_two_le_same (c i) (r i))
    _ = A ^ 2 * ∑' i : B, l * μ (ball (c i) (r i)) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc, mul_comm l]
    _ ≤ A ^ 2 * ∑' i : B, ∫⁻ x in ball (c i) (r i), u x ∂μ := by
          gcongr; exact h2u _ (hB𝓑 (Subtype.coe_prop _))
    _ = A ^ 2 * ∫⁻ x in ⋃ i ∈ B, ball (c i) (r i), u x ∂μ := by
          congr; simpa using (lintegral_iUnion (fun i ↦ measurableSet_ball) disj u).symm
    _ ≤ A ^ 2 * ∫⁻ x, u x ∂μ := by
          gcongr; exact setLIntegral_le_lintegral (⋃ i ∈ B, ball (c i) (r i)) u

protected theorem Finset.measure_biUnion_le_lintegral [OpensMeasurableSpace X] (𝓑 : Finset ι)
    (l : ℝ≥0∞) (u : X → ℝ≥0∞)
    (h2u : ∀ i ∈ 𝓑, l * μ (ball (c i) (r i)) ≤ ∫⁻ x in ball (c i) (r i), u x ∂μ) :
    l * μ (⋃ i ∈ 𝓑, ball (c i) (r i)) ≤ A ^ 2 * ∫⁻ x, u x ∂μ  :=
  let ⟨c, hc⟩ := 𝓑.exists_image_le r
  𝓑.countable_toSet.measure_biUnion_le_lintegral l u c hc h2u

protected theorem MeasureTheory.AEStronglyMeasurable.maximalFunction [BorelSpace X] {p : ℝ}
    {u : X → E} (h𝓑 : 𝓑.Countable) : AEStronglyMeasurable (maximalFunction μ 𝓑 c r p u) μ :=
  (AEMeasurable.biSup 𝓑 h𝓑 fun _ _ ↦ aemeasurable_const.indicator measurableSet_ball).pow
    aemeasurable_const |>.aestronglyMeasurable

theorem MeasureTheory.AEStronglyMeasurable.maximalFunction_toReal [BorelSpace X]
    {p : ℝ} {u : X → E} (h𝓑 : 𝓑.Countable) :
    AEStronglyMeasurable (fun x ↦ maximalFunction μ 𝓑 c r p u x |>.toReal) μ :=
  AEStronglyMeasurable.maximalFunction h𝓑 |>.ennreal_toReal

theorem MB_le_eLpNormEssSup {u : X → E} {x : X} : MB μ 𝓑 c r u x ≤ eLpNormEssSup u μ :=
  calc MB μ 𝓑 c r u x ≤
    ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x)
        fun _x ↦ ⨍⁻ _y in ball (c i) (r i), eLpNormEssSup u μ ∂μ := by
        simp_rw [MB, maximalFunction, inv_one, ENNReal.rpow_one]
        gcongr
        exact coe_nnnorm_ae_le_eLpNormEssSup u μ
    _ ≤ ⨆ i ∈ 𝓑, (ball (c i) (r i)).indicator (x := x) fun _x ↦ eLpNormEssSup u μ := by
      gcongr; apply setLaverage_const_le
    _ ≤ ⨆ i ∈ 𝓑, eLpNormEssSup u μ := by gcongr; apply indicator_le_self
    _ ≤ eLpNormEssSup u μ := by
      simp_rw [iSup_le_iff, le_refl, implies_true]

protected theorem HasStrongType.MB_top [BorelSpace X] (h𝓑 : 𝓑.Countable) :
    HasStrongType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) ⊤ ⊤ μ μ 1 := by
  intro f _
  use AEStronglyMeasurable.maximalFunction_toReal h𝓑
  simp only [ENNReal.coe_one, one_mul, eLpNorm_exponent_top]
  refine essSup_le_of_ae_le _ (Eventually.of_forall fun x ↦ ?_)
  simp_rw [enorm_eq_nnnorm, ENNReal.nnorm_toReal]
  exact ENNReal.coe_toNNReal_le_self |>.trans MB_le_eLpNormEssSup

/- The proof is roughly between (9.0.12)-(9.0.22). -/
protected theorem HasWeakType.MB_one [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (MB (E := E) μ 𝓑 c r) 1 1 μ μ (A ^ 2) := by
  intro f _
  use AEStronglyMeasurable.maximalFunction h𝓑
  let Bₗ (ℓ : ℝ≥0∞) := { i ∈ 𝓑 | ∫⁻ y in (ball (c i) (r i)), ‖f y‖₊ ∂μ ≥ ℓ * μ (ball (c i) (r i)) }
  simp only [wnorm, one_ne_top, wnorm', one_toReal, inv_one, ENNReal.rpow_one, reduceIte,
    ENNReal.coe_pow, eLpNorm, one_ne_zero, eLpNorm', ne_eq, not_false_eq_true, div_self,
    iSup_le_iff]
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hBₗ : (Bₗ t).Countable := h𝓑.mono (fun i hi ↦ mem_of_mem_inter_left hi)
  refine le_trans ?_ (hBₗ.measure_biUnion_le_lintegral (c := c) (r := r) (l := t)
    (u := fun x ↦ ‖f x‖₊) (R := R) ?_ ?_)
  · refine mul_left_mono <| μ.mono (fun x hx ↦ mem_iUnion₂.mpr ?_)
    -- We need a ball in `Bₗ t` containing `x`. Since `MB μ 𝓑 c r f x` is large, such a ball exists
    simp only [mem_setOf_eq] at hx
    -- replace hx := lt_of_lt_of_le hx coe_toNNReal_le_self
    simp only [MB, maximalFunction, ENNReal.rpow_one, inv_one] at hx
    obtain ⟨i, ht⟩ := lt_iSup_iff.mp hx
    replace hx : x ∈ ball (c i) (r i) :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    refine ⟨i, ?_, hx⟩
    -- It remains only to confirm that the chosen ball is actually in `Bₗ t`
    simp only [ge_iff_le, mem_setOf_eq, Bₗ]
    have hi : i ∈ 𝓑 :=
      by_contradiction <| fun h ↦ not_lt_of_ge (zero_le t) (ENNReal.coe_lt_coe.mp <| by simp [h] at ht)
    exact ⟨hi, mul_le_of_le_div <| le_of_lt (by simpa [setLaverage_eq, hi, hx] using ht)⟩
  · exact fun i hi ↦ hR i (mem_of_mem_inter_left hi)
  · exact fun i hi ↦ hi.2.trans (setLIntegral_mono' measurableSet_ball fun x _ ↦ by simp)

protected theorem HasWeakType.MB_one_toReal [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R) :
    HasWeakType (fun (u : X → E) (x : X) ↦ MB μ 𝓑 c r u x |>.toReal) 1 1 μ μ (A ^ 2) :=
  HasWeakType.MB_one h𝓑 hR |>.toReal

include A in
theorem MB_ae_ne_top [BorelSpace X] (h𝓑 : 𝓑.Countable)
    {R : ℝ} (hR : ∀ i ∈ 𝓑, r i ≤ R)
    {u : X → E} (hu : Memℒp u 1 μ) : ∀ᵐ x : X ∂μ, MB μ 𝓑 c r u x ≠ ∞ := by
  simpa only [enorm_eq_self] using HasWeakType.MB_one h𝓑 hR |>.memWℒp hu |>.ae_ne_top

-- move

/- Start of proof attempt -/
lemma round1_Memℒp_eLpNormEssSup_lt_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → E} (hu : Memℒp u ⊤ μ) : eLpNormEssSup u μ < ⊤ := by
  exact hu.2

theorem MeasureTheory.Memℒp.eLpNormEssSup_lt_top {α} [MeasurableSpace α] {μ : Measure α}
    {u : α → E} (hu : Memℒp u ⊤ μ) : eLpNormEssSup u μ < ⊤  := by

  exact round1_Memℒp_eLpNormEssSup_lt_top hu
