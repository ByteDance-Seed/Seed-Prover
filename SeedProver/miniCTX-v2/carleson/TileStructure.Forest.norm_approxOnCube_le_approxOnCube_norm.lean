-- In carleson/Carleson/ForestOperator/PointwiseEstimate.lean

import Carleson.Forest
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.ToMathlib.Misc
import Carleson.Psi

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.1 and Lemma 7.1.3 -/

variable (t) in
/-- The definition `σ(u, x)` given in Section 7.1.
We may assume `u ∈ t` whenever proving things about this definition. -/
def σ (u : 𝔓 X) (x : X) : Finset ℤ := .image 𝔰 { p | p ∈ t u ∧ x ∈ E p }

variable (t) in
private lemma exists_p_of_mem_σ (u : 𝔓 X) (x : X) {s : ℤ} (hs : s ∈ t.σ u x) :
    ∃ p ∈ t.𝔗 u, x ∈ E p ∧ 𝔰 p = s := by
  have ⟨p, hp⟩ := Finset.mem_image.mp hs
  simp only [mem_𝔗, Finset.mem_filter] at hp
  use p, hp.1.2.1, hp.1.2.2, hp.2

/- \overline{σ} from the blueprint. -/
variable (t) in
def σMax (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.max' hσ

/- \underline{σ} from the blueprint. -/
variable (t) in
def σMin (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.min' hσ

variable (t) in
private lemma σMax_mem_σ (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : σMax t u x hσ ∈ t.σ u x :=
  (t.σ u x).max'_mem hσ

/-- The definition of `𝓙₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓙₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {J : Grid X | s J = -S ∨ ∀ p ∈ 𝔖, ¬(𝓘 p : Set X) ⊆ ball (c J) (100 * D ^ (s J + 1))}

/-- The definition of `𝓙(𝔖), defined above Lemma 7.1.2 -/
def 𝓙 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓙₀ 𝔖) x}

lemma 𝓙_subset_𝓙₀ {𝔖 : Set (𝔓 X)} : 𝓙 𝔖 ⊆ 𝓙₀ 𝔖 := sep_subset ..

lemma pairwiseDisjoint_𝓙 : (𝓙 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓙 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

/-- The definition of `𝓛₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓛₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {L : Grid X | s L = -S ∨ (∃ p ∈ 𝔖, L ≤ 𝓘 p) ∧ ∀ p ∈ 𝔖, ¬𝓘 p ≤ L}

/-- The definition of `𝓛(𝔖), defined above Lemma 7.1.2 -/
def 𝓛 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓛₀ 𝔖) x}

lemma 𝓛_subset_𝓛₀ {𝔖 : Set (𝔓 X)} : 𝓛 𝔖 ⊆ 𝓛₀ 𝔖 := sep_subset ..

private lemma s_le_s_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖)
    {p : 𝔓 X} (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : s L ≤ s (𝓘 p) := by
  simp only [𝓛, 𝓛₀, Grid.le_def, not_and, not_le, and_imp] at hL
  rcases hL.1 with h | h
  · exact h ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1
  · by_contra!
    exact lt_asymm this <| h.2 p hp <| (GridStructure.fundamental_dyadic' this.le).resolve_right hpL

private lemma subset_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖) {p : 𝔓 X}
    (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : (L : Set X) ⊆ (𝓘 p : Set X) :=
  GridStructure.fundamental_dyadic' (s_le_s_of_mem_𝓛 hL hp hpL) |>.resolve_right fun h ↦ hpL h.symm

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x

lemma stronglyMeasurable_approxOnCube (C : Set (Grid X)) (f : X → E') :
    StronglyMeasurable (approxOnCube (X := X) (K := K) C f) :=
  Finset.stronglyMeasurable_sum _ (fun _ _ ↦ stronglyMeasurable_const.indicator coeGrid_measurable)

lemma integrable_approxOnCube (C : Set (Grid X)) {f : X → E'} : Integrable (approxOnCube C f) := by
  refine integrable_finset_sum _ (fun i hi ↦ ?_)
  constructor
  · exact (aestronglyMeasurable_indicator_iff coeGrid_measurable).mpr aestronglyMeasurable_const
  · simp_rw [hasFiniteIntegral_iff_enorm, enorm_indicator_eq_indicator_enorm]
    apply lt_of_le_of_lt <| lintegral_indicator_const_le (i : Set X) _
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top volume_coeGrid_lt_top

lemma approxOnCube_nonneg {C : Set (Grid X)} {f : X → ℝ} (hf : ∀ (y : X), f y ≥ 0) {x : X} :
    approxOnCube C f x ≥ 0 :=
  Finset.sum_nonneg' (fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ integral_nonneg hf) _)

lemma approxOnCube_apply {C : Set (Grid X)} (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    (f : X → E') {x : X} {J : Grid X} (hJ : J ∈ C) (xJ : x ∈ J) :
    (approxOnCube C f) x = ⨍ y in J, f y := by
  rw [approxOnCube, ← Finset.sum_filter_not_add_sum_filter _ (J = ·)]
  have eq0 : ∑ i ∈ Finset.filter (¬ J = ·) (Finset.univ.filter (· ∈ C)),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 := by
    suffices ∀ i ∈ (Finset.univ.filter (· ∈ C)).filter (¬ J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 by simp [Finset.sum_congr rfl this]
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply indicator_of_not_mem <|
      Set.disjoint_left.mp ((hC.eq_or_disjoint hJ hi.1).resolve_left hi.2) xJ
  have eq_ave : ∑ i ∈ (Finset.univ.filter (· ∈ C)).filter (J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = ⨍ y in J, f y := by
    suffices (Finset.univ.filter (· ∈ C)).filter (J = ·) = {J} by simp [this, xJ, ← Grid.mem_def]
    exact subset_antisymm (fun _ h ↦ Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2.symm)
      (fun _ h ↦ by simp [Finset.mem_singleton.mp h, hJ])
  rw [eq0, eq_ave, zero_add]

lemma boundedCompactSupport_approxOnCube {𝕜 : Type*} [RCLike 𝕜] {C : Set (Grid X)} {f : X → 𝕜} :
    BoundedCompactSupport (approxOnCube C f) :=
  BoundedCompactSupport.finset_sum fun J hJ ↦
    BoundedCompactSupport.indicator_of_isBounded_range (by simp) stronglyMeasurable_const
    ((isBounded_iff_subset_ball (c J)).mpr ⟨4 * D ^ s J, Grid_subset_ball⟩) coeGrid_measurable

-- Used in the proof of Lemma 7.1.6
lemma integral_eq_lintegral_approxOnCube {C : Set (Grid X)}
    (hC : C.PairwiseDisjoint fun I ↦ (I : Set X)) {J : Grid X} (hJ : J ∈ C) {f : X → ℂ}
    (hf : BoundedCompactSupport f) : ENNReal.ofReal (∫ y in J, ‖f y‖) =
    ∫⁻ (y : X) in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖₊ := by
  have nonneg : 0 ≤ᶠ[ae (volume.restrict J)] fun y ↦ ‖f y‖ := Filter.Eventually.of_forall (by simp)
  have vol_J_ne_zero := (volume_coeGrid_pos (X := X) (i := J) (defaultD_pos' a)).ne.symm
  have eq : ∫⁻ (y : X) in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖₊ =
      ∫⁻ y in (J : Set X), ENNReal.ofReal (⨍ z in J, ‖f z‖) := by
    refine setLIntegral_congr_fun coeGrid_measurable (Filter.Eventually.of_forall fun y hy ↦ ?_)
    rw [approxOnCube_apply hC _ hJ hy, ENNReal.ofReal]
    · apply congrArg
      have : ‖⨍ y in J, (‖f y‖ : ℂ)‖₊ = ‖⨍ y in J, ‖f y‖‖₊ := by
        convert congrArg (‖·‖₊) <| integral_ofReal (f := (‖f ·‖)) using 1
        simp [average]
      exact this ▸ (Real.toNNReal_eq_nnnorm_of_nonneg <| integral_nonneg (fun y ↦ by simp)).symm
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable.norm.restrict nonneg,
    eq, lintegral_const, average_eq, smul_eq_mul, ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos,
    ENNReal.ofReal_toReal, ofReal_integral_eq_lintegral_ofReal hf.norm.integrable nonneg, mul_comm,
    ← mul_assoc, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    ENNReal.mul_inv_cancel vol_J_ne_zero volume_coeGrid_lt_top.ne, one_mul]
  · simp [volume_coeGrid_lt_top.ne]
  · simpa using ENNReal.toReal_pos vol_J_ne_zero volume_coeGrid_lt_top.ne
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg

lemma approxOnCube_ofReal (C : Set (Grid X)) (f : X → ℝ) (x : X) :
    approxOnCube C (Complex.ofReal <| f ·) x = Complex.ofReal (approxOnCube C f x) := by
  simp_rw [approxOnCube, ofReal_sum]
  refine Finset.sum_congr rfl (fun J _ ↦ ?_)
  by_cases hx : x ∈ (J : Set X)
  · simpa only [indicator_of_mem hx] using integral_ofReal
  · simp only [indicator_of_not_mem hx, ofReal_zero]


/- Start of proof attempt -/
lemma round1_h_ineq (C : Set (Grid X)) (f : X → E') (x : X) :
    ∀ (J : Grid X), ‖⨍ y in J, f y‖ ≤ ⨍ y in J, ‖f y‖ := by
  intro J
  have h11 : volume (J : Set X) ≠ 0 := by
    have h111 : 0 < volume (J : Set X) := volume_coeGrid_pos (X := X) (i := J) (defaultD_pos' a)
    intro h112
    rw [h112] at h111
    <;> norm_num at h111 <;> linarith
  have h12 : volume (J : Set X) ≠ ⊤ := by
    have h121 : volume (J : Set X) < ⊤ := volume_coeGrid_lt_top
    intro h122
    rw [h122] at h121
    <;> norm_num at h121 <;> linarith
  have h1 : 0 < (volume (J : Set X)).toReal := by
    apply ENNReal.toReal_pos
    <;> aesop
  have h3 : ‖∫ y in (J : Set X), f y‖ ≤ ∫ y in (J : Set X), ‖f y‖ := by
    apply norm_integral_le_integral_norm
  have h5 : (volume (J : Set X)).toReal⁻¹ * ‖∫ y in (J : Set X), f y‖ ≤ (volume (J : Set X)).toReal⁻¹ * (∫ y in (J : Set X), ‖f y‖) := by
    have h1' : 0 < (volume (J : Set X)).toReal := h1
    have h51 : 0 < (volume (J : Set X)).toReal⁻¹ := by positivity
    have h52 : ‖∫ y in (J : Set X), f y‖ ≤ ∫ y in (J : Set X), ‖f y‖ := h3
    nlinarith
  have h6 : ‖⨍ y in J, f y‖ = (volume (J : Set X)).toReal⁻¹ * ‖∫ y in (J : Set X), f y‖ := by
    have h61 : 0 < (volume (J : Set X)).toReal := h1
    have h62 : 0 < (volume (J : Set X)).toReal⁻¹ := by positivity
    simp [average_eq, norm_smul, abs_of_pos h62]
    <;> ring
  have h7 : ⨍ y in J, ‖f y‖ = (volume (J : Set X)).toReal⁻¹ * ∫ y in (J : Set X), ‖f y‖ := by
    simp [average_eq]
    <;> ring
  rw [h6, h7]
  linarith

lemma round1_h2 (C : Set (Grid X)) (f : X → E') (x : X) :
    ∀ (J : Grid X), ‖(J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x‖ ≤ (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x := by
  have h_ineq : ∀ (J : Grid X), ‖⨍ y in J, f y‖ ≤ ⨍ y in J, ‖f y‖ := round1_h_ineq C f x
  intro J
  by_cases h : x ∈ (J : Set X)
  · -- Case 1: x ∈ (J : Set X)
    have h21 : (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x = ⨍ y in J, f y := by
      simp [Set.indicator_of_mem h]
    have h22 : (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x = ⨍ y in J, ‖f y‖ := by
      simp [Set.indicator_of_mem h]
    rw [h21, h22]
    exact h_ineq J
  · -- Case 2: x ∉ (J : Set X)
    have h21 : (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x = 0 := by
      simp [Set.indicator_of_not_mem h]
    have h22 : (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x = 0 := by
      simp [Set.indicator_of_not_mem h]
    rw [h21, h22]
    simp

theorem norm_approxOnCube_le_approxOnCube_norm {C : Set (Grid X)} {f : X → E'} {x : X} :
    ‖approxOnCube C f x‖ ≤ approxOnCube C (‖f ·‖) x  := by


  have h2 : ∀ (J : Grid X), ‖(J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x‖ ≤ (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x := 
    round1_h2 C f x
  have h1 : ‖approxOnCube C f x‖ ≤ ∑ J ∈ { p | p ∈ C }, ‖(J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x‖ := by
    apply norm_sum_le
  have h3 : ∑ J ∈ { p | p ∈ C }, ‖(J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x‖ ≤ ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x := by
    apply Finset.sum_le_sum
    intro J _
    exact h2 J
  have h4 : ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y in J, ‖f y‖) x = approxOnCube C (‖f ·‖) x := by
    simp [approxOnCube]
    <;> rfl
  linarith
