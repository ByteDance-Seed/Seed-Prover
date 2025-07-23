-- In carleson/Carleson/ToMathlib/WeakType.lean

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Misc

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

section move

variable {α 𝕜 E : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞}

-- todo: move/rename/and perhaps reformulate in terms of ‖.‖ₑ
lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ :=
  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)

lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ :=
  (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) :
    μ B ≤ μ A := by
  apply measure_mono_ae
  change μ {x | ¬ B x ≤ A x} = 0
  simp only [le_Prop_eq, Classical.not_imp]
  exact h

lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_mono_ae
  apply Eventually.of_forall
  simp [implies_true]

lemma eLpNormEssSup_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ ≤ eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  gcongr
  simp

lemma eLpNorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ = eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_le
  · exact eLpNorm'_toReal_le toReal_nonneg

lemma eLpNorm_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm (ENNReal.toReal ∘ f) p μ = eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_eq hf
  · exact eLpNorm'_toReal_eq hf

end move

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {t s x y : ℝ≥0∞}
  {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) :=
  fun _ _ h ↦ distribution_mono_right h

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  simp_rw [distribution]
  apply measure_mono
  simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
  intro x hx
  exact hx.trans_le enorm_toReal_le

/- Start of proof attempt -/
lemma round1_h1 (f : α → ℝ≥0∞) :
    ∀ x, f x ≠ ∞ → ‖(ENNReal.toReal ∘ f) x‖ₑ = f x := by
  intro x hx
  have h11 : 0 ≤ ENNReal.toReal (f x) := ENNReal.toReal_nonneg
  have h12 : ‖(ENNReal.toReal ∘ f) x‖ₑ = ENNReal.ofReal (ENNReal.toReal (f x)) := by
    simp [Function.comp_apply]
    <;> aesop
  have h13 : ENNReal.ofReal (ENNReal.toReal (f x)) = f x := by
    rw [ENNReal.ofReal_toReal]
    <;> aesop
  rw [h12, h13]

lemma round1_h2 (f : α → ℝ≥0∞) (hf : ∀ᵐ x ∂μ, f x ≠ ∞) (h1 : ∀ x, f x ≠ ∞ → ‖(ENNReal.toReal ∘ f) x‖ₑ = f x) :
    ∀ᵐ x ∂μ, (t < ‖(ENNReal.toReal ∘ f) x‖ₑ ↔ t < f x) := by
  filter_upwards [hf] with x hx
  have h21 : ‖(ENNReal.toReal ∘ f) x‖ₑ = f x := h1 x hx
  constructor
  · -- Assume t < ‖(ENNReal.toReal ∘ f) x‖ₑ, we need to show t < f x
    intro h
    rw [h21] at h
    exact h
  · -- Assume t < f x, we need to show t < ‖(ENNReal.toReal ∘ f) x‖ₑ
    intro h
    rw [h21]
    exact h

lemma round1_h4 (f : α → ℝ≥0∞) (hf : ∀ᵐ x ∂μ, f x ≠ ∞) (h1 : ∀ x, f x ≠ ∞ → ‖(ENNReal.toReal ∘ f) x‖ₑ = f x) :
    μ {x | t < ‖(ENNReal.toReal ∘ f) x‖ₑ} = μ {x | t < f x} := by
  have h2 : ∀ᵐ x ∂μ, (t < ‖(ENNReal.toReal ∘ f) x‖ₑ ↔ t < f x) := round1_h2 f hf h1
  apply measure_congr
  filter_upwards [h2] with x hx
  simpa using hx

lemma round1_h6 (f : α → ℝ≥0∞) :
    distribution f t μ = μ {x | t < f x} := by
  have h61 : ∀ x, ‖f x‖ₑ = f x := by
    intro x
    simp
  have h62 : {x : α | t < ‖f x‖ₑ} = {x : α | t < f x} := by
    ext x
    simp [h61]
    <;> aesop
  simp only [distribution]
  rw [h62]
  <;> aesop

theorem distribution_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    distribution (ENNReal.toReal ∘ f) t μ = distribution f t μ  := by

  have h1 : ∀ x, f x ≠ ∞ → ‖(ENNReal.toReal ∘ f) x‖ₑ = f x := round1_h1 f
  have h4 : μ {x | t < ‖(ENNReal.toReal ∘ f) x‖ₑ} = μ {x | t < f x} := round1_h4 f hf h1
  have h6 : distribution f t μ = μ {x | t < f x} := round1_h6 f
  have h5 : distribution (ENNReal.toReal ∘ f) t μ = μ {x | t < ‖(ENNReal.toReal ∘ f) x‖ₑ} := rfl
  rw [h5, h6]
  exact h4
