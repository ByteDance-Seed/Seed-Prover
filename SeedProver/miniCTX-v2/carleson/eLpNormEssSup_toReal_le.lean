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

/- Start of proof attempt -/
lemma round1_h1 : ∀ (r : ℝ≥0∞), ENNReal.ofReal (r.toReal) ≤ r := by
  intro r
  by_cases h : r = ∞
  · -- Case r = ∞
    rw [h]
    simp
  · -- Case r ≠ ∞
    have h2 : r ≠ ∞ := h
    have h3 : ENNReal.ofReal (r.toReal) = r := by
      simp [ENNReal.ofReal_toReal, h2]
    rw [h3]
    <;> rfl

lemma round1_h4 (f : α → ℝ≥0∞) (μ : Measure α) : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) = ENNReal.ofReal ((f x).toReal) := by
  intro x
  simp [ENNReal.ofReal]
  <;> norm_cast
  <;> simp [Real.norm_eq_abs, abs_of_nonneg]
  <;> norm_num

lemma round1_h5 (f : α → ℝ≥0∞) (μ : Measure α) (h1 : ∀ (r : ℝ≥0∞), ENNReal.ofReal (r.toReal) ≤ r) (h4 : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) = ENNReal.ofReal ((f x).toReal)) : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x := by
  intro x
  have h51 : (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) = ENNReal.ofReal ((f x).toReal) := h4 x
  have h52 : ENNReal.ofReal ((f x).toReal) ≤ f x := h1 (f x)
  rw [h51]
  exact h52

lemma round1_h5' (f : α → ℝ≥0∞) (μ : Measure α) (h5 : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x) : ∀ᵐ x ∂μ, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x := by
  filter_upwards with x
  exact h5 x

lemma round1_h7 (f : α → ℝ≥0∞) (μ : Measure α) (h5' : ∀ᵐ x ∂μ, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x) (h6 : ∀ᵐ x ∂μ, f x ≤ essSup f μ) : ∀ᵐ x ∂μ, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ essSup f μ := by
  filter_upwards [h5', h6] with x h5'x h6x
  exact le_trans h5'x h6x

theorem eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ  := by

  have h1 : ∀ (r : ℝ≥0∞), ENNReal.ofReal (r.toReal) ≤ r := by
    exact round1_h1

  have h4 : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) = ENNReal.ofReal ((f x).toReal) := by
    exact round1_h4 f μ

  have h5 : ∀ x : α, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x := by
    exact round1_h5 f μ h1 h4

  have h5' : ∀ᵐ x ∂μ, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ f x := by
    exact round1_h5' f μ h5

  have h6 : ∀ᵐ x ∂μ, f x ≤ essSup f μ := by
    exact?

  have h7 : ∀ᵐ x ∂μ, (‖(ENNReal.toReal ∘ f) x‖₊ : ℝ≥0∞) ≤ essSup f μ := by
    exact round1_h7 f μ h5' h6

  have h8 : MeasureTheory.eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ essSup f μ := by
    apply MeasureTheory.eLpNormEssSup_lt_top_of_ae_ennnorm_bound
    exact h7

  have h9 : essSup f μ ≤ MeasureTheory.eLpNormEssSup f μ := by
    exact?

  exact le_trans h8 h9
