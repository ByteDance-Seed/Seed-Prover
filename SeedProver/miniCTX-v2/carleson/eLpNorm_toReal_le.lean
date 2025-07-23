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

/- Start of proof attempt -/
lemma round1_eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
  by_cases h : p = ∞
  · -- Case 1: p = ∞
    rw [h]
    simpa using eLpNormEssSup_toReal_le
  · -- Case 2: p ≠ ∞
    have h1 : ∃ (p' : ℝ), 0 ≤ p' ∧ p = ENNReal.ofReal p' := by
      have h2 : p ≠ ∞ := h
      have h3 : (p : ℝ≥0∞) ≠ ∞ := by simpa using h2
      have h4 : ∃ (r : ℝ), 0 ≤ r ∧ p = ENNReal.ofReal r := by
        refine' ⟨(p : ℝ≥0∞).toReal, _⟩
        constructor
        · -- Show 0 ≤ (p : ℝ≥0∞).toReal
          positivity
        · -- Show p = ENNReal.ofReal ((p : ℝ≥0∞).toReal)
          have h5 : (p : ℝ≥0∞) ≠ ∞ := h3
          have h6 : (p : ℝ≥0∞).toReal ≥ 0 := by positivity
          simp [ENNReal.ofReal_toReal, h5]
          <;> aesop
      obtain ⟨r, hr1, hr2⟩ := h4
      refine' ⟨r, hr1, hr2⟩
    obtain ⟨p', hp1, hp2⟩ := h1
    rw [hp2]
    simp only [eLpNorm]
    by_cases h5 : p' ≤ 0
    · -- Case 2.1: p' ≤ 0
      have h6 : p' = 0 := by linarith
      simp [h6]
      <;> norm_num
    · -- Case 2.2: ¬(p' ≤ 0)
      have h9 : ¬(p' ≤ 0) := h5
      simp [h9]
      have h12 : 0 ≤ p' := by linarith
      have h13 : eLpNorm' (ENNReal.toReal ∘ f) p' μ ≤ eLpNorm' f p' μ := eLpNorm'_toReal_le h12
      have h14 : (ENNReal.ofReal p').toReal = p' := by
        rw [ENNReal.toReal_ofReal]
        linarith
      simp only [h14]
      exact h13

theorem eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ  := by

  exact round1_eLpNorm_toReal_le
